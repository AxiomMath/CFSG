module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeHeisSL3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary
public import CFSG.LieType.Chevalley.E6GraphLeviTheta
public import CFSG.RankThree.PartOne.KLAY.RootSL2

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.RankThree.PartOne.KLAY
open CFSG.RankThree.Classical2 (fixSubgroup mem_fixSubgroup unitarySet statedSUToSL
  mem_range_statedSUToSL_iff coe_inv_eq_nonsing_inv)

open CFSG.RankThree.E6 (chainRoot)

open scoped MatrixGroups

set_option linter.unusedSectionVars false

@[expose] def e6LinePair : Fin 3 → (Fin Tag.E6.rank → ℤ) × (Fin Tag.E6.rank → ℤ)
  | 0 => (![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0])
  | 1 => (![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1])
  | 2 => (![0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 2, 1])

theorem e6LineRoots_eq_pair (i : Fin 3) :
    e6LineRoots i = e6A2Roots (e6LinePair i).1 (e6LinePair i).2 := by
  fin_cases i <;> rfl

theorem e6LinePair_iform : ∀ i : Fin 3,
    iform (e6LinePair i).2 (e6LinePair i).2 = iform (e6LinePair i).1 (e6LinePair i).1 ∧
      2 * iform (e6LinePair i).1 (e6LinePair i).2 = - iform (e6LinePair i).1 (e6LinePair i).1 := by
  decide +kernel

section ActSub

variable {τ : Tag} {K : Type} [Field K]

theorem conjSL_diagGL3 (d : Fin 3 → Kˣ) (s : SpecialLinearGroup (Fin 3) K) :
    conjSL (diagGL3 d) s = conjDiag3 d s :=
  Subtype.ext rfl

@[expose] def frameActSub (ρ : SpecialLinearGroup (Fin 3) K →* ModGL τ K) :
    Subgroup (ModGL τ K) where
  carrier := {g | ∃ γ : GL (Fin 3) K, ∀ s, g * ρ s * g⁻¹ = ρ (conjSL γ s)}
  one_mem' := ⟨1, fun s => by simp⟩
  mul_mem' := by
    rintro a b ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
    refine ⟨γ₁ * γ₂, fun s => ?_⟩
    calc a * b * ρ s * (a * b)⁻¹ = a * (b * ρ s * b⁻¹) * a⁻¹ := by group
      _ = ρ (conjSL (γ₁ * γ₂) s) := by rw [h₂, h₁, map_mul]; rfl
  inv_mem' := by
    rintro a ⟨γ, h⟩
    refine ⟨γ⁻¹, fun s => ?_⟩
    have h1 := h (conjSL γ⁻¹ s)
    have h2 : conjSL γ (conjSL γ⁻¹ s) = s := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [h2] at h1
    rw [inv_inv, ← h1]
    group

theorem mem_frameActSub {ρ : SpecialLinearGroup (Fin 3) K →* ModGL τ K} {g : ModGL τ K} :
    g ∈ frameActSub ρ ↔ ∃ γ : GL (Fin 3) K, ∀ s, g * ρ s * g⁻¹ = ρ (conjSL γ s) :=
  Iff.rfl

end ActSub

section Frames


theorem isA2Pair_e6LinePair (i : Fin 3) :
    IsA2Pair (τ := Tag.E6) (e6LinePair i).1 (e6LinePair i).2 := by
  have hmem : ∀ x ∈ e6A2Roots (e6LinePair i).1 (e6LinePair i).2, IsRoot Tag.E6 x := fun x hx =>
    isRoot_of_mem_e6LineRoots (i := i) (by rw [e6LineRoots_eq_pair]; exact hx)
  have hform := e6LinePair_iform i
  refine ⟨hmem _ ?_, hmem _ ?_, hmem _ ?_, hform.1, hform.2⟩ <;> simp [e6A2Roots]

theorem frame_roots_eq {u w : Fin Tag.E6.rank → ℤ}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hneg : ∀ a b, σ b a = -σ a b) (hadd : ∀ a b c, σ a b + σ b c = σ a c)
    (h01 : σ 0 1 = u) (h12 : σ 1 2 = w) :
    {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ a b} = (e6A2Roots u w : Set (Fin Tag.E6.rank → ℤ)) := by
  have h02 : σ 0 2 = u + w := by rw [← hadd 0 1 2, h01, h12]
  have h10 : σ 1 0 = -u := by rw [hneg 0 1, h01]
  have h21 : σ 2 1 = -w := by rw [hneg 1 2, h12]
  have h20 : σ 2 0 = -(u + w) := by rw [hneg 0 2, h02]
  ext r
  simp only [Set.mem_setOf_eq, e6A2Roots, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    fin_cases a <;> fin_cases b <;>
      first | exact absurd rfl hab | simp [h01, h12, h02, h10, h21, h20]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, h01.symm⟩
    · exact ⟨1, 2, by decide, h12.symm⟩
    · exact ⟨0, 2, by decide, h02.symm⟩
    · exact ⟨1, 0, by decide, h10.symm⟩
    · exact ⟨2, 1, by decide, h21.symm⟩
    · exact ⟨2, 0, by decide, h20.symm⟩

theorem exists_frame_e6Line (K : Type) [Field K] (i : Fin 3) :
    ∃ (ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K)
      (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsA2Frame ρ σ ∧ ρ.range = e6LineFactor K i := by
  obtain ⟨v, h1, h2⟩ := exists_weyl_a2Pair_E6 (isA2Pair_e6LinePair i)
  have hfr := (e6Std_frame K).transport v
  refine ⟨_, _, hfr, ?_⟩
  rw [hfr.range, e6LineFactor, e6LineRoots_eq_pair]
  congr 1
  refine frame_roots_eq (hneg := hfr.neg) (hadd := hfr.add) ?_ ?_
  · show v • chainRoot (CFSG.RankThree.E6.chain13) 0 1 = _
    rw [chainRoot13_zero_one]
    exact h1
  · show v • chainRoot (CFSG.RankThree.E6.chain13) 1 2 = _
    rw [chainRoot13_one_two]
    exact h2

theorem rootDiagUnit_mem_frameActSub {τ : Tag} {K : Type} [Field K]
    {ρ : SpecialLinearGroup (Fin 3) K →* ModGL τ K}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsA2Frame ρ σ) (b : Fin τ.rank → Kˣ) :
    rootDiagUnit τ b ∈ frameActSub ρ :=
  ⟨diagGL3 (fun j => rootChar b (σ j 0)), fun s => by
    rw [conjSL_diagGL3]
    exact hfr.torus b s⟩

theorem exists_lineFrames (K : Type) [Field K] :
    ∃ ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K,
      (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = e6LineFactor K i) ∧
        ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i) := by
  choose ρ σ hfr hrange using exists_frame_e6Line K
  exact ⟨ρ, fun i => (hfr i).injective, hrange, fun i b => rootDiagUnit_mem_frameActSub (hfr i) b⟩

theorem torusGroup_le_range_rootDiagUnitHom_E6 {K : Type} [Field K] :
    torusGroup Tag.E6 K ≤ (rootDiagUnitHom Tag.E6 K).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, u⟩, rfl⟩
  exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩

theorem toralRootGroup_le_frameActSub {K : Type} [Field K] {ω : Kˣ} (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) {ρ : Fin 3 → SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    (hrange : ∀ i, (ρ i).range = e6LineFactor K i)
    (hd : ∀ i b, rootDiagUnit Tag.E6 b ∈ frameActSub (ρ i)) (i : Fin 3) :
    toralRootGroup Tag.E6 K (e6LineChar ω) ≤ frameActSub (ρ i) := by
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨b, rfl⟩ := torusGroup_le_range_rootDiagUnitHom_E6 hg
    exact hd i b
  · rw [e6Line_kernel h3 h1, rootSpan_eq_iSup_e6LineFactor]
    refine iSup_le fun j => ?_
    rw [← hrange j]
    rintro _ ⟨A, rfl⟩
    rcases eq_or_ne j i with rfl | hji
    · refine ⟨SpecialLinearGroup.toGL A, fun s => ?_⟩
      rw [conjSL_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]
    · refine ⟨1, fun s => ?_⟩
      rw [map_one, MulAut.one_apply]
      have hx : ρ j A ∈ e6LineFactor K j := (hrange j) ▸ ⟨A, rfl⟩
      have hy : ρ i s ∈ e6LineFactor K i := (hrange i) ▸ ⟨s, rfl⟩
      exact mul_inv_eq_iff_eq_mul.2 (e6LineFactor_commute hji hx hy)

end Frames

section OriginalJ


variable {Ω : Type} [Field Ω]

theorem e6BlockSL3_bound : 0 + 3 ≤ 6 := by omega

@[expose] def e6BlockSL3 (Ω : Type) [Field Ω] : SL(3, Ω) →* SL(6, Ω) :=
  CFSG.ClassicalInvolution.WeakCT.blockSL Ω 6 3 0 e6BlockSL3_bound

abbrev e6Realize (h2 : (2 : Ω) = 0) : SL(6, Ω) →* ModGL Tag.E6 Ω :=
  E6GraphLevi.realize h2

abbrev e6TwistHom (σ : Ω →+* Ω) : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  twistHom TwistTag.E6 Ω σ

theorem coe_e6BlockSL3_reindex (P : SL(3, Ω)) :
    ((e6BlockSL3 Ω P : SL(6, Ω)) : Matrix (Fin 6) (Fin 6) Ω) =
      Matrix.reindex (finSumFinEquiv (m := 3) (n := 3))
        (finSumFinEquiv (m := 3) (n := 3))
        (Matrix.fromBlocks (P : Matrix (Fin 3) (Fin 3) Ω)
          (0 : Matrix (Fin 3) (Fin 3) Ω) (0 : Matrix (Fin 3) (Fin 3) Ω)
          (1 : Matrix (Fin 3) (Fin 3) Ω)) := by
  have h0 : (finSumFinEquiv (m := 3) (n := 3)).symm (0 : Fin 6) = Sum.inl 0 := by decide
  have h1 : (finSumFinEquiv (m := 3) (n := 3)).symm (1 : Fin 6) = Sum.inl 1 := by decide
  have h2 : (finSumFinEquiv (m := 3) (n := 3)).symm (2 : Fin 6) = Sum.inl 2 := by decide
  have h3 : (finSumFinEquiv (m := 3) (n := 3)).symm (3 : Fin 6) = Sum.inr 0 := by decide
  have h4 : (finSumFinEquiv (m := 3) (n := 3)).symm (4 : Fin 6) = Sum.inr 1 := by decide
  have h5 : (finSumFinEquiv (m := 3) (n := 3)).symm (5 : Fin 6) = Sum.inr 2 := by decide
  simp only [e6BlockSL3, CFSG.ClassicalInvolution.WeakCT.coe_blockSL, Matrix.reindex_apply]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
      h0, h1, h2, h3, h4, h5, CFSG.ClassicalInvolution.Phan.blockMat_apply]

@[expose] def e6FirstBlockRealize (h2 : (2 : Ω) = 0) : SL(3, Ω) →* ModGL Tag.E6 Ω :=
  (e6Realize h2).comp (e6BlockSL3 Ω)

def firstA2Chain : Fin 2 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 0 1, Pi.single 2 1]

def firstA2Index (c : Fin 2) : Fin 5 := ⟨c, by omega⟩

theorem firstA2Chain_eq_single_pathIdx (c : Fin 2) :
    firstA2Chain c = Pi.single (E6GraphLevi.pathIdx (firstA2Index c)) 1 := by
  fin_cases c <;> ext i <;> fin_cases i <;>
    simp [firstA2Chain, firstA2Index, E6GraphLevi.pathIdx, E6GraphHighestRoot.a5Path,
      E6GraphHighestRoot.e6Idx] <;> rfl

theorem firstBlockRealize_comp_blockSL2 (h2 : (2 : Ω) = 0) (c : Fin 2) :
    (e6FirstBlockRealize h2).comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c) =
      rootSL2 Tag.E6 Ω (firstA2Chain c) := by
  have hcomp : (e6BlockSL3 Ω).comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c) =
      CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 5 (firstA2Index c) := by
    simp only [e6BlockSL3, CFSG.ClassicalInvolution.WeakCT.blockSL2]
    rw [CFSG.ClassicalInvolution.WeakCT.blockSL_comp]
    congr 1
    simp [firstA2Index]
  have hcomp' : ∀ A : SL2 Ω,
      e6BlockSL3 Ω (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c A) =
        CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 5 (firstA2Index c) A :=
    fun A => DFunLike.congr_fun hcomp A
  have hφ : (e6FirstBlockRealize h2).comp (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c) =
      simpleRootSL2 Tag.E6 Ω (E6GraphLevi.pathIdx (firstA2Index c)) := by
    refine eq_simpleRootSL2 (E6GraphLevi.pathIdx (firstA2Index c)) ?_ ?_
    · intro t
      change E6GraphLevi.realize h2
        (e6BlockSL3 Ω (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c (uSL t))) =
        xUnit TwistTag.E6.tag Ω (E6GraphLevi.pathIdx (firstA2Index c)) t
      rw [hcomp' (uSL t)]
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.blockSL2_uSL_eq,
        E6GraphLevi.realize_x]
    · intro t
      change E6GraphLevi.realize h2
        (e6BlockSL3 Ω (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c (vSL t))) =
        yUnit TwistTag.E6.tag Ω (E6GraphLevi.pathIdx (firstA2Index c)) t
      rw [hcomp' (vSL t)]
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.blockSL2_vSL_eq,
        E6GraphLevi.realize_y]
  rw [hφ, ← CFSG.RankThree.PartOne.KLAY.rootSL2_single (τ := Tag.E6) (K := Ω)
    (i := E6GraphLevi.pathIdx (firstA2Index c))]
  rw [firstA2Chain_eq_single_pathIdx]
  rfl

theorem e6FirstBlockRealize_range (h2 : (2 : Ω) = 0) :
    (e6FirstBlockRealize h2).range = e6LineFactor Ω 0 := by
  have hβ : ∀ c : Fin 2, IsRoot Tag.E6 (firstA2Chain c) := by
    intro c
    fin_cases c
    · simpa [firstA2Chain] using isRoot_single Tag.E6 (0 : Fin Tag.E6.rank)
    · simpa [firstA2Chain] using isRoot_single Tag.E6 (2 : Fin Tag.E6.rank)
  have hG : ∀ c d : Fin 2, iform (firstA2Chain c) (firstA2Chain d) = chainGram c d := by
    decide +kernel
  have hψ : ∀ c : Fin 2, (e6FirstBlockRealize h2).comp
      (CFSG.ClassicalInvolution.WeakCT.blockSL2 Ω 2 c) =
      rootSL2 Tag.E6 Ω (firstA2Chain c) :=
    fun c => firstBlockRealize_comp_blockSL2 h2 c
  have hfr : IsSLFrame (e6FirstBlockRealize h2) (chainσ firstA2Chain) :=
    isSLFrame_chainHom (τ := Tag.E6) (L := Ω) (m := 2) (Or.inr (Or.inl rfl)) hβ hG hψ
  rw [hfr.range]
  change rootSpan Tag.E6 Ω (frameRoots (chainσ firstA2Chain)) =
    rootSpan Tag.E6 Ω (e6LineRoots 0 : Set (Fin Tag.E6.rank → ℤ))
  congr 1
  rw [e6LineRoots_eq_pair]
  exact frame_roots_eq (σ := chainσ firstA2Chain) (u := (e6LinePair 0).1) (w := (e6LinePair 0).2)
    (hneg := chainσ_neg firstA2Chain) (hadd := chainσ_add firstA2Chain)
    (by ext i; fin_cases i <;> decide +kernel)
    (by ext i; fin_cases i <;> decide +kernel)

theorem e6FirstBlockRealize_injective (h2 : (2 : Ω) = 0) :
    Function.Injective (e6FirstBlockRealize h2) := by
  intro P Q hPQ
  have hker : P * Q⁻¹ ∈ (e6FirstBlockRealize h2).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hPQ, mul_inv_cancel]
  have hkerR : e6BlockSL3 Ω (P * Q⁻¹) ∈ (E6GraphLevi.realize h2).ker := by
    rw [MonoidHom.mem_ker] at hker ⊢
    change e6FirstBlockRealize h2 (P * Q⁻¹) = 1
    exact hker
  obtain ⟨l, -, hl⟩ := (E6GraphLevi.mem_ker_realize h2 _).1 hkerR
  have h55 : (1 : Ω) = l := by
    have h := congrFun (congrFun hl 5) 5
    simp only [e6BlockSL3, CFSG.ClassicalInvolution.WeakCT.coe_blockSL] at h
    rw [CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left
      (m := 6) (k := 3) (i := 0)
      (A := ((P * Q⁻¹ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω))
      (a := (5 : Fin 6)) (ha := by omega)] at h
    simpa [Matrix.scalar_apply] using h
  have hb0 : e6BlockSL3 Ω (P * Q⁻¹) = 1 := by
    apply Subtype.ext
    rw [hl, ← h55]
    simp
  have hPQinv : P * Q⁻¹ = 1 := by
    apply CFSG.ClassicalInvolution.WeakCT.blockSL_injective (h := e6BlockSL3_bound)
    simpa only [e6BlockSL3, map_one] using hb0
  rwa [mul_inv_eq_one] at hPQinv

@[expose] def e6IdentityFormFrobenius (h2 : (2 : Ω) = 0) (σQ : Ω ≃+* Ω)
    (J6 : SL(6, Ω)) (dθ : ModGL Tag.E6 Ω) : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (dθ * e6Realize h2 J6)).toMonoidHom.comp (e6TwistHom σQ.toRingHom)

theorem coe_unitaryTwist (σQ : Ω ≃+* Ω) (Y : SL(6, Ω)) :
    ((E6GraphLevi.unitaryTwist σQ.toRingHom Y : SL(6, Ω)) :
      Matrix (Fin 6) (Fin 6) Ω) =
      E6GraphLevi.antiId Ω *
        ((((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)⁻¹)ᵀ) *
        E6GraphLevi.antiId Ω := by
  simp only [E6GraphLevi.unitaryTwist, MonoidHom.comp_apply,
    E6GraphLevi.coe_graphSL, CFSG.RankThree.Classical2.coe_inv_eq_nonsing_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

theorem antiId_conj_antiId (N : Matrix (Fin 6) (Fin 6) Ω) :
    E6GraphLevi.antiId Ω *
        (E6GraphLevi.antiId Ω * N * E6GraphLevi.antiId Ω) *
        E6GraphLevi.antiId Ω = N := by
  calc E6GraphLevi.antiId Ω *
        (E6GraphLevi.antiId Ω * N * E6GraphLevi.antiId Ω) *
        E6GraphLevi.antiId Ω =
      (E6GraphLevi.antiId Ω * E6GraphLevi.antiId Ω) * N *
        (E6GraphLevi.antiId Ω * E6GraphLevi.antiId Ω) := by
          simp only [Matrix.mul_assoc]
    _ = N := by rw [E6GraphLevi.antiId_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem e6IdentityFormFrobenius_realize (h2 : (2 : Ω) = 0) (σQ : Ω ≃+* Ω)
    {J6 : SL(6, Ω)} (hJ6 : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθ : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range) (Y : SL(6, Ω)) :
    e6IdentityFormFrobenius h2 σQ J6 dθ (e6Realize h2 Y) =
      e6Realize h2 (stdUnitaryEquiv (ν := 6) σQ Y) := by
  have hJ : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω := hJ6
  have hJs : J6 * J6 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hJ, E6GraphLevi.antiId_mul_self,
      Matrix.SpecialLinearGroup.coe_one]
  have hJinv : J6⁻¹ = J6 := inv_eq_of_mul_eq_one_right hJs
  let dθT : ModGL TwistTag.E6.tag Ω := dθ
  set ψ := E6GraphLevi.realize h2 with hψdef
  have hcomm : ∀ Z : SL(6, Ω), dθT * ψ Z = ψ Z * dθT := by
    intro Z
    have hZ : ψ Z ∈ subsystemGroup TwistTag.E6.tag Ω E6GraphLevi.setA := by
      rw [← E6GraphLevi.range_realize h2]
      exact ⟨Z, rfl⟩
    have hcent := E6GraphLevi.subsystemGroup_le_centralizer_thetaSL2 (E := Ω) h2 hZ
    have hdθT : dθT ∈ (E6GraphLevi.thetaSL2 Ω).range := hdθ
    exact (Subgroup.mem_centralizer_iff.mp hcent) dθT hdθT
  have hUmat := coe_unitaryTwist (Ω := Ω) σQ Y
  have hSmat : ((stdUnitaryEquiv (ν := 6) σQ Y : SL(6, Ω)) :
      Matrix (Fin 6) (Fin 6) Ω) =
      (((Y : Matrix (Fin 6) (Fin 6) Ω).map σQ.toRingHom)⁻¹)ᵀ := by
    rw [stdUnitaryEquiv_apply, coe_stdUnitary]
  have hmatSL : J6 * E6GraphLevi.unitaryTwist σQ.toRingHom Y * J6 =
      stdUnitaryEquiv (ν := 6) σQ Y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hUmat, hSmat, hJ]
    exact antiId_conj_antiId _
  have hJcomm : Commute dθT (ψ J6) := hcomm J6
  have hUcomm : Commute dθT (ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y)) :=
    hcomm (E6GraphLevi.unitaryTwist σQ.toRingHom Y)
  have hXcomm : Commute dθT
      (ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹) :=
    (hJcomm.mul_right hUcomm).mul_right hJcomm.inv_right
  have hconj : (dθT * ψ J6) * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) *
      (dθT * ψ J6)⁻¹ =
        ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹ := by
    calc (dθT * ψ J6) * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (dθT * ψ J6)⁻¹ =
          dθT * (ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹) * dθT⁻¹ := by
            group
      _ = (ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹) * dθT * dθT⁻¹ := by
            rw [hXcomm.eq]
      _ = ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹ := by group
  have hone : ψ J6 * ψ (E6GraphLevi.unitaryTwist σQ.toRingHom Y) * (ψ J6)⁻¹ =
      ψ (stdUnitaryEquiv (ν := 6) σQ Y) := by
    rw [← map_inv, ← map_mul, ← map_mul, hJinv, hmatSL]
  change (dθT * ψ J6) * twistHom TwistTag.E6 Ω σQ.toRingHom (ψ Y) * (dθT * ψ J6)⁻¹ =
    ψ (stdUnitaryEquiv (ν := 6) σQ Y)
  rw [E6GraphLevi.twistHom_realize]
  rw [hconj, hone]

theorem stdUnitaryEquiv_blockSL (σQ : Ω ≃+* Ω) (P : SL(3, Ω)) :
    stdUnitaryEquiv (ν := 6) σQ (e6BlockSL3 Ω P) =
      e6BlockSL3 Ω (stdUnitaryEquiv (ν := 3) σQ P) := by
  have hstd : ∀ (m : Nat) (X : SL(m, Ω)), stdUnitaryEquiv (ν := m) σQ X =
      CFSG.ClassicalInvolution.WeakCT.invTransposeSL m
        (CFSG.ClassicalInvolution.WeakCT.fieldAutSL σQ m X) := by
    intro m X
    apply Subtype.ext
    rw [stdUnitaryEquiv_apply, stdUnitary, MonoidHom.comp_apply,
      CFSG.RankThree.Classical2.coe_invTransposeSL,
      CFSG.ClassicalInvolution.WeakCT.coe_invTransposeSL]
    rfl
  rw [hstd 6, hstd 3]
  simp only [e6BlockSL3]
  rw [CFSG.ClassicalInvolution.WeakCT.fieldAutSL_blockSL (ψ := σQ)
    (m := 6) (k := 3) (i := 0) (h := e6BlockSL3_bound) P]
  rw [CFSG.ClassicalInvolution.WeakCT.invTransposeSL_blockSL (h := e6BlockSL3_bound)]

theorem e6IdentityFormFrobenius_firstBlockRealize (h2 : (2 : Ω) = 0) (σQ : Ω ≃+* Ω)
    {J6 : SL(6, Ω)} (hJ6 : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθ : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range) (P : SL(3, Ω)) :
    e6IdentityFormFrobenius h2 σQ J6 dθ (e6FirstBlockRealize h2 P) =
      e6FirstBlockRealize h2 (stdUnitaryEquiv (ν := 3) σQ P) := by
  change e6IdentityFormFrobenius h2 σQ J6 dθ (e6Realize h2 (e6BlockSL3 Ω P)) =
    e6Realize h2 (e6BlockSL3 Ω (stdUnitaryEquiv (ν := 3) σQ P))
  rw [e6IdentityFormFrobenius_realize h2 σQ hJ6 hdθ (e6BlockSL3 Ω P)]
  rw [stdUnitaryEquiv_blockSL]

theorem stdUnitaryEquiv_eq_self_iff_mem_range_statedSUToSL {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (F : Subfield Ω) (hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (ℓ ^ f) ^ 2) (σQ : Ω ≃+* Ω)
    (hσ : ∀ a, σQ a = a ^ (ℓ ^ f)) (P : SL(3, Ω)) :
    stdUnitaryEquiv (ν := 3) σQ P = P ↔
      P ∈ (statedSUToSL F 3 (ℓ ^ f)).range := by
  rw [← mem_fixSubgroup]
  rw [mem_fixSubgroup_stdUnitaryEquiv_iff σQ hσ P,
    mem_range_statedSUToSL_iff hℓ F hF hFcard (by norm_num : 1 ≤ 3) P]

theorem e6LineFactor_inf_eq_range_of_fixed (h2 : (2 : Ω) = 0) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (F : Subfield Ω) (hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (ℓ ^ f) ^ 2) (σQ : Ω ≃+* Ω)
    (hσ : ∀ a, σQ a = a ^ (ℓ ^ f)) {J6 : SL(6, Ω)}
    (hJ6 : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθ : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range)
    {Γ : Subgroup (ModGL Tag.E6 Ω)}
    (hfix : ∀ g ∈ Γ, e6IdentityFormFrobenius h2 σQ J6 dθ g = g)
    (hΓ : ((e6FirstBlockRealize h2).comp (statedSUToSL F 3 (ℓ ^ f))).range ≤ Γ) :
    e6LineFactor Ω 0 ⊓ Γ =
      ((e6FirstBlockRealize h2).comp (statedSUToSL F 3 (ℓ ^ f))).range := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgC0, hgΓ⟩ := hg
    rw [← e6FirstBlockRealize_range h2, MonoidHom.mem_range] at hgC0
    obtain ⟨P, rfl⟩ := hgC0
    have hFW : e6IdentityFormFrobenius h2 σQ J6 dθ (e6FirstBlockRealize h2 P) =
        e6FirstBlockRealize h2 P := hfix _ hgΓ
    rw [e6IdentityFormFrobenius_firstBlockRealize h2 σQ hJ6 hdθ P] at hFW
    have hPfix : stdUnitaryEquiv (ν := 3) σQ P = P :=
      e6FirstBlockRealize_injective h2 hFW
    have hPmem : P ∈ (statedSUToSL F 3 (ℓ ^ f)).range :=
      (stdUnitaryEquiv_eq_self_iff_mem_range_statedSUToSL hℓ F hF hFcard σQ hσ P).1 hPfix
    rw [MonoidHom.mem_range]
    obtain ⟨s, rfl⟩ := hPmem
    exact ⟨s, rfl⟩
  · intro g hg
    refine ⟨?_, hΓ hg⟩
    rw [MonoidHom.mem_range] at hg
    obtain ⟨s, rfl⟩ := hg
    rw [← e6FirstBlockRealize_range h2]
    exact ⟨statedSUToSL F 3 (ℓ ^ f) s, rfl⟩

theorem e6OriginalJ_map_eq_inf (h2 : (2 : Ω) = 0) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (F : Subfield Ω) (hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c)
    (hFcard : Nat.card F = (ℓ ^ f) ^ 2) (σQ : Ω ≃+* Ω)
    (hσ : ∀ a, σQ a = a ^ (ℓ ^ f)) {J6 : SL(6, Ω)}
    (hJ6 : (J6 : Matrix (Fin 6) (Fin 6) Ω) = E6GraphLevi.antiId Ω)
    {dθ : ModGL Tag.E6 Ω} (hdθ : dθ ∈ (E6GraphLevi.thetaSL2 Ω).range)
    {H : Type} [Group H] {J : Subgroup H}
    (Φ3 : CFSG.Open.StatedSU 3 (ℓ ^ f) F →* H) (hΦ3 : Φ3.range = J)
    (iotaT : H →* ModGL Tag.E6 Ω)
    (hdiag : ∀ s, iotaT (Φ3 s) =
      e6FirstBlockRealize h2 (statedSUToSL F 3 (ℓ ^ f) s))
    {Γ : Subgroup (ModGL Tag.E6 Ω)} (hJΓ : J.map iotaT ≤ Γ)
    (hfix : ∀ g ∈ Γ, e6IdentityFormFrobenius h2 σQ J6 dθ g = g) :
    J.map iotaT = e6LineFactor Ω 0 ⊓ Γ := by
  have hcomp : iotaT.comp Φ3 =
      (e6FirstBlockRealize h2).comp (statedSUToSL F 3 (ℓ ^ f)) :=
    MonoidHom.ext hdiag
  have hJmap : J.map iotaT =
      ((e6FirstBlockRealize h2).comp (statedSUToSL F 3 (ℓ ^ f))).range := by
    rw [← hΦ3, MonoidHom.map_range, hcomp]
  have hΓ' : ((e6FirstBlockRealize h2).comp (statedSUToSL F 3 (ℓ ^ f))).range ≤ Γ := by
    rw [← hJmap]
    exact hJΓ
  have hinter := e6LineFactor_inf_eq_range_of_fixed h2 hℓ F hF hFcard σQ hσ hJ6 hdθ hfix hΓ'
  rw [hJmap, hinter]

end OriginalJ

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
