module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverFork

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus StatedSp)
open CFSG.ClassicalInvolution.WeakCT (B12 B23 LinearBlockStandardPair)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.SymplecticPilot (suppGL planeCoords)
open CFSG.SeitzReduction.LinearPilot (consecutiveBlock)
open scoped MatrixGroups

section Abstract

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem center_spinGroup_quadPlus_eq_bot' [CharP F 2] {n : ℕ} (hn : 3 ≤ n) :
    center (spinGroup (Spin.quadPlus n F)) = ⊥ := by
  obtain ⟨-, h1, h2⟩ := Spin.spinToStatedProj_quadPlus (n := n) (K := F) hn
  rw [← h2, h1]
  exact CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn
    CharTwo.two_eq_zero

theorem exists_weakCT_spinPlus_of_pieces_two_pow {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) (hF4 : 4 ≤ Nat.card F) (U : Fin n → Subgroup G) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ k, U k)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      U i ≤ centralizer (U j : Set G))
    (hpair : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, F) →* G, θ.ker ≤ center SL(3, F) ∧
      (B12 F).map θ = U i ∧ (B23 F).map θ = U j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* G₀, Function.Surjective Ψ ∧
      center G₀ = (center (spinGroup (Spin.quadPlus n F))).map Ψ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) .POmegaPlus n 2 f := by
  have hle : ∀ k, U k ≤ G₀ := fun k => hG₀ ▸ le_iSup U k
  have hUmap : ∀ k, ((U k).subgroupOf G₀).map G₀.subtype = U k := fun k => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle k)]
  have hgen : ⨆ k, (U k).subgroupOf G₀ = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hG₀.symm
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ (U i).subgroupOf G₀, ∀ b ∈ (U j).subgroupOf G₀, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    have h := mem_centralizer_iff.1 (hcomm i j hij h1 h2 (mem_subgroupOf.1 ha)) (b : G)
      (mem_subgroupOf.1 hb)
    exact Subtype.ext h.symm
  have hpair' : ∀ i j : Fin n, edgeD n i j →
      ∃ W, LinearBlockStandardPair F W ((U i).subgroupOf G₀) ((U j).subgroupOf G₀) := by
    intro i j hij
    obtain ⟨θ, hθker, hθ12, hθ23⟩ := hpair i j hij
    have hθG₀ : ∀ A, θ A ∈ G₀ := by
      intro A
      have hA : θ A ∈ θ.range := ⟨A, rfl⟩
      rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23 (K := F),
        Subgroup.map_sup, hθ12, hθ23] at hA
      exact sup_le (hle i) (hle j) hA
    let θ' : SL(3, F) →* G₀ := θ.codRestrict G₀ hθG₀
    have hθ' : ∀ H : Subgroup SL(3, F), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [Subgroup.map_map]
      rfl
    refine ⟨θ'.range, θ', 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hθker
    · rw [map_conj_one_inv_eq']
      apply Subgroup.map_injective G₀.subtype_injective
      rw [hθ', hθ12, hUmap]
    · rw [map_conj_one_inv_eq']
      apply Subgroup.map_injective G₀.subtype_injective
      rw [hθ', hθ23, hUmap]
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus n 2 f :=
    ⟨Nat.prime_two, hf, hn⟩
  obtain ⟨Ψ, hΨs, -, -, hcen, hmodel, -⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_spinPlus hadm (by omega) hF hF4
      (fun k => (U k).subgroupOf G₀) hgen hcomm' hpair'
  exact ⟨Ψ, hΨs, hcen, hmodel⟩

end Abstract

section Nodes

variable (K : Type) [Field K]

@[expose] noncomputable def siegelNode (n : ℕ) (j : Fin n) : Subgroup (GL (Fin n ⊕ Fin n) K) :=
  (siegelBlockGL K (plusNodeSet n j)).map (MulAut.conj (flipGL K (plusNodeFlip n j))).toMonoidHom

variable {K}

theorem map_flipGL_siegelBlockGL_of_disjoint {m : ℕ} {B P : Finset (Fin m)} (h : Disjoint B P) :
    (siegelBlockGL K B).map (MulAut.conj (flipGL K P)).toMonoidHom = siegelBlockGL K B := by
  have hfix : ∀ x ∈ siegelBlockGL K B, flipGL K P * x * (flipGL K P)⁻¹ = x := by
    intro x hx
    have hsupp := siegelBlockGL_le_suppGL B hx
    apply Units.ext
    ext a b
    rw [flipGL_conj_apply]
    have hfa : ∀ c : Fin m ⊕ Fin m, c ∈ planeCoords B → flipPerm P c = c := by
      intro c hc
      have hi : SymplecticPilot.planeOf c ∉ P := Finset.disjoint_left.1 h hc
      rcases c with i | i
      · have hi' : i ∉ P := hi
        simp [flipPerm_apply, flipPermFun, hi']
      · have hi' : i ∉ P := hi
        simp [flipPerm_apply, flipPermFun, hi']
    by_cases hab : a ∈ planeCoords B ∧ b ∈ planeCoords B
    · rw [hfa a hab.1, hfa b hab.2]
    · have hab' : ¬(flipPerm P a ∈ planeCoords B ∧ flipPerm P b ∈ planeCoords B) := by
        rwa [flipPerm_mem_planeCoords_iff, flipPerm_mem_planeCoords_iff]
      rw [hsupp _ _ hab', hsupp _ _ hab]
      simp only [Matrix.one_apply, (flipPerm P).injective.eq_iff]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change flipGL K P * x * (flipGL K P)⁻¹ ∈ siegelBlockGL K B
    rw [hfix x hx]
    exact hx
  · intro hy
    exact ⟨y, hy, hfix y hy⟩

theorem siegelNode_le_statedOmega [Finite K] (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 2 ≤ n)
    (j : Fin n) : siegelNode K n j ≤ StatedOmega (StatedQuadPlus n K) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 (flipGL_mem_normalizer (F := K) (plusNodeFlip n j)) x).1
    (siegelBlockGL_le_statedOmega hK (two_le_card_plusNodeSet hn j) hx)

theorem plusNodeSet_eq_consecutiveBlock_left {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    plusNodeSet n i = consecutiveBlock n i.val 2 := by
  ext x
  rw [mem_plusNodeSet, LinearPilot.mem_consecutiveBlock]
  unfold edgeD at hij
  have := x.isLt
  have := j.isLt
  omega

theorem plusNodeSet_eq_consecutiveBlock_right {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    plusNodeSet n j = consecutiveBlock n (i.val + 1) 2 := by
  ext x
  rw [mem_plusNodeSet, LinearPilot.mem_consecutiveBlock]
  unfold edgeD at hij
  have := x.isLt
  have := j.isLt
  omega

theorem exists_theta_siegelNode {n : ℕ} {i j : Fin n} (hij : edgeD n i j) :
    ∃ θ : SL(3, K) →* GL (Fin n ⊕ Fin n) K, θ.ker ≤ center SL(3, K) ∧
      (B12 K).map θ = siegelNode K n i ∧ (B23 K).map θ = siegelNode K n j := by
  have ha : i.val + 3 ≤ n := by
    unfold edgeD at hij
    have := j.isLt
    omega
  obtain ⟨hdi, hdj⟩ := disjoint_plusNodeSet_plusNodeFlip hij
  refine ⟨modelTheta K i.val ha (plusNodeFlip n j), fun A hA => ?_, ?_, ?_⟩
  · have h1 : A = 1 := modelTheta_injective i.val ha (plusNodeFlip n j)
      (by rw [MonoidHom.mem_ker.1 hA, map_one])
    rw [h1]
    exact one_mem _
  · rw [map_B12_modelTheta, siegelNode, ← plusNodeSet_eq_consecutiveBlock_left hij,
      map_flipGL_siegelBlockGL_of_disjoint hdi, map_flipGL_siegelBlockGL_of_disjoint hdj]
  · rw [map_B23_modelTheta, siegelNode, ← plusNodeSet_eq_consecutiveBlock_right hij]

theorem siegelNode_le_centralizer [Finite K] (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (h1 : ¬ edgeD n i j) (h2 : ¬ edgeD n j i) :
    siegelNode K n i ≤ centralizer (siegelNode K n j : Set (GL (Fin n ⊕ Fin n) K)) := by
  have hfork : ∀ a b : Fin n, a.val + 2 = n → b.val + 1 = n →
      ∀ x ∈ siegelNode K n a, ∀ y ∈ siegelNode K n b, Commute x y := by
    intro a b ha hb x hx y hy
    have hset : plusNodeSet n a = plusNodeSet n b := by
      ext z
      rw [mem_plusNodeSet, mem_plusNodeSet]
      have := z.isLt
      omega
    have hPa : plusNodeFlip n a = ∅ := by
      ext z
      rw [mem_plusNodeFlip]
      simp only [Finset.notMem_empty, iff_false]
      omega
    have hcard : (plusNodeSet n a).card = 2 :=
      le_antisymm (card_plusNodeSet_le a) (two_le_card_plusNodeSet (by omega) a)
    have hPB : plusNodeSet n a ∩ plusNodeFlip n b = {b} := by
      ext z
      rw [Finset.mem_inter, mem_plusNodeSet, mem_plusNodeFlip, Finset.mem_singleton, Fin.ext_iff]
      have := z.isLt
      omega
    rw [siegelNode, hPa, flipGL_empty, map_conj_one_eq] at hx
    rw [siegelNode, ← hset] at hy
    exact commute_siegelBlockGL_flip hK hcard hPB hx hy
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  by_cases hf1 : i.val + 2 = n ∧ j.val + 1 = n
  · exact (hfork i j hf1.1 hf1.2 x hx y hy).eq.symm
  by_cases hf2 : j.val + 2 = n ∧ i.val + 1 = n
  · exact (hfork j i hf2.1 hf2.2 y hy x hx).eq
  exact (commute_of_mem_flip_siegelBlockGL (disjoint_plusNodeSet hij h1 h2 hf1 hf2) hx hy).eq.symm

theorem iSup_siegelNode_eq_statedOmega [Finite K] [CharP K 2] {n f : ℕ} (hn : 4 ≤ n)
    (hKf : Nat.card K = 2 ^ f) (hK : 4 ≤ Nat.card K) :
    ⨆ j, siegelNode K n j = StatedOmega (StatedQuadPlus n K) := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0, pow_zero] at hKf
    omega
  set X := ⨆ j, siegelNode K n j with hX
  have hle : X ≤ StatedOmega (StatedQuadPlus n K) :=
    iSup_le fun j => siegelNode_le_statedOmega hK (by omega) j
  obtain ⟨Ψ, -, hcen, hmodel⟩ := exists_weakCT_spinPlus_of_pieces_two_pow hn hf hKf hK
    (siegelNode K n) hX (fun i j hij h1 h2 => siegelNode_le_centralizer hK (by omega) hij h1 h2)
    (fun i j hij => exists_theta_siegelNode hij)
  have hcen' : center X = ⊥ := by
    rw [hcen, center_spinGroup_quadPlus_eq_bot' (by omega), Subgroup.map_bot]
  obtain ⟨φ⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hmodel K hKf
  have h1 : Nat.card (X ⧸ center X) = Nat.card X :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcen').trans
      QuotientGroup.quotientBot).toEquiv
  have h2 : Nat.card (X ⧸ center X) = Nat.card (StatedOmega (StatedQuadPlus n K)) :=
    Nat.card_congr φ.toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [← h1, h2])

end Nodes

section Rational

open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ}

@[expose] noncomputable def rationalNode (hn : 1 ≤ n) (j : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  ((siegelNode K n j).subgroupOf (StatedOmega (StatedQuadPlus n K))).map
    (statedOmegaPlusEquiv K n hn).toMonoidHom

theorem iSup_rationalNode {f : ℕ} (hn : 4 ≤ n) (hKf : Nat.card K = 2 ^ f) (hK : 4 ≤ Nat.card K) :
    ⨆ j, rationalNode (K := K) (by omega : 1 ≤ n) j = ⊤ := by
  have hgen : ⨆ j, (siegelNode K n j).subgroupOf (StatedOmega (StatedQuadPlus n K)) = ⊤ := by
    apply Subgroup.map_injective (StatedOmega (StatedQuadPlus n K)).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [subgroupOf_map_subtype]
    rw [iSup_congr fun j => inf_eq_left.mpr (siegelNode_le_statedOmega hK (by omega) j)]
    exact iSup_siegelNode_eq_statedOmega hn hKf hK
  have hmap : ⨆ j, rationalNode (K := K) (by omega : 1 ≤ n) j =
      (⨆ j, (siegelNode K n j).subgroupOf (StatedOmega (StatedQuadPlus n K))).map
        (statedOmegaPlusEquiv K n (by omega)).toMonoidHom := by
    rw [Subgroup.map_iSup]
    rfl
  rw [hmap, hgen, Subgroup.map_top_of_surjective _
    (statedOmegaPlusEquiv K n (by omega)).surjective]

theorem rationalNode_le_centralizer (hn : 1 ≤ n) (j : Fin n) :
    rationalNode (K := K) hn j ≤
      centralizer (plusSignedLevelTorus K (plusNodeSet n j) (plusNodeFlip n j) : Set _) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ hz
  have hz' : _ ∈ frameTorusOf (coordinateQuadPlus n K) (plusFrameLeft n) (plusFrameRight n)
      (signedLevelParam (plusNodeSet n j) (plusNodeFlip n j)) := hz
  rw [(isHypFrame_plus K n).frameTorusOf_eq_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  apply (statedOmegaPlusEquiv K n hn).symm.injective
  rw [map_mul, map_mul]
  change _ * (statedOmegaPlusEquiv K n hn).symm (statedOmegaPlusEquiv K n hn y) =
    (statedOmegaPlusEquiv K n hn).symm (statedOmegaPlusEquiv K n hn y) * _
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [statedOmegaPlusEquiv_symm_frameHom hn s]
  obtain ⟨z, hzB, hzy⟩ := mem_subgroupOf.1 hy
  rw [← hzy]
  change diagOmega K n s * (flipGL K (plusNodeFlip n j) * z * (flipGL K (plusNodeFlip n j))⁻¹) =
    flipGL K (plusNodeFlip n j) * z * (flipGL K (plusNodeFlip n j))⁻¹ * diagOmega K n s
  have hs' : diagOmega K n s = flipGL K (plusNodeFlip n j) *
      diagOmega K n (flipParam K (plusNodeFlip n j) s) * (flipGL K (plusNodeFlip n j))⁻¹ := by
    rw [flipGL_mul_diagOmega_mul_inv, flipParam_flipParam]
  have hc : z * diagOmega K n (flipParam K (plusNodeFlip n j) s) =
      diagOmega K n (flipParam K (plusNodeFlip n j) s) * z := by
    have h1 := mem_centralizer_iff.1 (siegelBlockGL_le_centralizer
      (D := {flipParam K (plusNodeFlip n j) s}) (fun s' hs' i hi l hl => by
        rw [Set.mem_singleton_iff] at hs'
        rw [hs']
        exact hs i hi l hl) hzB) _ ⟨_, rfl, rfl⟩
    exact h1.symm
  rw [hs']
  calc flipGL K (plusNodeFlip n j) * diagOmega K n (flipParam K (plusNodeFlip n j) s) *
        (flipGL K (plusNodeFlip n j))⁻¹ *
        (flipGL K (plusNodeFlip n j) * z * (flipGL K (plusNodeFlip n j))⁻¹)
      = flipGL K (plusNodeFlip n j) * (diagOmega K n (flipParam K (plusNodeFlip n j) s) * z) *
        (flipGL K (plusNodeFlip n j))⁻¹ := by group
    _ = flipGL K (plusNodeFlip n j) * (z * diagOmega K n (flipParam K (plusNodeFlip n j) s)) *
        (flipGL K (plusNodeFlip n j))⁻¹ := by rw [hc]
    _ = _ := by group

theorem commutator_rationalNode (hn : 2 ≤ n) (hK : 4 ≤ Nat.card K) (j : Fin n) :
    ⁅rationalNode (K := K) (by omega : 1 ≤ n) j, rationalNode (K := K) (by omega : 1 ≤ n) j⁆ =
      rationalNode (K := K) (by omega : 1 ≤ n) j := by
  have hperf : ⁅siegelNode K n j, siegelNode K n j⁆ = siegelNode K n j := by
    rw [siegelNode, ← Subgroup.map_commutator,
      commutator_siegelBlockGL hK (two_le_card_plusNodeSet hn j)]
  rw [rationalNode, ← Subgroup.map_commutator,
    commutator_subgroupOf_eq_of_le_perfect (siegelNode_le_statedOmega hK hn j) hperf]

theorem le_iSup_plusNode (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {f : ℕ}
    (hn : 4 ≤ n) (hKf : Nat.card K = 2 ^ f) (hK : 4 ≤ Nat.card K) :
    L ≤ ⨆ j, plusNode e j := by
  have h1 : modelToG e (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))) ≤
      ⨆ j, plusNode e j := by
    rw [← iSup_rationalNode hn hKf hK, UnitaryPilot.modelToG_iSup]
    exact iSup_mono fun j => UnitaryPilot.modelToG_le_centralizerPerfectCore e
      (rationalNode_le_centralizer _ j) (commutator_rationalNode (by omega) hK j)
  rwa [UnitaryPilot.modelToG_top e] at h1

end Rational

end CFSG.SeitzReduction.OmegaPilot
