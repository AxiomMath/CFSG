module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Frame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Spin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10T1Root

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open scoped MatrixGroups

theorem center_eq_bot_of_isSimpleGroup_of_exists {T : Type} [Group T] [IsSimpleGroup T]
    (h : ∃ x y : T, x * y ≠ y * x) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    exact hxy (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y) x)

theorem exists_quotient_of_frame {S G P : Type} [Group S] [Group G] [Group P] (Ψ : S →* G)
    {W : Subgroup G} (hW : Ψ.range = W) (hker : Ψ.ker ≤ Subgroup.center S) (π : S →* P)
    (hπ : Function.Surjective π) (hπker : π.ker = Subgroup.center S)
    (hP : Subgroup.center P = ⊥) :
    ∃ θ : W →* P, Function.Surjective θ ∧ θ.ker = Subgroup.center W ∧
      ∀ x (hx : Ψ x ∈ W), θ ⟨Ψ x, hx⟩ = π x := by
  subst hW
  have hle : Ψ.rangeRestrict.ker ≤ π.ker := by
    rw [MonoidHom.ker_rangeRestrict, hπker]
    exact hker
  let e := QuotientGroup.quotientKerEquivOfSurjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  let θ : Ψ.range →* P := (QuotientGroup.lift _ π hle).comp e.symm.toMonoidHom
  have hθ : ∀ x, θ (Ψ.rangeRestrict x) = π x := by
    intro x
    have h1 : e.symm (Ψ.rangeRestrict x) = (x : S ⧸ Ψ.rangeRestrict.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift _ π hle (e.symm (Ψ.rangeRestrict x)) = π x
    rw [h1, QuotientGroup.lift_mk]
  refine ⟨θ, fun z => ?_, ?_, fun x _ => hθ x⟩
  · obtain ⟨x, rfl⟩ := hπ z
    exact ⟨_, hθ x⟩
  · ext w
    obtain ⟨x, rfl⟩ := Ψ.rangeRestrict_surjective w
    rw [MonoidHom.mem_ker, hθ]
    constructor
    · intro h
      have hx : x ∈ Subgroup.center S := by
        rw [← hπker]
        exact h
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro w'
      obtain ⟨x', rfl⟩ := Ψ.rangeRestrict_surjective w'
      rw [← map_mul, ← map_mul, hx x']
    · intro h
      have h1 : π x ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨x', rfl⟩ := hπ z
        rw [← hθ, ← hθ, ← map_mul θ, ← map_mul θ, Subgroup.mem_center_iff.mp h]
      rw [hP] at h1
      exact h1

section Spin

variable {n : ℕ} (K : Type) [Field K]

@[expose] def spinProj (hn : 3 ≤ n) :
    spinGroup (quadPlus n K) →* matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).toMonoidHom.comp
    (spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn))

@[expose] def spinDerived (hn : 3 ≤ n) (x : spinGroup (quadPlus n K)) :
    matrixDerived (coordinateQuadPlus n K) :=
  statedDerivedReindexEquiv (plusIndexEquiv n) (quadPlus n K) (coe_quadPlus n K)
    ⟨spinMatrix (quadPlus n K) x,
      spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn) x⟩

theorem spinProj_apply (hn : 3 ≤ n) (x : spinGroup (quadPlus n K)) :
    spinProj K hn x = matrixProjectiveProjection (coordinateQuadPlus n K) (spinDerived K hn x) := by
  rw [spinProj, MonoidHom.comp_apply, spinToStatedProj_apply]
  exact statedProjectiveReindexEquiv_mk _ _ _ _

theorem coe_spinDerived (hn : 3 ≤ n) (x : spinGroup (quadPlus n K)) :
    (((spinDerived K hn x : matrixDerived (coordinateQuadPlus n K)) : GL (Fin (2 * n)) K) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      Matrix.reindex (plusIndexEquiv n) (plusIndexEquiv n)
        (spinMatrix (quadPlus n K) x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  rw [spinDerived, statedDerivedReindexEquiv_val, reindexMatrixEquiv_val]

theorem spinProj_surjective (hn : 3 ≤ n) : Function.Surjective (spinProj K hn) :=
  (coordinatePlusWitnessEquiv K (MulEquiv.refl _)).surjective.comp
    (spinToStatedProj_quadPlus hn).1

theorem ker_spinProj (hn : 3 ≤ n) :
    (spinProj K hn).ker = Subgroup.center (spinGroup (quadPlus n K)) := by
  rw [← (spinToStatedProj_quadPlus (K := K) hn).2.2]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, spinProj, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem center_matrixProjectiveDerived_plus (hn : 3 ≤ n) :
    Subgroup.center (matrixProjectiveDerived (coordinateQuadPlus n K)) = ⊥ := by
  have := isPerfect_statedOmega_quadPlus (K := K) hn
  have := ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hn
  have h0 := center_eq_bot_of_isSimpleGroup_of_exists
    (exists_mul_ne_mul_statedProj (H := StatedOmega (StatedQuadPlus n K)))
  set e := coordinatePlusWitnessEquiv K
    (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadPlus n K))))
  rw [← Subgroup.map_center_eq e, h0, Subgroup.map_bot]

end Spin

theorem rootSL2_uSL_mem_rootSubgroup
    {τ : Tag} {K : Type} [Field K] (β : Fin τ.rank → ℤ) (c : K) :
    rootSL2 τ K β (uSL c) ∈ rootSubgroup τ K β := by
  rw [rootSL2_uSL_eq]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem rootSL2_uSL_mem_pairSpan
    {τ : Tag} {K : Type} [Field K] {S : Set (Fin τ.rank → ℤ)} {β : Fin τ.rank → ℤ} (hβ : β ∈ S)
    (c : K) : rootSL2 τ K β (uSL c) ∈ pairSpan τ K S :=
  le_iSup₂_of_le (f := fun β _ => rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) β hβ le_sup_left
    (rootSL2_uSL_mem_rootSubgroup β c)

theorem exists_rootSL2_uSL_eq
    {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ} {g : ModGL τ K}
    (hg : g ∈ rootSubgroup τ K β) : ∃ c : K, rootSL2 τ K β (uSL c) = g := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.mp hg
  refine ⟨(pinnedData τ β).2.2 • c, ?_⟩
  rw [rootSL2_uSL_eq]
  congr 1
  rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp

theorem e6D5TwRoot_zero_mem :
    e6D5TwRoot 0 ∈ Set.range e6D5TwRoot := ⟨0, rfl⟩

theorem exists_pairSpan_e6D5Tw_proj
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    ∃ θ : pairSpan .E6 K (Set.range e6D5TwRoot) →*
        matrixProjectiveDerived (coordinateQuadPlus 5 K),
      Function.Surjective θ ∧ θ.ker = Subgroup.center _ ∧
      ∃ (N : Matrix (Fin (2 * 5)) (Fin (2 * 5)) K) (r : K → matrixDerived (coordinateQuadPlus 5 K)),
        N * N = 0 ∧ N ≠ 0 ∧
        (∀ c, (((r c : matrixDerived (coordinateQuadPlus 5 K)) : GL (Fin (2 * 5)) K) :
          Matrix (Fin (2 * 5)) (Fin (2 * 5)) K) = 1 + c • N) ∧
        (∀ c, ∃ d, θ ⟨rootSL2 .E6 K (e6D5TwRoot 0) (uSL c),
          rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ =
            matrixProjectiveProjection _ (r d)) ∧
        ∀ d, ∃ c, θ ⟨rootSL2 .E6 K (e6D5TwRoot 0) (uSL c),
          rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ =
            matrixProjectiveProjection _ (r d) := by
  have hn : 3 ≤ 5 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_e6D5Tw hp hp2 hK
  obtain ⟨y, hy⟩ := exists_conj_rootGroup_le hp hp2 hK Ψ (hrk 0)
  set ΨM := (adjointGroup .E6 K).subtype.comp Ψ with hΨM
  have hrangeM : ΨM.range = pairSpan .E6 K (Set.range e6D5TwRoot) := by
    rw [hΨM, MonoidHom.range_comp, hrange]
  have hkerM : ΨM.ker ≤ Subgroup.center _ := fun x hx => hker (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx)
  obtain ⟨θ, hθs, hθk, hθ⟩ := exists_quotient_of_frame ΨM hrangeM hkerM (spinProj K hn)
    (spinProj_surjective K hn) (ker_spinProj K hn) (center_matrixProjectiveDerived_plus K hn)
  set F := plusFrame 5 K hn with hF
  have hij : rootIdxD 5 (0 : Fin 5) ≠ rootIdxD' 5 0 := rootIdxD_ne 5 (by norm_num) 0
  set t := rootSignD 5 (0 : Fin 5) with ht
  set N₀ := eichlerMatrix F (rootIdxD 5 0) (rootIdxD' 5 0) true t with hN₀
  set M := spinMatrix (quadPlus 5 K) y with hM
  set N := Matrix.reindex (plusIndexEquiv 5) (plusIndexEquiv 5)
    ((M : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) * N₀ *
      ((M⁻¹ : GL (Fin 5 ⊕ Fin 5) K) : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K)) with hN
  set x : K → spinGroup (quadPlus 5 K) := fun d =>
    y * F.longRoot hij true t (.ofAdd d) * y⁻¹ with hx
  set r : K → matrixDerived (coordinateQuadPlus 5 K) := fun d => spinDerived K hn (x d) with hr
  have hN2 : N * N = 0 :=
    reindex_mul_self_eq_zero _ (conj_mul_self_eq_zero (eichlerMatrix_mul_self F hij true t) M)
  have hN0 : N ≠ 0 := reindex_ne_zero _ (conj_ne_zero (eichlerMatrix_ne_zero F hij true t) M)
  have hrc : ∀ c, (((r c : matrixDerived (coordinateQuadPlus 5 K)) : GL (Fin (2 * 5)) K) :
      Matrix (Fin (2 * 5)) (Fin (2 * 5)) K) = 1 + c • N := by
    intro c
    rw [hr, coe_spinDerived, hx, spinMatrix_conj_longRoot F hij true t y c, reindex_one_add_smul]
  have hxU : ∀ d, ΨM (x d) ∈ rootSubgroup .E6 K (e6D5TwRoot 0) := by
    intro d
    have hβ : IsRoot .E6 (e6D5TwRoot 0) := isRoot_single _ _
    rw [← map_subtype_rootGroup _ hβ]
    refine ⟨Ψ (x d), hy ⟨_, ⟨F.longRoot hij true t (.ofAdd d), ?_, rfl⟩, rfl⟩, rfl⟩
    rw [plusRootGroup_single]
    exact ⟨_, rfl⟩
  have hsup : ∀ d, ∃ c, θ ⟨rootSL2 .E6 K (e6D5TwRoot 0) (uSL c),
      rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ =
        matrixProjectiveProjection _ (r d) := by
    intro d
    obtain ⟨c, hc⟩ := exists_rootSL2_uSL_eq (hxU d)
    refine ⟨c, ?_⟩
    have h1 : (⟨rootSL2 .E6 K (e6D5TwRoot 0) (uSL c),
        rootSL2_uSL_mem_pairSpan e6D5TwRoot_zero_mem c⟩ :
          pairSpan .E6 K (Set.range e6D5TwRoot)) =
        ⟨ΨM (x d), by rw [← hrangeM]; exact ⟨x d, rfl⟩⟩ := Subtype.ext hc
    rw [h1, hθ, spinProj_apply]
  refine ⟨θ, hθs, hθk, N, r, hN2, hN0, hrc, ?_, hsup⟩
  choose cf hcf using hsup
  have hinj : Function.Injective cf := fun d₁ d₂ h =>
    rootClass_injective (by norm_num) hN2 hN0 r hrc (by rw [← hcf, ← hcf, h])
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro c
  obtain ⟨d, rfl⟩ := hsurj c
  exact ⟨d, hcf d⟩

end CFSG.ComponentClassification.Burgoyne.X10
