module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionBNormalForm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusionBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_mono map_perfectCore)

variable {K : Type*} [Field K]

section Rank

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

omit [Fintype ι] in
theorem nilOf_col_w {u w : Fin k → ι} (hw : Function.Injective w) (a : Fin k) :
    (nilOf K u w).col (w a) = Pi.single (u a) 1 := by
  ext i
  rw [col_apply, nilOf_apply, Pi.single_apply]
  by_cases hi : i = u a
  · rw [ite_eq_left_iff.2 fun h => absurd ⟨a, hi.symm, rfl⟩ h,
      ite_eq_left_iff.2 fun h => absurd hi h]
  · rw [ite_eq_right_iff.2 fun h => absurd h hi, ite_eq_right_iff.2]
    rintro ⟨b, hb, hba⟩
    exact absurd (by rw [← hb, hw hba]) hi

omit [Fintype ι] in
theorem nilOf_col_of_forall_ne {u w : Fin k → ι} {j : ι} (hj : ∀ a, w a ≠ j) :
    (nilOf K u w).col j = 0 := by
  ext i
  rw [col_apply, nilOf_apply, ite_eq_right_iff.2, Pi.zero_apply]
  rintro ⟨a, -, ha⟩
  exact absurd ha (hj a)

theorem rank_nilOf {u w : Fin k → ι} (hu : Function.Injective u) (hw : Function.Injective w) :
    (nilOf K u w).rank = k := by
  have hspan : Submodule.span K (Set.range (nilOf K u w).col) =
      Submodule.span K (Set.range fun a => (Pi.single (u a) 1 : ι → K)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨j, rfl⟩
      by_cases hj : ∃ a, w a = j
      · obtain ⟨a, rfl⟩ := hj
        rw [nilOf_col_w hw]
        exact Submodule.subset_span ⟨a, rfl⟩
      · rw [nilOf_col_of_forall_ne fun a ha => hj ⟨a, ha⟩]
        exact Submodule.zero_mem _
    · rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨w a, nilOf_col_w hw a⟩
  have hli : LinearIndependent K fun a => (Pi.single (u a) 1 : ι → K) := by
    have h := (Pi.basisFun K ι).linearIndependent.comp u hu
    convert h using 1
    ext a : 1
    rw [Function.comp_apply, Pi.basisFun_apply]
  rw [rank_eq_finrank_span_cols, hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Rank

section NormalForm

variable {n : ℕ}

theorem exists_conj_eq_elt_of_isInvolutionClass_one [Finite K] [CharP K 2]
    {z : projectiveSL n K} (hz : IsInvolutionClass 1 z) :
    ∃ (P : InvPlacement n 1) (c : projectiveSL n K), c * z * c⁻¹ = P.elt K := by
  obtain ⟨g, rfl, hgg, hrk⟩ := hz
  obtain ⟨k, u, w, hu, hw, huw, h, hh⟩ := exists_conj_eq_one_add_nilOf (K := K) hgg
  have hhinv : (h : Matrix (Fin n) (Fin n) K) * ((h⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hN : nilOf K u w = (h : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
      ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hhinv, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hh, add_sub_cancel_left]
  have hk : k = 1 := by
    have hdet : ∀ A : SpecialLinearGroup (Fin n) K, IsUnit (A : Matrix (Fin n) (Fin n) K).det :=
      fun A => by rw [A.2]; exact isUnit_one
    rw [← rank_nilOf (K := K) hu hw, hN, rank_mul_eq_left_of_isUnit_det _ _ (hdet _),
      rank_mul_eq_right_of_isUnit_det _ _ (hdet _), hrk]
  subst hk
  refine ⟨InvPlacement.ofFun u w hu hw huw, proj n K h, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, InvPlacement.elt]
  congr 1
  exact Subtype.ext (hh.trans (one_add_nilOf_eq_coe_mat u w hu hw huw))

theorem IsInvolutionClass.conj {k : ℕ} {y : projectiveSL n K} (h : IsInvolutionClass k y)
    (x : projectiveSL n K) : IsInvolutionClass k (x * y * x⁻¹) := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  have h' := h.conjAut (Matrix.SpecialLinearGroup.toGL g)
  rwa [conjAut_toGL, MulAut.conj_apply] at h'

theorem exists_conj_mem_blockSL_of_isInvolutionClass_one [Finite K] [CharP K 2]
    {I : Finset (Fin n)} (hI : 2 ≤ I.card) {z : projectiveSL n K} (hz : IsInvolutionClass 1 z) :
    ∃ c : projectiveSL n K, IsInvolutionClass 1 (c * z * c⁻¹) ∧ c * z * c⁻¹ ∈ blockSL I := by
  obtain ⟨P, c₁, hc₁⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hz
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
  obtain ⟨σ, hσu, hσw⟩ := exists_perm_apply_eq_apply_eq (P.u_ne_w 0 0) hab
  obtain ⟨c₂, hc₂⟩ := exists_conj_blockSL (K := K) σ P.outer
  have hsub : P.outer.map σ.toEmbedding ⊆ I := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨s, rfl⟩ := P.mem_outer.1 hj
    rcases s with s | s
    · rw [Subsingleton.elim s 0]
      simpa [InvPlacement.supp, hσu] using ha
    · rw [Subsingleton.elim s 0]
      simpa [InvPlacement.supp, hσw] using hb
  have hmem : c₂ * P.elt K * c₂⁻¹ ∈ blockSL I := by
    refine blockSL_mono hsub ?_
    rw [← hc₂]
    exact ⟨P.elt K, P.elt_mem_blockSL le_rfl, by simp [MulAut.conj_apply]⟩
  have he : c₂ * c₁ * z * (c₂ * c₁)⁻¹ = c₂ * P.elt K * c₂⁻¹ := by
    rw [← hc₁]
    group
  exact ⟨c₂ * c₁, hz.conj _, he ▸ hmem⟩

end NormalForm

section Perfect

theorem isPerfect_specialLinearGroup_fin_one : Group.IsPerfect (SpecialLinearGroup (Fin 1) K) := by
  have : Subsingleton (SpecialLinearGroup (Fin 1) K) := by
    refine ⟨fun A B => Matrix.SpecialLinearGroup.ext A B fun i j => ?_⟩
    have hA := A.2
    have hB := B.2
    rw [det_unique] at hA hB
    rw [Subsingleton.elim i default, Subsingleton.elim j default, hA, hB]
  infer_instance

theorem isPerfect_specialLinearGroup_of_three_le_card (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : 3 ≤ Fintype.card ι) : Group.IsPerfect (SpecialLinearGroup ι K) := by
  have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) hι
  exact Group.IsPerfect.ofSurjective
    (f := (reindexSpecialLinear (K := K) (Fintype.equivFin ι).symm).toMonoidHom)
    (MulEquiv.surjective _)

theorem four_le_card_of_card_ne_two [Finite K] [CharP K 2] (h : Nat.card K ≠ 2) :
    4 ≤ Nat.card K := by
  have := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hm] at h ⊢
  have hm2 : 2 ≤ (m : ℕ) := by
    by_contra hlt
    have hm1 : (m : ℕ) = 1 := by have := m.pos; omega
    rw [hm1, pow_one] at h
    exact h rfl
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) hm2

end Perfect

theorem map_mem_perfectCore_centralizer {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) {y : X} (hy : y ∈ perfectCore (centralizer ({y} : Set X))) :
    f y ∈ perfectCore (centralizer ({f y} : Set Y)) := by
  have h1 : f y ∈ (perfectCore (centralizer ({y} : Set X))).map f := ⟨y, hy, rfl⟩
  rw [map_perfectCore] at h1
  refine perfectCore_mono ?_ h1
  calc (centralizer ({y} : Set X)).map f ≤ centralizer (f '' {y}) :=
        map_centralizer_le_centralizer_image _ f
    _ = centralizer ({f y} : Set Y) := by rw [Set.image_singleton]

section Theorem

variable {n : ℕ}

theorem InvPlacement.elt_mem_perfectCore_centralizer [CharP K 2] (P : InvPlacement n 1)
    [Group.IsPerfect (SpecialLinearGroup P.free K)] (hJ : 2 ≤ P.free.card) :
    P.elt K ∈ perfectCore (centralizer ({P.elt K} : Set (projectiveSL n K))) := by
  have := isPerfect_specialLinearGroup_fin_one (K := K)
  rw [P.perfectCore_centralizer_elt (K := K) hJ]
  refine mem_sup_left (Subgroup.mem_map_of_mem _ ?_)
  intro i j hij
  rw [InvPlacement.coe_mat, Matrix.add_apply, P.nil_apply_of_le hij, add_zero]

theorem mem_perfectCore_centralizer_transvection' [Finite K] [CharP K 2]
    (hn : 4 ≤ n) (hnK : 5 ≤ n ∨ 4 ≤ Nat.card K) {z : projectiveSL n K}
    (hz : IsInvolutionClass 1 z) :
    z ∈ perfectCore (centralizer ({z} : Set (projectiveSL n K))) := by
  obtain ⟨P, c, hc⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hz
  have hJ : P.free.card = n - 2 := P.card_free
  have : Group.IsPerfect (SpecialLinearGroup P.free K) := by
    rcases hnK with h5 | hK4
    · exact isPerfect_specialLinearGroup_of_three_le_card _
        (by rw [Fintype.card_coe, hJ]; omega)
    · exact InvPlacement.isPerfect_specialLinearGroup_of_four_le hK4 _
  have hy := P.elt_mem_perfectCore_centralizer (K := K) (by omega)
  have hφ := map_mem_perfectCore_centralizer (MulAut.conj c⁻¹).toMonoidHom hy
  have hz' : (MulAut.conj c⁻¹).toMonoidHom (P.elt K) = z := by
    rw [← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rwa [hz'] at hφ

theorem mem_perfectCore_centralizer_transvection [Finite K] [CharP K 2]
    (hn : 4 ≤ n) (hnK : ¬(n = 4 ∧ Nat.card K = 2)) {z : projectiveSL n K}
    (hz : IsInvolutionClass 1 z) :
    z ∈ perfectCore (centralizer ({z} : Set (projectiveSL n K))) := by
  refine mem_perfectCore_centralizer_transvection' hn ?_ hz
  by_cases h4 : n = 4
  · exact Or.inr (four_le_card_of_card_ne_two fun h2 => hnK ⟨h4, h2⟩)
  · exact Or.inl (by omega)

end Theorem

end CFSG.SeitzReduction.LinearPilot
