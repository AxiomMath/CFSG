module

public import CFSG.GH74.Generic.S1.Exo.Defs
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap

section Conj

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

@[expose] def linearEquivConj (e : V ≃ₗ[K] W) : (W ≃ₗ[K] W) ≃* (V ≃ₗ[K] V) where
  toFun g := (e.trans g).trans e.symm
  invFun g := (e.symm.trans g).trans e
  left_inv g := by ext w; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp

theorem linearEquivConj_apply (e : V ≃ₗ[K] W) (g : W ≃ₗ[K] W) (v : V) :
    linearEquivConj e g v = e.symm (g (e v)) :=
  rfl

theorem det_linearEquivConj (e : V ≃ₗ[K] W) (g : W ≃ₗ[K] W) :
    LinearEquiv.det (linearEquivConj e g) = LinearEquiv.det g :=
  LinearEquiv.det_conj g e.symm

theorem linearEquivConj_neg (e : V ≃ₗ[K] W) :
    linearEquivConj e (LinearEquiv.neg K) = LinearEquiv.neg K := by
  ext v
  simp [linearEquivConj_apply]

theorem linearEquivConj_mem_soForm {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') {g : W ≃ₗ[K] W} (hg : g ∈ soForm Q') :
    linearEquivConj e.toLinearEquiv g ∈ soForm Q := by
  rw [mem_soForm_iff] at hg ⊢
  refine ⟨fun v => ?_, by rw [det_linearEquivConj, hg.2]⟩
  rw [linearEquivConj_apply]
  have h1 := e.map_app v
  have h2 : Q (e.toLinearEquiv.symm (g (e.toLinearEquiv v))) = Q' (g (e.toLinearEquiv v)) :=
    e.symm.map_app (g (e.toLinearEquiv v))
  rw [h2, hg.1]
  exact h1

end Conj

section Index

theorem mem_or_mul_mem_of_card {G : Type*} [Group G] [Finite G] {O S Ω : Subgroup G} {n r : G}
    {N₀ : ℕ} (hO : Nat.card O = 2 * N₀) (hΩ : Nat.card Ω * 2 = N₀) (hΩS : Ω ≤ S) (hSO : S ≤ O)
    (hnS : n ∈ S) (hnΩ : n ∉ Ω) (hrO : r ∈ O) (hrS : r ∉ S) :
    ∀ g ∈ S, g ∈ Ω ∨ n * g ∈ Ω := by
  have hSlt : Nat.card S < Nat.card O := by
    by_contra hge
    exact hrS ((Subgroup.eq_of_le_of_card_ge hSO (not_lt.mp hge)) ▸ hrO)
  have hΩlt : Nat.card Ω < Nat.card S := by
    by_contra hge
    exact hnΩ ((Subgroup.eq_of_le_of_card_ge hΩS (not_lt.mp hge)) ▸ hnS)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSO
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hΩS
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have hΩpos : 0 < Nat.card Ω := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> omega
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m <;> omega
  have hSle : Nat.card S ≤ N₀ := by nlinarith
  have hSeq : Nat.card S = Nat.card Ω * 2 := by nlinarith
  have hidx : (Ω.subgroupOf S).index = 2 := by
    have h1 := Subgroup.card_mul_index (Ω.subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩS).toEquiv, hSeq] at h1
    exact Nat.eq_of_mul_eq_mul_left hΩpos h1
  intro g hg
  by_cases hgΩ : g ∈ Ω
  · exact Or.inl hgΩ
  · refine Or.inr ?_
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨n, hnS⟩ : S))
      (b := (⟨g, hg⟩ : S))).mpr (by simp [Subgroup.mem_subgroupOf, hnΩ, hgΩ])
    exact Subgroup.mem_subgroupOf.mp this

end Index

section Minus

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem exists_quadForm_ne_zero_of_nondegenerate [Nontrivial V] (Q : QuadraticForm K V)
    (hnd : (polarBilin Q).Nondegenerate) : ∃ v, Q v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  refine hnd.1 x fun y => ?_
  simp [polarBilin_apply_apply, QuadraticMap.polar, hcon]

theorem det_neg_eq_one_of_finrank_four (hdim : finrank K V = 4) :
    LinearEquiv.det (LinearEquiv.neg K : V ≃ₗ[K] V) = 1 := by
  have hfd : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  apply Units.val_injective
  rw [LinearEquiv.coe_det]
  have : (LinearEquiv.neg K : V ≃ₗ[K] V).toLinearMap = (-1 : K) • LinearMap.id := by
    ext v
    simp
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim]
  norm_num

theorem neg_mem_soForm_of_finrank_four (hdim : finrank K V = 4) (Q : QuadraticForm K V) :
    (LinearEquiv.neg K : V ≃ₗ[K] V) ∈ soForm Q := by
  rw [mem_soForm_iff]
  refine ⟨fun v => ?_, det_neg_eq_one_of_finrank_four hdim⟩
  simp

theorem natCard_orthogonalGroup_minus_four [Finite K] (hdim : finrank K V = 4)
    (Q : QuadraticForm K V) (hnd : (polarBilin Q).Nondegenerate)
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 * (Nat.card K ^ 2 * (Nat.card K ^ 4 - 1)) := by
  have hfd : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hnd (m := 1)
    (by simpa using hdim) (ε := -1) (Or.inr ⟨rfl, hnp⟩)
  simp only [Finset.Icc_self, Finset.prod_singleton] at h
  have hq1 : 1 ≤ Nat.card K ^ 4 := Nat.one_le_pow _ _ Nat.card_pos
  zify [hq1]
  rw [h]
  ring

theorem exists_reflection_not_mem_soForm (h2 : (2 : K) ≠ 0) (hdim : finrank K V = 4)
    (Q : QuadraticForm K V) (hnd : (polarBilin Q).Nondegenerate) :
    ∃ r ∈ TauCeti.QuadraticMap.orthogonalGroup Q, r ∉ soForm Q := by
  have hfd : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hdim
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨v, hv⟩ := exists_quadForm_ne_zero_of_nondegenerate Q hnd
  let _ : Invertible (Q v) := invertibleOfNonzero hv
  refine ⟨TauCeti.QuadraticMap.reflection Q v,
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q v, fun h => ?_⟩
  rw [mem_soForm_iff, TauCeti.QuadraticMap.det_reflection] at h
  have h1 := congrArg Units.val h.2
  simp only [Units.val_neg, Units.val_one] at h1
  exact h2 (by linear_combination -h1)

end Minus

end CFSG.GH74.Generic.S1.Exo
