module

public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

theorem not_four_dvd_orderOf {K : Type} [Group K] [Finite K] {M : Subgroup K}
    (hsyl : ∀ P : Sylow 2 ↥M, CFSG.IsElementaryAbelian 2 ↥(P : Subgroup ↥M)) {m : K} (hm : m ∈ M) :
    ¬ 4 ∣ orderOf m := by
  intro h4
  have hpos : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨s, t, ht, hst⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hs : 2 ≤ s := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := ht
    rw [hst] at h4
    interval_cases s <;> omega
  have htpos : t ≠ 0 := by
    rintro rfl
    simp at ht
  have hdvd : t ∣ orderOf m := ⟨2 ^ s, by rw [hst, mul_comm]⟩
  have hord1 : orderOf (m ^ t) = 2 ^ s := by
    rw [orderOf_pow_of_dvd htpos hdvd, hst, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero htpos)]
  let m' : ↥M := ⟨m ^ t, M.pow_mem hm t⟩
  have hord : orderOf m' = 2 ^ s := by
    rw [Subgroup.orderOf_mk]
    exact hord1
  have hP : IsPGroup 2 (Subgroup.zpowers m') :=
    IsPGroup.of_card (n := s) (by rw [Nat.card_zpowers, hord])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have : CFSG.IsElementaryAbelian 2 ↥(Q : Subgroup ↥M) := hsyl Q
  have hmQ : m' ∈ (Q : Subgroup ↥M) := hQ (Subgroup.mem_zpowers m')
  have hsq : m' ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := (Q : Subgroup ↥M)) m' hmQ
  have hd : 2 ^ s ∣ 2 := hord ▸ orderOf_dvd_of_pow_eq_one hsq
  have hle : 2 ^ s ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  omega

theorem fixed_of_perfect {K A : Type*} [Group K] [Group A] (y : MulAut K) (π : K →* A)
    (hker : π.ker ≤ Subgroup.center K) {D : Subgroup K} (hD : ⁅D, D⁆ = D)
    (hy : ∀ k ∈ D, π (y k) = π k) : ∀ k ∈ D, y k = k := by
  have : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.2 hD
  have hc : ∀ k : ↥D, (k : K)⁻¹ * y k ∈ Subgroup.center K := fun k =>
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hy k k.2, inv_mul_cancel])
  let δ : ↥D →* ↥(Subgroup.center K) :=
    { toFun := fun k => ⟨(k : K)⁻¹ * y k, hc k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ((a : K) * (b : K))⁻¹ * y ((a : K) * (b : K)) =
          ((a : K)⁻¹ * y a) * ((b : K)⁻¹ * y b)
        have hcomm := (Subgroup.mem_center_iff.mp (hc a)) (b : K)⁻¹
        calc ((a : K) * (b : K))⁻¹ * y ((a : K) * (b : K))
            = (b : K)⁻¹ * ((a : K)⁻¹ * y a) * y b := by rw [map_mul]; group
          _ = ((a : K)⁻¹ * y a) * (b : K)⁻¹ * y b := by rw [hcomm]
          _ = ((a : K)⁻¹ * y a) * ((b : K)⁻¹ * y b) := mul_assoc _ _ _ }
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative δ
  intro k hk
  have h2 := congrArg (fun ψ : ↥D →* ↥(Subgroup.center K) => ((ψ ⟨k, hk⟩ : ↥(Subgroup.center K)) : K)) h1
  have h3 : (k : K)⁻¹ * y k = 1 := h2
  exact (inv_mul_eq_one.mp h3).symm

theorem exists_fixed_perfect_lift {K A : Type*} [Group K] [Group A] (y : MulAut K) (π : K →* A)
    (hker : π.ker ≤ Subgroup.center K)
    (X : Subgroup A) (hXr : X ≤ π.range) (hX : ⁅X, X⁆ = X)
    (hy : ∀ k : K, π k ∈ X → π (y k) = π k) :
    ∃ D : Subgroup K, (∀ k ∈ D, π k ∈ X) ∧ (∀ a ∈ X, ∃ k ∈ D, π k = a) ∧ ∀ k ∈ D, y k = k := by
  let Xt : Subgroup K := X.comap π
  let D : Subgroup K := ⁅Xt, Xt⁆
  have hDle : D ≤ Xt := Subgroup.commutator_le_self Xt
  have hπD : D.map π = X := by
    show (⁅Xt, Xt⁆).map π = X
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.2 hXr, hX]
  have hXt : Xt = D ⊔ π.ker := by
    show X.comap π = _
    rw [← Subgroup.comap_map_eq, hπD]
  have hDperf : ⁅D, D⁆ = D := by
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central D π.ker hker
    rw [← hXt] at h
    exact h.symm
  refine ⟨D, fun k hk => hDle hk, fun a ha => ?_,
    fixed_of_perfect y π hker hDperf (fun k hk => hy k (hDle hk))⟩
  have : a ∈ D.map π := hπD ▸ ha
  obtain ⟨k, hk, rfl⟩ := this
  exact ⟨k, hk, rfl⟩

theorem exists_sigma {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) (yb : MulAut (alternatingGroup (Fin n)))
    (h1 : yb ≠ 1) (h2 : yb * yb = 1) :
    ∃ σ : Perm (Fin n), σ * σ = 1 ∧ σ ≠ 1 ∧
      ∀ a : alternatingGroup (Fin n),
        ((yb a : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * a * σ⁻¹ := by
  obtain ⟨σ, rfl⟩ := CFSG.Quasithin.SteinbergCB.conjPerm_surjective hn yb
  refine ⟨σ, ?_, ?_, fun a => CFSG.Quasithin.SteinbergCB.conjPerm_apply n σ a⟩
  · apply CFSG.Quasithin.SteinbergCB.conjPerm_injective (by omega)
    rw [map_mul, h2, map_one]
  · rintro rfl
    exact h1 (map_one _)

end CFSG.GH74.Generic.S45.LAlt
