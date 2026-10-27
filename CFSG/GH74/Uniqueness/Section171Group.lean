module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have : Fintype G := Fintype.ofFinite G
  by_contra hab
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  have ha1 : a ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have hb1 : b ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h
    · rw [h]
      exact one_pow 2
    · rw [h, ← ha]
      exact pow_orderOf_eq_one a
    · rw [h, ← hb]
      exact pow_orderOf_eq_one b
  have hcard : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [ha1.symm, hb1.symm]
  have := Finset.card_le_card hsub
  omega

theorem isCyclic_quotient_of_normal_complement {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (hodd : Odd (Nat.card N)) {k : ℕ} (hk : Nat.card G = Nat.card N * 2 ^ k)
    (hcyc : ∀ P : Sylow 2 G, IsCyclic (P : Subgroup G)) : IsCyclic (G ⧸ N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.coprime_two_left.mpr hodd
  have hPcard : Nat.card P = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hk, Nat.factorization_mul hN0 (pow_ne_zero _ two_ne_zero),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (fun h => by
        have := Nat.Coprime.eq_one_of_dvd hcop h
        omega)]
    simp
  let f : (P : Subgroup G) →* G ⧸ N := (QuotientGroup.mk' N).comp (P : Subgroup G).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have h1 : orderOf (x : G) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
    have h2 : orderOf x ∣ Nat.card P := orderOf_dvd_natCard x
    rw [hPcard] at h2
    have h3 : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
    rw [h3] at h1
    have hc : Nat.Coprime (2 ^ k) (Nat.card N) := Nat.Coprime.pow_left k hcop
    have h4 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hc) h1
    exact orderOf_eq_one_iff.mp h4
  have hQcard : Nat.card (G ⧸ N) = 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hk] at h
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hN0) (by rw [← h, mul_comm])).symm
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hQcard, hPcard])
  have := hcyc P
  exact isCyclic_of_surjective f hbij.2

theorem exists_pow_conj_of_inverted {G : Type*} [Group G] {w e : G} (hodd : Odd (orderOf e))
    (hinv : w * e * w⁻¹ = e⁻¹) (hw : w * w = 1) :
    ∃ n : ℕ, e * w = e ^ n * w * (e ^ n)⁻¹ := by
  obtain ⟨m, hm⟩ := hodd
  have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have he1 : e ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
  refine ⟨m + 1, ?_⟩
  have hconj : w * e ^ (m + 1) * w⁻¹ = (e ^ (m + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hconj' : w * (e ^ (m + 1))⁻¹ * w⁻¹ = e ^ (m + 1) := by
    have := congrArg (fun y => y⁻¹) hconj
    simp only [mul_inv_rev, inv_inv] at this
    calc w * (e ^ (m + 1))⁻¹ * w⁻¹ = (w⁻¹)⁻¹ * (e ^ (m + 1))⁻¹ * w⁻¹ := by rw [inv_inv]
      _ = (w * e ^ (m + 1) * w⁻¹)⁻¹ := by group
      _ = e ^ (m + 1) := by rw [hconj, inv_inv]
  calc e * w = e ^ (2 * m + 1) * e * w := by rw [he1, one_mul]
    _ = e ^ (m + 1) * e ^ (m + 1) * w := by
        have h2 : e ^ (2 * m + 1) * e = e ^ (m + 1) * e ^ (m + 1) := by
          rw [← pow_succ, ← pow_add]
          congr 1
          ring
        rw [h2]
    _ = e ^ (m + 1) * (w * (e ^ (m + 1))⁻¹ * w⁻¹) * w := by rw [hconj']
    _ = e ^ (m + 1) * w * (e ^ (m + 1))⁻¹ := by group

theorem ncard_conjOrbit_mul_card_cent {G : Type*} [Group G] (P : Subgroup G) [Finite P] (g : G) :
    {y | ∃ x ∈ P, x * g * x⁻¹ = y}.ncard * Nat.card (P ⊓ centralizer {g} : Subgroup G) =
      Nat.card P := by
  let _ : MulAction P G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp P.subtype)
  have hsmul : ∀ (x : P) (y : G), x • y = (x : G) * y * (x : G)⁻¹ := fun x y =>
    ConjAct.toConjAct_smul (x : G) y
  have horb : MulAction.orbit P g = {y | ∃ x ∈ P, x * g * x⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x g).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ g⟩
  have hstab : MulAction.stabilizer P g = (centralizer {g}).subgroupOf P := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer P g).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

end CFSG.GH74.Uniqueness
