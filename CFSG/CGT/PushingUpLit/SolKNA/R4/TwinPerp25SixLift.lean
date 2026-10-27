module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTransport

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3

section Lift

theorem exists_order_four_lift {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hN : Odd (Nat.card N)) {L : Subgroup H} {x : H ⧸ N}
    (hx : x ∈ L.map (QuotientGroup.mk' N)) (hx4 : orderOf x = 4) :
    ∃ m ∈ L, orderOf m = 4 ∧ QuotientGroup.mk' N m = x := by
  obtain ⟨m₀, hm₀L, hm₀x⟩ := Subgroup.mem_map.mp hx
  obtain ⟨k, q, hq, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m₀).ne'
  have hx4' : x ^ 4 = 1 := hx4 ▸ pow_orderOf_eq_one x
  have hqq : x ^ (q * q) = x := by
    obtain ⟨j, rfl⟩ := hq
    have : (2 * j + 1) * (2 * j + 1) = 4 * (j * (j + 1)) + 1 := by ring
    rw [this, pow_succ, pow_mul, hx4', one_pow, one_mul]
  have hmx : QuotientGroup.mk' N (m₀ ^ (q * q)) = x := by
    rw [map_pow, hm₀x, hqq]
  have hm2 : (m₀ ^ (q * q)) ^ (2 ^ k) = 1 := by
    have : (m₀ ^ (q * q)) ^ (2 ^ k) = (m₀ ^ (2 ^ k * q)) ^ q := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [this, ← he, pow_orderOf_eq_one, one_pow]
  have hdvd : orderOf (m₀ ^ (q * q)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hm2
  have h4dvd : 4 ∣ orderOf (m₀ ^ (q * q)) := by
    rw [← hx4, ← hmx]
    exact orderOf_map_dvd _ _
  have h4mem : (m₀ ^ (q * q)) ^ 4 ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    have : (QuotientGroup.mk' N) ((m₀ ^ (q * q)) ^ 4) = 1 := by
      rw [map_pow, hmx, hx4']
    simpa using this
  have h1 : orderOf ((m₀ ^ (q * q)) ^ 4) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N h4mem
  have h2 : orderOf ((m₀ ^ (q * q)) ^ 4) ∣ 2 ^ k := (orderOf_pow_dvd 4).trans hdvd
  have hcop : Nat.Coprime (Nat.card N) (2 ^ k) := (Odd.coprime_two_right hN).pow_right k
  have h3 : orderOf ((m₀ ^ (q * q)) ^ 4) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  exact ⟨m₀ ^ (q * q), L.pow_mem hm₀L _, Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h3) h4dvd,
    hmx⟩

theorem exists_orderOf_four_of_uniqueInvolution {G : Type} [Group G] [Finite G] {M X : Subgroup G}
    {u : G} (hu : IsUniqueInvolution M u) (hXM : X ≤ M) (hX2 : IsPGroup 2 X)
    (hX4 : 4 ≤ Nat.card X) : ∃ x ∈ X, orderOf x = 4 := by
  classical
  have hex : ∃ x ∈ X, x ≠ 1 ∧ x ≠ u := by
    by_contra hcon
    push Not at hcon
    have hsub : (X : Set G) ⊆ {1, u} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have hc : Nat.card X ≤ 2 := by
      have h1 : Nat.card X = (X : Set G).ncard := Nat.card_coe_set_eq (X : Set G)
      rw [h1]
      refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  obtain ⟨x, hxX, hx1, hxu⟩ := hex
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hX2) ⟨x, hxX⟩
  have hk' : orderOf x = 2 ^ k := by rw [← hk]; simp [← Subgroup.orderOf_coe]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk'))
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hx2 : x * x = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hk', pow_one, pow_two] at this
    rcases hu.unique x (hXM hxX) hx2 with h | h
    · exact hx1 h
    · exact hxu h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨x ^ (2 ^ j), X.pow_mem hxX _, ?_⟩
  have hdvd : 2 ^ j ∣ orderOf x := by rw [hk']; exact pow_dvd_pow 2 (Nat.le_add_right j 2)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hk', pow_add, Nat.mul_div_cancel_left _
    (pow_pos two_pos j)]
  norm_num

theorem mk_ne_one_of_involution_of_odd {T : Type} [Group T] {N : Subgroup T} [N.Normal]
    (hN : Odd (Nat.card N)) {g : T} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    QuotientGroup.mk' N g ≠ 1 := by
  intro h
  have hgN : g ∈ N := (QuotientGroup.eq_one_iff g).mp h
  have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have h1 := Subgroup.orderOf_dvd_natCard N hgN
  rw [hord] at h1
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h1)

end Lift

section Top

variable {H : Type} [Group H] [Finite H]

abbrev topMk (h : H) : ↥(⊤ : Subgroup H) := ⟨h, Subgroup.mem_top h⟩

theorem mem_oddCore_of_top {n : ↥(⊤ : Subgroup H)}
    (hn : n ∈ classicalInvolutionOddCore ↥(⊤ : Subgroup H)) :
    (n : H) ∈ classicalInvolutionOddCore H := by
  have h : Subgroup.map (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).toMonoidHom
      (classicalInvolutionOddCore ↥(⊤ : Subgroup H)) = classicalInvolutionOddCore H :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  have h1 := Subgroup.mem_map_of_mem (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H).toMonoidHom hn
  rw [h] at h1
  exact h1

theorem tightInO2_top {h : H}
    (hin : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore H) h)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(⊤ : Subgroup H)) (topMk h)) := by
  let e := QuotientGroup.congr (classicalInvolutionOddCore ↥(⊤ : Subgroup H))
    (classicalInvolutionOddCore H) (Subgroup.topEquiv : ↥(⊤ : Subgroup H) ≃* H)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)
  refine TA3.TightInO2.of_map_equiv e ?_
  have : e (QuotientGroup.mk' _ (topMk h)) = QuotientGroup.mk' _ h := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.congr_mk _ _ _ _ (topMk h)
  rw [this]
  exact hin

end Top

end CFSG.CGT.PushingUpLit.SolKNA.R4
