module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterCoreFree

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.I271 (mulAut_mul_conj_mul_inv conj_injective_of_center_bot)

theorem exists_zpow_mul_of_mem_closure_pair {G : Type*} [Group G] {β β' : G}
    (h : Commute β β') {y : G} (hy : y ∈ Subgroup.closure ({β, β'} : Set G)) :
    ∃ a b : ℤ, y = β ^ a * β' ^ b := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, b, rfl⟩ := ihx
    obtain ⟨c, d, rfl⟩ := ihy
    refine ⟨a + c, b + d, ?_⟩
    have hc : Commute (β' ^ b) (β ^ c) := (h.zpow_zpow c b).symm
    calc β ^ a * β' ^ b * (β ^ c * β' ^ d) = β ^ a * (β' ^ b * β ^ c) * β' ^ d := by group
      _ = β ^ a * (β ^ c * β' ^ b) * β' ^ d := by rw [hc.eq]
      _ = β ^ (a + c) * β' ^ (b + d) := by rw [zpow_add, zpow_add]; group
  | inv x _ ih =>
    obtain ⟨a, b, rfl⟩ := ih
    refine ⟨-a, -b, ?_⟩
    have hc : Commute (β ^ a) (β' ^ b) := h.zpow_zpow a b
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact hc.inv_inv.eq.symm

theorem exists_int_mul_eq_one_add {p : ℕ} (hp : p.Prime) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    ∃ u v : ℤ, u * b + v * p = 1 := by
  have h1 : IsCoprime b (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime b.natAbs p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hb (Int.natCast_dvd.2 h)
    simpa [Int.gcd] using this
  obtain ⟨u, v, huv⟩ := h1
  exact ⟨u, v, huv⟩

theorem zpow_eq_of_add_mul {G : Type*} [Group G] {g : G} {p : ℕ} (hg : g ^ p = 1) (k m c : ℤ)
    (h : k = m + c * p) : g ^ k = g ^ m := by
  rw [h, zpow_add, mul_comm c, zpow_mul, zpow_natCast, hg, one_zpow, mul_one]

theorem exists_inner_on_fixSubgroup_of_pump {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) {β : MulAut S} (hβ : orderOf β = p) (hout : β ∉ innerAut S)
    (hE : ∀ D : Subgroup (MulAut S), (∀ a ∈ D, a ^ p = 1) → p < Nat.card D →
      ∃ x ∈ D ⊓ innerAut S, x ≠ 1)
    {β' : MulAut S} (hβ' : β' ^ p = 1) (hcomm : β' * β = β * β') :
    ∃ s ∈ fixSubgroup β, ∀ x ∈ fixSubgroup β, β' x = s * x * s⁻¹ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  have hinj := conj_injective_of_center_bot hZ
  have hβp : β ^ p = 1 := hβ ▸ pow_orderOf_eq_one β
  have hzfix : ∀ (k : ℤ) (x : S), β x = x → (β ^ k) x = x := by
    intro k x hx
    have hstab : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut S) x :=
      Subgroup.zpowers_le.2 hx
    have := hstab (Subgroup.zpow_mem_zpowers β k)
    simpa using this
  by_cases hmem : β' ∈ Subgroup.zpowers β
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine ⟨1, one_mem _, fun x hx => ?_⟩
    rw [← hk, hzfix k x (mem_fixSubgroup.1 hx)]
    simp
  · have hcm : Commute β β' := hcomm.symm
    set E : Subgroup (MulAut S) := Subgroup.closure ({β, β'} : Set (MulAut S)) with hE_def
    have hβE : β ∈ E := Subgroup.subset_closure (by simp)
    have hβ'E : β' ∈ E := Subgroup.subset_closure (by simp)
    have hexp : ∀ a ∈ E, a ^ p = 1 := by
      intro a ha
      obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_closure_pair hcm ha
      rw [(hcm.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hβp, hβ', one_zpow,
        one_zpow, one_mul]
    have hlt : Subgroup.zpowers β < E := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.2 hβE) fun heq => hmem ?_
      rw [heq]
      exact hβ'E
    have hcard : p < Nat.card E := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_zpowers, hβ] at this
    obtain ⟨e, ⟨heE, heI⟩, he1⟩ := hE E hexp hcard
    obtain ⟨a, b, rfl⟩ := exists_zpow_mul_of_mem_closure_pair hcm heE
    obtain ⟨t, ht⟩ := heI
    by_cases hb : (p : ℤ) ∣ b
    · exfalso
      obtain ⟨c, rfl⟩ := hb
      have hb1 : β' ^ ((p : ℤ) * c) = 1 := by
        rw [zpow_mul, zpow_natCast, hβ', one_zpow]
      rw [hb1, mul_one] at he1 ht
      have ha : ¬ (p : ℤ) ∣ a := by
        rintro ⟨d, rfl⟩
        apply he1
        rw [zpow_mul, zpow_natCast, hβp, one_zpow]
      obtain ⟨u, v, huv⟩ := exists_int_mul_eq_one_add hp ha
      apply hout
      have : β = (β ^ a) ^ u := by
        rw [← zpow_mul]
        have h1 : a * u = 1 + (-v) * p := by linarith [huv]
        rw [zpow_eq_of_add_mul hβp (a * u) 1 (-v) h1, zpow_one]
      rw [this, ← ht]
      exact ⟨t ^ u, by rw [map_zpow]⟩
    · obtain ⟨u, v, huv⟩ := exists_int_mul_eq_one_add hp hb
      have heu : (β ^ a * β' ^ b) ^ u = β ^ (a * u) * β' := by
        rw [(hcm.zpow_zpow a b).mul_zpow, ← zpow_mul, ← zpow_mul]
        have h1 : b * u = 1 + (-v) * p := by linarith [huv]
        rw [zpow_eq_of_add_mul hβ' (b * u) 1 (-v) h1, zpow_one]
      set s : S := t ^ u with hs
      have hconj : MulAut.conj s = (β ^ a * β' ^ b) ^ u := by rw [← ht, hs, map_zpow]
      have hcβ : Commute β (β ^ a * β' ^ b) :=
        (Commute.self_zpow β a).mul_right (hcm.zpow_right b)
      have hsfix : β s = s := by
        apply hinj
        rw [← mulAut_mul_conj_mul_inv β s, hconj]
        rw [(hcβ.zpow_right u).eq, mul_inv_cancel_right]
      have hsC : s ∈ fixSubgroup β := mem_fixSubgroup.2 hsfix
      refine ⟨s, hsC, fun x hx => ?_⟩
      have hxC := mem_fixSubgroup.1 hx
      have hsxs : s * x * s⁻¹ ∈ fixSubgroup β := by
        rw [mem_fixSubgroup, map_mul, map_mul, map_inv, hsfix, hxC]
      have hβ'eq : β' = β ^ (-(a * u)) * MulAut.conj s := by
        rw [hconj, heu, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      calc β' x = (β ^ (-(a * u)) * MulAut.conj s) x := by rw [← hβ'eq]
        _ = (β ^ (-(a * u))) (s * x * s⁻¹) := by
            rw [MulAut.mul_apply, MulAut.conj_apply]
        _ = s * x * s⁻¹ := hzfix _ _ (mem_fixSubgroup.1 hsxs)

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
