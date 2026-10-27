module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenGroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteen

theorem orderOf_conj_eq' {H : Type*} [Group H] (c x : H) : orderOf (c * x * c⁻¹) = orderOf x := by
  have : c * x * c⁻¹ = (MulAut.conj c) x := by simp [MulAut.conj_apply]
  rw [this, MulEquiv.orderOf_eq]

section Fix

theorem thirteen_mul_card_fix_le {Γ X : Type*} [Group Γ] [Finite Γ] [MulAction Γ X]
    [MulAction.IsPretransitive Γ X] (x₀ : X) {t : Γ} (ht : orderOf t = 13) (htx : t • x₀ = x₀)
    (hS : 13 * Nat.card {h : MulAction.stabilizer Γ x₀ // orderOf (h : Γ) = 13} ≤
      Nat.card (MulAction.stabilizer Γ x₀)) {c : ℕ}
    (hC : Nat.card (centralizer ({t} : Set Γ)) ≤ c) :
    13 * Nat.card {y : X // t • y = y} ≤ c := by
  have hf := CFSG.GroupAction.card_fix_mul_card_stabilizer x₀ t
  set S := MulAction.stabilizer Γ x₀ with hSdef
  have hspos : 0 < Nat.card S := Nat.card_pos
  have hinj : Nat.card {h : Γ // h ∈ S ∧ IsConj t h} ≤
      Nat.card {h : S // orderOf (h : Γ) = 13} := by
    refine Nat.card_le_card_of_injective (fun h => ⟨⟨h.1, h.2.1⟩, ?_⟩) ?_
    · show orderOf h.1 = 13
      obtain ⟨c, hc⟩ := isConj_iff.1 h.2.2
      rw [← hc, orderOf_conj_eq', ht]
    · intro a b hab
      have := congrArg (fun z : {h : S // orderOf (h : Γ) = 13} => ((z.1 : S) : Γ)) hab
      exact Subtype.ext this
  set F := Nat.card {y : X // t • y = y} with hF
  set s := Nat.card S with hs
  set cc := Nat.card (centralizer ({t} : Set Γ)) with hcc
  set m := Nat.card {h : Γ // h ∈ S ∧ IsConj t h} with hm
  set m' := Nat.card {h : S // orderOf (h : Γ) = 13} with hm'
  have h1 : 13 * F * s ≤ c * s := by
    calc 13 * F * s = 13 * (F * s) := by ring
      _ = 13 * (cc * m) := by rw [hf]
      _ ≤ 13 * (cc * m') := by gcongr
      _ = cc * (13 * m') := by ring
      _ ≤ cc * s := by gcongr
      _ ≤ c * s := by gcongr
  exact Nat.le_of_mul_le_mul_right h1 hspos

end Fix

section Count

theorem exists_conj_pow_of_orderOf_thirteen {S : Type*} [Group S] [Finite S]
    (hS : ¬ 13 ^ 2 ∣ Nat.card S) {t : S} (ht : orderOf t = 13) {h : S} (hh : orderOf h = 13) :
    ∃ j : ℕ, 0 < j ∧ j < 13 ∧ ∃ σ : S, σ⁻¹ * h * σ = t ^ j := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_sylow_eq_of_card_eq_prime hS
    (zpowers t) (by rw [Nat.card_zpowers, ht])
  have hhp : IsPGroup 13 (zpowers h) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hh, pow_one])
  obtain ⟨σ, hσ⟩ := CFSG.Monster.Existence.StdOdd.Cert.exists_conj_mem_sylow P hhp
  rw [hP] at hσ
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hσ
  have hlt : j % 13 < 13 := Int.emod_lt_of_pos j (by norm_num)
  have hnn : 0 ≤ j % 13 := Int.emod_nonneg j (by norm_num)
  obtain ⟨j', hj'⟩ := Int.eq_ofNat_of_zero_le hnn
  have htj : t ^ j = t ^ j' := by
    have := zpow_mod_orderOf t j
    rw [ht] at this
    rw [← this]
    have e : j % ((13 : ℕ) : ℤ) = j' := hj'
    rw [e, zpow_natCast]
  have hj'lt : j' < 13 := by omega
  have hj0 : j' ≠ 0 := by
    rintro rfl
    have h1 : σ⁻¹ * h * σ = 1 := by rw [← hj, htj]; simp
    have hh1 : h = 1 := by
      have := congrArg (fun z => σ * z * σ⁻¹) h1
      simpa [mul_assoc] using this
    rw [hh1, orderOf_one] at hh
    omega
  exact ⟨j', Nat.pos_of_ne_zero hj0, hj'lt, σ, by rw [← hj, htj]⟩

theorem isConj_pow_of_conj {S : Type*} [Group S] {t g : S} {k : ℕ} (hg : g * t * g⁻¹ = t ^ k)
    (m : ℕ) : IsConj t (t ^ (k ^ m)) := by
  refine isConj_iff.2 ⟨g ^ m, ?_⟩
  induction m with
  | zero => simp
  | succ m ih =>
    calc g ^ (m + 1) * t * (g ^ (m + 1))⁻¹ = g * (g ^ m * t * (g ^ m)⁻¹) * g⁻¹ := by
          rw [pow_succ']; group
      _ = g * t ^ (k ^ m) * g⁻¹ := by rw [ih]
      _ = (g * t * g⁻¹) ^ (k ^ m) := conj_pow.symm
      _ = (t ^ k) ^ (k ^ m) := by rw [hg]
      _ = t ^ (k ^ (m + 1)) := by rw [← pow_mul, pow_succ, mul_comm]

theorem thirteen_mul_card_orderOf_le {H : Type*} [Group H] [Finite H]
    (hH : ¬ 13 ^ 2 ∣ Nat.card H) {y g : H} (hy : orderOf y = 13) (hg : g * y * g⁻¹ = y ^ 2) :
    13 * Nat.card {h : H // orderOf h = 13} ≤ Nat.card H := by
  have hconj : ∀ h : H, orderOf h = 13 → IsConj y h := by
    intro h hh
    obtain ⟨j, hj0, hj13, σ, hσ⟩ := exists_conj_pow_of_orderOf_thirteen hH hy hh
    have key : ∀ j : Fin 13, 0 < j.val → ∃ m : Fin 12, (2 ^ m.val) % 13 = j.val := by decide
    obtain ⟨m, hm⟩ := key ⟨j, hj13⟩ hj0
    have h1 : IsConj y (y ^ (2 ^ m.val)) := isConj_pow_of_conj hg m.val
    have h2 : y ^ (2 ^ m.val) = y ^ j := by
      rw [← pow_mod_orderOf y (2 ^ m.val), hy, hm]
    have h3 : IsConj (y ^ j) h := isConj_iff.2 ⟨σ, by rw [← hσ]; group⟩
    exact (h2 ▸ h1).trans h3
  have hle := thirteen_mul_card_isConj_le (S := H) hy
  have hcard : Nat.card {h : H // orderOf h = 13} ≤ Nat.card {h : H // IsConj y h} := by
    refine Nat.card_le_card_of_injective (fun h => ⟨h.1, hconj h.1 h.2⟩) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext this
  calc 13 * Nat.card {h : H // orderOf h = 13} ≤ 13 * Nat.card {h : H // IsConj y h} :=
        Nat.mul_le_mul_left 13 hcard
    _ ≤ Nat.card H := hle

theorem card_isConj_mul_card_centralizer {H : Type*} [Group H] [Finite H] (t : H) :
    Nat.card {h : H // IsConj t h} * Nat.card (centralizer ({t} : Set H)) = Nat.card H := by
  have h1 := Subgroup.index_mul_card (centralizer ({t} : Set H))
  rw [Subgroup.index_centralizer_eq_ncard] at h1
  have h3 : (conjugatesOf t).ncard = Nat.card {h : H // IsConj t h} := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h3] at h1
  exact h1

theorem le_card_of_orderOf_thirteen_two {H : Type*} [Group H] [Finite H] {K : Subgroup H} {y z : H}
    (hy : orderOf y = 13) (hz : orderOf z = 2) (hyK : y ∈ K) (hzK : z ∈ K) :
    26 ≤ Nat.card K := by
  have h13 : 13 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hyK
    rwa [hy] at this
  have h2 : 2 ∣ Nat.card K := by
    have := Subgroup.orderOf_dvd_natCard K hzK
    rwa [hz] at this
  have h26 : 26 ∣ Nat.card K := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 13) h2 h13
    simpa using this
  exact Nat.le_of_dvd Nat.card_pos h26

theorem thirteen_mul_card_orderOf_le_of_involution {H : Type*} [Group H] [Finite H]
    (hH : ¬ 13 ^ 2 ∣ Nat.card H) {y g z : H} (hy : orderOf y = 13) (hg : g * y * g⁻¹ = y ^ 4)
    (hz : orderOf z = 2) (hzy : z * y = y * z) :
    13 * Nat.card {h : H // orderOf h = 13} ≤ Nat.card H := by
  have hg2 : g * y ^ 2 * g⁻¹ = (y ^ 2) ^ 4 := by
    rw [← conj_pow, hg, ← pow_mul, ← pow_mul, mul_comm]
  have hy2o : orderOf (y ^ 2) = 13 := by
    rw [orderOf_pow' _ (by norm_num), hy]
    norm_num
  have hcover : ∀ h : H, orderOf h = 13 → IsConj y h ∨ IsConj (y ^ 2) h := by
    intro h hh
    obtain ⟨j, hj0, hj13, σ, hσ⟩ := exists_conj_pow_of_orderOf_thirteen hH hy hh
    have key : ∀ j : Fin 13, 0 < j.val →
        (∃ m : Fin 6, (4 ^ m.val) % 13 = j.val) ∨ (∃ m : Fin 6, (2 * 4 ^ m.val) % 13 = j.val) := by
      decide
    have h3 : IsConj (y ^ j) h := isConj_iff.2 ⟨σ, by rw [← hσ]; group⟩
    rcases key ⟨j, hj13⟩ hj0 with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      have h1 : IsConj y (y ^ (4 ^ m.val)) := isConj_pow_of_conj hg m.val
      have h2 : y ^ (4 ^ m.val) = y ^ j := by
        rw [← pow_mod_orderOf y (4 ^ m.val), hy, hm]
      exact (h2 ▸ h1).trans h3
    · right
      have h1 : IsConj (y ^ 2) ((y ^ 2) ^ (4 ^ m.val)) := isConj_pow_of_conj hg2 m.val
      have h2 : (y ^ 2) ^ (4 ^ m.val) = y ^ j := by
        rw [← pow_mul, ← pow_mod_orderOf y (2 * 4 ^ m.val), hy, hm]
      exact (h2 ▸ h1).trans h3
  have hC1 : 26 ≤ Nat.card (centralizer ({y} : Set H)) :=
    le_card_of_orderOf_thirteen_two hy hz (mem_centralizer_singleton_iff.2 rfl)
      (mem_centralizer_singleton_iff.2 hzy)
  have hC2 : 26 ≤ Nat.card (centralizer ({y ^ 2} : Set H)) :=
    le_card_of_orderOf_thirteen_two hy2o hz (mem_centralizer_singleton_iff.2 rfl)
      (mem_centralizer_singleton_iff.2 (((show Commute z y from hzy).pow_right 2).eq))
  have hA := card_isConj_mul_card_centralizer y
  have hB := card_isConj_mul_card_centralizer (y ^ 2)
  have hA' : 26 * Nat.card {h : H // IsConj y h} ≤ Nat.card H := by
    calc 26 * Nat.card {h : H // IsConj y h} ≤
          Nat.card (centralizer ({y} : Set H)) * Nat.card {h : H // IsConj y h} :=
          Nat.mul_le_mul_right _ hC1
      _ = Nat.card H := by rw [mul_comm]; exact hA
  have hB' : 26 * Nat.card {h : H // IsConj (y ^ 2) h} ≤ Nat.card H := by
    calc 26 * Nat.card {h : H // IsConj (y ^ 2) h} ≤
          Nat.card (centralizer ({y ^ 2} : Set H)) * Nat.card {h : H // IsConj (y ^ 2) h} :=
          Nat.mul_le_mul_right _ hC2
      _ = Nat.card H := by rw [mul_comm]; exact hB
  have hcard : Nat.card {h : H // orderOf h = 13} ≤
      Nat.card {h : H // IsConj y h} + Nat.card {h : H // IsConj (y ^ 2) h} := by
    classical
    rw [← Nat.card_sum]
    refine Nat.card_le_card_of_injective (fun h =>
      if hc : IsConj y h.1 then Sum.inl ⟨h.1, hc⟩
      else Sum.inr ⟨h.1, (hcover h.1 h.2).resolve_left hc⟩) ?_
    intro a b hab
    by_cases ha : IsConj y a.1 <;> by_cases hb : IsConj y b.1 <;>
      simp only [ha, hb, dite_true, dite_false] at hab
    · have h1 := Sum.inl.inj hab
      exact Subtype.ext (Subtype.mk.inj h1)
    · exact absurd hab (by simp)
    · exact absurd hab (by simp)
    · have h1 := Sum.inr.inj hab
      exact Subtype.ext (Subtype.mk.inj h1)
  omega

theorem card_orderOf_thirteen_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card {h : H // orderOf h = 13} = Nat.card {k : K // orderOf k = 13} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun h => by
    show orderOf h = 13 ↔ orderOf (e h) = 13
    rw [MulEquiv.orderOf_eq])

end Count

end CFSG.HardMathSupport.Dickson.Sec6.I1431
