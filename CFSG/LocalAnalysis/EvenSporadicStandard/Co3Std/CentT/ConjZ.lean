module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Co3Inv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.CentSplit

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem mem_zpowers_sq_eq_one_or {G : Type*} [Group G] {x : G} (hx : x * x = 1) {c : G}
    (hc : c ∈ zpowers x) : c = 1 ∨ c = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

section Certified


theorem centFacts_of_centralizer_pair {G : Type} [Group G] [Finite G] {Λ : Subgroup G}
    (hΛ : IsSporadic ↥Λ .Co3) {w t : G} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hcent : centralizer ({w} : Set G) = Λ ⊔ zpowers w) (hdisj : Disjoint Λ (zpowers w))
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (htw : t * w = w * t) (htne : t ≠ w) :
    CentFacts ↥(centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G)) := by
  have hΛ_le_centw : Λ ≤ centralizer ({w} : Set G) := by
    rw [hcent]; exact le_sup_left
  have hzpw_le_centΛ : zpowers w ≤ centralizer (Λ : Set G) := by
    refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hΛ_le_centw hl)
  have hzpw_le_centt : zpowers w ≤ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 htw.symm)
  have ht_centw : t ∈ centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 htw
  have ht_sup : t ∈ Λ ⊔ zpowers w := by rw [← hcent]; exact ht_centw
  obtain ⟨l, hl, c, hc, htc⟩ :=
    CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hzpw_le_centΛ ht_sup
  have hc_or : c = 1 ∨ c = w := mem_zpowers_sq_eq_one_or hw2 hc
  have hc2 : c * c = 1 := by
    rcases hc_or with h | h
    · rw [h, mul_one]
    · rw [h, hw2]
  have hct : c * t = t * c := by
    rcases hc_or with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact htw.symm
  have hc_centΛ : c ∈ centralizer (Λ : Set G) := hzpw_le_centΛ hc
  have hl_eq : l = t * c := by
    rw [htc, mul_assoc, hc2, mul_one]
  have hl_sq : l * l = 1 := by
    calc l * l = (t * c) * (t * c) := by rw [hl_eq]
      _ = t * (c * t) * c := by group
      _ = t * (t * c) * c := by rw [hct]
      _ = (t * t) * (c * c) := by group
      _ = 1 := by rw [ht2, hc2, one_mul]
  have hl_ne : l ≠ 1 := by
    intro hl1
    have ht_eq_c : t = c := by
      have h1 : t * c = 1 := by rw [← hl_eq, hl1]
      calc t = t * c * c := by rw [mul_assoc, hc2, mul_one]
        _ = 1 * c := by rw [h1]
        _ = c := one_mul c
    rcases hc_or with h | h
    · exact ht1 (by rw [ht_eq_c, h])
    · exact htne (by rw [ht_eq_c, h])
  have hl_ord : orderOf l = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hl_sq) hl_ne
  set C : Subgroup G := Λ ⊓ centralizer ({l} : Set G) with hCdef
  have hC_le_centw : C ≤ centralizer ({w} : Set G) := fun x hx => hΛ_le_centw hx.1
  have hC_disj : Disjoint C (zpowers w) := hdisj.mono_left inf_le_left
  have hle : centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) ≤ C ⊔ zpowers w := by
    intro x hx
    obtain ⟨hxw, hxt⟩ := hx
    have hxw' : x ∈ Λ ⊔ zpowers w := by rw [← hcent]; exact hxw
    obtain ⟨l', hl', b, hb, hxlb⟩ :=
      CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hzpw_le_centΛ hxw'
    have hb_comm_t : b * t = t * b :=
      Subgroup.mem_centralizer_singleton_iff.1 (hzpw_le_centt hb)
    have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hxt
    have h1 : (l' * b) * t = t * (l' * b) := by rw [← hxlb]; exact hxt'
    have hlt : l' * t = t * l' := by
      apply mul_right_cancel
      calc (l' * t) * b = l' * (t * b) := by group
        _ = l' * (b * t) := by rw [hb_comm_t.symm]
        _ = (l' * b) * t := by group
        _ = t * (l' * b) := h1
        _ = (t * l') * b := by group
    have hl'_comm_l : l' * l = l * l' := by
      have hlt' : l' * (l * c) = (l * c) * l' := by rw [← htc]; exact hlt
      apply mul_right_cancel
      calc (l' * l) * c = l' * (l * c) := by group
        _ = (l * c) * l' := hlt'
        _ = l * (c * l') := by group
        _ = l * (l' * c) := by rw [(Subgroup.mem_centralizer_iff.1 hc_centΛ l' hl').symm]
        _ = (l * l') * c := by group
    rw [hxlb]
    exact Subgroup.mul_mem_sup
      ⟨hl', Subgroup.mem_centralizer_singleton_iff.2 hl'_comm_l⟩ hb
  have hge : C ⊔ zpowers w ≤ centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) := by
    refine sup_le (le_inf hC_le_centw ?_)
      (le_inf (by rw [hcent]; exact le_sup_right) hzpw_le_centt)
    intro x hx
    obtain ⟨hxΛ, hxCl⟩ := hx
    have hx_comm_l : x * l = l * x := Subgroup.mem_centralizer_singleton_iff.1 hxCl
    have hx_comm_c : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc_centΛ x hxΛ
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc x * t = x * (l * c) := by rw [← htc]
      _ = (x * l) * c := by group
      _ = (l * x) * c := by rw [hx_comm_l]
      _ = l * (x * c) := by group
      _ = l * (c * x) := by rw [hx_comm_c]
      _ = (l * c) * x := by group
      _ = t * x := by rw [htc]
  have hD : centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) = C ⊔ zpowers w :=
    le_antisymm hle hge
  rw [hD]
  exact centFacts_of_split (C := C) (w := w) hw2 hw1 hC_le_centw hC_disj
    (co3_centralizer_cases hΛ hl hl_ord)

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
