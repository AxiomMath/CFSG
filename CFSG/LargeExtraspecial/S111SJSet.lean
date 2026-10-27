module

public import CFSG.LargeExtraspecial.S111SIMoves

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.ComponentClassification

instance timmesfeldLayer_normal (H : Type*) [Group H] : (timmesfeldLayer H).Normal :=
  Layer.normal H

theorem conj_eq_of_mem_centralizer {H : Type*} [Group H] [Finite H] {O E F : Subgroup H}
    (hON : O.Normal) (hEn : E.Normal) (h3 : Nat.card O ∣ 3) (hF : F = O ⊔ E)
    (hFc : ∀ v : H, v * v = 1 → v ∈ centralizer (F : Set H) → v = 1)
    {c : H} (hc2 : c * c = 1) (hcE : ∀ e ∈ E, e * c = c * e) (m : H)
    (hcomm : (m * c * m⁻¹) * c = c * (m * c * m⁻¹)) : m * c * m⁻¹ = c := by
  by_contra hne
  set c' := m * c * m⁻¹ with hc'
  have hkill : ∀ v : H, v * v = 1 → (∀ e ∈ E, e * v = v * e) → (∀ o ∈ O, o * v = v * o) →
      v = 1 := by
    intro v hv2 hvE hvO
    refine hFc v hv2 (mem_centralizer_iff.mpr fun f hf => ?_)
    have hle : O ⊔ E ≤ centralizer ({v} : Set H) :=
      sup_le (fun o ho => mem_centralizer_singleton_iff.mpr (hvO o ho))
        (fun e he => mem_centralizer_singleton_iff.mpr (hvE e he))
    rw [hF] at hf
    exact mem_centralizer_singleton_iff.mp (hle hf)
  have hc'E : ∀ e ∈ E, e * c' = c' * e := by
    intro e he
    have he' : m⁻¹ * e * m ∈ E := by
      have := hEn.conj_mem e he m⁻¹
      simpa using this
    have h1 := hcE _ he'
    calc e * c' = m * ((m⁻¹ * e * m) * c) * m⁻¹ := by rw [hc']; group
      _ = m * (c * (m⁻¹ * e * m)) * m⁻¹ := by rw [h1]
      _ = c' * e := by rw [hc']; group
  have hc'2 : c' * c' = 1 := by
    calc c' * c' = m * (c * c) * m⁻¹ := by rw [hc']; group
      _ = 1 := by rw [hc2]; group
  have hc1 : c ≠ 1 := by
    intro h
    apply hne
    rw [hc', h]
    group
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    calc c = m⁻¹ * c' * m := by rw [hc']; group
      _ = 1 := by rw [h]; group
  have hO3 : Nat.card O = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exfalso
      refine hc1 (hkill c hc2 hcE fun o ho => ?_)
      rw [Subgroup.card_eq_one.mp h1, mem_bot] at ho
      rw [ho, one_mul, mul_one]
    · exact h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNb : O ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hO3
    omega
  obtain ⟨⟨y, hyN⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hNb
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyo : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := hO3 ▸ Subgroup.orderOf_dvd_natCard _ hyN
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1'
    · exact h
  have hNy : O = zpowers y := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hyN) ?_).symm
    rw [Nat.card_zpowers, hyo, hO3]
  have hcases : ∀ x : H, x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ := by
    intro x
    rcases eq_one_or_eq_or_eq_inv_of_orderOf_eq_three hyo
      (hNy ▸ hON.conj_mem y hyN x) with h | h | h
    · exfalso
      apply hy1'
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact Or.inl h
    · exact Or.inr h
  have hinv : ∀ v : H, v * v = 1 → v ≠ 1 → (∀ e ∈ E, e * v = v * e) → v * y * v⁻¹ = y⁻¹ := by
    intro v hv2 hv1 hvE
    rcases hcases v with h | h
    · exact absurd (hkill v hv2 hvE fun o ho => commute_of_mem_zpowers h (hNy ▸ ho)) hv1
    · exact h
  have hcy := hinv c hc2 hc1 hcE
  have hc'y := hinv c' hc'2 hc'1 hc'E
  have hv2 : (c * c') * (c * c') = 1 := by
    calc (c * c') * (c * c') = c * (c' * c) * c' := by group
      _ = c * (c * c') * c' := by rw [hcomm]
      _ = (c * c) * (c' * c') := by group
      _ = 1 := by rw [hc2, hc'2, one_mul]
  have hvE : ∀ e ∈ E, e * (c * c') = (c * c') * e := by
    intro e he
    calc e * (c * c') = (e * c) * c' := by group
      _ = c * (e * c') := by rw [hcE e he]; group
      _ = c * c' * e := by rw [hc'E e he]; group
  have hvy : (c * c') * y * (c * c')⁻¹ = y := by
    calc (c * c') * y * (c * c')⁻¹ = c * (c' * y * c'⁻¹) * c⁻¹ := by group
      _ = (c * y * c⁻¹)⁻¹ := by rw [hc'y]; group
      _ = y := by rw [hcy, inv_inv]
  have h1 := hkill (c * c') hv2 hvE fun o ho => commute_of_mem_zpowers hvy (hNy ▸ ho)
  apply hne
  calc c' = c⁻¹ * (c * c') := by group
    _ = c := by rw [h1, mul_one]; exact inv_eq_of_mul_eq_one_right hc2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem eq_one_of_mem_Lbar_of_commute (hy : Hyp S g) (hirr : ¬ S.IsReducible)
    (h6 : 6 ≤ S.width)
    (h55 : Nat.card (timmesfeldOddCore S.Mbar) ∣ 3 ∧
      CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∧
      timmesfeldFStar S.Mbar = timmesfeldOddCore S.Mbar ⊔ timmesfeldLayer S.Mbar)
    {x : S.Mbar} (hx : (x : S.O) ∈ S.Lbar g)
    (hxE : ∀ e ∈ timmesfeldLayer S.Mbar, e * x = x * e) : x = 1 := by
  by_contra hx1
  have hx2 : x * x = 1 := Subtype.ext (S4.mul_self_of_mem_Lbar S hy.hyp4.conj_mem hx)
  refine false_of_isolated hy hirr h6 hx (fun h => hx1 (Subtype.ext h)) fun m hm hc => ?_
  have h := conj_eq_of_mem_centralizer (S5.timmesfeldOddCore_normal S.Mbar)
    (Layer.normal S.Mbar) h55.1 h55.2.2 (fun _ hv2 hv => eq_one_of_mem_centralizer_fstar hv2 hv)
    hx2 hxE ⟨m, hm⟩ (Subtype.ext (by simpa using hc))
  simpa using congrArg Subtype.val h

end CFSG.LargeExtraspecial.S11
