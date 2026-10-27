module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne.CTP

section Abstract

variable {Y : Type} [Group Y] {L : Subgroup Y}

theorem mem_fixedSubgroup_conjNormal [L.Normal] {b : Y} {l : ↥L} :
    l ∈ fixedSubgroup (MulAut.conjNormal b : MulAut ↥L) ↔ b * (l : Y) = (l : Y) * b := by
  rw [mem_fixedSubgroup, ← Subtype.coe_inj, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]

theorem isOuterOfOrder_conjNormal [L.Normal] (hC : Subgroup.centralizer (L : Set Y) = ⊥) {b : Y}
    (hb5 : b ^ 5 = 1) (hbL : b ∉ L) : IsOuterOfOrder 5 (MulAut.conjNormal b : MulAut ↥L) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ L.one_mem)
  refine ⟨orderOf_eq_prime (by rw [← map_pow, hb5, map_one]) ?_, fun g hg => ?_⟩
  · intro h
    apply hb1
    have hb : b ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : b * l = l * b := by
        have h2 : ((MulAut.conjNormal b : MulAut ↥L) ⟨l, hl⟩ : Y) = l := by rw [h]; rfl
        rw [MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul] at h2
        exact h2
      exact h1.symm
    rw [hC] at hb
    exact Subgroup.mem_bot.mp hb
  · apply hbL
    have hb : (g : Y)⁻¹ * b ∈ Subgroup.centralizer (L : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h2 := congrArg (fun φ : MulAut ↥L => (φ ⟨l, hl⟩ : Y)) hg
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at h2
      calc l * ((g : Y)⁻¹ * b) = (g : Y)⁻¹ * ((g : Y) * l * (g : Y)⁻¹) * b := by group
        _ = (g : Y)⁻¹ * (b * l * b⁻¹) * b := by rw [h2]
        _ = (g : Y)⁻¹ * b * l := by group
    rw [hC, Subgroup.mem_bot] at hb
    have hgb : b = (g : Y) := by
      calc b = (g : Y) * ((g : Y)⁻¹ * b) := by group
        _ = (g : Y) := by rw [hb, mul_one]
    rw [hgb]
    exact g.2

theorem le_centralizer_sup_of_fieldAutData [L.Normal] (hC : Subgroup.centralizer (L : Set Y) = ⊥)
    (hd : FieldAutData ↥L 5) {x b : Y} (hxL : x ∈ L) (hx1 : x ≠ 1) (hx5 : x ^ 5 = 1)
    (hb5 : b ^ 5 = 1) (hbL : b ∉ L) (hxb : x * b = b * x) :
    L ≤ Subgroup.centralizer ({b} : Set Y) ⊔ Subgroup.centralizer ({x * b} : Set Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxbL : x * b ∉ L := fun h => hbL (by simpa using L.mul_mem (L.inv_mem hxL) h)
  have hxb5 : (x * b) ^ 5 = 1 := by
    rw [(show Commute x b from hxb).mul_pow, hx5, hb5, one_mul]
  set σ : MulAut ↥L := MulAut.conjNormal b with hσdef
  set τ : MulAut ↥L := MulAut.conjNormal (x * b) with hτdef
  have hσ : IsOuterOfOrder 5 σ := isOuterOfOrder_conjNormal hC hb5 hbL
  have hτ : IsOuterOfOrder 5 τ := isOuterOfOrder_conjNormal hC hxb5 hxbL
  have hxfix : (⟨x, hxL⟩ : ↥L) ∈ fixedSubgroup σ :=
    mem_fixedSubgroup_conjNormal.mpr hxb.symm
  have hx5dvd : 5 ∣ Nat.card (fixedSubgroup σ) := by
    have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    have h := orderOf_dvd_natCard (⟨⟨x, hxL⟩, hxfix⟩ : ↥(fixedSubgroup σ))
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord] at h
  have hne : fixedSubgroup σ ≠ fixedSubgroup τ := by
    intro heq
    apply hx1
    have hcen := hd.center σ hσ hx5dvd ⟨x, hxL⟩ hxfix fun y hy => by
      have hy' : y ∈ fixedSubgroup τ := heq ▸ hy
      have h1 : b * (y : Y) = (y : Y) * b := mem_fixedSubgroup_conjNormal.mp hy
      have h2 : (x * b) * (y : Y) = (y : Y) * (x * b) := mem_fixedSubgroup_conjNormal.mp hy'
      apply Subtype.ext
      show x * (y : Y) = (y : Y) * x
      have h3 : x * (y : Y) * b = (y : Y) * x * b := by
        calc x * (y : Y) * b = x * (b * (y : Y)) := by rw [mul_assoc, ← h1]
          _ = (x * b) * (y : Y) := by rw [mul_assoc]
          _ = (y : Y) * (x * b) := h2
          _ = (y : Y) * x * b := by rw [mul_assoc]
      exact mul_right_cancel h3
    exact congrArg Subtype.val hcen
  rcases hd.gen σ τ hσ hτ hne with hg | hsmall
  · intro l hl
    have hle : Subgroup.closure ((fixedSubgroup σ : Set ↥L) ∪ (fixedSubgroup τ : Set ↥L)) ≤
        (Subgroup.centralizer ({b} : Set Y) ⊔ Subgroup.centralizer ({x * b} : Set Y)).comap
          L.subtype := by
      rw [Subgroup.closure_le]
      rintro y (hy | hy)
      · exact Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr
          (mem_fixedSubgroup_conjNormal.mp hy).symm)
      · exact Subgroup.mem_sup_right (Subgroup.mem_centralizer_singleton_iff.mpr
          (mem_fixedSubgroup_conjNormal.mp hy).symm)
    have := hle (hg ▸ Subgroup.mem_top (⟨l, hl⟩ : ↥L))
    exact this
  · exact absurd hx5dvd hsmall

theorem le_iSup_centralizer_of_fieldAutData [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (hd : FieldAutData ↥L 5) {B : Subgroup Y} {x b : Y}
    (hB : IsElemAbelian 5 B) (hxB : x ∈ B) (hxL : x ∈ L) (hx1 : x ≠ 1) (hbB : b ∈ B)
    (hbL : b ∉ L) :
    L ≤ ⨆ c ∈ {c : Y | c ∈ B ∧ c ∉ L}, Subgroup.centralizer ({c} : Set Y) := by
  have hxb : x * b = b * x :=
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hxB⟩ : B) ⟨b, hbB⟩)
  have hxbL : x * b ∉ L := fun h => hbL (by simpa using L.mul_mem (L.inv_mem hxL) h)
  refine (le_centralizer_sup_of_fieldAutData hC hd hxL hx1 (hB.2 x hxB) (hB.2 b hbB) hbL
    hxb).trans (sup_le ?_ ?_)
  · exact le_iSup₂_of_le b ⟨hbB, hbL⟩ le_rfl
  · exact le_iSup₂_of_le (x * b) ⟨B.mul_mem hxB hbB, hxbL⟩ le_rfl

theorem le_iSup_centralizer_of_fieldAutData_of_card [Finite Y] [L.Normal]
    (hC : Subgroup.centralizer (L : Set Y) = ⊥) (hd : FieldAutData ↥L 5) {B : Subgroup Y} {x : Y}
    (hB : IsElemAbelian 5 B) (hBc : Nat.card B = 5 ^ 2) (hxB : x ∈ B) (hxL : x ∈ L) (hx1 : x ≠ 1)
    (hBL : ∀ b ∈ B, b ∈ L → b ∈ Subgroup.zpowers x) :
    L ≤ ⨆ c ∈ {c : Y | c ∈ B ∧ c ∉ L}, Subgroup.centralizer ({c} : Set Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨b, hbB, hbL⟩ : ∃ b ∈ B, b ∉ L := by
    by_contra hcon
    push Not at hcon
    have hle : B ≤ Subgroup.zpowers x := fun b hb => hBL b hb (hcon b hb)
    have h1 : Nat.card B ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (hB.2 x hxB) hx1, hBc] at h1
    omega
  exact le_iSup_centralizer_of_fieldAutData hC hd hB hxB hxL hx1 hbB hbL

end Abstract

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
