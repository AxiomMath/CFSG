module

public import CFSG.LocalAnalysis.EvenBN.U5.LinOddAction
public import CFSG.LocalAnalysis.EvenBN.U5.LinLayer
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TwelveCommon
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.LinRadicalsQuot

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.LinearThree

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem lin_sec311NotTrans (hl : d.LinCtx) (k : d.Know10) : d.Sec311NotTrans := by
  intro S hS hP J hJodd hJle htr
  have ha := k.s9a S hS hP
  have hES : d.E ≤ S := by rw [ha.S_eq]; exact le_sup_left
  have hDS : d.D ≤ S := by rw [ha.S_eq]; exact le_sup_right
  have hSN : ∀ s ∈ S, s ∈ normalizer (d.E : Set G) := fun s hs =>
    d.L₂_le_normalizer_E (hS.le hs)
  haveI hEn : (d.E.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).2 hSN
  have hJS : J ≤ normalizer (S : Set G) :=
    hJle.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hJE : J ≤ normalizer (d.E : Set G) := (hJle.trans inf_le_left).trans inf_le_right
  have hFD : d.F ≤ d.D := sec312_F_le_D hl.toCaseHyp k
  have hDF : d.D ≤ centralizer (d.F : Set G) := sec312_D_le_centralizer_F hl.toCaseHyp k
  have hf2 : 2 ≤ f := sec312_two_le hl.toCaseHyp
  have hq2 : 2 ≤ (2 ^ f) ^ 2 := by
    have h1 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact h1.trans (Nat.le_self_pow (by norm_num) _)
  obtain ⟨R₁, R₂, hrad⟩ := lin_exists_radicals_of_isSylowOf_M₂ hl ha.sylow₂
  have hQ0 := LinCase.radicals_quotient hES
    (inf_le_left : S ⊓ centralizer (d.I₂ : Set G) ≤ S) ha.S_eq₂.symm ha.E_inf₂ hrad
  obtain ⟨Q₁, Q₂, hQ⟩ : ∃ Q₁ Q₂ : Subgroup (↥S ⧸ d.E.subgroupOf S),
      Radicals (⊤ : Subgroup (↥S ⧸ d.E.subgroupOf S)) Q₁ Q₂ ((2 ^ f) ^ 2) := ⟨_, _, hQ0⟩
  have hne : Q₁ ≠ Q₂ := hQ.ne hq2
  obtain ⟨a, haQ₁, haQ₂⟩ : ∃ a ∈ Q₁, a ∉ Q₂ := by
    by_contra hcon
    push Not at hcon
    exact hne (Subgroup.eq_of_le_of_card_ge (fun a ha => hcon a ha)
      (hQ.card₂.trans hQ.card₁.symm).le)
  obtain ⟨b, hbQ₂, hbQ₁⟩ : ∃ b ∈ Q₂, b ∉ Q₁ := by
    by_contra hcon
    push Not at hcon
    exact hne.symm (Subgroup.eq_of_le_of_card_ge (fun b hb => hcon b hb)
      (hQ.card₁.trans hQ.card₂.symm).le)
  have hmk_eq : ∀ (z w : G) (hz : z ∈ S) (hw : w ∈ S), z⁻¹ * w ∈ d.E →
      QuotientGroup.mk' (d.E.subgroupOf S) ⟨z, hz⟩ =
        QuotientGroup.mk' (d.E.subgroupOf S) ⟨w, hw⟩ := by
    intro z w hz hw hzw
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact mem_subgroupOf.2 hzw
  have hdecomp : ∀ t : ↥S ⧸ d.E.subgroupOf S, ∃ (x : G) (hx : x ∈ d.D),
      QuotientGroup.mk' (d.E.subgroupOf S) ⟨x, hDS hx⟩ = t := by
    intro t
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (d.E.subgroupOf S) t
    have hs : (s : G) ∈ d.E ⊔ d.D := by rw [← ha.S_eq]; exact s.2
    obtain ⟨e, he, x, hx, hex⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (fun g hg => hSN g (hDS hg)) hs
    refine ⟨x, hx, hmk_eq _ _ _ _ ?_⟩
    have h1 : x⁻¹ * (s : G) = x⁻¹ * e * x := by rw [hex]; group
    have h2 := (mem_normalizer_iff.1 (inv_mem (hSN x (hDS hx))) e).1 he
    rw [inv_inv] at h2
    rw [h1]
    exact h2
  have hFN : d.F ≤ normalizer ((d.E ⊓ d.D : Subgroup G) : Set G) := by
    intro g hg
    have hgD : g ∈ d.D := hFD hg
    have hgE : g ∈ normalizer (d.E : Set G) := hSN g (hDS hgD)
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨hzE, hzD⟩ := Subgroup.mem_inf.1 hz
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hgE z).1 hzE,
      d.D.mul_mem (d.D.mul_mem hgD hzD) (d.D.inv_mem hgD)⟩
  have hFcen : ∀ (z : G) (hz : z ∈ d.F),
      QuotientGroup.mk' (d.E.subgroupOf S) ⟨z, hDS (hFD hz)⟩ ∈ Q₁ ⊓ Q₂ := by
    intro z hz
    rw [hQ.inf_eq]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, mem_centralizer_iff.2 fun t _ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hdecomp t
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (d.E.subgroupOf S))
      (Subtype.ext (mem_centralizer_iff.1 (hDF hx) z hz).symm)
  have hQF : ∀ (z : G) (hz : z ∈ S), z ∈ (d.E ⊓ d.D) ⊔ d.F →
      QuotientGroup.mk' (d.E.subgroupOf S) ⟨z, hz⟩ ∈ Q₁ ⊓ Q₂ := by
    intro z hz hzQ
    obtain ⟨e, he, f', hf', hef⟩ := exists_mul_of_mem_sup_of_le_normalizer hFN hzQ
    have hf'S : f' ∈ S := hDS (hFD hf')
    have heq : QuotientGroup.mk' (d.E.subgroupOf S) ⟨z, hz⟩ =
        QuotientGroup.mk' (d.E.subgroupOf S) ⟨f', hf'S⟩ := by
      refine hmk_eq _ _ _ _ ?_
      have h1 : z⁻¹ * f' = f'⁻¹ * e⁻¹ * f' := by rw [hef]; group
      have h2 := (mem_normalizer_iff.1 (inv_mem (hSN f' hf'S)) e⁻¹).1
        (d.E.inv_mem (Subgroup.mem_inf.1 he).1)
      rw [inv_inv] at h2
      rw [h1]
      exact h2
    rw [heq]
    exact hFcen f' hf'
  obtain ⟨x, hxD, hxa⟩ := hdecomp a
  obtain ⟨y, hyD, hyb⟩ := hdecomp b
  have hxQ : x ∉ (d.E ⊓ d.D) ⊔ d.F := by
    intro hx
    have := hQF x (hDS hxD) hx
    rw [hxa] at this
    exact haQ₂ this.2
  have hyQ : y ∉ (d.E ⊓ d.D) ⊔ d.F := by
    intro hy
    have := hQF y (hDS hyD) hy
    rw [hyb] at this
    exact hbQ₁ this.1
  obtain ⟨j, hj, hjxy⟩ := htr x hxD hxQ y hyD hyQ
  obtain ⟨hjx, hjxQ⟩ := LinCase.odd_conj_mem_radical hq2 hQ hJodd hJS hJE hj (hDS hxD)
    (by rw [hxa]; exact haQ₁)
  have hzS : (j * x * j⁻¹) * y⁻¹ ∈ S := S.mul_mem hjx (S.inv_mem (hDS hyD))
  have hzQ := hQF _ hzS hjxy
  have hmul : QuotientGroup.mk' (d.E.subgroupOf S) ⟨(j * x * j⁻¹) * y⁻¹, hzS⟩ =
      QuotientGroup.mk' (d.E.subgroupOf S) ⟨j * x * j⁻¹, hjx⟩ *
        (QuotientGroup.mk' (d.E.subgroupOf S) ⟨y, hDS hyD⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [hyb] at hmul
  have hbinv : b⁻¹ ∈ Q₁ := by
    have e1 : b⁻¹ = (QuotientGroup.mk' (d.E.subgroupOf S) ⟨j * x * j⁻¹, hjx⟩)⁻¹ *
        QuotientGroup.mk' (d.E.subgroupOf S) ⟨(j * x * j⁻¹) * y⁻¹, hzS⟩ := by
      rw [hmul]
      group
    rw [e1]
    exact Q₁.mul_mem (Q₁.inv_mem hjxQ) hzQ.1
  exact hbQ₁ (by simpa using Q₁.inv_mem hbinv)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
