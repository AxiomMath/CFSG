module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open Subgroup

theorem le_of_isSylowOf_gamma {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y) : P ≤ Y := by
  by_cases hP : P = ⊥
  · rw [hP]
    exact bot_le
  · exact (le_inf hPsyl.le Subgroup.le_normalizer).trans (hΓ P le_rfl hP)

theorem dvd_card_of_isSylowOf_gamma {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hpF : p ∣ Nat.card F) : p ∣ Nat.card Y := by
  have hk : 0 < (Nat.card F).factorization p :=
    (Fact.out : p.Prime).factorization_pos_of_dvd (Nat.card_pos.ne') hpF
  have hpP : p ∣ Nat.card P := by
    rw [hPsyl.card_eq]
    exact dvd_pow_self p hk.ne'
  exact hpP.trans (Subgroup.card_dvd_of_le (le_of_isSylowOf_gamma hPsyl hΓ))

theorem not_dvd_card_center_of_gamma {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hYF : Y ≤ F) (hYne : Y ≠ F) : ¬ p ∣ Nat.card (Subgroup.center ↥F) := by
  intro hpZ
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥F) p hpZ
  let zc : ↥F := (z : Subgroup.center ↥F)
  have hzc : zc ∈ Subgroup.center ↥F := z.2
  have hzorder' : orderOf zc = p := by
    rw [Subgroup.orderOf_coe]
    exact hzorder
  have hzcne : zc ≠ 1 := by
    intro h
    have h1 : orderOf zc = 1 := by
      rw [h]
      exact orderOf_one
    exact (Fact.out : p.Prime).ne_one (hzorder'.symm.trans h1)
  let U' : Subgroup ↥F := Subgroup.zpowers zc
  have hU'normal : U'.Normal := by
    change (Subgroup.zpowers zc).Normal
    exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
  have hU'p : IsPGroup p U' := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card (Subgroup.zpowers zc) = p ^ 1
    rw [Nat.card_zpowers, hzorder', pow_one]
  have hU'ne : U' ≠ ⊥ := by
    change Subgroup.zpowers zc ≠ ⊥
    exact Subgroup.zpowers_ne_bot.mpr hzcne
  obtain ⟨Q, hQ⟩ := hPsyl
  haveI : U'.Normal := hU'normal
  have hle : U' ≤ Q := IsPGroup.le_sylow_of_normal hU'p Q
  let U : Subgroup X := U'.map F.subtype
  have hUP : U ≤ P := by
    change U'.map F.subtype ≤ P
    rw [← hQ]
    exact Subgroup.map_mono hle
  have hUne : U ≠ ⊥ := by
    intro h
    exact hU'ne ((Subgroup.map_eq_bot_iff_of_injective U' F.subtype_injective).mp h)
  have hFN : F ≤ Subgroup.normalizer (U : Set X) := by
    have hUF : U ≤ F := Subgroup.map_subtype_le U'
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hUF).mp ?_
    have hsub : U.subgroupOf F = U' := by
      change (U'.map F.subtype).subgroupOf F = U'
      simpa only [Subgroup.subgroupOf] using
        Subgroup.comap_map_eq_self_of_injective F.subtype_injective U'
    rw [hsub]
    exact hU'normal
  have hFY : F ≤ Y := by
    have := hΓ U hUP hUne
    rwa [inf_eq_left.mpr hFN] at this
  exact hYne (le_antisymm hYF hFY)

private theorem normalizer_le_subgroupOf_of_gamma {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {F Y P : Subgroup X} (hPsylY : CFSG.ABGLocalTools.IsSylowOf p P Y)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hYF : Y ≤ F) {Q : Subgroup ↥F} (hQne : Q ≠ ⊥) (hQp : IsPGroup p Q)
    (hQY : Q ≤ Y.subgroupOf F) :
    Subgroup.normalizer (Q : Set ↥F) ≤ Y.subgroupOf F := by
  intro q hq
  let Qx : Subgroup X := Q.map F.subtype
  have hQxY : Qx ≤ Y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hQY hy
  have hQxne : Qx ≠ ⊥ := by
    intro h
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective Q F.subtype_injective).mp h)
  have hQxp : IsPGroup p Qx := hQp.map F.subtype
  obtain ⟨S, hSle⟩ := (hQxp.comap_subtype (K := Y)).exists_le_sylow
  let T : Subgroup X := (S : Subgroup ↥Y).map Y.subtype
  have hT : CFSG.ABGLocalTools.IsSylowOf p T Y := ⟨S, rfl⟩
  have hQxT : Qx ≤ T := by
    intro x hx
    have hxY : x ∈ Y := hQxY hx
    exact ⟨⟨x, hxY⟩, hSle hx, rfl⟩
  obtain ⟨k, hkY, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPsylY hT
  have hkF : k ∈ F := hYF hkY
  let U : Subgroup X := Qx.map (MulAut.conj k⁻¹).toMonoidHom
  have hUP : U ≤ P := by
    intro u hu
    obtain ⟨x, hxQx, rfl⟩ := hu
    have hxP : k⁻¹ * x * k ∈ P := (hconj x).mp (hQxT hxQx)
    simpa [U, MulAut.conj_apply] using hxP
  have hUne : U ≠ ⊥ := by
    intro h
    apply hQxne
    exact (Subgroup.map_eq_bot_iff_of_injective Qx (MulAut.conj k⁻¹).injective).mp h
  have hFU : F ⊓ Subgroup.normalizer (U : Set X) ≤ Y := hΓ U hUP hUne
  have hqNQx : (q : X) ∈ Subgroup.normalizer (Qx : Set X) :=
    Subgroup.le_normalizer_map F.subtype (Subgroup.mem_map_of_mem F.subtype hq)
  let q' : X := k⁻¹ * (q : X) * k
  have hq'F : q' ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hkF) q.2) hkF
  have hq'NU : q' ∈ Subgroup.normalizer (U : Set X) := by
    change q' ∈ Subgroup.normalizer
      ((Qx.map (MulAut.conj k⁻¹).toMonoidHom : Subgroup X) : Set X)
    rw [← Subgroup.map_equiv_normalizer_eq Qx (MulAut.conj k⁻¹)]
    have hmem : (MulAut.conj k⁻¹) (q : X) ∈
        (Subgroup.normalizer (Qx : Set X)).map (MulAut.conj k⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hqNQx
    simpa [q', MulAut.conj_apply] using hmem
  have hq'Y : q' ∈ Y := hFU (Subgroup.mem_inf.mpr ⟨hq'F, hq'NU⟩)
  have hqY : (q : X) ∈ Y := by
    have hqeq : (q : X) = k * q' * k⁻¹ := by
      simp only [q']
      group
    rw [hqeq]
    exact Y.mul_mem (Y.mul_mem hkY hq'Y) (Y.inv_mem hkY)
  rwa [Subgroup.mem_subgroupOf]

theorem isStronglyPEmbedded_subgroupOf_of_gamma {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hYF : Y ≤ F) (hYne : Y ≠ F) (hpF : p ∣ Nat.card F) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p (Y.subgroupOf F) := by
  have hPY : P ≤ Y := le_of_isSylowOf_gamma hPsyl hΓ
  have hPsylY : CFSG.ABGLocalTools.IsSylowOf p P Y :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hPsyl hPY hYF
  have hY'ne : Y.subgroupOf F ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hYne (le_antisymm hYF htop)
  have hpY : p ∣ Nat.card Y := dvd_card_of_isSylowOf_gamma hPsyl hΓ hpF
  have hpM : p ∣ Nat.card (Y.subgroupOf F) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYF).toEquiv]
    exact hpY
  exact CFSG.LocalAnalysis.RankThreeUC.isStronglyPEmbedded_of_normalizer_le (G := ↥F)
    hY'ne hpM fun Q hQne hQp hQY =>
      normalizer_le_subgroupOf_of_gamma hPsylY hΓ hYF hQne hQp hQY

theorem not_dvd_card_inf_conj_of_gamma {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hYF : Y ≤ F) (hYne : Y ≠ F) (hpF : p ∣ Nat.card F) :
    ∀ k ∈ F, k ∉ Y →
      ¬ p ∣ Nat.card (Y ⊓ Y.map (MulAut.conj k).toMonoidHom : Subgroup X) := by
  have hStr := isStronglyPEmbedded_subgroupOf_of_gamma hPsyl hΓ hYF hYne hpF
  intro k hkF hkY
  have hkg : (⟨k, hkF⟩ : ↥F) ∉ Y.subgroupOf F := by
    intro h
    exact hkY h
  have hnd := hStr.2.2 ⟨k, hkF⟩ hkg
  have hmap : (Y.subgroupOf F ⊓
      (Y.subgroupOf F).map (MulAut.conj (⟨k, hkF⟩ : ↥F)).toMonoidHom).map F.subtype =
      Y ⊓ Y.map (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ F.subtype_injective]
    congr 1
    · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYF]
    · rw [Subgroup.map_map]
      have hcomp : F.subtype.comp (MulAut.conj (⟨k, hkF⟩ : ↥F)).toMonoidHom =
          (MulAut.conj k).toMonoidHom.comp F.subtype := by
        ext y
        simp [MulAut.conj_apply]
      rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hYF]
  intro hdvd
  apply hnd
  rw [← hmap, Subgroup.card_map_of_injective F.subtype_injective] at hdvd
  exact hdvd

theorem inf_normalizer_le_of_gamma {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {F Y P : Subgroup X} (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P F)
    (hΓ : ∀ U : Subgroup X, U ≤ P → U ≠ ⊥ →
      F ⊓ Subgroup.normalizer (U : Set X) ≤ Y)
    (hYF : Y ≤ F) (hYne : Y ≠ F) (hpF : p ∣ Nat.card F) :
    F ⊓ Subgroup.normalizer (Y : Set X) ≤ Y := by
  intro k hk
  obtain ⟨hkF, hkN⟩ := Subgroup.mem_inf.mp hk
  by_contra hkY
  have hnd := not_dvd_card_inf_conj_of_gamma hPsyl hΓ hYF hYne hpF k hkF hkY
  apply hnd
  have hmap : Y.map (MulAut.conj k).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hkN
  have hdvdY : p ∣ Nat.card Y := dvd_card_of_isSylowOf_gamma hPsyl hΓ hpF
  rw [hmap, inf_idem]
  exact hdvdY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
