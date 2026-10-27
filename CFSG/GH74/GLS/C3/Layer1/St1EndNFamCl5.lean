module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFam
public import CFSG.GH74.Generic.S45.LLinSel

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.ComponentClassification.RestrictedStd
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem center_le_pPrimeCore (h : Lem711Cfg X L K x y) : center ↥K ≤ pPrimeCore 2 ↥K := by
  intro z hz
  have h' : HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => Odd q ∧ 3 < q) :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨⟨4, rfl⟩, by norm_num⟩) h.l2
  have hc : center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ :=
    Stage1.Thm6.Glue.center_eq_bot_of_isL2Model (Stage1.Thm6.Glue.isL2Model_of_hasL2Model h')
  have hzc : (QuotientGroup.mk z : ↥K ⧸ pPrimeCore 2 ↥K) ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz k]
  rw [hc, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc
  exact hzc

theorem pPrimeCore_eq_center (h : Lem711Cfg X L K x y) : pPrimeCore 2 ↥K = center ↥K := by
  have hnt : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [h.card_K_bar]; norm_num)
  have hle : pPrimeCore 2 ↥K ≤ center ↥K := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple h.K_quasi (pPrimeCore 2 ↥K) with
      hle | htop
    · exact hle
    · exfalso
      have : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (not_nontrivial_iff_subsingleton.2 this) hnt
  exact le_antisymm hle h.center_le_pPrimeCore

theorem odd_card_center (h : Lem711Cfg X L K x y) : Odd (Nat.card (center ↥K)) := by
  rw [← h.pPrimeCore_eq_center]
  exact TwoThin.odd_card_pPrimeCore _

theorem isComponentOf_centralizer (h : Lem711Cfg X L K x y) :
    CFSG.Assembly.IsComponentOf K (centralizer ({x} : Set X)) :=
  (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.comp.1).2 h.comp.2

theorem centralizer_eq_bot (h : Lem711Cfg X L K x y) : centralizer (L : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  exact h.soc.centralizer_trivial n (Subgroup.mem_top n) fun l hl =>
    (Subgroup.mem_centralizer_iff.1 hn l hl).symm

theorem exists_noncomm (h : Lem711Cfg X L K x y) : ∃ a b : ↥L, a * b ≠ b * a :=
  IVK.exists_noncomm_of_le_isQuasisimple h.K_le h.K_quasi

theorem exists_hsrc (h : Lem711Cfg X L K x y) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      LieModel (↥K ⧸ center ↥K) .PSL 2 p f := by
  obtain ⟨p, f, hp, hf, hq, hmodel⟩ := h.l2
  let e : (↥K ⧸ pPrimeCore 2 ↥K) ≃* (↥K ⧸ center ↥K) :=
    QuotientGroup.quotientMulEquivOfEq h.pPrimeCore_eq_center
  refine ⟨p, f, hp, ?_, hf, by omega, LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩
  rintro rfl
  have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
  rw [hq] at h2
  exact absurd h2 (by decide)

theorem smallSource (h : Lem711Cfg X L K x y) : SmallSource K := by
  obtain ⟨p, f, hp, hp2, hf, hq, hmodel⟩ := h.exists_hsrc
  exact Or.inl ⟨p, f, hp, hp2, hf, hq, hmodel, h.odd_card_center⟩

end Lem711Cfg


theorem lem711_l5 (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 3) :
    Lem711Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro X _ _ L K x y h hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    have := Nat.even_iff.1 h2
    omega
  have := h.normal
  obtain ⟨p', f', hp', hp2', hf', hq', hmodel'⟩ := h.exists_hsrc
  obtain ⟨⟨hr, hf'', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := Generic.S45.LQ.stated_of_lieModel_PSL hm
  let φ : ↥L ≃* projectiveSL 5 F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
  exact Generic.S45.linear_selector_five_false (W := L) h.centralizer_eq_bot h.hx h.K_le
    h.isComponentOf_centralizer hp2' (Generic.S45.LQ.stated_of_lieModel_PSL hmodel')
    h.odd_card_center (le_refl 5) hr hp2 hf'' hF φ

theorem lem711_u5 (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 1) :
    Lem711Empty (fun X _ => LieModel X .PSU 5 p f) := by
  intro X _ _ L K x y h hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    have := Nat.even_iff.1 h2
    omega
  have := h.normal
  exact ComponentClassification.OddClassSelector.su_family_false (W := L) h.soc.simple h.exists_noncomm
    h.centralizer_eq_bot h.hx h.K_le h.isComponentOf_centralizer h.smallSource hp hp2 hf (le_refl 5) hm


end CFSG.GH74.GLS
