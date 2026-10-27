module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupConsAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.OddStandard.AltStdSecDich
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.RankThree.PartOne
open CFSG.Sporadic.Schreier (fixSub)

theorem lookup_generalizedFitting_normal (X : Type) [Group X] :
    (CFSG.generalizedFitting X).Normal := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal X

theorem index_le_card_outer {X : Type} [Group X] [Finite X] (W : Subgroup X) [W.Normal]
    (hC : centralizer (W : Set X) = ⊥) : W.index ≤ Nat.card (Outer W) := by
  let f : X →* Outer W := (QuotientGroup.mk' (inner W)).comp (MulAut.conjNormal (H := W))
  have hker : f.ker = W := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨w, hw⟩
      have hx : (w : X)⁻¹ * x ∈ centralizer (W : Set X) := by
        rw [mem_centralizer_iff]
        intro y hy
        have h1 := congrArg (fun φ : MulAut W => ((φ ⟨y, hy⟩ : W) : X)) hw
        simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
        calc y * ((w : X)⁻¹ * x) = (w : X)⁻¹ * ((w : X) * y * (w : X)⁻¹) * x := by group
          _ = (w : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
          _ = (w : X)⁻¹ * x * y := by group
      rw [hC, mem_bot, inv_mul_eq_one] at hx
      rw [← hx]
      exact w.2
    · intro hx
      exact ⟨⟨x, hx⟩, by ext y; simp [MulAut.conjNormal_apply]⟩
  have h1 : W.index = Nat.card (X ⧸ W) := rfl
  have h2 : Nat.card (X ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hker] at h2
  rw [h1, h2]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card f.range)

theorem almostSimple_setup {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {m : ℕ}
    (hK : CFSG.SectionRank.IsKGroupCat X) (hO : CFSG.oddCore X = ⊥) (h : ExactShape t A m)
    (hm : 5 ≤ m) (hF : AlmostSimple X) :
    ∃ (W : Subgroup X) (_ : W.Normal), IsSimpleGroup W ∧ (∃ x y : W, x * y ≠ y * x) ∧
      centralizer (W : Set X) = ⊥ ∧ Catalog W ∧ A ≤ W ∧
      CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)) := by
  obtain ⟨W, hWdef, hWs, hWnab⟩ := hF
  have hWN : W.Normal := hWdef ▸ lookup_generalizedFitting_normal X
  have : IsSimpleGroup W := hWs
  have hz : center W = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center W) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨x, y, hxy⟩ := hWnab
      exact hxy (Subgroup.mem_center_iff.mp (hc ▸ mem_top y) x)
  have hCW : centralizer (W : Set X) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ W := by
      have := CFSG.centralizer_generalizedFitting_le X (hWdef ▸ hx)
      rwa [← hWdef] at this
    have : (⟨x, hxW⟩ : W) ∈ center W := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 hx y y.2)
    rw [hz, mem_bot] at this
    rw [mem_bot]
    exact congrArg Subtype.val this
  have hcat : Catalog W := by
    have hq : IsSimpleGroup (↥W ⧸ (⊥ : Subgroup ↥W)) :=
      (QuotientGroup.quotientBot (G := ↥W)).isSimpleGroup
    exact CFSG.SectionRank.catalog_of_mulEquiv (QuotientGroup.quotientBot (G := ↥W)).symm
      (hK W ⊥ hq)
  have hpp : pPrimeCore 2 X = ⊥ := by
    rw [← ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]
    exact hO
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order] at this
  have hAcomp : CFSG.IsComponent (A.subgroupOf (centralizer ({t} : Set X))) :=
    isComponent_subgroupOf_centralizer h (by omega)
  have hAW : A ≤ W := by
    have h1 := CFSG.SeitzReduction.isComponent_centralizer_le_layer hpp ht2 h.le_cent hAcomp
    rw [hWdef]
    exact h1.trans le_sup_right
  exact ⟨W, hWN, hWs, hWnab, hCW, hcat, hAW,
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.le_cent).2
      hAcomp⟩

theorem not_mem_of_HN (hHN : HNLocalComponentsInput) {X : Type} [Group X] [Finite X] {t : X}
    {A W : Subgroup X} {m : ℕ} (h : ExactShape t A m) (hm : 9 ≤ m) (hAW : A ≤ W)
    (hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X)))
    (eHN : W ≃* NativeSporadic.HN) : t ∉ W := by
  intro htW
  obtain ⟨B, hB, ⟨φ⟩⟩ :=
    CFSG.ComponentClassification.RestrictedStd.exists_isComponent_centralizer_of_mem htW hAW hcomp
  have ht' : orderOf (⟨t, htW⟩ : W) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.order
  obtain ⟨eA⟩ := h.iso
  exact not_isLargeAlt_of_card_quotient (c := 44352000)
    (fun m' _ => lookup_factorial_div_two_ne (k := 11) (by norm_num [Nat.factorial])
      (by norm_num [Nat.factorial]) m')
    (hHN W eHN _ ht' B hB) ⟨m, hm, ⟨φ.trans eA⟩⟩

theorem exactShape_almostSimple (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : SporadicOuterOrderLeTwoSimple) {X : Type} [Group X] [Finite X] {t : X}
    {A : Subgroup X} {m : ℕ} (hK : CFSG.SectionRank.IsKGroupCat X) (hO : CFSG.oddCore X = ⊥)
    (h : ExactShape t A m) (hm : 9 ≤ m) (hF : AlmostSimple X) :
    SymOutcome t m ∨ (m = 10 ∧ HNOutcome t) := by
  obtain ⟨W, hWN, hWs, hWnab, hCW, hcat, hAW, hcomp⟩ := almostSimple_setup hK hO h (by omega) hF
  have := hWN
  rcases hlookup X W hWs hWnab hCW hcat t h.order A hAW hcomp m hm h.iso with
    ⟨N, ⟨eW⟩⟩ | ⟨hm10, ⟨eHN⟩⟩
  · exact Or.inl (symOutcome_of_alt h (by omega) hAW hCW hcomp eW).1
  · have htW : t ∉ W := not_mem_of_HN hHN h hm hAW hcomp eHN
    have hout : Nat.card (Outer W) ≤ 2 :=
      hOut .HN (Or.inr (Or.inr (Or.inl rfl))) W hWnab ⟨eHN⟩
    have hidx : W.index ≤ 2 := (index_le_card_outer W hCW).trans hout
    have hne : W.index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one] at h1
      exact htW (h1 ▸ mem_top t)
    refine Or.inr ⟨hm10, W, hWN, ?_, htW, ⟨eHN⟩⟩
    have : W.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega

theorem lookup_exists_mul_zpow_of_mem_sup {X : Type} [Group X] {A : Subgroup X} {t x : X}
    (hA : A ≤ centralizer ({t} : Set X)) (hx : x ∈ A ⊔ zpowers t) :
    ∃ a ∈ A, ∃ k : ℤ, x = a * t ^ k := by
  have hc : ∀ a ∈ A, ∀ k : ℤ, t ^ k * a = a * t ^ k := fun a ha k =>
    ((Commute.zpow_left (show Commute t a from (mem_centralizer_singleton_iff.1 (hA ha)).symm)
      k)).eq
  let S : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ k : ℤ, x = a * t ^ k}
      one_mem' := ⟨1, one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, k, rfl⟩ ⟨b, hb, l, rfl⟩
        refine ⟨a * b, mul_mem ha hb, k + l, ?_⟩
        calc a * t ^ k * (b * t ^ l) = a * (t ^ k * b) * t ^ l := by group
          _ = a * (b * t ^ k) * t ^ l := by rw [hc b hb k]
          _ = a * b * t ^ (k + l) := by rw [zpow_add]; group
      inv_mem' := by
        rintro _ ⟨a, ha, k, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, -k, ?_⟩
        calc (a * t ^ k)⁻¹ = (t ^ k)⁻¹ * a⁻¹ := by group
          _ = t ^ (-k) * a⁻¹ := by rw [zpow_neg]
          _ = a⁻¹ * t ^ (-k) := hc a⁻¹ (inv_mem ha) (-k) }
  have hle : A ⊔ zpowers t ≤ S := sup_le (fun a ha => ⟨a, ha, 0, by simp⟩) (by
    rw [zpowers_le]
    exact ⟨1, one_mem _, 1, by simp⟩)
  exact hle hx

theorem false_of_almostSimple_shape_one (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) {X : Type} [Group X] [Finite X]
    {t : X} {A : Subgroup X} {m : ℕ} (hK : CFSG.SectionRank.IsKGroupCat X)
    (hO : CFSG.oddCore X = ⊥) (h : ExactShape t A m) (hm : 9 ≤ m) (hF : AlmostSimple X)
    (hE : centralizer ({t} : Set X) ≤ A ⊔ zpowers t) : False := by
  obtain ⟨W, hWN, hWs, hWnab, hCW, hcat, hAW, hcomp⟩ := almostSimple_setup hK hO h (by omega) hF
  have := hWN
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order, sq] at this
  have hdecomp : t ∉ W → ∀ x ∈ W, x ∈ centralizer ({t} : Set X) → x ∈ A := by
    intro htW x hxW hxC
    obtain ⟨a, ha, k, rfl⟩ := lookup_exists_mul_zpow_of_mem_sup h.le_cent (hE hxC)
    have hk : t ^ k ∈ W := by
      have := mul_mem (inv_mem (hAW ha)) hxW
      simpa using this
    rcases lookup_zpow_eq_one_or_self ht2 k with h1 | h1
    · rw [h1, mul_one]
      exact ha
    · rw [h1] at hk
      exact absurd hk htW
  rcases hlookup X W hWs hWnab hCW hcat t h.order A hAW hcomp m hm h.iso with
    ⟨N, ⟨eW⟩⟩ | ⟨hm10, ⟨eHN⟩⟩
  · obtain ⟨-, htW, x, hxW, hxC, hxA⟩ := symOutcome_of_alt h (by omega) hAW hCW hcomp eW
    exact hxA (hdecomp htW x hxW hxC)
  · have htW : t ∉ W := not_mem_of_HN hHN h hm hAW hcomp eHN
    have hσ2 : (MulAut.conjNormal t : MulAut W) * MulAut.conjNormal t = 1 :=
      conjNormal_mul_self h.order
    have hσ1 : (MulAut.conjNormal t : MulAut W) ≠ 1 := by
      intro h1
      have h2 : t ∈ centralizer (W : Set X) := by
        rw [mem_centralizer_iff]
        intro w hw
        have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : X)) h1
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
        calc w * t = t * w * t⁻¹ * t := by rw [h3]
          _ = t * w := by group
      rw [hCW, mem_bot] at h2
      have h4 := h.order
      rw [h2, orderOf_one] at h4
      omega
    have hσ : orderOf (MulAut.conjNormal t : MulAut W) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
    obtain ⟨-, -, -, -, -, hcard, -⟩ :=
      hFour W hWs hWnab (Or.inr (Or.inl ⟨eHN⟩)) _ hσ (conjNormal_not_mem_inner hCW htW)
    have hCt : Nat.card (W ⊓ centralizer ({t} : Set X) : Subgroup X) = 3628800 := by
      rw [← map_fixSub_conjNormal, Subgroup.card_map_of_injective W.subtype_injective]
      exact hcard
    have hle : W ⊓ centralizer ({t} : Set X) ≤ A := fun x hx => hdecomp htW x hx.1 hx.2
    have h1 := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hle)
    obtain ⟨eA⟩ := h.iso
    rw [hCt, card_eq_of_equiv_alt (by omega) eA, hm10] at h1
    exact absurd h1 (by norm_num [Nat.factorial])

end CFSG.OddStandard.AltStdSec
