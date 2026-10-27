module

public import CFSG.LocalAnalysis.GH72.L2Local
public import CFSG.GroupTheory.ABGDGroups.LinearOddCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerThreeCycle
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenOrderThreeCentralizerCard
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySL2Props
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitInputs
public import CFSG.LocalAnalysis.GH72.GWTwoExtension
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.Walter.Defs

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

local notation "A₇" => alternatingGroup (Fin 7)

theorem aSeven_exists_card_eq_three_forall_odd_mem {v : A₇} (hv : orderOf v = 2) :
    ∃ U : Subgroup A₇, U ≤ centralizer ({v} : Set A₇) ∧ Nat.card U = 3 ∧
      ∀ x ∈ centralizer ({v} : Set A₇), Odd (orderOf x) → x ∈ U := by
  have hv1 : v ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hv
    exact absurd hv (by norm_num)
  have hvi : BenderSuzuki.PFAppendixIII.IsInvolution v :=
    ⟨hv1, by rw [← hv]; exact pow_orderOf_eq_one v⟩
  haveI : IsSimpleGroup A₇ := alternatingGroup.isSimpleGroup (by simp)
  have h4 : 4 < Nat.card A₇ := by rw [CFSG.ABGDGroups.card_alternatingGroup_fin_seven]; norm_num
  have hti : BenderSuzuki.PFAppendixIII.IsInvolution CFSG.GorensteinWalter.a7t :=
    ⟨by decide +kernel, by decide +kernel⟩
  obtain ⟨g, hg⟩ := (gw_lemma_2_1_of_isSimpleGroup h4
    CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven).1 v
    CFSG.GorensteinWalter.a7t hvi hti
  have hv' : v = g⁻¹ * CFSG.GorensteinWalter.a7t * g := by rw [← hg]; group
  have hat : CFSG.GorensteinWalter.a7a * CFSG.GorensteinWalter.a7t =
      CFSG.GorensteinWalter.a7t * CFSG.GorensteinWalter.a7a := by decide +kernel
  have ha3 : orderOf CFSG.GorensteinWalter.a7a = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  refine ⟨(zpowers CFSG.GorensteinWalter.a7a).map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [mem_centralizer_singleton_iff]
    have hc : CFSG.GorensteinWalter.a7a ^ k * CFSG.GorensteinWalter.a7t =
        CFSG.GorensteinWalter.a7t * CFSG.GorensteinWalter.a7a ^ k :=
      ((Commute.zpow_left hat) k).eq
    change g⁻¹ * CFSG.GorensteinWalter.a7a ^ k * g⁻¹⁻¹ * v = v * (g⁻¹ *
      CFSG.GorensteinWalter.a7a ^ k * g⁻¹⁻¹)
    rw [hv', inv_inv]
    calc g⁻¹ * CFSG.GorensteinWalter.a7a ^ k * g * (g⁻¹ * CFSG.GorensteinWalter.a7t * g)
        = g⁻¹ * (CFSG.GorensteinWalter.a7a ^ k * CFSG.GorensteinWalter.a7t) * g := by group
      _ = g⁻¹ * (CFSG.GorensteinWalter.a7t * CFSG.GorensteinWalter.a7a ^ k) * g := by rw [hc]
      _ = g⁻¹ * CFSG.GorensteinWalter.a7t * g * (g⁻¹ * CFSG.GorensteinWalter.a7a ^ k * g) := by
          group
  · rw [card_map_of_injective (MulAut.conj g⁻¹).injective, Nat.card_zpowers, ha3]
  · intro x hx hodd
    set y := g * x * g⁻¹ with hydef
    have hy : y * CFSG.GorensteinWalter.a7t = CFSG.GorensteinWalter.a7t * y := by
      have hx' := mem_centralizer_singleton_iff.mp hx
      rw [hydef, ← hg]
      calc g * x * g⁻¹ * (g * v * g⁻¹) = g * (x * v) * g⁻¹ := by group
        _ = g * (v * x) * g⁻¹ := by rw [hx']
        _ = g * v * g⁻¹ * (g * x * g⁻¹) := by group
    have hord : orderOf y = orderOf x := by
      rw [hydef, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨h12, h3⟩ := (CFSG.ABGDGroups.aSeven_centralizer_involution_a7V_certificate y).1 hy
    have hy3 : y ^ 3 = 1 := by
      have hdvd : orderOf y ∣ 3 * 4 := orderOf_dvd_of_pow_eq_one h12
      have hcop : Nat.Coprime (orderOf y) 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact (Nat.coprime_two_right.mpr (hord ▸ hodd)).pow_right 2
      exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hdvd)
    have hymem : y ∈ zpowers CFSG.GorensteinWalter.a7a := by
      rcases h3 hy3 with h | h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact mem_zpowers _
      · rw [h]
        exact Subgroup.pow_mem _ (mem_zpowers _) 2
    refine ⟨y, hymem, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem exists_card_eq_three_forall_odd_mem_of_aSeven {X : Type*}
    [Group X] {L : Subgroup X} (e : L ≃* A₇) {a : X} (haL : a ∈ L) (ha : orderOf a = 2) :
    ∃ U : Subgroup X, U ≤ L ⊓ centralizer ({a} : Set X) ∧ Nat.card U = 3 ∧
      ∀ x ∈ L ⊓ centralizer ({a} : Set X), Odd (orderOf x) → x ∈ U := by
  set f : A₇ →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hfr : f.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  have hft : f (e ⟨a, haL⟩) = a := by simp [f]
  have ht : orderOf (e ⟨a, haL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ha
  obtain ⟨U, hU, hUc, hodd⟩ := aSeven_exists_card_eq_three_forall_odd_mem ht
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUcyc : IsCyclic U := isCyclic_of_prime_card hUc
  obtain ⟨h1, -, h3⟩ := exists_isCyclic_forall_odd_mem_map f hf hU hUcyc hodd
  rw [hfr, hft] at h1 h3
  exact ⟨U.map f, h1, by rw [card_map_of_injective hf, hUc], h3⟩

variable {X : Type*} [Group X] [Finite X]

theorem pow_two_eq_one_of_isKleinFour {V : Subgroup X} (hV : IsKleinFour V) (v : V) :
    v ^ 2 = 1 := by
  have h := Monoid.pow_exponent_eq_one v
  rwa [hV.exponent_two] at h

theorem isCyclic_and_exists_le_centralizer_of_aSeven
    {L V K : Subgroup X} (e : L ≃* A₇) (hV : IsKleinFour V) (hVL : V ≤ L) (hKL : K ≤ L)
    (hK : Odd (Nat.card K)) (hVK : V ≤ normalizer (K : Set X)) :
    IsCyclic K ∧ ∃ a ∈ V, a ≠ 1 ∧ K ≤ centralizer ({a} : Set X) := by
  set f : A₇ →* X := L.subtype.comp e.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hfr : f.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [f]⟩
  have hcyc : IsCyclic K := by
    have hK' : Odd (Nat.card (K.comap f)) := by
      rwa [card_comap_of_le_range f hf (hfr ▸ hKL)]
    have hV' := isKleinFour_comap f hf hV (hfr ▸ hVL)
    exact isCyclic_of_isCyclic_comap f hf (hfr ▸ hKL)
      (CFSG.ABGDGroups.aSeven_isCyclic_of_odd_of_kleinFour (MulEquiv.refl A₇) hV' hK'
        (comap_le_normalizer_comap f hVK))
  refine ⟨hcyc, ?_⟩
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two V K (pow_two_eq_one_of_isKleinFour hV) (by rw [hV.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h)) hVK
  have hU : ∀ w : V, w ≠ 1 → ∃ U : Subgroup X, U ≤ L ⊓ centralizer ({(w : X)} : Set X) ∧
      Nat.card U = 3 ∧ K ⊓ centralizer ({(w : X)} : Set X) ≤ U := fun w hw => by
    have hw2 : orderOf (w : X) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (pow_two_eq_one_of_isKleinFour hV w) hw
    obtain ⟨U, hUle, hUc, hodd⟩ := exists_card_eq_three_forall_odd_mem_of_aSeven e (hVL w.2) hw2
    exact ⟨U, hUle, hUc, fun x hx => hodd x ⟨hKL hx.1, hx.2⟩
      (hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hx.1))⟩
  by_cases hne : ∃ v : V, v ≠ 1 ∧ K ⊓ centralizer ({(v : X)} : Set X) ≠ ⊥
  · obtain ⟨v, hv1, hvK⟩ := hne
    obtain ⟨Uv, hUvle, hUvc, hKUv⟩ := hU v hv1
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hfull : ∀ (w : V) (U : Subgroup X), Nat.card U = 3 →
        K ⊓ centralizer ({(w : X)} : Set X) ≤ U → K ⊓ centralizer ({(w : X)} : Set X) ≠ ⊥ →
        K ⊓ centralizer ({(w : X)} : Set X) = U := fun w U hUc hle hne => by
      have hfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hUc]; norm_num)
      have hdvd : Nat.card ↥(K ⊓ centralizer ({(w : X)} : Set X)) ∣ 3 :=
        hUc ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd ((Subgroup.card_eq_one).mp h1) hne
      · exact Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hUc])
    have hKv := hfull v Uv hUvc hKUv hvK
    have hUvK : Uv ≤ K := hKv ▸ inf_le_left
    have hall : K ≤ Uv := by
      rw [hgen]
      refine iSup₂_le fun w hw => ?_
      by_cases hwK : K ⊓ centralizer ({(w : X)} : Set X) = ⊥
      · rw [hwK]
        exact bot_le
      obtain ⟨Uw, -, hUwc, hKUw⟩ := hU w hw
      have hKw := hfull w Uw hUwc hKUw hwK
      have hUwK : Uw ≤ K := hKw ▸ inf_le_left
      have heq : Uw.subgroupOf K = Uv.subgroupOf K := by
        haveI : Finite (Uw.subgroupOf K) := Nat.finite_of_card_ne_zero (by
          rw [Nat.card_congr (subgroupOfEquivOfLe hUwK).toEquiv, hUwc]; norm_num)
        haveI : Finite (Uv.subgroupOf K) := Nat.finite_of_card_ne_zero (by
          rw [Nat.card_congr (subgroupOfEquivOfLe hUvK).toEquiv, hUvc]; norm_num)
        rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_congr (subgroupOfEquivOfLe hUwK).toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe hUvK).toEquiv, hUwc, hUvc]
      have : Uw = Uv :=
        (inf_eq_left.mpr hUwK).symm.trans ((subgroupOf_inj.mp heq).trans (inf_eq_left.mpr hUvK))
      rw [hKw, this]
    exact ⟨v, v.2, fun h => hv1 (Subtype.ext h), hall.trans (hUvle.trans inf_le_right)⟩
  · push Not at hne
    have hbot : K = ⊥ := by
      rw [hgen]
      exact iSup₂_eq_bot.mpr hne
    obtain ⟨a, ha, ha1, -⟩ := exists_mem_kleinFour_ne hV (one_mem V)
    exact ⟨a, ha, ha1, by rw [hbot]; exact bot_le⟩

theorem card_eq_three_and_isMaxInvIn_of_aSeven {J V : Subgroup X}
    (e : J ≃* A₇) (hV : IsKleinFour V) (hVJ : V ≤ J) {U : Subgroup X} (hUJ : U ≤ J)
    (hU : Odd (Nat.card U)) (hUV : U ≤ centralizer (V : Set X)) (hU1 : U ≠ ⊥) :
    Nat.card U = 3 ∧ IsMaxInvIn 3 V J U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbound : ∀ w ∈ V, w ≠ 1 → ∀ R : Subgroup X, R ≤ J ⊓ centralizer ({w} : Set X) →
      Odd (Nat.card R) → Nat.card R ∣ 3 := fun w hw hw1 R hR hRodd => by
    have hw2 : orderOf w = 2 := orderOf_eq_prime (sq_eq_one_of_mem_kleinFour hV hw) hw1
    obtain ⟨Uw, -, hUwc, hodd⟩ := exists_card_eq_three_forall_odd_mem_of_aSeven e (hVJ hw) hw2
    have hle : R ≤ Uw := fun x hx =>
      hodd x (hR hx) (hRodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard R hx))
    have hfin : Finite Uw := Nat.finite_of_card_ne_zero (by rw [hUwc]; norm_num)
    exact hUwc ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨v, hv, hv1, -⟩ := exists_mem_kleinFour_ne hV (one_mem V)
  have hUv : U ≤ J ⊓ centralizer ({v} : Set X) := fun x hx =>
    ⟨hUJ hx, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hUV hx)) v hv).symm⟩
  have hU3 : Nat.card U = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hbound v hv hv1 U hUv hU) with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hU1
    · exact h3
  have hVN : V ≤ normalizer (U : Set X) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun u hu =>
      ((mem_centralizer_iff.mp (hUV hu)) w hw).symm)
  refine ⟨hU3, hUJ, IsPGroup.of_card (n := 1) (by rw [hU3, pow_one]), hVN, ?_⟩
  intro Q hQJ hQ hVQ hUQ
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    exact Nat.odd_iff.mpr (by rw [Nat.pow_mod]; norm_num)
  obtain ⟨-, w, hw, hw1, hQw⟩ := isCyclic_and_exists_le_centralizer_of_aSeven e hV hVJ hQJ hQodd hVQ
  have hQ3 := Nat.le_of_dvd (by norm_num) (hbound w hw hw1 Q (le_inf hQJ hQw) hQodd)
  exact (Subgroup.eq_of_le_of_card_ge hUQ (by rw [hU3]; exact hQ3)).symm

theorem eq_bot_of_isSylowOf_le_centralizer_aSeven {X : Type} [Group X]
    [Finite X] {J : Subgroup X} (e : J ≃* A₇) {S : Subgroup X} (hS : IsSylowOf 2 S J)
    {U : Subgroup X} (hUJ : U ≤ J) (hU : Odd (Nat.card U))
    (hSU : S ≤ centralizer (U : Set X)) : U = ⊥ := by
  obtain ⟨Q, hQ⟩ := hS
  obtain ⟨φ, hφ⟩ := CFSG.ABGDGroups.exists_mulEquiv_aSeven_map_sylow_eq e Q
  set f : A₇ →* X := J.subtype.comp φ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := J.subtype_injective.comp φ.symm.injective
  have hfS : ∀ y ∈ CFSG.GorensteinWalter.a7S, f y ∈ S := fun y hy => by
    rw [← hφ] at hy
    obtain ⟨q, hq, hqy⟩ := hy
    rw [← hQ]
    refine ⟨q, hq, ?_⟩
    simp [f, ← hqy]
  have hV : IsKleinFour (CFSG.GorensteinWalter.a7V.map f) :=
    CFSG.ABGDGroups.isKleinFour_map_of_injective hf
      CFSG.GorensteinWalter.aSeven_structure_fact_1_8_ii_centralizer.2.2.2
  have hVS : CFSG.GorensteinWalter.a7V.map f ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfS y (CFSG.ABGDGroups.a7V_le_a7S hy)
  have hVJ : CFSG.GorensteinWalter.a7V.map f ≤ J := by
    rintro _ ⟨y, -, rfl⟩
    exact (φ.symm y).2
  by_contra hU1
  have hUV : U ≤ centralizer ((CFSG.GorensteinWalter.a7V.map f : Subgroup X) : Set X) :=
    fun u hu => mem_centralizer_iff.mpr fun w hw =>
      (mem_centralizer_iff.mp (hSU (hVS hw)) u hu).symm
  obtain ⟨hU3, -⟩ := card_eq_three_and_isMaxInvIn_of_aSeven e hV hVJ hUJ hU hUV hU1
  obtain ⟨u, hu, hu1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hU1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu3 : orderOf u = 3 := by
    have hdvd : orderOf u ∣ 3 := hU3 ▸ Subgroup.orderOf_dvd_natCard U hu
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  set u' : A₇ := φ ⟨u, hUJ hu⟩ with hu'def
  have hfu : f u' = u := by simp [f, u']
  have hu'3 : orderOf u' = 3 := by
    rw [hu'def, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hu3
  have hcomm : ∀ y : A₇, f y * u = u * f y → y ∈ centralizer ({u'} : Set A₇) := fun y hy => by
    rw [mem_centralizer_singleton_iff]
    apply hf
    rw [map_mul, map_mul, hfu]
    exact hy
  have hVc : CFSG.GorensteinWalter.a7V ≤ centralizer ({u'} : Set A₇) := fun y hy =>
    hcomm y (mem_centralizer_iff.mp (hUV hu) (f y) ⟨y, hy, rfl⟩)
  have hSc : CFSG.GorensteinWalter.a7S ≤ centralizer ({u'} : Set A₇) := fun y hy =>
    hcomm y ((mem_centralizer_iff.mp (hSU (hfS y hy)) u hu).symm)
  have h36 := CFSG.GorensteinWalter.aSeven_order_three_centralizer_card_eq_thirty_six_of_kleinFour
    u' hu'3 _ CFSG.GorensteinWalter.aSeven_structure_fact_1_8_ii_centralizer.2.2.2 hVc
  have h8 := Subgroup.card_dvd_of_le hSc
  rw [CFSG.ABGDGroups.card_a7S, h36] at h8
  norm_num at h8

end CFSG.GH72
