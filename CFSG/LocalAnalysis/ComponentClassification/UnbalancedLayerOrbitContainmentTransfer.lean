module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAFixedLayerPComponent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreActiveTwoComponent
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mem_of_mem_sup {K R A B : Subgroup G} (hKR : K ≤ normalizer (R : Set G))
    (hAK : A ≤ K) (hBK : B ≤ K) {e : G} (hA : ∀ y ∈ A, y⁻¹ * e⁻¹ * y * e ∈ R)
    (hB : ∀ y ∈ B, y⁻¹ * e⁻¹ * y * e ∈ R) {y : G} (hy : y ∈ A ⊔ B) :
    y⁻¹ * e⁻¹ * y * e ∈ R := by
  let S : Subgroup G :=
    { carrier := {k | k ∈ K ∧ k⁻¹ * e⁻¹ * k * e ∈ R}
      one_mem' := ⟨one_mem K, by simp⟩
      mul_mem' := by
        rintro k l ⟨hk, hkR⟩ ⟨hl, hlR⟩
        refine ⟨mul_mem hk hl, ?_⟩
        have h1 := (mem_normalizer_iff.mp (inv_mem (hKR hl)) _).mp hkR
        rw [show (k * l)⁻¹ * e⁻¹ * (k * l) * e =
          l⁻¹ * (k⁻¹ * e⁻¹ * k * e) * l⁻¹⁻¹ * (l⁻¹ * e⁻¹ * l * e) by group]
        exact mul_mem h1 hlR
      inv_mem' := by
        rintro k ⟨hk, hkR⟩
        refine ⟨inv_mem hk, ?_⟩
        have h1 := (mem_normalizer_iff.mp (hKR hk) _).mp (inv_mem hkR)
        rwa [show k * (k⁻¹ * e⁻¹ * k * e)⁻¹ * k⁻¹ = k⁻¹⁻¹ * e⁻¹ * k⁻¹ * e by group] at h1 }
  have hAS : A ≤ S := fun z hz => ⟨hAK hz, hA z hz⟩
  have hBS : B ≤ S := fun z hz => ⟨hBK hz, hB z hz⟩
  exact (sup_le hAS hBS hy).2

theorem mem_normalizer_of_subgroupOf {M C : Subgroup G} (hMC : M ≤ C) {g : C}
    (hg : g ∈ normalizer (M.subgroupOf C : Set C)) : (g : G) ∈ normalizer (M : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact (mem_normalizer_iff.mp hg ⟨y, hMC hy⟩).mp hy
  · intro hy
    have hyC : y ∈ C := by
      have h := mul_mem (mul_mem (inv_mem g.2) (hMC hy)) g.2
      rwa [show (g : G)⁻¹ * (g * y * (g : G)⁻¹) * g = y by group] at h
    exact (mem_normalizer_iff.mp hg ⟨y, hyC⟩).mpr hy

theorem conjugate_subgroupOf_eq (M C : Subgroup G) (g : C) :
    conjugate (M.subgroupOf C) g = (conjugate M (g : G)).subgroupOf C := by
  ext y
  rw [mem_conjugate_iff, mem_subgroupOf, mem_subgroupOf, mem_conjugate_iff, coe_mul, coe_mul,
    coe_inv]

theorem mem_normalizer_of_conjugate_eq {J : Subgroup G} {g : G} (h : conjugate J g = J) :
    g ∈ normalizer (J : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  have h1 : y ∈ conjugate J g ↔ g * y * g⁻¹ ∈ J := mem_conjugate_iff
  rw [h] at h1
  exact h1

theorem normalizer_inf_mem {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA y) (mem_normalizer_iff.mp hB y)

theorem conj_mem_coreActionKernel {J : Subgroup G} {g q : G} (hg : g ∈ normalizer (J : Set G))
    (hq : q ∈ coreActionKernel J) : g * q * g⁻¹ ∈ coreActionKernel J := by
  obtain ⟨hqN, hqJ⟩ := mem_coreActionKernel.mp hq
  refine mem_coreActionKernel.mpr ⟨mul_mem (mul_mem hg hqN) (inv_mem hg), fun j hj => ?_⟩
  have hj' : g⁻¹ * j * g⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp (inv_mem hg) j).mp hj
  have h1 := (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
    J (pPrimeCore 2 J) hg) _).mp (hqJ _ hj')
  rwa [show g * ((g⁻¹ * j * g⁻¹⁻¹)⁻¹ * q⁻¹ * (g⁻¹ * j * g⁻¹⁻¹) * q) * g⁻¹ =
    j⁻¹ * (g * q * g⁻¹)⁻¹ * j * (g * q * g⁻¹) by group] at h1

theorem normalizer_le_normalizer_coreActionKernel (J : Subgroup G) :
    normalizer (J : Set G) ≤ normalizer (coreActionKernel J : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro q
  refine ⟨conj_mem_coreActionKernel hg, fun h => ?_⟩
  have h1 := conj_mem_coreActionKernel (inv_mem hg) h
  rwa [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group] at h1

variable [Finite G]

omit [Finite G] in
theorem inf_subgroupOf_centralizer_facts {C O : Subgroup G} {x : G} (hxC : x ∈ C)
    (hOx : O ≤ centralizer ({x} : Set G))
    (hON : centralizer ({x} : Set G) ≤ normalizer (O : Set G)) (hOodd : Odd (Nat.card O)) :
    (O ⊓ C).subgroupOf C ≤ centralizer ({(⟨x, hxC⟩ : C)} : Set C) ∧
      (((O ⊓ C).subgroupOf C).subgroupOf (centralizer ({(⟨x, hxC⟩ : C)} : Set C))).Normal ∧
      Odd (Nat.card ((O ⊓ C).subgroupOf C)) := by
  have hmemD : ∀ d : C, d ∈ (O ⊓ C).subgroupOf C ↔ (d : G) ∈ O := by
    intro d
    rw [mem_subgroupOf, mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, d.2⟩⟩
  have hDC : (O ⊓ C).subgroupOf C ≤ centralizer ({(⟨x, hxC⟩ : C)} : Set C) := by
    intro d hd
    have h := mem_centralizer_singleton_iff.mp (hOx ((hmemD d).mp hd))
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext h
  refine ⟨hDC, ?_, ?_⟩
  · rw [normal_subgroupOf_iff_le_normalizer hDC]
    have key : ∀ c ∈ centralizer ({(⟨x, hxC⟩ : C)} : Set C), ∀ d ∈ (O ⊓ C).subgroupOf C,
        c * d * c⁻¹ ∈ (O ⊓ C).subgroupOf C := by
      intro c hc d hd
      rw [hmemD] at hd ⊢
      have hcx : (c : G) ∈ centralizer ({x} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
      exact (mem_normalizer_iff.mp (hON hcx) d).mp hd
    intro c hc
    rw [mem_normalizer_iff]
    intro d
    refine ⟨key c hc d, fun hd => ?_⟩
    have h := key c⁻¹ (inv_mem hc) _ hd
    rwa [show c⁻¹ * (c * d * c⁻¹) * c⁻¹⁻¹ = d by group] at h
  · rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : O ⊓ C ≤ C)).toEquiv]
    exact hOodd.of_dvd_nat (card_dvd_of_le inf_le_left)

theorem map_pPrimeCore_le_of_le_normalizer {M K : Subgroup G} (hMK : M ≤ K)
    (hKN : K ≤ normalizer (M : Set G)) :
    (pPrimeCore 2 M).map M.subtype ≤ (pPrimeCore 2 K).map K.subtype := by
  have hOK : (pPrimeCore 2 M).map M.subtype ≤ K := (map_subtype_le _).trans hMK
  have hle : ((pPrimeCore 2 M).map M.subtype).subgroupOf K ≤ pPrimeCore 2 K := by
    apply le_sSup
    refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hl ⊢
      exact (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic
        M (pPrimeCore 2 M) (hKN z.2)) l).mp hl
    · rw [Nat.card_congr (subgroupOfEquivOfLe hOK).toEquiv,
        card_map_of_injective M.subtype_injective]
      exact pPrimeCore_coprime_card
  calc (pPrimeCore 2 M).map M.subtype
      = (((pPrimeCore 2 M).map M.subtype).subgroupOf K).map K.subtype :=
        (map_subgroupOf_eq_of_le hOK).symm
    _ ≤ (pPrimeCore 2 K).map K.subtype := map_mono hle

theorem le_map_pPrimeCore_of_sup_eq {J T W : Subgroup G}
    (hTJ : T ⊔ (pPrimeCore 2 J).map J.subtype = J) (hWT : W ≤ T)
    (hTW : T ≤ normalizer (W : Set G)) (hW : Odd (Nat.card W)) :
    W ≤ (pPrimeCore 2 J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTle : T ≤ J := le_sup_left.trans hTJ.le
  have hWJ : W ≤ J := hWT.trans hTle
  have hT' : T.subgroupOf J ⊔ pPrimeCore 2 J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hTle, ← MonoidHom.range_eq_map, range_subtype]
    exact hTJ
  have hTmap : (T.subgroupOf J).map (QuotientGroup.mk' (pPrimeCore 2 J)) = ⊤ := by
    have h := congrArg (map (QuotientGroup.mk' (pPrimeCore 2 J))) hT'
    have hbot : (pPrimeCore 2 J).map (QuotientGroup.mk' (pPrimeCore 2 J)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup, hbot, sup_bot_eq, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk'] at h
  have hnorm : ((W.subgroupOf J).map (QuotientGroup.mk' (pPrimeCore 2 J))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ (T.subgroupOf J).map (QuotientGroup.mk' (pPrimeCore 2 J)) := by
      rw [hTmap]
      exact mem_top g
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hg
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hn
    refine ⟨t * w * t⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [mem_subgroupOf] at hw ht
    show ((t * w * t⁻¹ : J) : G) ∈ W
    exact (mem_normalizer_iff.mp (hTW ht) w).mp hw
  have hcop : Nat.Coprime 2
      (Nat.card ((W.subgroupOf J).map (QuotientGroup.mk' (pPrimeCore 2 J)))) := by
    refine Nat.Coprime.coprime_dvd_right (card_map_dvd _ _) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hWJ).toEquiv]
    exact Nat.coprime_two_left.mpr hW
  have hbot := pPrimeCore_eq_bot_iff.mp (pPrimeCore_quotient_pPrimeCore_eq_bot (G := J) 2) _
    hnorm hcop
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro w hw
  exact ⟨⟨w, hWJ hw⟩, hbot (show (⟨w, hWJ hw⟩ : J) ∈ W.subgroupOf J from hw), rfl⟩

theorem le_of_inf_centralizer_le {F Q : Subgroup G} {b : G} (hb : b * b = 1)
    (hFodd : Odd (Nat.card F)) (hbF : b ∈ normalizer (F : Set G))
    (hbQ : b ∈ normalizer (Q : Set G)) (hFQ : F ≤ normalizer (Q : Set G))
    (hcomm : ∀ f ∈ F, f⁻¹ * b⁻¹ * f * b ∈ Q)
    (hle : F ⊓ centralizer ({b} : Set G) ≤ Q) : F ≤ Q := by
  set R := F ⊓ Q with hR
  set Y := normalizer (R : Set G) with hY
  have hbY : b ∈ Y := normalizer_inf_mem hbF hbQ
  have hFY : F ≤ Y := fun f hf => normalizer_inf_mem (le_normalizer hf) (hFQ hf)
  have hRY : R ≤ Y := inf_le_left.trans hFY
  have hRodd : Odd (Nat.card (R.subgroupOf Y)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRY).toEquiv]
    exact hFodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  intro f hf
  have hbb : (⟨b, hbY⟩ : Y) * ⟨b, hbY⟩ = 1 := Subtype.ext hb
  have hx : (⟨f, hFY hf⟩ : Y)⁻¹ * ((⟨b, hbY⟩ : Y)⁻¹ * ⟨f, hFY hf⟩ * ⟨b, hbY⟩) ∈
      R.subgroupOf Y := by
    rw [mem_subgroupOf]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h := (mem_normalizer_iff.mp (inv_mem hbF) f).mp hf
      rw [inv_inv] at h
      exact mul_mem (inv_mem hf) h
    · have h := hcomm f hf
      rwa [show f⁻¹ * b⁻¹ * f * b = f⁻¹ * (b⁻¹ * f * b) by group] at h
  obtain ⟨c, hc, hcR⟩ := exists_mem_centralizer_of_inv_mul_conj_mem hRodd hbb hx
  rw [mem_subgroupOf] at hcR
  have hcR' : f⁻¹ * (c : G) ∈ R := hcR
  have hcF : (c : G) ∈ F := by
    have h := mul_mem hf (mem_inf.mp hcR').1
    rwa [mul_inv_cancel_left] at h
  have hcb : (c : G) ∈ centralizer ({b} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
  have h := mul_mem (hle (mem_inf.mpr ⟨hcF, hcb⟩)) (inv_mem (mem_inf.mp hcR').2)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h

theorem gsFixedLayer_sup_map_pPrimeCore {J : Subgroup G} {b : G} (hbo : orderOf b = 2)
    (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) (hbN : b ∈ normalizer (J : Set G))
    (hcomm : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) :
    UnbalancedGS.gsFixedLayer J b ⊔ (pPrimeCore 2 J).map J.subtype = J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbb : b * b = 1 := by rw [← sq, ← hbo, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hzp : ∀ c ∈ zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  have hBN : zpowers b ≤ normalizer (J : Set G) := zpowers_le.mpr hbN
  let α : zpowers b →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (c : zpowers b) (j : J), ((α c j : J) : G) = (c : G) * j * (c : G)⁻¹ :=
    fun c j => Subgroup.normalizerMonoidHom_apply_apply_coe J _ j
  have hB2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have htriv : ∀ (c : zpowers b) (j : J),
      ((α c j : J) : J ⧸ pPrimeCore 2 J) = (j : J ⧸ pPrimeCore 2 J) := by
    intro c j
    rcases hzp c c.2 with hc | hc
    · have hc1 : c = 1 := Subtype.ext hc
      rw [hc1, map_one]
      rfl
    · rw [eq_comm, QuotientGroup.eq]
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp (hcomm (j : G) j.2)
      have hoe : o = j⁻¹ * α c j := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hα, hc, hbinv]
        rw [hbinv] at hoeq
        change J.subtype o = _
        rw [hoeq]
        group
      rwa [hoe] at ho
  have hCmem : ∀ j : J, j ∈ (centralizer ({b} : Set G)).subgroupOf J ↔ ∀ c : zpowers b,
      α c j = j := by
    intro j
    rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h c
      apply Subtype.ext
      rw [hα]
      rcases hzp c c.2 with hc | hc
      · rw [hc]
        group
      · rw [hc, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := congrArg Subtype.val (h ⟨b, mem_zpowers b⟩)
      rw [hα] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  set CJ := (centralizer ({b} : Set G)).subgroupOf J with hCJ
  set TJ := (pLayer CJ 2).map CJ.subtype with hTJ
  obtain ⟨hTN, -, -⟩ :=
    UnbalancedGS.fixed_prime_layer_covers_core_quotient 2 hB2 α hJq htriv CJ hCmem TJ hTJ
  have hTb : TJ.map J.subtype = UnbalancedGS.gsFixedLayer J b := by
    rw [hTJ, Subgroup.map_map, UnbalancedGS.gsFixedLayer]
    let φ : CJ ≃* (J ⊓ centralizer ({b} : Set G) : Subgroup G) :=
      { toFun := fun x => ⟨x, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hcomp : J.subtype.comp CJ.subtype =
        (J ⊓ centralizer ({b} : Set G)).subtype.comp φ.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 φ]
  rw [← hTb, ← Subgroup.map_sup, hTN, ← MonoidHom.range_eq_map, range_subtype]

theorem unbalancing_orbit_containment_transfer {a x : G} {J : Subgroup G}
    (hU : GSUnbalancingTriple a x J) {b : G} (hb : orderOf b = 2) (hab : a * b = b * a)
    (hbx : b * x = x * b) (hbJ : b ∈ normalizer (J : Set G))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    {M : Subgroup G} (hMb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hTK : UnbalancedGS.gsFixedLayer J b ≤ M ⊔ conjugate M a) :
    GSUnbalancingTriple b x M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hx, -, hJa, hJ, -, hJF⟩ := gsUnbalancingTriple_iff.mp hU
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  set Cx := centralizer ({x} : Set G) with hCx
  set Ca := centralizer ({a} : Set G) with hCa
  set Cb := centralizer ({b} : Set G) with hCb
  set Ox := (pPrimeCore 2 Cx).map Cx.subtype with hOxdef
  set NJ := (pPrimeCore 2 J).map J.subtype with hNJ
  set F := Ox ⊓ Ca with hFdef
  set T := UnbalancedGS.gsFixedLayer J b with hTdef
  have hOx : Ox ≤ Cx := map_subtype_le _
  have hOxodd : Odd (Nat.card Ox) := by
    rw [hOxdef, card_map_of_injective Cx.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOxN : Cx ≤ normalizer (Ox : Set G) := fun c hc =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic Cx (pPrimeCore 2 Cx)
      (le_normalizer hc)
  have hNJN : normalizer (J : Set G) ≤ normalizer (NJ : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 J)
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
  have hJN : ¬ J ≤ NJ := by
    intro hle
    obtain ⟨-, -, u, v, huv⟩ := hJq
    apply huv
    have h1 : ∀ q : J ⧸ pPrimeCore 2 J, q = 1 := by
      intro q
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.eq_one_iff]
      exact (mem_map_iff_mem J.subtype_injective).mp (hle j.2)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [h1 u, h1 v]
  have hFN : F ≤ normalizer (J : Set G) := by
    have h := le_normalizer_commutator F J
    rwa [commutator_comm, hJF] at h
  have hFodd : Odd (Nat.card F) := hOxodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hbCx : b ∈ Cx := mem_centralizer_singleton_iff.mpr hbx
  have hbCa : b ∈ Ca := mem_centralizer_singleton_iff.mpr hab.symm
  have hbF : b ∈ normalizer (F : Set G) := normalizer_inf_mem (hOxN hbCx) (le_normalizer hbCa)
  have hbQ : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨hbJ, hJb⟩
  have hQN := normalizer_le_normalizer_coreActionKernel J
  have hcommQ : ∀ f ∈ F, f⁻¹ * b⁻¹ * f * b ∈ coreActionKernel J := by
    intro f hf
    have h := conj_mem_coreActionKernel (inv_mem (hFN hf)) (inv_mem hbQ)
    rw [inv_inv] at h
    exact mul_mem h hbQ
  have hEQ : ¬ F ⊓ Cb ≤ coreActionKernel J := by
    intro hle
    have hFQ := le_of_inf_centralizer_le hbb hFodd hbF (le_normalizer hbQ)
      (fun f hf => hQN (hFN hf)) hcommQ hle
    apply hJN
    calc J = ⁅J, F⁆ := hJF.symm
      _ ≤ NJ := by
        rw [commutator_le]
        intro j hj f hf
        have h := (mem_coreActionKernel.mp (hFQ (inv_mem hf))).2 j⁻¹ (inv_mem hj)
        rw [commutatorElement_def]
        simpa only [inv_inv] using h
  have hxCb : x ∈ Cb := mem_centralizer_singleton_iff.mpr hbx.symm
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have hx' : orderOf (⟨x, hxCb⟩ : Cb) = 2 := by rw [Subgroup.orderOf_mk, hx]
  obtain ⟨hDC, hDn, hDodd⟩ := inf_subgroupOf_centralizer_facts hxCb hOx hOxN hOxodd
  have hMD : ¬ ⁅M.subgroupOf Cb, (Ox ⊓ Cb).subgroupOf Cb⁆ ≤
      (pPrimeCore 2 (M.subgroupOf Cb)).map (M.subgroupOf Cb).subtype := by
    intro hcon
    apply hEQ
    intro e he
    obtain ⟨heF, heb⟩ := mem_inf.mp he
    have heOx : e ∈ Ox := (mem_inf.mp heF).1
    have heCa : e ∈ Ca := (mem_inf.mp heF).2
    have heJ : e ∈ normalizer (J : Set G) := hFN heF
    have hMe : ∀ m ∈ M, m⁻¹ * e⁻¹ * m * e ∈ (pPrimeCore 2 M).map M.subtype := by
      intro m hm
      have h1 : ⁅(⟨m, hMb hm⟩ : Cb)⁻¹, (⟨e, heb⟩ : Cb)⁻¹⁆ ∈
          ⁅M.subgroupOf Cb, (Ox ⊓ Cb).subgroupOf Cb⁆ :=
        commutator_mem_commutator (inv_mem (show (⟨m, hMb hm⟩ : Cb) ∈ M.subgroupOf Cb from hm))
          (inv_mem (show (⟨e, heb⟩ : Cb) ∈ (Ox ⊓ Cb).subgroupOf Cb from mem_inf.mpr ⟨heOx, heb⟩))
      have h2 := mem_map_of_mem Cb.subtype (hcon h1)
      rw [pPrimeCore_map_subgroupOf 2 M Cb hMb] at h2
      have h3 : Cb.subtype ⁅(⟨m, hMb hm⟩ : Cb)⁻¹, (⟨e, heb⟩ : Cb)⁻¹⁆ = m⁻¹ * e⁻¹ * m * e := by
        simp [commutatorElement_def]
      rwa [h3] at h2
    have hMaCb : conjugate M a ≤ Cb := by
      intro y hy
      rw [mem_conjugate_iff] at hy
      have h := mul_mem (mul_mem (inv_mem haCb) (hMb hy)) haCb
      rwa [show a⁻¹ * (a * y * a⁻¹) * a = y by group] at h
    have hMa' : IsPComponent 2 ((conjugate M a).subgroupOf Cb) := by
      have h := isPComponent_conjugate hM (⟨a, haCb⟩ : Cb)
      rwa [conjugate_subgroupOf_eq] at h
    have hMaN : conjugate M a ≤ normalizer (M : Set G) := by
      have hle : (conjugate M a).subgroupOf Cb ≤ normalizer (M.subgroupOf Cb : Set Cb) := by
        by_cases heq : M.subgroupOf Cb = (conjugate M a).subgroupOf Cb
        · rw [← heq]
          exact le_normalizer
        · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
            _ _ hM hMa').2 heq).1
      intro y hy
      exact mem_normalizer_of_subgroupOf hMb
        (hle (show (⟨y, hMaCb hy⟩ : Cb) ∈ (conjugate M a).subgroupOf Cb from hy))
    set K := M ⊔ conjugate M a with hKdef
    have hKN : K ≤ normalizer (M : Set G) := sup_le le_normalizer hMaN
    have hOMK := map_pPrimeCore_le_of_le_normalizer le_sup_left hKN
    have hKR : K ≤ normalizer ((pPrimeCore 2 K).map K.subtype : Set G) := fun k hk =>
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 K)
        (le_normalizer hk)
    have haK : a ∈ normalizer (K : Set G) := by
      apply mem_normalizer_of_conjugate_eq
      rw [hKdef, conjugate_sup, conjugate_conjugate_self_of_mul_self haa, sup_comm]
    have haR := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 K) haK
    have hea : a⁻¹ * e * a = e := by
      rw [mul_assoc, mem_centralizer_singleton_iff.mp heCa, inv_mul_cancel_left]
    have hea' : a⁻¹ * e⁻¹ * a = e⁻¹ := by
      calc a⁻¹ * e⁻¹ * a = (a⁻¹ * e * a)⁻¹ := by group
        _ = e⁻¹ := by rw [hea]
    have hKe : ∀ k ∈ K, k⁻¹ * e⁻¹ * k * e ∈ (pPrimeCore 2 K).map K.subtype := by
      intro k hk
      refine commutator_mem_of_mem_sup hKR le_sup_left le_sup_right
        (fun y hy => hOMK (hMe y hy)) (fun y hy => ?_) hk
      have hm : a * y * a⁻¹ ∈ M := mem_conjugate_iff.mp hy
      have h1 := (mem_normalizer_iff.mp (inv_mem haR) _).mp (hOMK (hMe _ hm))
      rwa [show a⁻¹ * ((a * y * a⁻¹)⁻¹ * e⁻¹ * (a * y * a⁻¹) * e) * a⁻¹⁻¹ =
        y⁻¹ * (a⁻¹ * e⁻¹ * a) * y * (a⁻¹ * e * a) by group, hea, hea'] at h1
    have heT : e ∈ normalizer (T : Set G) := by
      have : (pLayer ↥(J ⊓ Cb) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
      exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (J ⊓ Cb)
        (pLayer ↥(J ⊓ Cb) 2) (normalizer_inf_mem heJ (le_normalizer heb))
    have hTJ : T ⊔ NJ = J := gsFixedLayer_sup_map_pPrimeCore hb hJq hbJ hJb
    have hTle : T ≤ J := le_sup_left.trans hTJ.le
    have hW : T ⊓ (pPrimeCore 2 K).map K.subtype ≤ NJ := by
      refine le_map_pPrimeCore_of_sup_eq hTJ inf_le_left
        (fun t ht => normalizer_inf_mem (le_normalizer ht) (hKR (hTK ht))) ?_
      have hodd : Odd (Nat.card ((pPrimeCore 2 K).map K.subtype)) := by
        rw [card_map_of_injective K.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact hodd.of_dvd_nat (card_dvd_of_le inf_le_right)
    have hTe : ∀ t ∈ T, t⁻¹ * e⁻¹ * t * e ∈ NJ := by
      intro t ht
      apply hW
      refine mem_inf.mpr ⟨?_, hKe t (hTK ht)⟩
      have h := (mem_normalizer_iff.mp (inv_mem heT) t).mp ht
      rw [inv_inv] at h
      rw [show t⁻¹ * e⁻¹ * t * e = t⁻¹ * (e⁻¹ * t * e) by group]
      exact mul_mem (inv_mem ht) h
    have hNe : ∀ n ∈ NJ, n⁻¹ * e⁻¹ * n * e ∈ NJ := by
      intro n hn
      have h := (mem_normalizer_iff.mp (inv_mem (hNJN heJ)) n).mp hn
      rw [inv_inv] at h
      rw [show n⁻¹ * e⁻¹ * n * e = n⁻¹ * (e⁻¹ * n * e) by group]
      exact mul_mem (inv_mem hn) h
    have hJR : J ≤ normalizer (NJ : Set G) := fun j hj => hNJN (le_normalizer hj)
    refine mem_coreActionKernel.mpr ⟨heJ, fun j hj => ?_⟩
    exact commutator_mem_of_mem_sup hJR hTle (map_subtype_le _) hTe hNe
      (by rw [hTJ]; exact hj)
  obtain ⟨-, -, hMD', hMx'⟩ := odd_fixed_core_active_two_component hx' hDC hDn hDodd hM hMD
  have hsubM : (M.subgroupOf Cb).map Cb.subtype = M := map_subgroupOf_eq_of_le hMb
  refine gsUnbalancingTriple_iff.mpr ⟨hb, hx, hbx, hMb, hM, ?_, ?_⟩
  · have hz : zpowers x = (zpowers (⟨x, hxCb⟩ : Cb)).map Cb.subtype := by
      rw [MonoidHom.map_zpowers]
      rfl
    conv_lhs => rw [← hsubM, hz]
    rw [← map_commutator, hMx', hsubM]
  · conv_lhs => rw [← hsubM, ← map_subgroupOf_eq_of_le (inf_le_right : Ox ⊓ Cb ≤ Cb)]
    rw [← map_commutator, hMD', hsubM]

end CFSG.ComponentClassification.UnbalancedLayer
