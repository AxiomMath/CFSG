module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNMain
public import CFSG.GH74.GLS.C3.Layer1.St1L710Lift
public import CFSG.GH74.GLS.C3.Layer1.St1P41H2

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.Th2
open CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem odd_card_of_forall_odd_orderOf {H : Subgroup G} (h : ∀ d ∈ H, Odd (orderOf d)) :
    Odd (Nat.card H) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card H := by
    rcases Nat.even_or_odd (Nat.card H) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h g g.2
  rw [Subgroup.orderOf_coe g, hg] at this
  exact absurd this (by decide)

omit [Finite G] in
theorem pow_mul_mem_of_normalizer {K : Subgroup G} {k w : G} (hk : k ∈ K)
    (hw : w ∈ normalizer (K : Set G)) (n : ℕ) :
    ∃ k'' ∈ K, (k * w) ^ n = k'' * w ^ n := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨k₁, hk₁, h₁⟩ := ih
    refine ⟨k₁ * (w ^ m * k * (w ^ m)⁻¹), ?_, ?_⟩
    · have : w ^ m ∈ normalizer (K : Set G) := Subgroup.pow_mem _ hw m
      exact K.mul_mem hk₁ ((Subgroup.mem_normalizer_iff.1 this k).1 hk)
    · rw [pow_succ, h₁]
      group

theorem W_le_KO
    (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hG : C3Hyp G) {x y : G} {K : Subgroup G} (hxK : IsIL2Pair x K)
    (hL9 : HasL2Model (kBar K) (fun q => q = 9))
    (h1 : pRank 2 ↥(CxK x K) = 1) (hy2 : orderOf y = 2)
    (hyC : y ∈ centralizer ({x} : Set G)) (hyK : y ∈ normalizer (K : Set G))
    :
    ∀ w ∈ pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ centralizer ({x} : Set G),
      ∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)), w = k * o := by
  intro w hw
  have hlift : ∀ w : G, w ∈ normalizer (K : Set G) → w * y = y * w → Odd (orderOf w) →
      ∃ k ∈ K, y * k = k * y ∧ ∀ k' ∈ K, ⁅k', k⁻¹ * w⁆ ∈ pPrimeCoreOf 2 K :=
    fun w hwK hwy hw => L710.exists_lift_inner hL9 hy2 hyK hwK hwy hw
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set D : Subgroup G := CxK x K with hD
  set O : Subgroup G := pPrimeCoreOf 2 C with hO
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ C with hW
  set CKy : Subgroup G := K ⊓ centralizer ({y} : Set G) with hCKy
  have hx2 : orderOf x = 2 := hxK.1
  have hr4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hLodd : HasL2Model (kBar K) Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨4, rfl⟩) hL9
  have hKC : K ≤ C := hxK.2.1
  have hnormK : ∀ c ∈ C, c ∈ normalizer (K : Set G) := fun c hc =>
    mem_normalizer_of_mem_centralizer hr4 hxK hLodd hc
  have hDC : D ≤ C := inf_le_left
  have hxD : x ∈ D := hxK.x_mem_CxK
  have hDnorm : ∀ c ∈ C, c ∈ normalizer (D : Set G) := fun c hc =>
    PumpL42.mem_normalizer_CxK ⟨hc, hnormK c hc⟩
  have hcenK : Subgroup.center (kBar K) = ⊥ := by
    have h' : HasL2Model (kBar K) (fun q => Odd q ∧ 3 < q) :=
      C3.Layer1.Back.hasL2Model_mono (fun q hq => by rw [hq]; exact ⟨⟨4, rfl⟩, by norm_num⟩) hL9
    exact Stage1.Thm6.Glue.center_eq_bot_of_isL2Model (Stage1.Thm6.Glue.isL2Model_of_hasL2Model h')
  have hKD : ∀ k ∈ K ⊓ D, k ∈ pPrimeCoreOf 2 K := fun k hk =>
    PumpElim.mem_pPrimeCoreOf_of_cSec hcenK hk.1 hk.2.2
  have hinvD : ∀ u ∈ D, orderOf u = 2 → u = x := by
    intro u hu hu2
    by_contra hne
    have hcomm : u * x = x * u := mem_centralizer_singleton_iff.1 (hDC hu)
    have := C3.Layer1.U1a.two_le_pRank_of_commute hu hxD hu2 hx2 hcomm hne
    omega
  have hWodd : Odd (Nat.card W) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({y} : Set G)))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hWodd' : ∀ v ∈ W, Odd (orderOf v) := fun v hv =>
    Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hv)
  have hWnorm : ∀ c ∈ C ⊓ centralizer ({y} : Set G), ∀ v ∈ W, c * v * c⁻¹ ∈ W := by
    intro c hc v hv
    obtain ⟨hcC, hcy⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨hvO, hvC⟩ := Subgroup.mem_inf.1 hv
    exact Subgroup.mem_inf.2 ⟨TwoThin.pPrimeCoreOf_normalized (centralizer ({y} : Set G)) hcy hvO,
      mul_mem (mul_mem hcC hvC) (inv_mem hcC)⟩
  have hCKyN : CKy ≤ normalizer (W : Set G) := by
    intro k hk
    obtain ⟨hkK, hky⟩ := Subgroup.mem_inf.1 hk
    have hkc : k ∈ C ⊓ centralizer ({y} : Set G) := Subgroup.mem_inf.2 ⟨hKC hkK, hky⟩
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hWnorm k hkc v hv, fun hv => ?_⟩
    have := hWnorm k⁻¹ (inv_mem hkc) _ hv
    simpa [mul_assoc] using this
  set D₂ : Subgroup G := (D ⊓ centralizer ({y} : Set G)) ⊓ (CKy ⊔ W) with hD₂
  have hD₂D : D₂ ≤ D := fun d hd => hd.1.1
  have hD₂C : D₂ ≤ C := fun d hd => hDC hd.1.1
  have hD₂odd_el : ∀ d ∈ D₂, Odd (orderOf d) := by
    intro d hd
    obtain ⟨hdDy, hdW⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hdD, hdy⟩ := Subgroup.mem_inf.1 hdDy
    obtain ⟨k, hk, v, hv, hdkv⟩ := (Th2.HY.mem_sup_iff_mul_of_le_normalizer hCKyN).1 hdW
    have hvodd := hWodd' v hv
    have hkK : k ∈ K := (Subgroup.mem_inf.1 hk).1
    have hvC : v ∈ C := (Subgroup.mem_inf.1 hv).2
    obtain ⟨k'', hk'', hpow⟩ := pow_mul_mem_of_normalizer hkK (hnormK v hvC) (orderOf v)
    have hdn : d ^ orderOf v = k'' := by
      rw [hdkv, hpow, pow_orderOf_eq_one, mul_one]
    have hdnD : d ^ orderOf v ∈ D := Subgroup.pow_mem D hdD _
    have hdnO : d ^ orderOf v ∈ pPrimeCoreOf 2 K := hKD _ ⟨hdn ▸ hk'', hdnD⟩
    have hmodd : Odd (orderOf (d ^ orderOf v)) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K)
        (Subgroup.orderOf_dvd_natCard (pPrimeCoreOf 2 K) hdnO)
    have hdvd : orderOf d ∣ orderOf v * orderOf (d ^ orderOf v) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact pow_orderOf_eq_one _)
    exact Odd.of_dvd_nat (hvodd.mul hmodd) hdvd
  have hD₂odd : Odd (Nat.card D₂) := odd_card_of_forall_odd_orderOf hD₂odd_el
  have hD₂norm : ∀ c ∈ C ⊓ centralizer ({y} : Set G), ∀ d ∈ D₂, c * d * c⁻¹ ∈ D₂ := by
    intro c hc d hd
    obtain ⟨hcC, hcy⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨hdDy, hdW⟩ := Subgroup.mem_inf.1 hd
    obtain ⟨hdD, hdy⟩ := Subgroup.mem_inf.1 hdDy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hDnorm c hcC) d).1 hdD,
      mul_mem (mul_mem hcy hdy) (inv_mem hcy)⟩, ?_⟩
    obtain ⟨k, hk, v, hv, rfl⟩ := (Th2.HY.mem_sup_iff_mul_of_le_normalizer hCKyN).1 hdW
    have e : c * (k * v) * c⁻¹ = (c * k * c⁻¹) * (c * v * c⁻¹) := by group
    rw [e]
    obtain ⟨hkK, hky⟩ := Subgroup.mem_inf.1 hk
    have hckc : c * k * c⁻¹ ∈ CKy := by
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hnormK c hcC) k).1 hkK, ?_⟩
      exact mul_mem (mul_mem hcy hky) (inv_mem hcy)
    exact Subgroup.mul_mem_sup hckc (hWnorm c hc v hv)
  have hkey : ∀ v ∈ W, ∃ k ∈ CKy, k⁻¹ * v ∈ D₂ := by
    intro v hv
    obtain ⟨hvO, hvC⟩ := Subgroup.mem_inf.1 hv
    have hvyc : v ∈ centralizer ({y} : Set G) := TwoThin.pPrimeCoreOf_le _ hvO
    have hvy : v * y = y * v := mem_centralizer_singleton_iff.1 hvyc
    obtain ⟨k, hk, hyk, hcomm⟩ := hlift v (hnormK v hvC) hvy (hWodd' v hv)
    have hkcy : k ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.2 hyk.symm
    have hkCKy : k ∈ CKy := Subgroup.mem_inf.2 ⟨hk, hkcy⟩
    have hkinv : k⁻¹ ∈ CKy := inv_mem hkCKy
    refine ⟨k, hkCKy, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mul_mem_sup hkinv hv⟩⟩
    · have hnk : k⁻¹ * v ∈ normalizer (K : Set G) :=
        mul_mem (inv_mem (Subgroup.le_normalizer hk)) (hnormK v hvC)
      exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hKC hk)) hvC,
        ⟨hnk, mem_normalizer_pPrimeCoreOf hnk, hcomm⟩⟩
    · exact mul_mem (inv_mem hkcy) hvyc
  by_cases hD₂O : D₂ ≤ O
  · obtain ⟨k, hk, hkD₂⟩ := hkey w hw
    exact ⟨k, (Subgroup.mem_inf.1 hk).1, k⁻¹ * w, hD₂O hkD₂, by group⟩
  · exfalso
    set yC : ↥C := ⟨y, hyC⟩ with hyCdef
    have hyC2 : orderOf yC = 2 := (Subgroup.orderOf_mk y hyC).trans hy2
    set D₂' : Subgroup ↥C := D₂.subgroupOf C with hD₂'
    have hmemD₂' : ∀ d : ↥C, d ∈ D₂' ↔ (d : G) ∈ D₂ := fun d => Subgroup.mem_subgroupOf
    have hD₂y : ∀ d ∈ D₂, d ∈ centralizer ({y} : Set G) := fun d hd =>
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hd).1).2
    have hD₂'cent : D₂' ≤ centralizer ({yC} : Set ↥C) := by
      intro d hd
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hD₂y _ ((hmemD₂' d).1 hd)))
    have hD₂'norm : (D₂'.subgroupOf (centralizer ({yC} : Set ↥C))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hnG : ((n : ↥C) : G) ∈ D₂ := (hmemD₂' _).1 hn
      have hgC : ((g : ↥C) : G) ∈ C := (g : ↥C).2
      have hgy : ((g : ↥C) : G) ∈ centralizer ({y} : Set G) := by
        have := g.2
        rw [mem_centralizer_singleton_iff] at this ⊢
        exact congrArg Subtype.val this
      have := hD₂norm ((g : ↥C) : G) (Subgroup.mem_inf.2 ⟨hgC, hgy⟩) _ hnG
      exact (hmemD₂' _).2 (by simpa using this)
    have hD₂'odd : Odd (Nat.card D₂') := by
      rw [hD₂', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₂C).toEquiv]
      exact hD₂odd
    have hDR : ¬ D₂' ≤ pPrimeCore 2 ↥C := by
      intro h
      apply hD₂O
      intro d hd
      have hdC : d ∈ C := hD₂C hd
      have : (⟨d, hdC⟩ : ↥C) ∈ D₂' := (hmemD₂' _).2 hd
      exact ⟨⟨d, hdC⟩, h this, rfl⟩
    obtain ⟨J, hJ, hyJ, hDJ, hJD, hJy⟩ :=
      CFSG.ComponentClassification.UnbalancedLayer.exists_active_two_component hyC2 hD₂'cent
        hD₂'norm hD₂'odd hDR
    set J'' : Subgroup G := J.map C.subtype with hJ''
    have hJ''C : J'' ≤ C := by
      rintro _ ⟨j, -, rfl⟩
      exact j.2
    have hJcomp : IsPCompIn 2 C J'' := by
      refine ⟨hJ''C, ?_⟩
      have : J''.subgroupOf C = J := Subgroup.comap_map_eq_self_of_injective C.subtype_injective J
      rw [this]
      exact hJ
    have hJleD : J ≤ D.subgroupOf C := by
      calc J = ⁅J, D₂'⁆ := hJD.symm
        _ ≤ D.subgroupOf C := by
          rw [Subgroup.commutator_le]
          intro j hj d hd
          rw [Subgroup.mem_subgroupOf]
          have hdD : (d : G) ∈ D := hD₂D ((hmemD₂' d).1 hd)
          have hjnorm : ((j : ↥C) : G) ∈ normalizer (D : Set G) := hDnorm _ (j : ↥C).2
          have e : ((⁅j, d⁆ : ↥C) : G) = ((j : G) * (d : G) * (j : G)⁻¹) * (d : G)⁻¹ := by
            simp [commutatorElement_def]
          rw [e]
          exact mul_mem ((Subgroup.mem_normalizer_iff.1 hjnorm _).1 hdD) (inv_mem hdD)
    have hJ''D : J'' ≤ D := by
      rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hJleD hj)
    have hqs : IsQuasisimple (↥J'' ⧸ pPrimeCore 2 ↥J'') := TwoThin.isQuasisimple_hat hJcomp
    have hJeven : 2 ∣ Nat.card J'' := by
      by_contra hne
      have hodd : Odd (Nat.card J'') := by
        rcases Nat.even_or_odd (Nat.card J'') with he | ho
        · exact absurd (even_iff_two_dvd.1 he) hne
        · exact ho
      have hsolv : Group.IsSolvable ↥J'' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
      have hsolv' : Group.IsSolvable (↥J'' ⧸ pPrimeCore 2 ↥J'') := inferInstance
      exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hqs hsolv'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' 2 hJeven
    have huD : (u : G) ∈ D := hJ''D u.2
    have hu2' : orderOf (u : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hu2
    have hux : (u : G) = x := hinvD _ huD hu2'
    have hxJ : x ∈ J'' := hux ▸ u.2
    have hyJ'' : y ∈ normalizer (J'' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨yC * j * yC⁻¹, (Subgroup.mem_normalizer_iff.1 hyJ j).1 hj, rfl⟩
      · rintro ⟨j, hj, hjeq⟩
        have hjeq' : (j : G) = y * h * y⁻¹ := hjeq
        have hhj : h = y⁻¹ * (j : G) * y := by
          rw [hjeq']; group
        refine ⟨yC⁻¹ * j * yC, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.1 (inv_mem hyJ) j).1 hj
          simpa [mul_assoc] using this
        · show y⁻¹ * (j : G) * y = h
          exact hhj.symm
    have hbad : ¬ pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) ≤
        centralizerSection J'' (pPrimeCoreOf 2 J'') := by
      intro hle
      have hZ : D₂ ≤ centralizer ({x, y} : Set G) := by
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rcases hh with rfl | hh
        · exact (mem_centralizer_singleton_iff.1 (hD₂C hd)).symm
        · rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact (mem_centralizer_singleton_iff.1 (hD₂y d hd)).symm
      have hDZN : (D₂.subgroupOf (centralizer ({x, y} : Set G))).Normal := by
        refine ⟨fun d hd n => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hd ⊢
        have hnZ := n.2
        have hnx : (n : G) ∈ C :=
          mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hnZ x (by simp)).symm
        have hny : (n : G) ∈ centralizer ({y} : Set G) :=
          mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hnZ y (by simp)).symm
        have := hD₂norm (n : G) (Subgroup.mem_inf.2 ⟨hnx, hny⟩) _ hd
        simpa using this
      have hD₂le : D₂ ≤ pPrimeCoreOf 2 (centralizer ({x, y} : Set G)) :=
        le_pPrimeCoreOf_of_normal_odd hZ hDZN (Nat.coprime_two_left.2 hD₂odd)
      have hcommle : ⁅J, D₂'⁆ ≤ (pPrimeCoreOf 2 J'').comap C.subtype := by
        rw [Subgroup.commutator_le]
        intro j hj d hd
        rw [Subgroup.mem_comap]
        have hdsec := hle (hD₂le ((hmemD₂' d).1 hd))
        have := hdsec.2.2 (j : G) ⟨j, hj, rfl⟩
        simpa [commutatorElement_def] using this
      have hJle : J ≤ (pPrimeCoreOf 2 J'').comap C.subtype :=
        calc J = ⁅J, D₂'⁆ := hJD.symm
          _ ≤ _ := hcommle
      have hJ''le : J'' ≤ pPrimeCoreOf 2 J'' := by
        rintro _ ⟨j, hj, rfl⟩
        exact hJle hj
      have hoddJ : Odd (Nat.card J'') :=
        Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd J'') (Subgroup.card_dvd_of_le hJ''le)
      exact (Nat.not_even_iff_odd.mpr hoddJ) (even_iff_two_dvd.mpr hJeven)
    have hLU : IsLocallyUnbalancing x y J'' := ⟨⟨hx2, hJcomp⟩, hy2, hyC, hyJ'', hbad⟩
    have hU2 := h102 G hG x y J'' hLU
    have hno : ¬ IsL34Quotient (kBar J'') := fun hl34 =>
      hL34 G hG.gen4 x J'' hx2 hJcomp ⟨hl34, (inU2_center hU2).1, (inU2_center hU2).2⟩
    have hs : IsSimpleGroup (kBar J'') := isSimpleGroup_kBar_of_inU2 hU2 hno
    have hcen : Subgroup.center (kBar J'') = ⊥ := center_eq_bot_of_simple_quasisimple hs hqs
    have hxcen : (QuotientGroup.mk (⟨x, hxJ⟩ : ↥J'') : kBar J'') ∈ Subgroup.center (kBar J'') := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (mem_centralizer_singleton_iff.1 (hJ''C j.2))
    rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxcen
    have hodd2 : Odd (Nat.card ↥(pPrimeCore 2 ↥J'')) := odd_card_pPrimeCore _
    have hdvd := Subgroup.orderOf_dvd_natCard _ hxcen
    rw [Subgroup.orderOf_mk x hxJ, hx2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd2) (even_iff_two_dvd.mpr hdvd)

end CFSG.GH74.GLS.C3.Layer1.EndN

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.EndN

theorem b_st1_prop71_lemma710_proved
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) : B_st1_prop71_lemma710 := by
  intro G _ _ hG hNoU T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP x y K hxyK hT hy hKM hL29 h1
  obtain ⟨hstar, -, -, -⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hNoU P41 hxyK
  have hunb : IsUnbalancingTriple x y K := hxyK.unbalancing
  have hxK : IsIL2Pair x K := hunb.1
  have hx2 : orderOf x = 2 := hxK.1
  have hy2 : orderOf y = 2 := hunb.2.1
  have hyC : y ∈ centralizer ({x} : Set G) := hunb.2.2.1
  have hyK : y ∈ normalizer (K : Set G) := hunb.2.2.2.1
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  have hTrank : pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) = pRank 2 G := by
    rw [pRank_eq_of_isSylowOf hT]
    exact hstar.2
  obtain ⟨A', hA'T, hA'⟩ := exists_isEStar_le hTrank
  have hA'S : A' ≤ S := hA'T.trans inf_le_left
  have hA'C : A' ≤ centralizer ({x} : Set G) := hA'T.trans inf_le_right
  have hxA' : x ∈ A' := hA'.mem_of_commute hstar.1 fun a ha =>
    (mem_centralizer_singleton_iff.mp (hA'C ha)).symm
  have hV : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ M :=
    (pPrimeCoreOf_le_thetaGA hxA' hx1).trans
      ((hMP.theta A' hA'S hA').le.trans (Subgroup.le_normalizer.trans hMN))
  have hKO := W_le_KO h102 hL34 hG hxK hL29 h1 hy2 hyC hyK
  intro hle
  apply hunb.2.2.2.2
  intro w hw
  obtain ⟨hwO, hwC⟩ := Subgroup.mem_inf.1 hw
  obtain ⟨k, hk, o, ho, hwko⟩ := hKO w hw
  have hwM : w ∈ M := by
    rw [hwko]
    exact M.mul_mem (hKM hk) (hV ho)
  set Z : Subgroup G := centralizer ({y} : Set G) ⊓ M with hZ
  have hWZ : pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ M ≤ Z :=
    inf_le_inf_right M (TwoThin.pPrimeCoreOf_le _)
  have hN : ((pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ M).subgroupOf Z).Normal := by
    refine ⟨fun v hv n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    obtain ⟨hvO, hvM⟩ := Subgroup.mem_inf.1 hv
    obtain ⟨hnY, hnM⟩ := Subgroup.mem_inf.1 n.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa using TwoThin.pPrimeCoreOf_normalized (centralizer ({y} : Set G)) hnY hvO
    · simpa using M.mul_mem (M.mul_mem hnM hvM) (M.inv_mem hnM)
  have hodd : Odd (Nat.card ↥(pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ M)) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({y} : Set G)))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hW_M : pPrimeCoreOf 2 (centralizer ({y} : Set G)) ⊓ M ≤ pPrimeCoreOf 2 Z :=
    le_pPrimeCoreOf_of_normal_odd hWZ hN (Nat.coprime_two_left.2 hodd)
  exact hle (Subgroup.mem_inf.2 ⟨hW_M (Subgroup.mem_inf.2 ⟨hwO, hwM⟩), hwC⟩)

theorem b_st1_prop71_endB_of_lemma711
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hB2 : B_B2) (hX : B_st1_prop71_lemma711) :
    B_st1_prop71_endB :=
  b_st1_prop71_endB_of_leaves h102 h14 hL34 hadd hB2
    (b_st1_prop71_lemma710_proved h102 h14 hL34 hadd) hX

end CFSG.GH74.GLS
