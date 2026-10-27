module

public import CFSG.Quasithin.H13.L32AC36m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC36j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

theorem card_tildeV_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) :
    Nat.card ↥((subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
      (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H))) = 4 := by
  obtain ⟨-, hV8, -, hV12, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hIHN := hF.conjClosure_le_normalizer_V₁ (le_refl (conjClosure V H))
  have hVIH : V ≤ conjClosure (conjClosure V H) H :=
    (le_conjClosure V H).trans (le_conjClosure _ H)
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  have hsub : subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V ≤
      subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H) :=
    fun w hw => secImg_mono (le_conjClosure V H) hw
  have hV4 : (fsuV1 T V).relIndex V = 4 := by
    have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) V
    rw [inf_eq_left.mpr hV₁V, hV8, hV12] at h1
    omega
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub).toEquiv, card_subM hIHN hV₁V hVIH, hV4]

section Hat

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure (conjClosure V H) H)))]

theorem hat_C_eq_bot_F4 (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H) (hK₀ : conjClosure K T = K)
    (hHeq : H = K ⊔ (l1 T L V ⊔ T)) (hHat : IsHat (cStar K) (NativeSporadic.Carrier .M22))
    (h36H : Lemma14_7_36_HatIrr_F4)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ conjClosure V H, k * i * k⁻¹ * i⁻¹ ∈ fsuV1 T V) :
    (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H) ⊓
      fixV (autIH (fsuV1 T V) (conjClosure V H) H (conjClosure K T))).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)) = ⊥ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHI : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hIHN := hF.conjClosure_le_normalizer_V₁ (le_refl (conjClosure V H))
  have hIHU : conjClosure (conjClosure V H) H ≤ conjClosure V H :=
    conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi
  set J := centralizerMod (fsuV1 T V) (conjClosure V H) K with hJ
  have hV₁J : fsuV1 T V ≤ J := le_centralizerMod hF.H_le_normalizer_V₁ hKH hV₁I
  have hJU : J ≤ conjClosure V H := centralizerMod_le_left _ _ _
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_centralizerMod (hKH.trans hF.H_le_normalizer_V₁) (hKH.trans hHI)
      Subgroup.le_normalizer
  rcases h36H G T L V H S K hF.K_cComp hHeq hHat J hV₁J hJU hKJ with hJ1 | hJ2
  · rw [eq_bot_iff]
    intro w hw
    have hw' := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨a, haIH, ha⟩ := exists_mk_of_mem_tilde
      (w : ↥(tildeOf (fsuV1 T V) (conjClosure (conjClosure V H) H)))
    have hwa : (w : ↥(tildeOf (fsuV1 T V) (conjClosure (conjClosure V H) H))) =
        modMk hIHN (a : G) haIH := Subtype.ext ha.symm
    have haJ : (a : G) ∈ J := by
      refine ⟨hIHU haIH, a.2, fun k hk => ?_⟩
      have hkMp := actH_mem_autIH_of_mem (I := conjClosure V H) hF hF.K₀_le_H
        (le_conjClosure K T hk)
      have hfix := hw'.2 _ hkMp
      rw [hwa] at hfix
      have hc := hF.commutator_mem_of_actH_fix (le_refl (conjClosure V H)) haIH hfix
      have e : (a : G) * k * (a : G)⁻¹ * k⁻¹ = (k * a * k⁻¹ * (a : G)⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem hc
    rw [hJ1] at haJ
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Subtype.ext ?_)
    rw [hwa]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
      (x := ⟨(a : G), hIHN haIH⟩)).mpr haJ
  · exfalso
    apply hnt
    intro k hk i hi
    have hiJ : i ∈ J := by rw [hJ2]; exact hi
    have h1 := hiJ.2.2 k (hK₀ ▸ hk)
    have e : k * i * k⁻¹ * i⁻¹ = (i * k * i⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

theorem psiK_injective_hat_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H) (hHat : IsHat (cStar K) (NativeSporadic.Carrier .M22))
    (hc1 : ∀ l ∈ l1 T L V, ∃ k ∈ K, l⁻¹ * k ∈ pCoreOf 2 H ∧
      ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) :
    Function.Injective (psiKU hF hV₁I) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hker : ∀ x : ↥H, psiU hF hV₁I x = 1 ↔ (x : G) ∈ pCoreOf 2 H :=
    psiI_eq_one_iff hF le_rfl hV₁I (le_normalizer_conjClosure V H) le_rfl
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, hV8, -, hV12, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  obtain ⟨x, hxL1, -, hfpf⟩ := exists_l1_fpf_F4 S.hyp hMod h1222 h1332 h1334
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := by rw [L₁Of, oTwoRes_eq_oTwoUpper]
  have hxl : x ∈ l1 T L V := hl1eq ▸ hxL1
  have hxH : x ∈ H := hL1H hxl

  have hΨx : psiU hF hV₁I ⟨x, hxH⟩ ≠ 1 := by
    intro h1
    have hxQ := (hker ⟨x, hxH⟩).mp h1
    obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hno)
      rw [hV8, hV12] at this
      omega
    apply hv1
    refine hfpf v hv ?_
    have h2 := hF.toHypF98.toHypF91.commutator_conjClosure_le v (le_conjClosure V H hv) x hxQ
    have e : x * v * x⁻¹ * v⁻¹ = (v * x * v⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h2
  obtain ⟨k₀, hk₀, hxk₀, hk₀c⟩ := hc1 x hxl
  have hΨk₀ : psiU hF hV₁I ⟨k₀, hKH hk₀⟩ = psiU hF hV₁I ⟨x, hxH⟩ := by
    have h1 := (hker (⟨x, hxH⟩⁻¹ * ⟨k₀, hKH hk₀⟩)).mpr (by simpa using hxk₀)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  have hk0Z : (QuotientGroup.mk ⟨k₀, hk₀⟩ : cStar K) ∈ Subgroup.center (cStar K) :=
    (mk_mem_center_cStar_iff ⟨k₀, hk₀⟩).mpr hk₀c
  have hψk₀ : psiKU hF hV₁I (QuotientGroup.mk ⟨k₀, hk₀⟩) ≠ 1 := by
    have e : psiKU hF hV₁I (QuotientGroup.mk ⟨k₀, hk₀⟩) = psiU hF hV₁I ⟨k₀, hKH hk₀⟩ := rfl
    rw [e, hΨk₀]
    exact hΨx
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hHat.1
      (psiKU hF hV₁I).ker with hN | hN
  · have hdvd : Nat.card (psiKU hF hV₁I).ker ∣ 3 := hHat.2.1 ▸ Subgroup.card_dvd_of_le hN
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      apply hψk₀
      have heq : (psiKU hF hV₁I).ker = Subgroup.center (cStar K) :=
        Subgroup.eq_of_le_of_card_ge hN (by rw [h3, hHat.2.1])
      rw [← MonoidHom.mem_ker, heq]
      exact hk0Z
  · exfalso
    apply hψk₀
    rw [← MonoidHom.mem_ker, hN]
    exact Subgroup.mem_top _

theorem hat_code_F4
    (hSmall : HatM22SmallModules) (hA21 : AsA21SQTKSection) (h36H : Lemma14_7_36_HatIrr_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H) (hK₀ : conjClosure K T = K)
    (hHeq : H = K ⊔ (l1 T L V ⊔ T)) (hHat : IsHat (cStar K) (NativeSporadic.Carrier .M22))
    (hirrT : IsIrrPlusTildeT hF (le_refl (conjClosure V H)))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ conjClosure V H, k * i * k⁻¹ * i⁻¹ ∈ fsuV1 T V)
    (hψinj : Function.Injective (psiKU hF hV₁I)) :
    Mhat22Twelve ((K.subgroupOf H).map (psiU hF hV₁I)) ⊤ ⊥ := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hrange := range_psiK hF le_rfl hV₁I (le_normalizer_conjClosure V H)
  have hLmap := map_psiI hF le_rfl hV₁I (le_normalizer_conjClosure V H) hKH
  have eL : cStar K ≃* ↥(autSub (autIH (fsuV1 T V) (conjClosure V H) H K)
      (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H))) :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrange)
  have hcode := twelve_hat hSmall hA21 S hF hK₀ hV₁I le_rfl hirrT
    (le_normalizer_conjClosure V H) (IsHat.of_mulEquiv eL hHat)
  rw [hat_C_eq_bot_F4 S hF hV₁I hK₀ hHeq hHat h36H hnt, ← hLmap] at hcode
  exact hcode

theorem hat_inv_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H) (hψinj : Function.Injective (psiKU hF hV₁I))
    (hc1 : ∀ l ∈ l1 T L V, ∃ k ∈ K, l⁻¹ * k ∈ pCoreOf 2 H ∧
      ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K)
    (hl1n : (modO2Image H (l1 T L V)).Normal) :
    ∃ s ∈ (T.subgroupOf H).map (psiU hF hV₁I),
      ∃ z ∈ Subgroup.center ↥((K.subgroupOf H).map (psiU hF hV₁I)),
        s * (z : MulAut _) * s⁻¹ ≠ (z : MulAut _) := by
  have hTH : T ≤ H := hF.T_le_H
  have hker : ∀ x : ↥H, psiU hF hV₁I x = 1 ↔ (x : G) ∈ pCoreOf 2 H :=
    psiI_eq_one_iff hF le_rfl hV₁I (le_normalizer_conjClosure V H) le_rfl
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, -, -, ⟨hVc, -⟩⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G) := Setting147.H_le_N_l1_F4 S h1332 hl1n
  have hR1 := Setting147.R1_star_eq_F4 S h1222 h1332 h1334 hHL
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨t, ht, htn⟩ := S14.exists_T_not_triv_F4
  have htR : t ∉ pCoreOf 2 (l1 T L V ⊔ T) := fun h => htn (by
    have := (Setting147.T_trivSub_eq_F4 S h1222 h1332 h1334).symm.le h
    exact this.2)
  have htbar : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, hTH ht⟩ ∉
      modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) := by
    rintro ⟨r, hr, hre⟩
    have h1 := mk_eq_mk_iff.mp hre
    apply htR
    have h2 := (pCoreOf 2 (l1 T L V ⊔ T)).mul_mem (Subgroup.mem_subgroupOf.mp hr)
      (Setting147.O2H_le_R1 S h1)
    simpa using h2
  rw [hR1] at htbar
  have htT : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, hTH ht⟩ ∈ modO2Image H T :=
    ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have htC : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, hTH ht⟩ ∉
      Subgroup.centralizer (modO2Image H (l1 T L V) : Set _) := fun h => htbar ⟨htT, h⟩
  rw [Subgroup.mem_centralizer_iff] at htC
  push Not at htC
  obtain ⟨_, ⟨y, hy, rfl⟩, hyt⟩ := htC
  have hyl : (y : G) ∈ l1 T L V := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨k, hk, hyk, hkc⟩ := hc1 (y : G) hyl
  obtain ⟨z, hz, hzy⟩ := psiU_mem_center hF hV₁I hψinj y.2 hk hyk hkc
  refine ⟨psiU hF hV₁I ⟨t, hTH ht⟩, ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, z, hz, ?_⟩
  rw [hzy]
  intro hc
  apply hyt
  rw [← map_mul, ← map_mul, mk_eq_mk_iff]
  have h1 : psiU hF hV₁I (⟨t, hTH ht⟩ * y * ⟨t, hTH ht⟩⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    have e : y = ⟨(y : G), y.2⟩ := rfl
    rw [← e] at hc
    rw [hc]
    group
  have h2 := (hker _).mp h1
  have e2 : ((y * ⟨t, hTH ht⟩ : ↥H) : G)⁻¹ * ((⟨t, hTH ht⟩ * y : ↥H) : G) =
      ((y : G) * t)⁻¹ * (t * y * t⁻¹ * (y : G)⁻¹) * ((y : G) * t) := by
    simp only [Subgroup.coe_mul]
    group
  rw [e2]
  have h2' : t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 H := by simpa using h2
  exact (Subgroup.mem_normalizer_iff''.mp
    (le_normalizer_pCoreOf 2 H (H.mul_mem y.2 (hTH ht))) _).mp h2'

theorem hat_fixY_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H)
    (hfix2 : Nat.card ↥(fixV ((T.subgroupOf H).map (psiU hF hV₁I))) = 2) :
    fixV ((T.subgroupOf H).map (psiU hF hV₁I)) ≤
      (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)) := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, -, hV12, ⟨hVc, -⟩⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have hIHN := hF.conjClosure_le_normalizer_V₁ (le_refl (conjClosure V H))
  have hVIH : V ≤ conjClosure (conjClosure V H) H :=
    (le_conjClosure V H).trans (le_conjClosure _ H)
  have hV₁V : fsuV1 T V ≤ V := inf_le_left
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨-, a, -, -, -, ha, haV, -, -⟩ := S14.exists_basis_F4
  have haV' : a ∈ V := hV2.2.1 ha
  have haI : a ∈ conjClosure V H := le_conjClosure V H haV'
  obtain ⟨at', hat⟩ : ∃ w : ↥(subM (fsuV1 T V) (conjClosure (conjClosure V H) H)
      (conjClosure V H)), (w : ↥(tildeOf (fsuV1 T V) (conjClosure (conjClosure V H) H))) =
        modMk hIHN a (hVIH haV') :=
    ⟨⟨modMk hIHN a (hVIH haV'), (modMk_mem_subM_iff hIHN hV₁I _).mpr haI⟩, rfl⟩

  have hidx : ((fsuV1 T V).subgroupOf V₂).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) V₂
    rw [inf_eq_left.mpr hV2.1, hV2.2.2.2, hV12] at h1
    show (fsuV1 T V).relIndex V₂ = 2
    omega
  have hafix : at' ∈ fixV ((T.subgroupOf H).map (psiU hF hV₁I)) := by
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have htV₂ : (t : G) * a * (t : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (hV2.2.2.1 htT) a).mp ha
    have htV₁ : (t : G) * a * (t : G)⁻¹ ∉ fsuV1 T V := fun h => haV (by
      have := (Subgroup.mem_normalizer_iff.mp (hF.H_le_normalizer_V₁ t.2) a).mpr h
      exact this)
    have hrel : a⁻¹ * ((t : G) * a * (t : G)⁻¹) ∈ fsuV1 T V := by
      have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨a⁻¹, V₂.inv_mem ha⟩)
        (b := ⟨(t : G) * a * (t : G)⁻¹, htV₂⟩)).mpr
        ⟨fun h => absurd (by simpa using (fsuV1 T V).inv_mem h) haV,
          fun h => absurd h htV₁⟩
      exact Subgroup.mem_subgroupOf.mp h1
    apply Subtype.ext
    rw [psiI_apply, hat]
    rw [actH_modMk hF.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure _ H) t (hVIH haV')]
    apply Subtype.ext
    show secMk _ _ ⟨(t : G) * a * (t : G)⁻¹, _⟩ = secMk _ _ ⟨a, _⟩
    rw [secMk_eq_secMk_iff]
    have := (fsuV1 T V).inv_mem hrel
    simpa using this
  have ha1 : at' ≠ 1 := by
    intro h
    apply haV
    have h1 : (modMk hIHN a (hVIH haV') : ↥(tildeOf (fsuV1 T V)
        (conjClosure (conjClosure V H) H))) = 1 := by rw [← hat, h]; rfl
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
      (x := ⟨a, hIHN (hVIH haV')⟩)).mp (congrArg Subtype.val h1)
  have hord : orderOf at' = 2 := orderOf_eq_prime (sq_eq_one_subM at') ha1
  have hzle : Subgroup.zpowers at' ≤ fixV ((T.subgroupOf H).map (psiU hF hV₁I)) :=
    (Subgroup.zpowers_le).mpr hafix
  have hzeq : Subgroup.zpowers at' = fixV ((T.subgroupOf H).map (psiU hF hV₁I)) :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hfix2, Nat.card_zpowers, hord])
  rw [← hzeq, Subgroup.zpowers_le]
  show (at' : ↥(tildeOf (fsuV1 T V) (conjClosure (conjClosure V H) H))) ∈
    subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V
  rw [hat]
  exact (modMk_mem_subM_iff hIHN hV₁V _).mpr haV'

theorem hat_ZY_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H)
    (hF : HypF918 T V L (fsuV1 T V) V H K) (hV₁I : fsuV1 T V ≤ conjClosure V H)
    (hψinj : Function.Injective (psiKU hF hV₁I))
    (hc2 : ∀ k ∈ K, (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) →
      ∃ l ∈ l1 T L V, l⁻¹ * k ∈ pCoreOf 2 H) :
    ∀ z ∈ Subgroup.center ↥((K.subgroupOf H).map (psiU hF hV₁I)),
      ∀ y ∈ (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)),
      (z : MulAut _) y ∈ (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)) := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hker : ∀ x : ↥H, psiU hF hV₁I x = 1 ↔ (x : G) ∈ pCoreOf 2 H :=
    psiI_eq_one_iff hF le_rfl hV₁I (le_normalizer_conjClosure V H) le_rfl
  have hrange := range_psiK hF le_rfl hV₁I (le_normalizer_conjClosure V H)
  have hLmap := map_psiI hF le_rfl hV₁I (le_normalizer_conjClosure V H) hKH
  obtain ⟨-, -, hLTV, -, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hVIH : V ≤ conjClosure (conjClosure V H) H :=
    (le_conjClosure V H).trans (le_conjClosure _ H)
  have hl1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  intro z hz y hy
  let e1 : cStar K ≃* ↥((K.subgroupOf H).map (psiU hF hV₁I)) :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr (hrange.trans hLmap.symm))
  have hc : e1.symm ⟨z, z.2⟩ ∈ Subgroup.center (cStar K) := by
    rw [← Subgroup.map_center_eq e1.symm]
    exact ⟨_, hz, rfl⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e1.symm ⟨z, z.2⟩)
  rw [← hk] at hc
  obtain ⟨l, hl, hlk⟩ := hc2 (k : G) k.2 ((mk_mem_center_cStar_iff k).mp hc)
  have hzl : (z : MulAut _) = psiU hF hV₁I ⟨l, hL1H hl⟩ := by
    have h1 : (z : MulAut _) = (↑(e1 (QuotientGroup.mk k)) : MulAut ↥(subM (fsuV1 T V)
        (conjClosure (conjClosure V H) H) (conjClosure V H))) := by rw [hk]; simp
    rw [h1]
    have h2 := (hker (⟨l, hL1H hl⟩⁻¹ * ⟨k, hKH k.2⟩)).mpr (by simpa using hlk)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]
    rfl
  rw [hzl]
  exact psiI_mem_tildeV hF le_rfl hV₁I (le_normalizer_conjClosure V H) hVIH (hLN (hl1L hl)) hy

theorem hat_Pinv_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hV₁I : fsuV1 T V ≤ conjClosure V H) (hψinj : Function.Injective (psiKU hF hV₁I))
    (hc1 : ∀ l ∈ l1 T L V, ∃ k ∈ K, l⁻¹ * k ∈ pCoreOf 2 H ∧
      ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K)
    {P : Subgroup (MulAut ↥(subM (fsuV1 T V) (conjClosure (conjClosure V H) H)
      (conjClosure V H)))}
    (hSP : (T.subgroupOf H).map (psiU hF hV₁I) ≤ P) (hPX : P ≤ (H.subgroupOf H).map (psiU hF hV₁I))
    (hZP : (Subgroup.center ↥((K.subgroupOf H).map (psiU hF hV₁I))).map
      ((K.subgroupOf H).map (psiU hF hV₁I)).subtype ≤ P)
    (hPsolv : Group.IsSolvable ↥P) :
    ∀ p ∈ P, ∀ y ∈ (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)),
      p y ∈ (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) V).subgroupOf
        (subM (fsuV1 T V) (conjClosure (conjClosure V H) H) (conjClosure V H)) := by
  have hTH : T ≤ H := hF.T_le_H
  have hker : ∀ x : ↥H, psiU hF hV₁I x = 1 ↔ (x : G) ∈ pCoreOf 2 H :=
    psiI_eq_one_iff hF le_rfl hV₁I (le_normalizer_conjClosure V H) le_rfl
  obtain ⟨-, -, -, hV12, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hVIH : V ≤ conjClosure (conjClosure V H) H :=
    (le_conjClosure V H).trans (le_conjClosure _ H)
  set H₁ := (P.comap (psiU hF hV₁I)).map H.subtype with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.map_subtype_le _
  have hH₁sol : Group.IsSolvable ↥H₁ :=
    isSolvable_map_comap_subtype _ (fun x hx => (hker x).mp hx) hPsolv
  have hL1TH₁ : l1 T L V ⊔ T ≤ H₁ := by
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · obtain ⟨k, hk, hlk, hkc⟩ := hc1 l hl
      obtain ⟨z, hz, hzl⟩ := psiU_mem_center hF hV₁I hψinj (hL1H hl) hk hlk hkc
      refine ⟨⟨l, hL1H hl⟩, ?_, rfl⟩
      show psiU hF hV₁I ⟨l, hL1H hl⟩ ∈ P
      rw [← hzl]
      exact hZP ⟨z, hz, rfl⟩
    · exact ⟨⟨t, hTH ht⟩, hSP ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩, rfl⟩
  have hH₁M := h29 G T L V S.hyp H₁ hL1TH₁ (hH₁H.trans S.hz.2.1) hH₁sol
  have h6 := lemma1433Six_of_inputs_F4 h1332 h1334 h1222 G T L V S.hyp.hyp S.hyp.fsu
    (fsuV1 T V) H inf_le_left (fun h => by rw [h, Subgroup.card_bot] at hV12; omega) S.hz.2.1
  intro p hp y hy
  obtain ⟨h, -, rfl⟩ := hPX hp
  have hhV : (h : G) ∈ H ⊓ Subgroup.normalizer (V : Set G) := by
    rw [← h6]
    exact ⟨h.2, hH₁M ⟨h, hp, rfl⟩⟩
  exact psiI_mem_tildeV hF le_rfl hV₁I (le_normalizer_conjClosure V H) hVIH hhV.2 hy

end Hat

theorem false_of_hat_core_F4
    (hSmall : HatM22SmallModules) (hA21 : AsA21SQTKSection) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h28 : Lemma14_7_28_F4) (h29 : Thm14_7_29_F4)
    (h36H : Lemma14_7_36_HatIrr_F4) (h12H : CFSG.Quasithin.H.Mathieu.StmtH12_1HatM22)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    (hK₀ : conjClosure K T = K) (hHeq : H = K ⊔ (l1 T L V ⊔ T))
    (hHat : IsHat (cStar K) (NativeSporadic.Carrier .M22)) : False := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  obtain ⟨hc1, hc2, hl1n⟩ := hat_center_F4 h1222 h1332 h1334 h28 S hF.K_cComp hHat
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp hTH

  have hHKT : H = K ⊔ T := by
    refine le_antisymm ?_ (sup_le hKH hTH)
    conv_lhs => rw [hHeq]
    refine sup_le le_sup_left (sup_le (fun l hl => ?_) le_sup_right)
    obtain ⟨k, hk, hq, -⟩ := hc1 l hl
    have e : l = k * (l⁻¹ * k)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (hQT (inv_mem hq)))

  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFct := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have hIeq : I = conjClosure V H := by
    rcases h36H G T L V H S K hF.K_cComp hHeq hHat I hV₁I hIU (hK₀ ▸ hKI) with h | h
    · exfalso
      apply hnt
      intro k hk i hi
      rw [h] at hi
      have hkN := hF.H_le_normalizer_V₁ (hF.K₀_le_H hk)
      exact (fsuV1 T V).mul_mem ((Subgroup.mem_normalizer_iff.mp hkN i).mp hi)
        ((fsuV1 T V).inv_mem hi)
    · exact h
  subst hIeq
  have hψinj := psiK_injective_hat_F4 h1222 h1332 h1334 S hF hV₁I hHat hc1
  have hcode := hat_code_F4 hSmall hA21 h36H S hF hV₁I hK₀ hHeq hHat hirrT hnt hψinj
  obtain ⟨hLX, hXN, hCXL, hSyl, hXeq⟩ := hat_groups hF hV₁I hK₀ hHKT
  obtain ⟨hfix2, P, hSP, hPX, hZP, hPsolv, hPY⟩ := h12H _ sq_eq_one_subM _ _ _ hLX hXN hCXL
    hcode hSyl hXeq (hat_inv_F4 h1222 h1332 h1334 S hF hV₁I hψinj hc1 hl1n)
  exact hPY _ (card_tildeV_F4 h1332 h1334 S hF) (hat_fixY_F4 h1222 h1332 h1334 S hF hV₁I hfix2)
    (hat_ZY_F4 h1332 h1334 S hF hV₁I hψinj hc2)
    (hat_Pinv_F4 h1222 h1332 h1334 h29 S hF hV₁I hψinj hc1 hSP hPX hZP hPsolv)

end CFSG.Quasithin.H13.L32A.C
