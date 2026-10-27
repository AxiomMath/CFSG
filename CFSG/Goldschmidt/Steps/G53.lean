module

public import CFSG.Goldschmidt.Steps.G53Tools
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.Goldschmidt

open CFSG.GorensteinWalter CFSG.Walter

namespace G53

variable {G : Type} [Group G] [Finite G]

theorem inf_generalizedFitting_props {a : G} {H M Y : Subgroup G}
    (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hNM : Subgroup.normalizer (Y : Set G) ≤ M) :
    generalizedFittingSubgroupOf (M ⊓ generalizedFittingSubgroupOf H) =
        M ⊓ generalizedFittingSubgroupOf H ∧
      M ⊓ Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer ((M ⊓ generalizedFittingSubgroupOf H : Subgroup G) : Set G) := by
  have hFH := generalizedFittingSubgroupOf_le H
  have hYC : Y ⊔ Subgroup.centralizer (Y : Set G) ≤ M :=
    (sup_centralizer_le_normalizer Y).trans hNM
  have hEX : componentLayerOf H ≤ M ⊓ generalizedFittingSubgroupOf H :=
    le_inf ((componentLayerOf_le_sup_centralizer (hYF.trans hFH)
      (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hYF hYsn)).trans hYC) le_sup_right
  refine ⟨generalizedFittingSubgroupOf_eq_self_of_componentLayerOf_le hEX inf_le_right,
    fun c hc => mem_normalizer_inf (Subgroup.le_normalizer hc.1)
      (le_normalizer_of_isNormalIn (generalizedFittingSubgroupOf_isNormalIn H) (hCH hc.2))⟩

theorem eq_of_two_le {H M Y : Subgroup G} (hsimple : IsSimpleGroup G) (hH : IsCoatom H)
    (hM : IsCoatom M) (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hNM : Subgroup.normalizer (Y : Set G) ≤ M)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)))
    (hSbar : ∃ Sbar : Subgroup G, Sbar ≤ H ∧ Sbar ≤ generalizedFittingSubgroupOf M ∧
      (Sbar.subgroupOf (generalizedFittingSubgroupOf M)).IsSubnormal ∧
      generalizedFittingSubgroupOf M ⊓ Subgroup.centralizer (Sbar : Set G) ≤ Sbar) : M = H :=
  (bender1970_1_7_iii_equalityOfMaximal hsimple H hH (subnormalHull H Y)
    (subnormalHull_le_generalizedFitting hYF) (isSubnormal_subnormalHull hYF hYsn)
    (generalizedFitting_inf_centralizer_subnormalHull_le H Y)
    ((subnormalHull_le_sup_centralizer hYF hYsn).trans
      ((sup_centralizer_le_normalizer Y).trans hNM)) hM (Or.inl hπ) hSbar).symm

theorem eq_of_two_le_of_commutator_eq (h37 : S_G37) (hsimple : IsSimpleGroup G) {a : G}
    (ha1 : a ≠ 1) (ha2 : a * a = 1) {H M Y V A₁ : Subgroup G} (hH : IsCoatom H)
    (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) (hM : IsCoatom M)
    (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hNM : Subgroup.normalizer (Y : Set G) ≤ M) (hSS : IsSStarIn M A₁)
    (hA₁ : CFSG.Open.IsElemAbelian 2 A₁) (haA : a ∈ A₁)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hVV : ⁅V, Subgroup.zpowers a⁆ = V) (hVA : V ∈ goldA a H)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) : M = H := by
  have haM : a ∈ M := hSS.1 haA
  have hac : a ∈ M ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨haM, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set X := M ⊓ generalizedFittingSubgroupOf H with hXdef
  set X₁ := componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) with hX₁def
  obtain ⟨hXF, hXN⟩ := inf_generalizedFitting_props hCH hYF hYsn hNM
  have hX₁X : X₁ ≤ X := layer_sup_oddFitting_le X
  have hX₁N : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X₁ : Set G) :=
    fun c hc => mem_normalizer_layer_sup_oddFitting (hXN hc)
  have hVX : V ≤ X := le_inf (hVY.trans hNM) hVF
  have hVX₁ : V ≤ X₁ := le_layer_sup_oddFitting hXF (hXN hac) ha2 hVX hVV
  obtain ⟨⟨h1, h1sn⟩, -⟩ := h37 G M A₁ hSS hA₁ a haA ha1 X₁ (hX₁X.trans inf_le_left) hX₁N
    (layer_sup_oddFitting_eq X)
  have hcX₁ : ⁅X₁, Subgroup.zpowers a⁆ ≤ X₁ := commutator_zpowers_le_of_mem_normalizer (hX₁N hac)
  have hVc : V ≤ ⁅X₁, Subgroup.zpowers a⁆ :=
    calc V = ⁅V, Subgroup.zpowers a⁆ := hVV.symm
      _ ≤ ⁅X₁, Subgroup.zpowers a⁆ := Subgroup.commutator_mono hVX₁ le_rfl
  have hVsn₁ : (V.subgroupOf X₁).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hVX₁ (hX₁X.trans inf_le_right) hVsn
  have hVsn₂ : (V.subgroupOf ⁅X₁, Subgroup.zpowers a⁆).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hVc hcX₁ hVsn₁
  have hVFM : V ≤ generalizedFittingSubgroupOf M := hVc.trans h1
  have hVsnM : (V.subgroupOf (generalizedFittingSubgroupOf M)).IsSubnormal :=
    isSubnormal_subgroupOf_trans hVc hVsn₂ h1sn
  have hNVH : Subgroup.normalizer (V : Set G) ≤ H := normalizer_le_of_mem_goldA hsimple hH hπ hVA
  exact eq_of_two_le hsimple hH hM hYF hYsn hNM hπ ⟨subnormalHull M V,
    (subnormalHull_le_sup_centralizer hVFM hVsnM).trans
      ((sup_centralizer_le_normalizer V).trans hNVH),
    subnormalHull_le_generalizedFitting hVFM, isSubnormal_subnormalHull hVFM hVsnM,
    generalizedFitting_inf_centralizer_subnormalHull_le M V⟩

theorem eq_of_two_le_of_elementary (h37 : S_G37) (hsimple : IsSimpleGroup G) {a : G}
    (ha1 : a ≠ 1) {H M Y V A₁ : Subgroup G} (hH : IsCoatom H)
    (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) (hM : IsCoatom M)
    (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hNM : Subgroup.normalizer (Y : Set G) ≤ M) (hSS : IsSStarIn M A₁)
    (hA₁ : CFSG.Open.IsElemAbelian 2 A₁) (haA : a ∈ A₁)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVY : V ≤ Subgroup.normalizer (Y : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hVel : CFSG.Open.IsElemAbelian p V) (hVcard : Nat.card V = p ^ 2)
    (hVA : ∀ v ∈ V, v ≠ 1 → Subgroup.zpowers v ∈ goldA a H)
    (hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))) : M = H := by
  have : Fact p.Prime := ⟨hp⟩
  have hFH := generalizedFittingSubgroupOf_le H
  have hYC : Y ⊔ Subgroup.centralizer (Y : Set G) ≤ M :=
    (sup_centralizer_le_normalizer Y).trans hNM
  set X := M ⊓ generalizedFittingSubgroupOf H with hXdef
  set X₁ := componentLayerOf X ⊔ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) with hX₁def
  obtain ⟨-, hXN⟩ := inf_generalizedFitting_props hCH hYF hYsn hNM
  have hX₁X : X₁ ≤ X := layer_sup_oddFitting_le X
  have hX₁N : M ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X₁ : Set G) :=
    fun c hc => mem_normalizer_layer_sup_oddFitting (hXN hc)
  have hVp : IsPGroup p V := IsPGroup.of_card hVcard
  have hVnc : ¬ IsCyclic V := not_isCyclic_of_isElemAbelian hp hVel hVcard
  have hCvH : ∀ v ∈ V, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ H := fun v hv hv1 =>
    (centralizer_singleton_le_normalizer_zpowers v).trans
      (normalizer_le_of_mem_goldA hsimple hH hπ (hVA v hv hv1))
  have hVX : V ≤ X := le_inf (hVY.trans hNM) hVF
  have hVsnX : (V.subgroupOf X).IsSubnormal := isSubnormal_subgroupOf_of_le hVX inf_le_right hVsn
  have hVFX : V ≤ CFSG.fittingSubgroupOf X :=
    le_fittingSubgroupOf_of_isSubnormal hVX hVsnX hVp.isNilpotent
  have hVodd : Odd (Nat.card V) := by
    rw [hVcard]
    exact (hp.odd_of_ne_two hp2).pow
  have hVO : V ≤ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X) := by
    rw [goldOddCoreOf_eq]
    exact le_oddCoreOf_of_odd (CFSG.fittingSubgroupOf_isNilpotent X) hVFX hVodd
  have hVO₁ : V ≤ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X₁) :=
    hVO.trans (layer_le_and_oddFitting_le X).2
  have hEM : componentLayerOf M ≤ H := sSup_le fun L hL => by
    obtain ⟨v, hv, hv1, hLv⟩ := exists_ne_one_le_centralizer_of_isComponentOf h37 hSS hA₁ haA ha1
      (hX₁X.trans inf_le_left) hX₁N (layer_sup_oddFitting_eq X) hVO₁ hVnc hL
    exact hLv.trans (hCvH v hv hv1)
  have hVFH : V ≤ CFSG.fittingSubgroupOf H :=
    le_fittingSubgroupOf_of_isSubnormal (hVF.trans hFH)
      (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hVF hVsn) hVp.isNilpotent
  have hpπ : p ∈ primesOfOrder (CFSG.fittingSubgroupOf H) := by
    show p ∈ (Nat.card (CFSG.fittingSubgroupOf H)).primeFactors
    rw [Nat.mem_primeFactors]
    refine ⟨hp, ?_, Nat.card_pos.ne'⟩
    exact (dvd_pow_self p two_ne_zero).trans (hVcard ▸ Subgroup.card_dvd_of_le hVFH)
  have hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (CFSG.fittingSubgroupOf H) →
      qCoreOf M q = ⊥ := by
    intro q hq hqπ
    have h1 := qCoreOf_inf_eq_bot_of_sup_centralizer_le hsimple hH hYF hYsn hYC hq hqπ
    have hqp : q ≠ p := fun h => hqπ (h ▸ hpπ)
    have : Fact q.Prime := ⟨hq⟩
    refine eq_bot_of_forall_inf_centralizer_eq_bot hVel.1 hVnc
      ((hVX.trans inf_le_left).trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in M q))) ?_
      fun v hv hv1 => ?_
    · obtain ⟨k, hk⟩ := (qCoreOf_isPGroup M q).exists_card_eq
      rw [hVcard, hk]
      exact Nat.Coprime.pow 2 k ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
    · rw [eq_bot_iff]
      intro x hx
      rw [← h1]
      exact ⟨hx.1, hCvH v hv hv1 hx.2⟩
  have hres : ∀ q : ℕ, q.Prime → q ∈ primesOfOrder (CFSG.fittingSubgroupOf H) →
      pResidualOf (generalizedFittingSubgroupOf H) q ≠ ⊥ := by
    intro q hq _ hres
    have := card_primesOfOrder_le_one_of_isPGroup hq (isPGroup_of_pResidualOf_eq_bot _ q hq hres)
    omega
  have hFM : CFSG.fittingSubgroupOf M ≤ H :=
    fittingSubgroupOf_le_of_pResidualOf_ne_bot hsimple H hH (subnormalHull H Y)
      (subnormalHull_le_generalizedFitting hYF) (isSubnormal_subnormalHull hYF hYsn)
      (generalizedFitting_inf_centralizer_subnormalHull_le H Y)
      ((subnormalHull_le_sup_centralizer hYF hYsn).trans hYC) hres hO
  exact eq_of_two_le hsimple hH hM hYF hYsn hNM hπ ⟨generalizedFittingSubgroupOf M,
    sup_le hFM hEM, le_rfl, by rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top,
    inf_le_left⟩

theorem isPGroup_normalizer_centralizer (h37 : S_G37) {S : Sylow 2 G} {A : Subgroup G}
    (hG : GoldSetting G S A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {H M V : Subgroup G}
    (hH : IsCoatom H) (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) (hM : IsCoatom M)
    (haM : a ∈ M) (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal) (hVM : V ≤ M)
    (hVa : a ∈ Subgroup.normalizer (V : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hFp : IsPGroup p (generalizedFittingSubgroupOf H)) (hVel : CFSG.Open.IsElemAbelian p V)
    (hVcard : Nat.card V = p ^ 2) (hVA : ∀ v ∈ V, v ≠ 1 → Subgroup.zpowers v ∈ goldA a H)
    (hOp : qCoreOf M p ≠ ⊥) :
    IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer
      ((qCoreOf M p ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))) := by
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have hFH := generalizedFittingSubgroupOf_le H
  have haH : a ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hH1 : H ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haH))
  set P₀ := qCoreOf M p ⊓ Subgroup.centralizer (V : Set G) with hP₀def
  set K := Subgroup.normalizer (P₀ : Set G) with hKdef
  have hVp : IsPGroup p V := IsPGroup.of_card hVcard
  have hVnc : ¬ IsCyclic V := not_isCyclic_of_isElemAbelian hp hVel hVcard
  have hMO : M ≤ Subgroup.normalizer (qCoreOf M p : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in M p)
  have hP₀p : IsPGroup p P₀ := (qCoreOf_isPGroup M p).to_le inf_le_left
  have hP₀1 : P₀ ≠ ⊥ :=
    inf_centralizer_ne_bot_of_isPGroup hp hVp (qCoreOf_isPGroup M p) (hVM.trans hMO) hOp
  have hP₀M : P₀ ≤ M := inf_le_left.trans (qCoreOf_le M p)
  have hKtop : K ≠ ⊤ := normalizer_ne_top_of_le_isCoatom hsimple hM hP₀M hP₀1
  have hVK : V ≤ K := fun v hv => mem_normalizer_inf (hMO (hVM hv))
    (normalizer_le_normalizer_centralizer_subgroup V (Subgroup.le_normalizer hv))
  have haK : a ∈ K :=
    mem_normalizer_inf (hMO haM) (normalizer_le_normalizer_centralizer_subgroup V hVa)
  obtain ⟨g, hAg, hSS⟩ := hG.sstar K hKtop
  have hA₂ := isElemAbelian_conjSub_inf hG.elem g K
  have haA₂ : a ∈ conjSub g A ⊓ K := ⟨hAg ⟨haA, haK⟩, haK⟩
  set X' := K ⊓ qCoreOf H p with hX'def
  have hX'p : IsPGroup p X' := (qCoreOf_isPGroup H p).to_le inf_le_right
  have hX'N : K ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X' : Set G) :=
    fun c hc => mem_normalizer_inf (Subgroup.le_normalizer hc.1)
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in H p) (hCH hc.2))
  have hVOH : V ≤ qCoreOf H p :=
    le_qCoreOf_of_isSubnormal_isPGroup H V p (hVF.trans hFH)
      (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hVF hVsn) hVp
  have hVO' : V ≤ Goldschmidt.oddCoreOf (CFSG.fittingSubgroupOf X') := by
    rw [oddFitting_eq_of_isPGroup hp hp2 hX'p]
    exact le_inf hVK hVOH
  have hCv : ∀ v ∈ V, v ≠ 1 → IsPGroup p (generalizedFittingSubgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G))) := by
    intro v hv hv1
    obtain ⟨B, hB, hNB, hBp⟩ :=
      exists_isCoatom_isPGroup_of_mem_goldA hsimple hH hH1 hp hFp (hVA v hv hv1)
    have hvN : Subgroup.zpowers v ≤ Subgroup.normalizer (P₀ : Set G) :=
      Subgroup.zpowers_le.mpr (hVK hv)
    have hWp : IsPGroup p (Subgroup.zpowers v ⊔ P₀ : Subgroup G) :=
      (hVp.to_le (Subgroup.zpowers_le.mpr hv)).to_sup_of_normal_right' hP₀p hvN
    have hP₀v : P₀ ≤ Subgroup.centralizer ({v} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm)
    have hCvB : Subgroup.centralizer ({v} : Set G) ≤ B :=
      (centralizer_singleton_le_normalizer_zpowers v).trans hNB
    have hWB : Subgroup.zpowers v ⊔ P₀ ≤ B :=
      sup_le (Subgroup.le_normalizer.trans hNB) (hP₀v.trans hCvB)
    have h := isPGroup_generalizedFitting_inf_centralizer hp hBp hWB hWp
    have hCWB : Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G) ≤ B :=
      (Subgroup.centralizer_le (le_sup_left : Subgroup.zpowers v ≤ _)).trans
        (by rw [centralizer_zpowers_eq']; exact hCvB)
    rwa [inf_eq_right.mpr hCWB] at h
  have hCK : ∀ v : G,
      Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G) ≤ K := fun v =>
    (Subgroup.centralizer_le (le_sup_right : P₀ ≤ _)).trans (Subgroup.centralizer_le_normalizer _)
  have hP₀K : P₀ ≤ qCoreOf K p :=
    le_qCoreOf_of_normal_isPGroup K P₀ p Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hP₀p
  have hE : componentLayerOf K = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun L hL => ?_)
    exfalso
    obtain ⟨v, hv, hv1, hLv⟩ := exists_ne_one_le_centralizer_of_isComponentOf h37 hSS hA₂ haA₂
      ha1 inf_le_left hX'N (eq_layer_sup_oddFitting_of_isPGroup hp hp2 hX'p) hVO' hVnc hL
    have hLP₀ : L ≤ Subgroup.centralizer (P₀ : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (component_centralizes_fittingSubgroupOf hL)).trans
        (Subgroup.centralizer_le (hP₀K.trans (qCoreOf_le_fittingSubgroupOf K p hp)))
    have hLW : L ≤ Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ (Subgroup.le_centralizer_iff.mp hLP₀)
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hLv hl)
    have hLc : IsComponentOf L
        (Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G)) :=
      IsComponentOf.of_le hL hLW (hCK v)
    have hLF : L ≤ generalizedFittingSubgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G)) :=
      (le_sSup (s := {E : Subgroup G | IsComponentOf E _}) hLc).trans le_sup_right
    exact not_isNilpotent_of_isQuasisimple L hL.2.2 ((hCv v hv hv1).to_le hLF).isNilpotent
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → qCoreOf K q = ⊥ := by
    intro q hq hqp
    have : Fact q.Prime := ⟨hq⟩
    by_contra hne
    have hcop : Nat.Coprime (Nat.card V) (Nat.card (qCoreOf K q)) := by
      obtain ⟨k, hk⟩ := (qCoreOf_isPGroup K q).exists_card_eq
      rw [hVcard, hk]
      exact Nat.Coprime.pow 2 k ((Nat.coprime_primes hp hq).mpr (Ne.symm hqp))
    have hVN : V ≤ Subgroup.normalizer (qCoreOf K q : Set G) :=
      hVK.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in K q))
    obtain ⟨v, hv, hv1, hvne⟩ : ∃ v ∈ V, v ≠ 1 ∧
        qCoreOf K q ⊓ Subgroup.centralizer ({v} : Set G) ≠ ⊥ := by
      by_contra h
      push Not at h
      exact hne (eq_bot_of_forall_inf_centralizer_eq_bot hVel.1 hVnc hVN hcop h)
    set W' := qCoreOf K q ⊓ Subgroup.centralizer ({v} : Set G) with hW'def
    set CW := Subgroup.centralizer ((Subgroup.zpowers v ⊔ P₀ : Subgroup G) : Set G) with hCWdef
    have hW'P₀ : W' ≤ Subgroup.centralizer (P₀ : Set G) :=
      inf_le_left.trans ((qCoreOf_centralizer_of_ne K hp hq (Ne.symm hqp)).trans
        (Subgroup.centralizer_le hP₀K))
    have hW'CW : W' ≤ CW := by
      rw [hCWdef, Subgroup.le_centralizer_iff]
      refine sup_le ?_ (Subgroup.le_centralizer_iff.mp hW'P₀)
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mp hw.2
    have hCWv : CW ≤ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        ((le_sup_left : Subgroup.zpowers v ≤ Subgroup.zpowers v ⊔ P₀) (Subgroup.mem_zpowers v)))
    have hW'n : IsNormalIn W' CW := ⟨hW'CW, fun c hc x hx =>
      ⟨(qCoreOf_normal_in K q).2 c (hCK v hc) x hx.1,
        (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem (hCWv hc) hx.2)
          ((Subgroup.centralizer _).inv_mem (hCWv hc))⟩⟩
    have hW'q : IsPGroup q W' := (qCoreOf_isPGroup K q).to_le inf_le_left
    have hW'F : W' ≤ generalizedFittingSubgroupOf CW :=
      (le_fittingSubgroupOf_of_isNormalIn_nilpotent hW'CW hW'n hW'q.isNilpotent).trans le_sup_left
    exact hqp (eq_of_isPGroup_of_isPGroup hq hp hW'q ((hCv v hv hv1).to_le hW'F) hvne)
  exact isPGroup_generalizedFitting_of_qCoreOf_eq_bot hq hE

theorem isPGroup_of_isPGroup (h37 : S_G37) {S : Sylow 2 G} {A : Subgroup G}
    (hG : GoldSetting G S A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    {H M Y V : Subgroup G} (hH : IsCoatom H) (hCH : Subgroup.centralizer ({a} : Set G) ≤ H)
    (hM : IsCoatom M) (hYF : Y ≤ generalizedFittingSubgroupOf H)
    (hYsn : (Y.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hYa : a ∈ Subgroup.normalizer (Y : Set G)) (hNM : Subgroup.normalizer (Y : Set G) ≤ M)
    (hVF : V ≤ generalizedFittingSubgroupOf H)
    (hVsn : (V.subgroupOf (generalizedFittingSubgroupOf H)).IsSubnormal)
    (hVa : a ∈ Subgroup.normalizer (V : Set G)) (hVY : V ≤ Subgroup.normalizer (Y : Set G))
    (hcase : (⁅V, Subgroup.zpowers a⁆ = V ∧ V ∈ goldA a H) ∨
      (⁅V, Subgroup.zpowers a⁆ = ⊥ ∧
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Open.IsElemAbelian p V ∧ Nat.card V = p ^ 2) ∧
        ∀ v ∈ V, v ≠ 1 → Subgroup.zpowers v ∈ goldA a H))
    {p : ℕ} (hp : p.Prime) (hFp : IsPGroup p (generalizedFittingSubgroupOf H)) :
    IsPGroup p (generalizedFittingSubgroupOf M) := by
  have hsimple := hG.isSimpleGroup
  have : Fact p.Prime := ⟨hp⟩
  have haH : a ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have haM : a ∈ M := hNM hYa
  have hH1 : H ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haH))
  obtain ⟨g, hAg, hSS⟩ := hG.sstar M hM.1
  have hA₁ := isElemAbelian_conjSub_inf hG.elem g M
  have haA₁ : a ∈ conjSub g A ⊓ M := ⟨hAg ⟨haA, haM⟩, haM⟩
  have hVM : V ≤ M := hVY.trans hNM
  have hVX : V ≤ M ⊓ generalizedFittingSubgroupOf H := le_inf hVM hVF
  have hp2 : p ≠ 2 := by
    rcases hcase with ⟨hVV, hVA⟩ | ⟨-, ⟨q, hq, hq2, hVel, hVcard⟩, -⟩
    · rintro rfl
      exact hVA.1 (eq_bot_of_commutator_eq_self_of_isPGroup_two ha2 (hFp.to_le hVF) hVa hVV)
    · have hV1 : V ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hVcard
        have := hq.one_lt
        nlinarith
      rw [eq_of_isPGroup_of_isPGroup hp hq (hFp.to_le hVF) (IsPGroup.of_card hVcard) hV1]
      exact hq2
  set X := M ⊓ generalizedFittingSubgroupOf H with hXdef
  obtain ⟨-, hXN⟩ := inf_generalizedFitting_props hCH hYF hYsn hNM
  have hXp : IsPGroup p X := hFp.to_le inf_le_right
  have hXa : ⁅X, Subgroup.zpowers a⁆ ≤ qCoreOf M p :=
    commutator_le_qCoreOf_of_isPGroup h37 hSS hA₁ haA₁ ha1 inf_le_left hXN hp hp2 hXp
  obtain ⟨P₀, hP₀, hOp, hK⟩ : ∃ P₀ : Subgroup G, P₀ ≤ qCoreOf M p ∧ qCoreOf M p ≠ ⊥ ∧
      IsPGroup p (generalizedFittingSubgroupOf (Subgroup.normalizer (P₀ : Set G))) := by
    rcases hcase with ⟨hVV, hVA⟩ | ⟨-, ⟨q, hq, -, hVel, hVcard⟩, hVA⟩
    · have hVO : V ≤ qCoreOf M p :=
        (calc V = ⁅V, Subgroup.zpowers a⁆ := hVV.symm
          _ ≤ ⁅X, Subgroup.zpowers a⁆ := Subgroup.commutator_mono hVX le_rfl).trans hXa
      refine ⟨V, hVO, fun h => hVA.1 (le_bot_iff.mp (h ▸ hVO)), ?_⟩
      obtain ⟨B, hB, hNB, hBp⟩ := exists_isCoatom_isPGroup_of_mem_goldA hsimple hH hH1 hp hFp hVA
      have h := isPGroup_generalizedFitting_inf_normalizer hp hBp
        (Subgroup.le_normalizer.trans hNB) (hFp.to_le hVF)
      rwa [inf_eq_right.mpr hNB] at h
    · have hV1 : V ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hVcard
        have := hq.one_lt
        nlinarith
      have hpq : p = q :=
        eq_of_isPGroup_of_isPGroup hp hq (hFp.to_le hVF) (IsPGroup.of_card hVcard) hV1
      subst hpq
      have hS₀X : subnormalHull H Y ≤ X :=
        le_inf ((subnormalHull_le_sup_centralizer hYF hYsn).trans
          ((sup_centralizer_le_normalizer Y).trans hNM)) (subnormalHull_le_generalizedFitting hYF)
      have hCX : generalizedFittingSubgroupOf H ⊓ Subgroup.centralizer (X : Set G) ≤ X :=
        fun x hx => hS₀X (generalizedFitting_inf_centralizer_subnormalHull_le H Y
          ⟨hx.1, Subgroup.centralizer_le hS₀X hx.2⟩)
      have hXa1 : ⁅X, Subgroup.zpowers a⁆ ≠ ⊥ :=
        commutator_ne_bot_of_isPGroup hp hp2 hFp haH ha2 ha1 inf_le_right hCX
      have hOp : qCoreOf M p ≠ ⊥ := fun h => hXa1 (le_bot_iff.mp (h ▸ hXa))
      exact ⟨_, inf_le_left, hOp, isPGroup_normalizer_centralizer h37 hG haA ha1 hH hCH hM haM
        hVF hVsn hVM hVa hp hp2 hFp hVel hVcard hVA hOp⟩
  exact isPGroup_generalizedFitting_of_normalizer hsimple hM hp hP₀ hOp hK

end G53

theorem G53_of (h37 : S_G37) : S_G53 := by
  intro G _ _ S A hG a haA ha1 H hH Y V hY1 hYF hYsn hYa hVF hVsn hVa hVY hcase
  refine ⟨hY1, hYF, hYsn, hYa, fun M hM hNM => ?_⟩
  have hsimple := hG.isSimpleGroup
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact hG.elem.2 a haA
  have hHco : IsCoatom H := isCoatom_of_mem_benderM hH
  have hCH : Subgroup.centralizer ({a} : Set G) ≤ H := centralizer_le_of_mem_benderM hH
  have haH : a ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hH1 : H ≠ ⊥ := fun h => ha1 (Subgroup.mem_bot.mp (h ▸ haH))
  by_cases hπ : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf H))
  · left
    have haM : a ∈ M := hNM hYa
    obtain ⟨g, hAg, hSS⟩ := hG.sstar M hM.1
    have hA₁ := G53.isElemAbelian_conjSub_inf hG.elem g M
    have haA₁ : a ∈ conjSub g A ⊓ M := ⟨hAg ⟨haA, haM⟩, haM⟩
    rcases hcase with ⟨hVV, hVA⟩ | ⟨-, ⟨p, hp, hp2, hVel, hVcard⟩, hVA⟩
    · exact G53.eq_of_two_le_of_commutator_eq h37 hsimple ha1 ha2 hHco hCH hM hYF hYsn hNM hSS
        hA₁ haA₁ hVF hVsn hVY hVV hVA hπ
    · exact G53.eq_of_two_le_of_elementary h37 hsimple ha1 hHco hCH hM hYF hYsn hNM hSS hA₁ haA₁
        hVF hVsn hVY hp hp2 hVel hVcard hVA hπ
  · right
    have hπ1 : Nat.card (primesOfOrder (generalizedFittingSubgroupOf H)) = 1 :=
      le_antisymm (by omega) (one_le_card_primesOfOrder (generalizedFittingSubgroupOf_ne_bot hH1))
    obtain ⟨p, hp, hFp, -, -⟩ := exists_isPGroup_of_card_primesOfOrder_eq_one hπ1
    exact ⟨p, hp, G53.isPGroup_of_isPGroup h37 hG haA ha1 ha2 hHco hCH hM hYF hYsn hYa hNM hVF
      hVsn hVa hVY hcase hp hFp, hFp⟩

end CFSG.Goldschmidt
