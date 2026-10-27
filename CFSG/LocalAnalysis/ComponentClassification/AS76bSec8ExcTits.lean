module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsGroup
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcTitsCert
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Lemma83Mult
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Tits TitsSec8
open scoped commutatorElement

theorem isCharacteristicP_of_hasTwoCore {X : Type*} [Group X] (h : HasTwoCore X) :
    CFSG.IsCharacteristicP 2 X := by
  obtain ⟨J, hJ, hJ2, hJC⟩ := h
  have hle : J ≤ CFSG.pCore 2 X := le_sSup ⟨hJ, hJ2⟩
  exact (centralizer_le hle).trans (hJC.trans hle)

theorem exists_pow_eq_one_of_mem_generalizedFitting {X : Type*} [Group X] [Finite X]
    (h : CFSG.IsCharacteristicP 2 X) {x : X} (hx : x ∈ CFSG.generalizedFitting X) :
    ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [(CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).1 h] at hx
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 X)) ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

section Transport

variable {G : Type} [Group G] {A : Subgroup G} (φ : ↥A ≃* ↥titsD)

theorem map_cD_eq {a : G} (ha : a ∈ A) :
    ((cD (φ ⟨a, ha⟩)).map φ.symm.toMonoidHom).map A.subtype = A ⊓ centralizer {a} := by
  ext y
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨(φ.symm w).2, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := mem_centralizer_singleton_iff.1 hw
    have h2 := congrArg (fun v => ((φ.symm v : ↥A) : G)) h1
    simpa using h2
  · rintro hy
    obtain ⟨hyA, hyc⟩ := mem_inf.1 hy
    refine ⟨⟨y, hyA⟩, ⟨φ ⟨y, hyA⟩, mem_centralizer_singleton_iff.2 ?_, by simp⟩, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (mem_centralizer_singleton_iff.1 hyc))

noncomputable def centralizerEquiv {a : G} (ha : a ∈ A) :
    ↥(A ⊓ centralizer {a}) ≃* ↥(cD (φ ⟨a, ha⟩)) :=
  (MulEquiv.subgroupCongr (map_cD_eq φ ha)).symm.trans
    ((((cD (φ ⟨a, ha⟩)).map φ.symm.toMonoidHom).equivMapOfInjective A.subtype
      A.subtype_injective).symm.trans
      ((cD (φ ⟨a, ha⟩)).equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm)

theorem map_mem_cD {a y : G} (ha : a ∈ A) (hy : y ∈ A ⊓ centralizer {a}) :
    φ ⟨y, (mem_inf.1 hy).1⟩ ∈ cD (φ ⟨a, ha⟩) := by
  have hy' := hy
  rw [← map_cD_eq φ ha] at hy'
  obtain ⟨_, ⟨w, hw, rfl⟩, hwy⟩ := hy'
  have : (⟨y, (mem_inf.1 hy).1⟩ : ↥A) = φ.symm w := Subtype.ext hwy.symm
  rw [this, MulEquiv.apply_symm_apply]
  exact hw

end Transport

variable {G : Type} [Group G] [Finite G]

theorem false_of_tits
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) {A : Subgroup G} (hA : Hyp31 A)
    (hZ : center ↥A = ⊥) (φ : ↥A ≃* ↥titsD)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) : False := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hcheck := titsSec8_check
  obtain ⟨g, hg, R, T, hR, hT, hTN, -, hTR, hX, -⟩ :=
    section3Config_of h32 h33 h4 h34 G A hA
  have hc : Sec3 A R T g := ⟨hA, hR, hg, hT, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  have hRel := hc.elemR h32
  have hTel := hc.elemT h32
  have hAR : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := fun a ha r hr =>
    mem_centralizer_iff.1 (hR.le hr) a ha
  have hTR' : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t := fun t ht r hr =>
    (mem_centralizer_iff.1 (hc.le_centralizer ht) r hr).symm
  have hTT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hTel.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hRR : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' =>
    congrArg Subtype.val (hRel.1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
  have hRT := hc.inf_eq_bot
  have hZg : ∀ x ∈ rightConjugate A g, x ∈ rightConjugate (centralizer (A : Set G)) g → x = 1 := by
    intro x hxA hxK
    rw [mem_rightConjugate_iff] at hxA hxK
    have hmem : (⟨g * x * g⁻¹, hxA⟩ : ↥A) ∈ center ↥A := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (mem_centralizer_iff.1 hxK b b.2)
    rw [hZ, mem_bot] at hmem
    have h1 : g * x * g⁻¹ = 1 := congrArg Subtype.val hmem
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hinv : ∀ a (ha : a ∈ A), a * a = 1 → a ≠ 1 → orderOf (φ ⟨a, ha⟩) = 2 := by
    intro a ha ha2 ha1
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul]
      exact (map_eq_one_iff φ φ.injective).2 (Subtype.ext ha2)
    · intro h
      exact ha1 (congrArg Subtype.val ((map_eq_one_iff φ φ.injective).1 h))
  have hTA : A ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htA, htT⟩ := mem_inf.1 ht
    rw [mem_bot]
    by_contra ht1
    have ht2 : t * t = 1 := by rw [← sq]; exact hTel.2 t htT
    obtain ⟨⟨P, hP2, hPC, hxP⟩, -, -⟩ :=
      tits_involution_centralizer hcheck (hinv t htA ht2 ht1)
    let P' : Subgroup G := (P.map φ.symm.toMonoidHom).map A.subtype
    have hP'2 : IsPGroup 2 P' := (hP2.map _).map _
    have hP'C : P' ≤ ⁅A ⊓ centralizer {t}, A ⊓ centralizer {t}⁆ := by
      rw [← map_cD_eq φ htA, ← map_commutator, ← map_commutator]
      exact map_mono (map_mono hPC)
    have htP' : t ∈ ⁅P', P'⁆ := by
      rw [← map_commutator, ← map_commutator]
      refine ⟨φ.symm (φ ⟨t, htA⟩), ⟨φ ⟨t, htA⟩, hxP, rfl⟩, ?_⟩
      simp
    have hres := commutator_le_admResidual_of_isPGroup
      (X := oUpperTwo (A ⊓ centralizer ({t} : Set G)) ⊔
        ⁅A ⊓ centralizer ({t} : Set G), A ⊓ centralizer ({t} : Set G)⁆)
      (hP'C.trans le_sup_right) hP'2
    have htAg := (Lemma39.lemma39_one h4 h32 h34 hA hT htT ht1 hOut).1 (hres htP')
    exact ht1 (hZg t htAg (hT.le htT))
  have hpart : ∀ t ∈ T, ∃ p ∈ A, t⁻¹ * p ∈ R := fun t ht => hc.exists_aPart h32 h4 h34 ht
  have hcent : ∀ t ∈ T, ∀ p ∈ A, t⁻¹ * p ∈ R →
      A ⊓ centralizer ({t} : Set G) = A ⊓ centralizer ({p} : Set G) := by
    intro t _ p _ hr
    obtain ⟨r, hrR, rfl⟩ : ∃ r ∈ R, p = t * r := ⟨t⁻¹ * p, hr, by group⟩
    ext a
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun ha => ?_
    have hra := hAR a ha r hrR
    constructor
    · intro h
      calc a * (t * r) = a * t * r := by group
        _ = t * a * r := by rw [h]
        _ = t * (a * r) := by group
        _ = t * (r * a) := by rw [hra]
        _ = t * r * a := by group
    · intro h
      have h' : a * t * r = t * a * r := by
        calc a * t * r = a * (t * r) := by group
          _ = t * r * a := h
          _ = t * (r * a) := by group
          _ = t * (a * r) := by rw [hra]
          _ = t * a * r := by group
      exact mul_right_cancel h'
  have hpinv : ∀ t ∈ T, ∀ p ∈ A, t⁻¹ * p ∈ R → p * p = 1 := by
    intro t ht p _ hr
    have hp' : p = t * (t⁻¹ * p) := by group
    have h1 : t * t = 1 := by rw [← sq]; exact hTel.2 t ht
    have h2 : (t⁻¹ * p) * (t⁻¹ * p) = 1 := by rw [← sq]; exact hRel.2 _ hr
    rw [hp']
    calc t * (t⁻¹ * p) * (t * (t⁻¹ * p)) = t * t * ((t⁻¹ * p) * (t⁻¹ * p)) := by
          rw [mul_assoc t, ← mul_assoc (t⁻¹ * p), ← hTR' t ht _ hr]; group
      _ = 1 := by rw [h1, h2, one_mul]
  have hpne : ∀ t ∈ T, t ≠ 1 → ∀ p ∈ A, t⁻¹ * p ∈ R → p ≠ 1 := by
    intro t ht ht1 p _ hr hp1
    rw [hp1, mul_one] at hr
    have : t ∈ R ⊓ T := mem_inf.2 ⟨by simpa using inv_mem hr, ht⟩
    rw [hRT, mem_bot] at this
    exact ht1 this
  have hF : ∀ t ∈ T, t ≠ 1 → ∀ x ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, x ^ 2 ^ k ∈ (center A).map A.subtype := by
    intro t ht ht1 x hx
    obtain ⟨p, hpA, hr⟩ := hpart t ht
    have hx2 := hinv p hpA (hpinv t ht p hpA hr) (hpne t ht ht1 p hpA hr)
    obtain ⟨-, -, hcore⟩ := tits_involution_centralizer hcheck hx2
    have hchar : CFSG.IsCharacteristicP 2 ↥(A ⊓ centralizer ({t} : Set G)) := by
      rw [hcent t ht p hpA hr]
      exact CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
        (centralizerEquiv φ hpA).symm (isCharacteristicP_of_hasTwoCore hcore)
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_generalizedFitting hchar hy
    refine ⟨k, ?_⟩
    have : ((y : G)) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]
    rw [Subgroup.coe_subtype, this]
    exact one_mem _
  have hZT : (center A).map A.subtype ≤ centralizer (T : Set G) := by
    rw [hZ, Subgroup.map_bot]
    exact bot_le
  have h27 := lemma27 hTel (by rw [hc.card_eq]; exact hc.four_le) hTN hX hZT hF hTA
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    obtain ⟨⟨t, ht⟩, h⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc.T_ne_bot
    exact ⟨t, ht, fun h' => h (Subtype.ext h')⟩
  obtain ⟨p, hpA, hr⟩ := hpart t htT
  have hx2 := hinv p hpA (hpinv t htT p hpA hr) (hpne t htT ht1 p hpA hr)
  obtain ⟨-, hcen, -⟩ := tits_involution_centralizer hcheck hx2
  have hT2 : ∀ s ∈ T, s = 1 ∨ s = t := by
    intro s hs
    obtain ⟨q, hqA, hq⟩ := hpart s hs
    have hqp : q ∈ A ⊓ centralizer ({p} : Set G) := by
      refine mem_inf.2 ⟨hqA, mem_centralizer_singleton_iff.2 ?_⟩
      have hq' : q = s * (s⁻¹ * q) := by group
      have hp' : p = t * (t⁻¹ * p) := by group
      rw [hq', hp']
      have e1 := hTT s hs t htT
      have e2 := hTR' t htT _ hq
      have e3 := hTR' s hs _ hr
      have e4 := hRR _ hq _ hr
      calc s * (s⁻¹ * q) * (t * (t⁻¹ * p)) = s * t * ((s⁻¹ * q) * (t⁻¹ * p)) := by
            rw [mul_assoc s, ← mul_assoc (s⁻¹ * q), ← e2, mul_assoc t, ← mul_assoc s]
        _ = t * s * ((t⁻¹ * p) * (s⁻¹ * q)) := by rw [e1, e4]
        _ = t * (t⁻¹ * p) * (s * (s⁻¹ * q)) := by
            rw [mul_assoc t s, ← mul_assoc s (t⁻¹ * p), e3, mul_assoc, ← mul_assoc t]
    have hcomm : ∀ c ∈ A ⊓ centralizer ({p} : Set G), q * c = c * q := by
      intro c hc'
      have hcT : c ∈ A ⊓ centralizer ({t} : Set G) := by rw [hcent t htT p hpA hr]; exact hc'
      have hcs : c * s = s * c :=
        (mem_centralizer_iff.1
          ((commutator_eq_bot_iff_le_centralizer.1 (h27 t htT ht1)) hcT) s hs).symm
      have hcr := hAR c (mem_inf.1 hc').1 _ hq
      calc q * c = s * ((s⁻¹ * q) * c) := by group
        _ = s * (c * (s⁻¹ * q)) := by rw [← hcr]
        _ = (s * c) * (s⁻¹ * q) := by group
        _ = (c * s) * (s⁻¹ * q) := by rw [hcs]
        _ = c * q := by group
    have hw := map_mem_cD φ hpA hqp
    have hwc : ∀ c ∈ cD (φ ⟨p, hpA⟩), φ ⟨q, hqA⟩ * c = c * φ ⟨q, hqA⟩ := by
      intro c hc'
      have hc'' : ((φ.symm c : ↥A) : G) ∈ A ⊓ centralizer ({p} : Set G) := by
        rw [← map_cD_eq φ hpA]
        exact ⟨φ.symm c, ⟨c, hc', rfl⟩, rfl⟩
      have := hcomm _ hc''
      have h1 : (⟨q, hqA⟩ : ↥A) * φ.symm c = φ.symm c * ⟨q, hqA⟩ := Subtype.ext this
      have h2 := congrArg φ h1
      simpa using h2
    have hw2 : φ ⟨q, hqA⟩ * φ ⟨q, hqA⟩ = 1 := by
      rw [← map_mul]
      exact (map_eq_one_iff φ φ.injective).2 (Subtype.ext (hpinv s hs q hqA hq))
    rcases hcen _ hw hwc hw2 with h | h
    · left
      have hq1 : q = 1 := congrArg Subtype.val ((map_eq_one_iff φ φ.injective).1 h)
      rw [hq1, mul_one] at hq
      have : s ∈ R ⊓ T := mem_inf.2 ⟨by simpa using inv_mem hq, hs⟩
      rw [hRT, mem_bot] at this
      exact this
    · right
      have hqp' : q = p := congrArg Subtype.val (φ.injective h)
      rw [hqp'] at hq
      have h1 : s⁻¹ * t ∈ R := by
        have := mul_mem hq (inv_mem hr)
        simpa [mul_assoc] using this
      have : s⁻¹ * t ∈ R ⊓ T := mem_inf.2 ⟨h1, mul_mem (inv_mem hs) htT⟩
      rw [hRT, mem_bot, inv_mul_eq_one] at this
      exact this
  have hsub : (T : Set G) ⊆ {1, t} := fun s hs => by
    rcases hT2 s hs with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcard : Nat.card T ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have h4T : 4 ≤ Nat.card T := by rw [hc.card_eq]; exact hc.four_le
  omega

theorem step814_tits
    (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4) : Step814 .Tits := by
  intro G _ _ A D hD hA hZA
  cases D with
  | tits K hK e =>
    exfalso
    have hAp : commutator ↥A = ⊤ := hA.standard.1.1
    have hT : CFSG.Blueprint.ReeTitsModel (rankTwoQuot A) .Tits 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, K, inferInstance, inferInstance,
        by rw [hK]; norm_num, ⟨e⟩⟩
    have hZ : center ↥A = ⊥ := by
      have hlieT : CFSG.Blueprint.LieModel (↥A ⧸ center ↥A) .Tits 0 2 1 :=
        Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hT⟩))
      obtain ⟨-, ⟨eM⟩⟩ := LieType.Multipliers.Tits.multiplier_Tits _ hlieT
      have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hAp
      have h1 : Nat.card (RankThree.PerfectCover.hopfMultiplier (↥A ⧸ center ↥A)) = 1 := by
        rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
          Nat.card_congr eM.toEquiv, Nat.card_unique]
      have h2 := card_center_dvd_card_hopfMultiplier (MulEquiv.refl (↥A ⧸ center ↥A))
      rw [h1, Nat.dvd_one] at h2
      exact Subgroup.eq_bot_of_card_eq _ h2
    obtain ⟨e'⟩ := Sporadic.Schreier.Tits.titsModelEquiv (rankTwoQuot A) 2 1 hT
    let φ : ↥A ≃* ↥titsD :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e'
    have hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))) :=
      odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_Tits hT)
    exact false_of_tits h32 h33 h4 hA hZ φ hOut
  | g2 => simp [ExcModel.tag] at hD
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional
