module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92SylCat
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.ExclBridgeInner
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxFaith
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10FiCover
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.LocalBalance

theorem upD42_core_eq_bot {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ L) :
    GLAPPrimeCore 3 ↥L = ⊥ :=
  CFSG.HardMathSupport.Solomon.Coordinator.YS08.glaPPrimeCore_eq_bot_of_glaPComponent
    (glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO) hL

theorem upD42_isQuasisimple {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ L) :
    CFSG.Open.IsQuasisimple ↥L :=
  (CFSG.HardMathSupport.Solomon.Coordinator.YS08.isComponentOf_of_glaPComponent'
    (glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO) hL).2.2

theorem upD42_center_isPGroup {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ L) :
    IsPGroup 3 ↥(Subgroup.center ↥L) :=
  CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot
    Nat.prime_three (upD42_core_eq_bot L hO hL)

theorem upD42_barOf_equiv {X : Type} [Group X] [Finite X] (L : Subgroup X)
    (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ L) :
    Nonempty (barOf 3 L ≃* ↥L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (upD42_core_eq_bot L hO hL)).trans
    QuotientGroup.quotientBot⟩


theorem upD42Concl_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : UpD42Concl G) : UpD42Concl H := by
  have hc : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
    Subgroup.map_center_eq e
  rcases h with h | h | h
  · exact Or.inl (IsCatalogLieIso.of_mulEquiv (QuotientGroup.congr _ _ e hc) h)
  · exact Or.inr (Or.inl (IsCatalogLieIso.of_mulEquiv (QuotientGroup.congr _ _ e hc) h))
  · exact Or.inr (Or.inr (IsCatalogLieIso.of_mulEquiv (QuotientGroup.congr _ _ e hc) h))

theorem false_of_three_pow_nine_dvd_card {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (h : 3 ^ 9 ∣ Nat.card ↥L)
    (hsyl : ∀ P : Subgroup X, IsPGroup 3 P → Nat.card P ≤ 3 ^ 8) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥L) 3 h
  have hcard : Nat.card (P.map L.subtype) = 3 ^ 9 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hP]
  have hle := hsyl _ (IsPGroup.of_card hcard)
  rw [hcard] at hle
  exact absurd hle (by norm_num)

theorem upD42_center_eq_bot_of_isOmegaTwoBig
    {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (h : IsCatalogLieIso (L ⧸ Subgroup.center L) IsOmegaTwoBigIndex) :
    Subgroup.center L = ⊥ := by
  have hqn : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open L).2 hq)
  obtain ⟨t, n, ht, hn, hM⟩ := statedClassicalModel_of_isOmegaTwoBig h
  rcases ht with rfl | rfl
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier
        (K := K) (n := n) (p := 2) (f := 1) hn (by rw [hK, pow_one])
        (by rw [hK, pow_one])
    have hsub : Subsingleton (CFSG.Blueprint.Multiplier.generic .POmegaPlus n 2 1) := by
      have hgo : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n 2 1 = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      change Subsingleton (Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders
        .POmegaPlus n 2 1).1) × Multiplicative (ZMod (CFSG.Blueprint.Multiplier.genericOrders
          .POmegaPlus n 2 1).2))
      rw [hgo]
      infer_instance
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hqn e
      (eM.toEquiv.subsingleton_congr.mpr hsub)
  · obtain ⟨-, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hM
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaMinus_two_hopfMultiplier
        (K := K) (n := n) (b := b) (c := c) (p := 2) (f := 1) (by omega) hbc
        (by rw [hK, pow_one]) (by rw [hK, pow_one])
    have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    have hcop : Nat.Coprime 4 (2 ^ n + 1) := by
      simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    have hgcd : Nat.gcd 4 ((2 ^ 1) ^ n + 1) = 1 := by
      rw [pow_one]
      exact hcop.gcd_eq_one
    have hsub : Subsingleton (Multiplicative (ZMod (Nat.gcd 4 ((2 ^ 1) ^ n + 1)))) := by
      rw [hgcd]
      infer_instance
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hqn e
      (eM.toEquiv.subsingleton_congr.mpr hsub)

theorem upD42_exists_mem_conj_of_isOmegaTwoBig {X : Type} [Group X] [Finite X]
    (L : Subgroup X) (b : X) (hbL : b ∈ Subgroup.normalizer (L : Set X)) (hb3 : b ^ 3 = 1)
    (h : IsCatalogLieIso ↥L IsOmegaTwoBigIndex) :
    ∃ s : X, s ∈ L ∧ ∀ x ∈ L, b * x * b⁻¹ = s * x * s⁻¹ := by
  obtain ⟨t, n, ht, hn, hM⟩ := statedClassicalModel_of_isOmegaTwoBig h
  let β : MulAut ↥L := L.normalizerMonoidHom ⟨b, hbL⟩
  have hbN : (⟨b, hbL⟩ : Subgroup.normalizer (L : Set X)) ^ 3 = 1 := by
    ext
    simpa using hb3
  have hβ : β ^ 3 = 1 := by
    rw [← map_pow, hbN, map_one]
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthTwo_inner ht hn hM hβ
  refine ⟨s, s.2, fun x hx => ?_⟩
  have h1 : ((β ⟨x, hx⟩ : ↥L) : X) = b * x * b⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hbL⟩ ⟨x, hx⟩
  have h2 : ((β ⟨x, hx⟩ : ↥L) : X) = ((MulAut.conj s ⟨x, hx⟩ : ↥L) : X) := by rw [← hs]
  rw [← h1, h2]
  rfl


theorem false_of_upD42Concl_of_weaklyClosed
    (hΩ : UpD42ExclInnAt IsOmegaTwoBigIndex)
    {X : Type} [Group X] [Finite X] (L J A : Subgroup X) (b z : X)
    (hO : GLAPPrimeCore 3 X = ⊥) (hL : GLAPComponent 3 ⊤ L)
    (hbL : b ∈ Subgroup.normalizer (L : Set X)) (hb3 : b ^ 3 = 1)
    (hbnt : ∃ y ∈ L, y * b ≠ b * y) (hz : z ∈ Subgroup.center X)
    (hJ : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({b} : Set X)) J)
    (hJD : IsCatalogLieIso ↥J IsD42Index)
    (hAJ : A ≤ J) (hA : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4)
    (hC : ∀ y ∈ Subgroup.centralizer ({b} : Set X), y ∈ Subgroup.centralizer (J : Set X) →
      ∀ m : ℕ, y ^ 3 ^ m = 1 → y ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    (hwc : ∀ y : X, y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z ⊔ A →
      y * b * y⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers z)
    (hsyl : ∀ P : Subgroup X, IsPGroup 3 P → Nat.card P ≤ 3 ^ 8)
    (hcen : UpD42Concl (barOf 3 L)) : False := by
  obtain ⟨e⟩ := upD42_barOf_equiv L hO hL
  have hconcl : UpD42Concl ↥L := upD42Concl_of_mulEquiv e hcen
  have hq : CFSG.Open.IsQuasisimple ↥L := upD42_isQuasisimple L hO hL
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  rcases hconcl with hOm | hTw | hD8
  · have hZ : Subgroup.center ↥L = ⊥ := upD42_center_eq_bot_of_isOmegaTwoBig hq hOm
    have hLt : IsCatalogLieIso ↥L IsOmegaTwoBigIndex :=
      IsCatalogLieIso.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hOm
    have hLs : IsSimpleGroup ↥L :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isQuasisimple_of_center_eq_bot
        hq hZ
    obtain ⟨s, hsL, hsb⟩ := upD42_exists_mem_conj_of_isOmegaTwoBig L b hbL hb3 hLt
    obtain ⟨ℓ, hℓL, k, hbk⟩ :=
      exists_mem_mul_zpow_of_conj_inner hZ hJL hb3 hbnt hz hC hsL hsb
    exact false_of_upD42ExclInnAt_of_mem_mul_zpow hΩ hLs hLt hℓL hbk hz hb3 hbnt hJ hJD
      hAJ hA hA4 hC hwc
  · exact false_of_three_pow_nine_dvd_card
      ((StandardType.FrameRoute.FS81.three_pow_nine_dvd_card_of_isCatalogLieIso_twE62 hTw).trans
        (Subgroup.card_quotient_dvd_card (Subgroup.center ↥L))) hsyl
  · exact false_of_three_pow_nine_dvd_card
      ((StandardType.FrameRoute.FS81.three_pow_nine_dvd_card_of_isCatalogLieIso_d48 hD8).trans
        (Subgroup.card_quotient_dvd_card (Subgroup.center ↥L))) hsyl

end CFSG.HardMathSupport.Dickson.Sec6

end
