module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoYOneBeta
public import CFSG.Quasithin.Background.E6Nineteen
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupMain
public import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv AltStdBal AltStdSec

@[expose] def CycTwoCentInfLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G), OrderTwo G L Q n θ z → 13 ≤ n →
      centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q

@[expose] def CycTwoCentInfEleven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (θ : L ≃* alternatingGroup (Fin 11))
    (z : G), OrderTwo G L Q 11 θ z → centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q

namespace YOne

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem oddCore_le_oddY_of_base {θ : L ≃* alternatingGroup (Fin n)} (B : Two.Base G L Q n z) :
    (CFSG.oddCore (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ≤
      oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn8 : 8 ≤ n := by have := B.hn; omega
  set C := centralizer ({z} : Set G) with hC
  set N := (CFSG.oddCore C).map C.subtype with hN
  have hNC : N ≤ C := map_subtype_le _
  have hNodd : Odd (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective C.subtype_injective,
      ClassicalInvolution.QuaternionStructure.oddCore_eq_pPrimeCore_two]
    exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  have hNnorm : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
    rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, (CFSG.oddCore_normal C).conj_mem x hx _, rfl⟩
  have hLC : L ≤ C := le_cent_single B.std B.cyc
  have hCN : C ≤ normalizer (L : Set G) := cent_le_normalizer B.std B.cyc
  have hLN : L ⊓ N = ⊥ := by
    have hsL : IsSimpleGroup L := isSimpleGroup_of_alt (by omega) θ
    have hn : ((L ⊓ N).subgroupOf L).Normal := by
      refine ⟨fun m hm l => ?_⟩
      have hm' : (m : G) ∈ L ⊓ N := hm
      show ((l * m * l⁻¹ : L) : G) ∈ L ⊓ N
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.2 ⟨L.mul_mem (L.mul_mem l.2 m.2) (L.inv_mem l.2),
        hNnorm l (hLC l.2) m (Subgroup.mem_inf.1 hm').2⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ N).subgroupOf L) with h1 | h1
    · exact (Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le inf_le_left
    · exfalso
      have hLN' : L ≤ N := fun l hl =>
        (Subgroup.mem_inf.1 (Subgroup.subgroupOf_eq_top.1 h1 hl)).2
      have h2 : orderOf (YOne.invE θ hn8) ∣ Nat.card L := orderOf_dvd_natCard _
      rw [YOne.orderOf_invE θ hn8] at h2
      have h3 : Odd (Nat.card L) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hLN')
      exact (Nat.not_even_iff_odd.2 h3) (even_iff_two_dvd.2 h2)
  have hNK : N ≤ centralizer (L : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro l hl
    have h1 : l * x * l⁻¹ * x⁻¹ ∈ L ⊓ N := by
      refine Subgroup.mem_inf.2 ⟨?_, N.mul_mem (hNnorm l (hLC hl) x hx) (N.inv_mem hx)⟩
      have : x * l⁻¹ * x⁻¹ ∈ L := (mem_normalizer_iff.1 (hCN (hNC hx)) _).1 (L.inv_mem hl)
      have h2 : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
      rw [h2]
      exact L.mul_mem hl this
    rw [hLN, mem_bot] at h1
    calc l * x = (l * x * l⁻¹ * x⁻¹) * x * l := by group
      _ = x * l := by rw [h1, one_mul]
  set M := centralizer (L : Set G) ⊓ C with hM
  have hNM : N ≤ M := le_inf hNK hNC
  have hle : N.subgroupOf M ≤ CFSG.pPrimeCore 2 M := by
    refine le_sSup ⟨⟨fun x hx m => ?_⟩, ?_⟩
    · exact hNnorm m (Subgroup.mem_inf.1 m.2).2 x hx
    · rw [Nat.coprime_two_left]
      have : Nat.card (N.subgroupOf M) = Nat.card N :=
        Nat.card_congr (subgroupOfEquivOfLe hNM).toEquiv
      rwa [this]
  have h1 := Subgroup.map_mono (f := M.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hNM] at h1

theorem oddY_le_centralizer_pCore_of_base {θ : L ≃* alternatingGroup (Fin n)}
    (B : Two.Base G L Q n z) (w : L) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) ≤
      centralizer (CFSG.Open.pCoreOf 2 (centralizer ({(w : G)} : Set G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({(w : G)} : Set G) with hX
  set Y := oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) with hY
  have hYX : Y ≤ X := fun y hy => mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (Two.oddY_le_centralizer B.cyc hy) w w.2).symm
  have hzX : z ∈ X := mem_centralizer_of_mem_of_base (_θ := θ) B w
  have hz2 : IsPGroup 2 (zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, B.cyc.order, pow_one]
  refine CFSG.Quasithin.E6.le_centralizer_of_AxB ?_ (map_subtype_le _) ?_ hz2
    ((zpowers_le.2 hzX)) hYX ?_ (Two.odd_card_oddY B.cyc) ?_
  · exact CFSG.pCore_isPGroup.map _
  · intro x hx
    rw [mem_normalizer_iff]
    intro p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨x, hx⟩ * q * ⟨x, hx⟩⁻¹, CFSG.pCore_normal.conj_mem q hq _, rfl⟩
    · intro hp
      obtain ⟨q, hq, hqe⟩ := hp
      refine ⟨⟨x, hx⟩⁻¹ * q * ⟨x, hx⟩, ?_, ?_⟩
      · have := CFSG.pCore_normal.conj_mem q hq ⟨x, hx⟩⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hqe ⊢
        rw [hqe]
        group
  · rw [zpowers_eq_closure, centralizer_closure]
    exact Two.oddY_le_centralizer_z B.cyc
  · rw [zpowers_eq_closure, centralizer_closure]
    exact inf_le_right.trans (Two.le_normalizer_oddY B.std B.cyc)

theorem oddY_eq_bot_of_two_core {θ : L ≃* alternatingGroup (Fin n)} (B : Two.Base G L Q n z)
    (hn : 11 ≤ n) (hlook : AltLookupAt (n - 4))
    (hcore₁ : CFSG.oddCore (centralizer
      ({((invE θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥)
    (hcore₂ : CFSG.oddCore (centralizer
      ({((invE₂ θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥) :
    oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) = ⊥ := by
  have hn8 : 8 ≤ n := hn8_of_eleven hn
  set e := invE θ hn8 with he
  have hθe : θ e = dtE hn8 := MulEquiv.apply_symm_apply θ _
  have hsupp : ((θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).support.card = 4 := by
    rw [hθe]; exact support_card_dtE hn8
  set X := centralizer ({(e : G)} : Set G) with hX
  set Y := oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) with hY
  have hYX : Y ≤ X := fun y hy => mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (Two.oddY_le_centralizer B.cyc hy) e e.2).symm
  have hYodd := Two.odd_card_oddY B.cyc
  have hOX : CFSG.oddCore X = ⊥ := hcore₁
  have hOXin : CFSG.QuasithinUnique.oddCoreIn X = ⊥ := by
    show (CFSG.Open.fusionOddCore X).map X.subtype = ⊥
    have : CFSG.Open.fusionOddCore X = CFSG.oddCore X := rfl
    rw [this, hOX, Subgroup.map_bot]
  have h := localDatum_of_four_of_core (θ := θ) B hn (orderOf_invE θ hn8) hsupp hcore₁
  have hlook' : AltLookupAt
      (Fintype.card (fixFin ((θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)))) := by
    rw [Fintype.card_coe, card_fixFin, hsupp]
    exact hlook
  have hYsub : Odd (Nat.card (Y.subgroupOf X)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hYX).toEquiv]
  have hYt : Y.subgroupOf X ≤ centralizer
      ({(⟨z, mem_centralizer_of_mem_of_base (_θ := θ) B e⟩ : X)} : Set X) := by
    intro y hy
    rw [mem_centralizer_mk_iff]
    exact Two.oddY_le_centralizer_z B.cyc hy
  have hYD : Y.subgroupOf X ≤ centralizer
      (((fixGroup θ e).subgroupOf X : Subgroup X) : Set X) := by
    intro y hy
    rw [mem_centralizer_subgroupOf_iff (fixGroup_le_centralizer θ e), mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_iff.1 (Two.oddY_le_centralizer B.cyc hy) l (fixGroup_le θ e hl)
  have hE : ∀ K : Subgroup G, CFSG.QuasithinUnique.IsComponentIn K X →
      Y ≤ centralizer (K : Set G) := by
    rintro K ⟨hKX, hK⟩
    by_cases hβ : ⁅(fixGroup θ e).subgroupOf X, K.subgroupOf X⁆ = ⊥
    · exfalso
      refine no_beta_of_core (θ := θ) B hn hlook hn8 hcore₂ hKX hK ?_
      intro k hk
      rw [mem_centralizer_iff]
      intro l hl
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hβ
        (show (⟨l, fixGroup_le_centralizer θ e hl⟩ : X) ∈ (fixGroup θ e).subgroupOf X from hl)
      have h2 := mem_centralizer_iff.1 h1 ⟨k, hKX hk⟩ hk
      exact (congrArg Subtype.val h2).symm
    · have h1 := h.le_centralizer_alpha (etaW θ e) hlook' hYsub hYt hYD hK hβ
      intro y hy
      have h2 := h1 (show (⟨y, hYX hy⟩ : X) ∈ Y.subgroupOf X from hy)
      exact (mem_centralizer_subgroupOf_iff hKX).1 h2
  have hYO := CFSG.Quasithin.E6.le_oddCoreIn_of_centralizes hYX hYodd
    (oddY_le_centralizer_pCore_of_base (θ := θ) B e) (fun y _ => by
      rw [hOXin, mem_centralizer_iff]
      intro x hx
      simp only [SetLike.mem_coe, mem_bot] at hx
      rw [hx, one_mul, mul_one]) hE
  rw [hOXin] at hYO
  exact le_bot_iff.1 hYO

theorem oddCore_eq_bot_of_two_core {θ : L ≃* alternatingGroup (Fin n)} (B : Two.Base G L Q n z)
    (hn : 11 ≤ n) (hlook : AltLookupAt (n - 4))
    (hcore₁ : CFSG.oddCore (centralizer
      ({((invE θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥)
    (hcore₂ : CFSG.oddCore (centralizer
      ({((invE₂ θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥) :
    CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := by
  have h1 := oddCore_le_oddY_of_base (θ := θ) B
  rw [oddY_eq_bot_of_two_core (θ := θ) B hn hlook hcore₁ hcore₂, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  exact h1

theorem centralizer_inf_eq_of_two_local_balance {θ : L ≃* alternatingGroup (Fin n)}
    (B : Two.Base G L Q n z) (hn : 11 ≤ n) (hlook : AltLookupAt (n - 4))
    (hcore₁ : CFSG.oddCore (centralizer
      ({((invE θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥)
    (hcore₂ : CFSG.oddCore (centralizer
      ({((invE₂ θ (hn8_of_eleven hn) : L) : G)} : Set G)) = ⊥) :
    centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q :=
  inf_centralizer_eq B.cyc.le B.cyc.pgroup B.cyc.odd_index B.cyc.cyclic B.cyc.mem
    ((cent_le_normalizer B.std B.cyc).trans (normalizer_le_normalizer_centralizer L))
    (oddCore_eq_bot_of_two_core (θ := θ) B hn hlook hcore₁ hcore₂)

theorem centralizer_inf_eq {θ : L ≃* alternatingGroup (Fin n)} (O : OrderTwo G L Q n θ z)
    (hn : 11 ≤ n) (hlook : AltLookupAt (n - 4)) :
    centralizer (L : Set G) ⊓ centralizer ({z} : Set G) = Q :=
  centralizer_inf_eq_of_two_local_balance (θ := θ) (Two.Base.of_orderTwo O) hn hlook
    (O.bal4 (invE θ (hn8_of_eleven hn)) (orderOf_invE θ (hn8_of_eleven hn))
      (by
        rw [invE, MulEquiv.apply_symm_apply]
        exact support_card_dtE (hn8_of_eleven hn)))
    (O.bal4 (invE₂ θ (hn8_of_eleven hn)) (orderOf_invE₂ θ (hn8_of_eleven hn))
      (by
        rw [invE₂, MulEquiv.apply_symm_apply]
        exact support_card_dtE₂ (hn8_of_eleven hn)))

end YOne

theorem cycTwoCentInfLarge_of_lookup (hlookup : AltComponentLookup) : CycTwoCentInfLarge := by
  intro G _ _ L Q n θ z O hn
  obtain ⟨k, hk⟩ := O.odd
  exact YOne.centralizer_inf_eq O (by omega)
    (YOne.altLookupAt_of_altComponentLookup hlookup (by omega) (by omega))

theorem cycTwoCentInfEleven_of_lookup (hlookup : WeakA7Lookup) : CycTwoCentInfEleven := by
  intro G _ _ L Q θ z O
  exact YOne.centralizer_inf_eq O le_rfl (YOne.altLookupAt_seven_of_weakA7Lookup hlookup)

section Holds

open CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd.Spor

theorem cycTwoCentInfLarge_holds : CycTwoCentInfLarge :=
  cycTwoCentInfLarge_of_lookup
    (altComponentLookup_of_inputs SeitzReduction.gls3OddLieAutComponentsInput
      CatLeafProof.lieOrderFormulasInput CatLeafProof.evenLieOuterTwoComponentsInput_holds
      co1LocalComponentsInput_holds hnLocalComponentsInput_holds
      (fourExactOuterInput_of_BM BMCase.inner_of_mulEquiv_pinnedB CatLeafProof.monsterInnerInput)
      lyOuterTrivialInput Sporadic.FischerOddCore.fi22OuterComponentsInput_holds
      CatLeafProof.monsterInnerInput CatLeafProof.monsterLocalComponentsInput)

end Holds

end CFSG.OddStandard.AltStdCycTwo
