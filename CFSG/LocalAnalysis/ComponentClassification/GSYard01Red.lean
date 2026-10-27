module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39K2
public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Defs
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFinal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSuz
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Final
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

@[expose] def QuasisimpleCentralSquareFourI : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → 3 ≤ CFSG.pRank 2 Q → center Q ≠ ⊥ →
    (∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) → IsSolomonI Q → IsTwoDisconnected Q →
    CentralSquareFour Q

@[expose] def QuasisimpleRankTwoCentralSquareFour : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → CFSG.pRank 2 Q = 2 → center Q ≠ ⊥ →
    (∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) → CentralSquareFour Q

theorem k2_theta_inf_le_theta (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {a b : G}
    (ha2 : orderOf a = 2) (haQ : a ∈ coreActionKernel K') (hb2 : orderOf b = 2)
    (hbQ : b ∈ coreActionKernel K') (hab : a * b = b * a)
    (haV : V ≤ centralizer ({a} : Set G)) (hbV : V ≤ centralizer ({b} : Set G))
    {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) (hEa : E ≤ centralizer ({a} : Set G))
    {ε : G} (hεK : ε ∈ K) (hε2 : orderOf ε = 2) (hεb : ε * b = b * ε)
    (hVε : V ≤ centralizer ({ε} : Set G)) :
    theta V b ⊓ centralizer ({a} : Set G) ≤ theta V a := by
  set Ca := centralizer ({a} : Set G) with hCa
  set Y := theta V b ⊓ Ca with hYdef
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVe := isElemAbelian_of_isKleinFour hV
  have hV1 : V ≠ ⊥ := fun h => by
    have := hV.card_four
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hPa := conjClosure_le_of_isKleinFour hq hR1 hG hN hK' hK hne.symm haQ ha2 hE hEK hEa
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVθ : V ≤ normalizer (theta V b : Set G) :=
    le_normalizer_theta (hbV.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hVY : V ≤ normalizer (Y : Set G) := fun v hv =>
    mem_normalizer_inf (hVθ hv) (le_normalizer (haV hv))
  have hYOb : Y ≤ oddCoreIn (centralizer ({b} : Set G)) :=
    inf_le_left.trans (theta_le_oddCoreIn hbV)
  have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hYOb) (coprime_card_oddCoreIn _)
  have hYodd : Odd (Nat.card Y) := Nat.coprime_two_left.mp hYcop
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V Y hV2 hVY hYcop
  have hba : b ∈ Ca := mem_centralizer_singleton_iff.mpr hab.symm
  have hSe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hb2)
  have hTe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two ha2)
  have hS1 := zpowers_ne_bot_of_orderOf_eq_two hb2
  have hT1 := zpowers_ne_bot_of_orderOf_eq_two ha2
  have hST : zpowers b ≤ centralizer ((zpowers a : Subgroup G) : Set G) := by
    rw [centralizer_zpowers_eq]; exact zpowers_le.mpr hba
  rw [← hfac]
  refine sup_le ?_ ?_
  ·
    set X := ⁅Y, V⁆ with hXdef
    have hXY : X ≤ Y := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y V hVY
    have hXD : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ Ca :=
      le_inf (hXY.trans hYOb) (hXY.trans inf_le_right)
    have hXD' : X ≤ oddCoreIn (centralizer ((zpowers b : Subgroup G) : Set G)) ⊓
        centralizer ((zpowers a : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq, centralizer_zpowers_eq]; exact hXD
    have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXY) hYcop)
    have hXX : ⁅X, V⁆ = X :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hYodd hVY
    have h25 := sol25 hS1 hT1 hSe hTe hST
    rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h25
    have hCO : Ca ≤ normalizer (oddCoreIn Ca : Set G) := le_normalizer_oddCoreIn Ca
    have hXO : X ≤ oddCoreIn Ca := by
      refine le_oddCoreIn_of_commutator_le (hXD.trans inf_le_right) hXodd
        ((Subgroup.commutator_mono le_rfl hXD).trans h25.1) fun M hM => ?_
      have hM' : IsTwoComponentIn M (centralizer ((zpowers a : Subgroup G) : Set G)) := by
        rw [centralizer_zpowers_eq]; exact hM
      rcases pump_moves_of_le hK' haQ ha2 hPa hM with h | h
      · have hVKa : V ≤ twoLayerIn (K' ⊓ Ca) :=
          le_pump_of_isPGroup hK' haQ ha2 hV2 (le_inf hVK' haV)
        have hMV : ⁅M, V⁆ ≤ oddCoreIn Ca :=
          (commutator_le_oddCoreIn_of_le_coreActionKernel (hVKa.trans h)).trans
            (oddCoreIn_le_of_isTwoComponentIn hM)
        exact commutator_le_of_eq_commutator (hXD.trans (h25.2 M hM).1)
          ((hXD.trans inf_le_right).trans hCO)
          (haV.trans hCO) (hM.1.trans hCO) hMV hXX
      · have hMS := commutator_le_oddCoreIn_of_le_pump_of_le hK' haQ ha2 hPa
          (S := zpowers b) (zpowers_le.mpr hbQ) (zpowers_le.mpr hba) h
        have hmove : ⁅M, zpowers b ⊓ normalizer (M : Set G)⁆ ≤ oddCoreIn M := by
          have h1 : ⁅M, zpowers b ⊓ normalizer (M : Set G)⁆ ≤ M :=
            CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing _ _ inf_le_right
          have h2 : ⁅M, zpowers b ⊓ normalizer (M : Set G)⁆ ≤ oddCoreIn Ca :=
            (Subgroup.commutator_mono le_rfl inf_le_left).trans hMS
          exact (le_inf h2 h1).trans
            (inf_le_oddCoreIn (coprime_card_oddCoreIn Ca) (hM.1.trans hCO))
        exact (commutator_le_oddCoreIn_of_not_moves hS1 hT1 hSe hTe hST hM' hXD'
          (Or.inr hmove)).trans (oddCoreIn_le_of_isTwoComponentIn hM)
    rw [← hXX]
    exact le_sup_of_le_left (Subgroup.commutator_mono hXO le_rfl)
  ·
    intro y hy
    have h1 := theta_inf_centralizer_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hb2 hbQ hbV
      hεK hε2 hεb hVε ⟨hy.1.1, hy.2⟩
    have h2 := inf_inf_le_oddCoreIn_of_le hK' haQ ha2 hPa hV1 hVe hVK' haV hS1 hSe
      (zpowers_le.mpr hbQ) (zpowers_le.mpr hba)
    rw [centralizer_zpowers_eq] at h2
    have hyO : y ∈ oddCoreIn Ca := h2 ⟨⟨h1.2, h1.1⟩, hy.1.2⟩
    exact mem_sup_right ⟨hyO, h1.2⟩

@[expose] def K2GoodInv (K V : Subgroup G) (t : G) : Prop :=
  ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ∧ A ≤ centralizer ({t} : Set G) ∧
    A ≤ centralizer (V : Set G)

theorem k2_wGroup_le_of_commute (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V C D : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hC : IsKleinFour C) (hCQ : C ≤ coreActionKernel K') (hCV : C ≤ centralizer (V : Set G))
    (hD : IsKleinFour D) (hDQ : D ≤ coreActionKernel K') (hDV : D ≤ centralizer (V : Set G))
    (hCD : C ≤ centralizer (D : Set G))
    (hgC : ∀ t ∈ C, t ≠ 1 → K2GoodInv K V t) (hgD : ∀ t ∈ D, t ≠ 1 → K2GoodInv K V t) :
    wGroup C V ≤ wGroup D V := by
  refine iSup₂_le fun e he => iSup_le fun he1 => ?_
  have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hC he he1
  have heV : V ≤ centralizer ({e} : Set G) := le_centralizer_singleton_of_mem hCV he
  have heD : D ≤ centralizer ({e} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hCD he)) d hd)
  have hθle : theta V e ≤ oddCoreIn (centralizer ({e} : Set G)) := theta_le_oddCoreIn heV
  have hcop : Nat.Coprime 2 (Nat.card (theta V e)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hDθ : D ≤ normalizer (theta V e : Set G) :=
    le_normalizer_theta (heD.trans le_normalizer)
      (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hDV h))
      (fun _ h => le_normalizer (hDV h))
  obtain ⟨A, hA, hAK, hAe, hAV⟩ := hgC e he he1
  obtain ⟨ε, hεA, hε1⟩ := exists_mem_ne_one_of_isKleinFour hA
  refine (le_iSup_inf_centralizer_of_isKleinFour hD hDθ hcop).trans ?_
  refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
  have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hD hf hf1
  obtain ⟨B₁, hB₁, hB₁K, hB₁f, -⟩ := hgD f hf hf1
  have hfe : f * e = e * f := mem_centralizer_singleton_iff.mp (heD hf)
  exact (k2_theta_inf_le_theta hq hR1 hG hN hK hK' hne hV hVK' hf2 (hDQ hf) he2 (hCQ he) hfe
    (le_centralizer_singleton_of_mem hDV hf) heV hB₁ hB₁K hB₁f (hAK hεA)
    (orderOf_eq_two_of_isKleinFour hA hεA hε1) (mem_centralizer_singleton_iff.mp (hAe hεA))
    (le_centralizer_singleton_of_mem hAV hεA)).trans (theta_le_wGroup hf hf1)

theorem k2_wGroup_eq_of_commute (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V C D : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hC : IsKleinFour C) (hCQ : C ≤ coreActionKernel K') (hCV : C ≤ centralizer (V : Set G))
    (hD : IsKleinFour D) (hDQ : D ≤ coreActionKernel K') (hDV : D ≤ centralizer (V : Set G))
    (hCD : C ≤ centralizer (D : Set G))
    (hgC : ∀ t ∈ C, t ≠ 1 → K2GoodInv K V t) (hgD : ∀ t ∈ D, t ≠ 1 → K2GoodInv K V t) :
    wGroup C V = wGroup D V := by
  have hDC : D ≤ centralizer (C : Set G) := fun d hd => mem_centralizer_iff.mpr fun c hc =>
    ((mem_centralizer_iff.mp (hCD hc)) d hd).symm
  exact le_antisymm
    (k2_wGroup_le_of_commute hq hR1 hG hN hK hK' hne hV hVK' hC hCQ hCV hD hDQ hDV hCD hgC hgD)
    (k2_wGroup_le_of_commute hq hR1 hG hN hK hK' hne hV hVK' hD hDQ hDV hC hCQ hCV hDC hgD hgC)

theorem k2_wGroup_eq_of_chain (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') {Y : Subgroup G}
    (hYQ : Y ≤ coreActionKernel K') (hYV : Y ≤ centralizer (V : Set G))
    (hgood : ∀ t ∈ Y, t * t = 1 → K2GoodInv K V t) {E F : Subgroup G}
    (h : Relation.ReflTransGen (CommFourIn Y) E F) : wGroup F V = wGroup E V := by
  induction h with
  | refl => rfl
  | @tail C D _ hCD ih =>
    rw [← ih]
    obtain ⟨hC, hD, hCY, hDY, hCDc⟩ := hCD
    have hgC : ∀ t ∈ C, t ≠ 1 → K2GoodInv K V t := fun t ht _ =>
      hgood t (hCY ht) (by rw [← sq]; exact sq_eq_one_of_isKleinFour hC ht)
    have hgD : ∀ t ∈ D, t ≠ 1 → K2GoodInv K V t := fun t ht _ =>
      hgood t (hDY ht) (by rw [← sq]; exact sq_eq_one_of_isKleinFour hD ht)
    exact (k2_wGroup_eq_of_commute hq hR1 hG hN hK hK' hne hV hVK' hC (hCY.trans hYQ)
      (hCY.trans hYV) hD (hDY.trans hYQ) (hDY.trans hYV) hCDc hgC hgD).symm

private theorem k2_isKleinFour_map_inj {X X' : Type} [Group X] [Group X'] {f : X →* X'}
    (hf : Function.Injective f) {V : Subgroup X} (hV : IsKleinFour V) :
    IsKleinFour (V.map f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective hf, hV.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hV hv, map_one]

theorem k2_exists_chain_conj {Q U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUQ : U ≤ coreActionKernel Q) (hQ : ¬ IsTwoDisconnected ↥Q) {E F : Subgroup G}
    (hE : IsKleinFour E) (hEY : E ≤ Q ⊓ centralizer (U : Set G)) (hF : IsKleinFour F)
    (hFY : F ≤ Q ⊓ centralizer (U : Set G)) :
    ∃ (F₁ : Subgroup G) (c : G), IsKleinFour F₁ ∧ F₁ ≤ Q ⊓ centralizer (U : Set G) ∧
      c ∈ Q ⊓ centralizer (U : Set G) ∧ c ∈ oddCoreIn Q ∧
      Relation.ReflTransGen (CommFourIn (Q ⊓ centralizer (U : Set G))) E F₁ ∧
      F = F₁.map (MulAut.conj c).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := Q ⊓ centralizer (U : Set G) with hY
  set ψ := coverQuot Q U with hψ
  have hψs : Function.Surjective ψ := coverQuot_surjective (K := Q) (U := U) hU2 hUQ
  have hker : Odd (Nat.card ψ.ker) := coverQuot_ker_odd (K := Q) U
  have hQ' : ¬ IsTwoDisconnected (coreQuot Q) := by
    intro h
    refine hQ (isTwoDisconnected_of_quot (QuotientGroup.mk' (pPrimeCore 2 ↥Q))
      (QuotientGroup.mk'_surjective _) ?_ h)
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hEY' : IsKleinFour (E.subgroupOf Y) := isKleinFour_subgroupOf hE hEY
  have hFY' : IsKleinFour (F.subgroupOf Y) := isKleinFour_subgroupOf hF hFY
  have hchain : Relation.ReflTransGen (CommFourAdj (coreQuot Q)) ((E.subgroupOf Y).map ψ)
      ((F.subgroupOf Y).map ψ) := by
    by_contra hn
    exact hQ' ⟨_, _, isKleinFour_map_of_odd_ker ψ hker hEY', isKleinFour_map_of_odd_ker ψ hker hFY',
      hn⟩
  obtain ⟨F₁, hF₁, hF₁map, hEF₁⟩ := exists_lift_reflTransGen_commFourAdj ψ hψs hker hEY' hchain
  obtain ⟨c, hcker, hcF⟩ := exists_ker_conj_eq ψ hker hF₁ hFY' hF₁map
  refine ⟨F₁.map Y.subtype, (c : G), k2_isKleinFour_map_inj Y.subtype_injective hF₁,
    map_subtype_le _, c.2, ?_, ?_, ?_⟩
  · have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥Q) ⟨(c : G), c.2.1⟩ = 1 := hcker
    exact mk_eq_one_iff.mp h1
  · have h := reflTransGen_commFourIn_of_subtype hEF₁
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEY] at h
  · have hcomp : Y.subtype.comp (MulAut.conj c).toMonoidHom =
        (MulAut.conj (c : G)).toMonoidHom.comp Y.subtype := by
      ext x
      simp [MulAut.conj_apply]
    have h1 : (F₁.map (MulAut.conj c).toMonoidHom).map Y.subtype = F := by
      rw [hcF, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFY]
    rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

private theorem k2_mem_normalizer_qPrime {g : G} (hgN : g ∈ N)
    (hgK' : g ∈ normalizer (K' : Set G)) :
    g ∈ normalizer ((((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' : Subgroup G)) :
      Set G) := by
  refine mem_normalizer_inf ?_ (normalizer_le_normalizer_coreActionKernel K' hgK')
  have hN : N.map (MulAut.conj g).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hgN)
  have hM : (oddTwoCoreIn N ⊔ twoLayerIn N).map (MulAut.conj g).toMonoidHom =
      oddTwoCoreIn N ⊔ twoLayerIn N := by
    rw [Subgroup.map_sup, map_oddTwoCoreIn (MulAut.conj g) N, map_twoLayerIn (MulAut.conj g) N, hN]
  exact mem_normalizer_iff_map_conj_eq.mpr hM

private theorem k2_le_coreActionKernel_qPrime {V : Subgroup G} (hVN : V ≤ N) (hVK' : V ≤ K') :
    V ≤ coreActionKernel ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') := by
  set Q := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQ
  intro v hv
  have hvN : v ∈ normalizer (Q : Set G) :=
    k2_mem_normalizer_qPrime (hVN hv) (le_normalizer (hVK' hv))
  refine mem_coreActionKernel.mpr ⟨hvN, fun a ha => ?_⟩
  have haK' : a ∈ coreActionKernel K' := (mem_inf.mp ha).2
  have h1 : v⁻¹ * a⁻¹ * v * a ∈ oddCoreIn K' := (mem_coreActionKernel.mp haK').2 v (hVK' hv)
  have h2 : (v⁻¹ * a⁻¹ * v * a)⁻¹ ∈ oddCoreIn K' := inv_mem h1
  have h3 : (v⁻¹ * a⁻¹ * v * a)⁻¹ ∈ Q := by
    have hva : v⁻¹ * a * v⁻¹⁻¹ ∈ Q := (mem_normalizer_iff.mp (inv_mem hvN) a).mp ha
    have h := mul_mem (inv_mem ha) hva
    rwa [show a⁻¹ * (v⁻¹ * a * v⁻¹⁻¹) = (v⁻¹ * a⁻¹ * v * a)⁻¹ by group] at h
  have hQN : Q ≤ normalizer (oddCoreIn K' : Set G) := fun q hq =>
    mem_normalizer_oddCoreIn (mem_coreActionKernel.mp (mem_inf.mp hq).2).1
  have h4 : (v⁻¹ * a⁻¹ * v * a)⁻¹ ∈ oddCoreIn Q :=
    inf_le_oddCoreIn (coprime_card_oddCoreIn K') hQN ⟨h2, h3⟩
  have h5 : a⁻¹ * v⁻¹ * a * v ∈ oddCoreIn Q := by
    rwa [show (v⁻¹ * a⁻¹ * v * a)⁻¹ = a⁻¹ * v⁻¹ * a * v by group] at h4
  exact h5

theorem k2_wGroup_eq_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hBN : B ≤ N)
    (hE : IsKleinFour E) (hEB : E ≤ B) (hEK : E ≤ K)
    (hQ : ¬ IsTwoDisconnected ↥((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K'))
    (hgood : ∀ t ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓
        centralizer (V : Set G), t * t = 1 → K2GoodInv K V t)
    (hF : IsKleinFour F) (hFK : F ≤ K) (hFV : F ≤ centralizer (V : Set G)) :
    wGroup F V = wGroup E V := by
  set Q := (oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K' with hQdef
  have hKQ : K ≤ Q := le_inf ((le_twoLayerIn_of_isTwoComponentIn hK.1).trans le_sup_right)
    (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hVN : V ≤ N := hVK'.trans hK'.1.1
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel Q := k2_le_coreActionKernel_qPrime hVN hVK'
  have hEY : E ≤ Q ⊓ centralizer (V : Set G) := le_inf (hEK.trans hKQ) (hEB.trans hBV)
  have hFY : F ≤ Q ⊓ centralizer (V : Set G) := le_inf (hFK.trans hKQ) hFV
  obtain ⟨F₁, c, hF₁, hF₁Y, hcY, hcO, hchain, hFeq⟩ :=
    k2_exists_chain_conj hV2 hVQ hQ hE hEY hF hFY
  have hYQ : Q ⊓ centralizer (V : Set G) ≤ coreActionKernel K' := inf_le_left.trans inf_le_right
  have hYV : Q ⊓ centralizer (V : Set G) ≤ centralizer (V : Set G) := inf_le_right
  have hW1 : wGroup F₁ V = wGroup E V :=
    k2_wGroup_eq_of_chain hq hR1 hG hN hK hK' hne hV hVK' hYQ hYV hgood hchain
  have hOQ : oddCoreIn Q ≤ normalizer (wGroup B V : Set G) := by
    refine le_normalizer_wGroup_of_odd_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB
      hEK hB8 (coprime_card_oddCoreIn Q) ?_ ?_
    · exact fun b hb => mem_normalizer_oddCoreIn
        (k2_mem_normalizer_qPrime (hBN hb) (mem_coreActionKernel.mp (hBQ hb)).1)
    · exact fun v hv => mem_normalizer_oddCoreIn
        (k2_mem_normalizer_qPrime (hVN hv) (le_normalizer (hVK' hv)))
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hcN : c ∈ normalizer (wGroup E V : Set G) := by
    rw [hWE]
    exact hOQ hcO
  have hVc : V.map (MulAut.conj c).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer (V : Set G) hcY.2)
  calc wGroup F V
      = wGroup (F₁.map (MulAut.conj c).toMonoidHom) (V.map (MulAut.conj c).toMonoidHom) := by
        rw [← hFeq, hVc]
    _ = (wGroup F₁ V).map (MulAut.conj c).toMonoidHom := (map_wGroup (MulAut.conj c) F₁ V).symm
    _ = (wGroup E V).map (MulAut.conj c).toMonoidHom := by rw [hW1]
    _ = wGroup E V := mem_normalizer_iff_map_conj_eq.mp hcN

theorem k2_le_normalizer_wGroup_of_wGroup_eq (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N)
    (hkey : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      wGroup F V = wGroup E V) :
    K ≤ normalizer (wGroup B V : Set G) := by
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  rw [← inf_centralizer_sup_oddCoreIn_eq hV2 hVQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer (V : Set G) hg.2)
    set Eg := E.map (MulAut.conj g).toMonoidHom with hEg
    have hEg4 : IsKleinFour Eg := by
      refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
      · rw [hEg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE.card_four]
      · obtain ⟨v, hv, rfl⟩ := hx
        rw [← map_pow, sq_eq_one_of_isKleinFour hE hv, map_one]
    have hEX : E ≤ K ⊓ centralizer (V : Set G) := le_inf hEK (hEB.trans hBV)
    have hEgX : Eg ≤ K ⊓ centralizer (V : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem hg (hEX he)) (inv_mem hg)
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hVg]
      exact hkey Eg hEg4 hEgX
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

private def k2StabOdd (K : Subgroup G) (S : Set G) : Subgroup G where
  carrier := {d | d ∈ normalizer (K : Set G) ∧ ∀ a ∈ S, a⁻¹ * d⁻¹ * a * d ∈ oddCoreIn K}
  one_mem' := ⟨one_mem _, fun a _ => by simp⟩
  mul_mem' := by
    rintro d₁ d₂ ⟨hd₁N, hd₁⟩ ⟨hd₂N, hd₂⟩
    refine ⟨mul_mem hd₁N hd₂N, fun a ha => ?_⟩
    have hO := mem_normalizer_oddCoreIn (inv_mem hd₂N)
    have h1 := (mem_normalizer_iff.mp hO _).mp (hd₁ a ha)
    rw [inv_inv] at h1
    rw [show a⁻¹ * (d₁ * d₂)⁻¹ * a * (d₁ * d₂) =
      (a⁻¹ * d₂⁻¹ * a * d₂) * (d₂⁻¹ * (a⁻¹ * d₁⁻¹ * a * d₁) * d₂) by group]
    exact mul_mem (hd₂ a ha) h1
  inv_mem' := by
    rintro d ⟨hdN, hd⟩
    refine ⟨inv_mem hdN, fun a ha => ?_⟩
    have h1 := inv_mem ((mem_normalizer_iff.mp (mem_normalizer_oddCoreIn hdN) _).mp (hd a ha))
    rwa [show (d * (a⁻¹ * d⁻¹ * a * d) * d⁻¹)⁻¹ = a⁻¹ * d⁻¹⁻¹ * a * d⁻¹ by group] at h1

private theorem mem_k2StabOdd {K : Subgroup G} {S : Set G} {d : G} :
    d ∈ k2StabOdd K S ↔
      d ∈ normalizer (K : Set G) ∧ ∀ a ∈ S, a⁻¹ * d⁻¹ * a * d ∈ oddCoreIn K := Iff.rfl

private theorem k2_isPGroup_zpowers {t : G} (ht : t * t = 1) : IsPGroup 2 (zpowers t) := by
  have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem k2_exists_isKleinFour_le_inf_centralizer {N K : Subgroup G} (hK : IsTwoComponentIn K N)
    (hF : CentralSquareFour (coreQuot K)) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUK : U ≤ coreActionKernel K) {t : G} (htM : t ∈ oddTwoCoreIn N ⊔ twoLayerIn N)
    (ht2 : t * t = 1) (htU : U ≤ centralizer ({t} : Set G)) :
    ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ K ∧ A ≤ centralizer ({t} : Set G) ∧
      A ≤ centralizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hc⟩ := exists_inv_mul_mem_coreActionKernel hK htM
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  have htk : t = k * (k⁻¹ * t) := by group
  have htN : t ∈ normalizer (K : Set G) := by
    rw [htk]
    exact mul_mem (le_normalizer hk) (mem_coreActionKernel.mp hc).1
  have hkk : k * k ∈ coreActionKernel K := by
    have hn := (normalizer_le_normalizer_coreActionKernel (J := K)) (le_normalizer (inv_mem hk))
    have h1 : k⁻¹ * (k⁻¹ * t) * k ∈ coreActionKernel K := by
      have h := (mem_normalizer_iff.mp hn _).mp hc
      rwa [inv_inv] at h
    have e : (k⁻¹ * (k⁻¹ * t) * k) * (k⁻¹ * t) = (k * k)⁻¹ := by
      calc (k⁻¹ * (k⁻¹ * t) * k) * (k⁻¹ * t) = k⁻¹ * k⁻¹ * (t * t) := by
            simp only [mul_assoc, mul_inv_cancel_left]
        _ = (k * k)⁻¹ := by rw [ht2, mul_one, mul_inv_rev]
    have h2 : (k * k)⁻¹ ∈ coreActionKernel K := by
      rw [← e]
      exact mul_mem h1 hc
    simpa using inv_mem h2
  have hsq : π ⟨k, hk⟩ * π ⟨k, hk⟩ ∈ center (coreQuot K) := by
    have h := mk_mem_center_of_mem_coreActionKernel (u := ⟨k * k, mul_mem hk hk⟩) hkk
    rw [← map_mul]
    exact h
  obtain ⟨Ab, hAb, hAbc⟩ := hF (π ⟨k, hk⟩) hsq
  set S : Set G := {x | ∃ a : ↥K, π a ∈ Ab ∧ (a : G) = x} with hS
  have htS : t ∈ k2StabOdd K S := by
    refine mem_k2StabOdd.mpr ⟨htN, ?_⟩
    rintro _ ⟨a, haAb, rfl⟩
    have hcomm : π a * π ⟨k, hk⟩ = π ⟨k, hk⟩ * π a :=
      mem_centralizer_singleton_iff.mp (hAbc haAb)
    have h1 : (a : G)⁻¹ * k⁻¹ * a * k ∈ oddCoreIn K := (mk_mul_comm_iff a ⟨k, hk⟩).mp hcomm
    have e := comm_mul_mem_oddCoreIn_iff (a := (a : G)) hk hc a.2
    rw [← htk] at e
    exact e.mpr h1
  have hUS : U ≤ k2StabOdd K S := by
    intro u hu
    refine mem_k2StabOdd.mpr ⟨(mem_coreActionKernel.mp (hUK hu)).1, ?_⟩
    rintro _ ⟨a, -, rfl⟩
    exact (mem_coreActionKernel.mp (hUK hu)).2 a a.2
  set D : Subgroup G := zpowers t ⊔ U with hD
  have hDS : D ≤ k2StabOdd K S := sup_le (zpowers_le.mpr htS) hUS
  have htcU : t ∈ centralizer (U : Set G) :=
    mem_centralizer_iff.mpr fun u hu => mem_centralizer_singleton_iff.mp (htU hu)
  have hD2 : IsPGroup 2 D :=
    isPGroup_sup_of_le_centralizer (k2_isPGroup_zpowers ht2) hU2 (zpowers_le.mpr htcU)
  have hDK : D ≤ normalizer (K : Set G) := fun d hd => (mem_k2StabOdd.mp (hDS hd)).1
  have hcomm : ∀ a : ↥K, π a ∈ Ab → ∀ d ∈ D, (a : G)⁻¹ * d⁻¹ * a * d ∈ oddCoreIn K :=
    fun a ha d hd => (mem_k2StabOdd.mp (hDS hd)).2 a ⟨a, ha, rfl⟩
  obtain ⟨A, hA, hAle⟩ := exists_isKleinFour_le_inf_centralizer hD2 hDK hAb hcomm
  refine ⟨A, hA, hAle.trans inf_le_left, fun x hx => ?_, fun x hx => ?_⟩
  · exact centralizer_le (Set.singleton_subset_iff.mpr
      (show t ∈ (D : Set G) from mem_sup_left (mem_zpowers t))) (hAle hx).2
  · exact centralizer_le (by exact_mod_cast (le_sup_right : U ≤ D)) (hAle hx).2

theorem k2_centralSquareFour_coreQuot (hF1 : QuasisimpleCentralSquareFour)
    (hF1I : QuasisimpleCentralSquareFourI) (hF1R : QuasisimpleRankTwoCentralSquareFour)
    (hG : SimpleAmbient G) (hK : K ∈ kStarComponents N)
    (hcase : (IsTwoDisconnected (coreQuot K) ∧ IsSolomonI (coreQuot K)) ∨
      CFSG.Open.pRank 2 K ≤ 2) : CentralSquareFour (coreQuot K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : IsQuasisimple (coreQuot K) := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hO : pPrimeCore 2 (coreQuot K) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  have hcat := catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hK.1 hK.2
  have hr2 : 2 ≤ CFSG.Open.pRank 2 K := two_le_pRank_of_mem_solomonKStar hK.2
  have hrk : CFSG.pRank 2 (coreQuot K) = CFSG.Open.pRank 2 K := by
    rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
  intro x hx
  by_cases hZ4 : ∃ Z : Subgroup (coreQuot K), Z ≤ center (coreQuot K) ∧ IsKleinFour Z
  · obtain ⟨Z, hZc, hZ⟩ := hZ4
    exact ⟨Z, hZ, fun z hz => mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hZc hz) x).symm⟩
  have hZ4' : ∀ Z : Subgroup (coreQuot K), Z ≤ center (coreQuot K) → ¬ IsKleinFour Z :=
    fun Z hZc hZ => hZ4 ⟨Z, hZc, hZ⟩
  by_cases hZ1 : center (coreQuot K) = ⊥
  · have hx1 : x * x = 1 := by
      rw [hZ1, Subgroup.mem_bot] at hx
      exact hx
    have hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (coreQuot K)) := by
      rw [← SectionRank.pRank_eq_open_pRank_top, hrk]
      exact hr2
    obtain ⟨A, hA, hxA, -⟩ := exists_isKleinFour_mem_mem hr hx1 (mul_one (1 : coreQuot K))
      (by rw [mul_one, one_mul])
    exact ⟨A, hA, fun a ha => mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hA a ha x hxA)⟩
  by_cases h2 : CFSG.Open.pRank 2 K ≤ 2
  · exact hF1R (coreQuot K) hq hO hcat (by omega) hZ1 hZ4' x hx
  · have h3 : 3 ≤ CFSG.pRank 2 (coreQuot K) := by omega
    by_cases hI : IsSolomonI (coreQuot K)
    · have hd : IsTwoDisconnected (coreQuot K) := by
        rcases hcase with ⟨hd, -⟩ | h
        · exact hd
        · exact absurd h h2
      exact hF1I (coreQuot K) hq hO hcat h3 hZ1 hZ4' hI hd x hx
    · exact hF1 (coreQuot K) hq hO hcat h3 hZ4' hI x hx

section Sp4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsSp4
open SymplecticHigher SymplecticFlag
open CFSG.Open (StatedSp)

variable {F : Type} [Field F]

private theorem k2_J₁_mul_J₁ : (J₁ : Matrix (Fin 2) (Fin 2) F) * J₁ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁]

private theorem k2_kron_neg_one_neg_one : kron (-1 : Matrix (Fin 2) (Fin 2) F) (-1) = 1 := by
  rw [kron, ← fromBlocks_one]
  simp

private theorem k2_kron_J₁_J₁_symplectic :
    (kron (J₁ : Matrix (Fin 2) (Fin 2) F) J₁)ᵀ * formJ 2 F * kron J₁ J₁ = formJ 2 F := by
  refine (kron_symplectic_iff _ _).mpr ?_
  have hdet : (J₁ : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [J₁, det_fin_two]
  rw [hdet, one_smul, J₁_transpose_mul_self]

private noncomputable def k2U0 (F : Type) [Field F] : StatedSp 2 F :=
  toSp (kron J₁ J₁) k2_kron_J₁_J₁_symplectic

private theorem k2U0_coe : (((k2U0 F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = kron J₁ J₁ := rfl

private theorem k2U0_mul_self : k2U0 F * k2U0 F = 1 := by
  apply sp_ext
  simp [k2U0_coe, kron_mul, k2_J₁_mul_J₁, k2_kron_neg_one_neg_one]

private theorem k2U0_comm_T2 : k2U0 F * T2 F = T2 F * k2U0 F := by
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, k2U0_coe, coe_T2, kron_mul, Matrix.mul_one,
    Matrix.one_mul]

private theorem k2_kron_J₁_J₁_entry :
    (kron (J₁ : Matrix (Fin 2) (Fin 2) F) J₁) (Sum.inl 0) (Sum.inr 1) = 1 := by
  simp [kron, J₁]

private theorem k2_kron_J₁_J₁_ne_one :
    (kron (J₁ : Matrix (Fin 2) (Fin 2) F) J₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ 1 := by
  intro h
  have h' := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 1)
  rw [k2_kron_J₁_J₁_entry] at h'
  simp at h'

private theorem k2_kron_J₁_J₁_ne_neg_one :
    (kron (J₁ : Matrix (Fin 2) (Fin 2) F) J₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ -1 := by
  intro h
  have h' := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 1)
  rw [k2_kron_J₁_J₁_entry] at h'
  simp at h'

private theorem k2_exists_isKleinFour_of_sq_neg_one [Finite F] (h2 : (2 : F) ≠ 0)
    (y : StatedSp 2 F)
    (hy : ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((y : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1) :
    ∃ A : Subgroup (StatedSp 2 F), IsKleinFour A ∧ A ≤ centralizer ({y} : Set (StatedSp 2 F)) := by
  obtain ⟨g, hg⟩ := exists_conj_T2 h2 y hy
  have hyg : y = g * T2 F * g⁻¹ := by
    rw [← hg]
    group
  have hMz : (((y * y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
    rw [Subgroup.coe_mul, Units.val_mul]
    exact hy
  have huy : g * k2U0 F * g⁻¹ * y = y * (g * k2U0 F * g⁻¹) := by
    conv_lhs => rw [hyg]
    conv_rhs => rw [hyg]
    calc g * k2U0 F * g⁻¹ * (g * T2 F * g⁻¹) = g * (k2U0 F * T2 F) * g⁻¹ := by group
      _ = g * (T2 F * k2U0 F) * g⁻¹ := by rw [k2U0_comm_T2]
      _ = g * T2 F * g⁻¹ * (g * k2U0 F * g⁻¹) := by group
  have hzc : Commute (g * k2U0 F * g⁻¹) (y * y) := (Commute.mul_right huy huy)
  have hzz : (y * y) * (y * y) = 1 := by
    apply sp_ext
    simp only [Subgroup.coe_mul, Units.val_mul] at hMz ⊢
    simp [hMz]
  have huu : (g * k2U0 F * g⁻¹) * (g * k2U0 F * g⁻¹) = 1 := by
    calc (g * k2U0 F * g⁻¹) * (g * k2U0 F * g⁻¹) = g * (k2U0 F * k2U0 F) * g⁻¹ := by group
      _ = 1 := by rw [k2U0_mul_self]; group
  have hu1 : g * k2U0 F * g⁻¹ ≠ 1 := by
    intro h
    have h0 : k2U0 F = 1 := by
      calc k2U0 F = g⁻¹ * (g * k2U0 F * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h1 := congrArg (fun t : StatedSp 2 F => ((t : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h0
    simp only [k2U0_coe, Subgroup.coe_one, Units.val_one] at h1
    exact k2_kron_J₁_J₁_ne_one h1
  have hz1 : y * y ≠ 1 := by
    intro h
    have h1 := congrArg (fun t : StatedSp 2 F => ((t : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
    simp only [hMz, Subgroup.coe_one, Units.val_one] at h1
    have h3 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
    rw [Matrix.neg_apply, Matrix.one_apply_eq] at h3
    exact h2 (by linear_combination (-1 : F) * h3)
  have huz : g * k2U0 F * g⁻¹ ≠ y * y := by
    intro h
    have h0 : k2U0 F = g⁻¹ * (y * y) * g := by
      calc k2U0 F = g⁻¹ * (g * k2U0 F * g⁻¹) * g := by group
        _ = g⁻¹ * (y * y) * g := by rw [h]
    have h1 := congrArg (fun t : StatedSp 2 F => ((t : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h0
    have hgg := congrArg (fun t : StatedSp 2 F => ((t : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (inv_mul_cancel g)
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at h1 hgg hMz
    rw [k2U0_coe, hMz, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hgg] at h1
    exact k2_kron_J₁_J₁_ne_neg_one h1
  have hu2 : orderOf (g * k2U0 F * g⁻¹) = 2 := orderOf_eq_prime (by rw [sq]; exact huu) hu1
  have hz2 : orderOf (y * y) = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  refine ⟨closure {g * k2U0 F * g⁻¹, y * y},
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hu2 hz2 hzc.eq huz, ?_⟩
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl)
  · exact mem_centralizer_singleton_iff.mpr huy
  · exact mem_centralizer_singleton_iff.mpr (mul_assoc y y y)

theorem k2_quasisimpleRankTwoCentralSquareFour_of_symplectic
    (hS : R12.QuasisimpleRankTwoSymplecticInput) (hGA : TBLit.GriessMultipliersAllModels) :
    QuasisimpleRankTwoCentralSquareFour := by
  intro Q _ _ hq hO hcat hr hZ _ x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ, hτ2⟩ := exists_orderOf_eq_two_mem_center hO hZ
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_symplectic hS hGA hq hO hcat hr hτ hτ2
  by_cases hx1 : x * x = 1
  · have hr2 : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := by
      rw [← SectionRank.pRank_eq_open_pRank_top, hr]
    obtain ⟨A, hA, hxA, -⟩ := exists_isKleinFour_mem_mem hr2 hx1 (mul_one (1 : Q))
      (by rw [mul_one, one_mul])
    exact ⟨A, hA, fun a ha => mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hA a ha x hxA)⟩
  · have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hxc : e (x * x) ∈ center (StatedSp 2 F) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨x * x, hx, rfl⟩
    have hz : e (x * x) ∈ spScalars 2 F := by
      have h := hxc
      rw [CFSG.LieType.Universal.Symplectic.center_eq] at h
      exact h
    have hy : ((e x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((e x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -1 := by
      rcases (mem_spScalars_iff _).mp hz with h1 | h1
      · exfalso
        apply hx1
        apply e.injective
        rw [map_one]
        exact sp_ext (by rw [h1]; simp)
      · rw [map_mul] at h1
        simpa [Subgroup.coe_mul, Units.val_mul] using h1
    obtain ⟨A, hA, hAc⟩ := k2_exists_isKleinFour_of_sq_neg_one h2 (e x) hy
    refine ⟨A.map e.symm.toMonoidHom, k2_isKleinFour_map_inj e.symm.injective hA, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (hAc ha)
    refine mem_centralizer_singleton_iff.mpr ?_
    apply e.injective
    simp [map_mul, h]

end Sp4

theorem k2_lemma39TwoDiscK2At_solRestrictedHub_of_inputs (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF1 : QuasisimpleCentralSquareFour)
    (hF1I : QuasisimpleCentralSquareFourI) (hF1R : QuasisimpleRankTwoCentralSquareFour) :
    Lemma39TwoDiscK2At solRestrictedHub := by
  intro G _ _ hG N hN _ K K' V B hP _ _ _ _ _ _ _ hQ _ _ _ hcase _ _
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hCS : CentralSquareFour (coreQuot K) :=
    k2_centralSquareFour_coreQuot hF1 hF1I hF1R hG hK hcase
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  have hgood : ∀ t ∈ ((oddTwoCoreIn N ⊔ twoLayerIn N) ⊓ coreActionKernel K') ⊓
      centralizer (V : Set G), t * t = 1 → K2GoodInv K V t := by
    intro t ht ht2
    obtain ⟨A, hA, hAK, hAt, hAV⟩ := k2_exists_isKleinFour_le_inf_centralizer hK.1 hCS hV2 hVQ
      (mem_inf.mp (mem_inf.mp ht).1).1 ht2
      (fun w hw => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp ht.2) w hw))
    exact ⟨A, hA, hAK, hAt, hAV⟩
  refine k2_le_normalizer_wGroup_of_wGroup_eq hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
    hEK hBN fun F hF hFY => ?_
  exact k2_wGroup_eq_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hBN hE hEB hEK hQ hgood
    hF (hFY.trans inf_le_left) (hFY.trans inf_le_right)

section Certified

theorem lemma39TwoDiscK2At_solRestrictedHub_of_leaves (hF1 : QuasisimpleCentralSquareFour)
    (hF1I : QuasisimpleCentralSquareFourI) : Lemma39TwoDiscK2At solRestrictedHub := by
  have hq : QuasisimpleTwoPartInput :=
    quasisimpleTwoPartInput_of_centralFour Hq4.quasisimpleCentralFourInput_holds
  have h𝒜 : ∀ (G : Type) [Group G] [Finite G], Sol76T13.simpleAmbient G → KStarKProper G :=
    fun _ _ _ hG => kStarKProper_of_simpleAmbient hG
  have hR1 : Lemma32ConditionTwoInputFor Sol76T13.simpleAmbient :=
    lemma32ConditionTwoInputFor_of_rankTwo
      (lemma32ConditionTwoRankTwoInputFor_of_kernel hq h𝒜
        (lemma32RankTwoKernelInput_of_central
          (R12.quasisimpleRankTwoCentralInput_of_symplectic
            (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz R12.Pcls.sporadicCoverRankInput_Suz))))
  exact k2_lemma39TwoDiscK2At_solRestrictedHub_of_inputs hq hR1 hF1 hF1I
    (k2_quasisimpleRankTwoCentralSquareFour_of_symplectic
      (R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz R12.Pcls.sporadicCoverRankInput_Suz) TBLit.griessMultipliersAllModels_holds)

end Certified

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
