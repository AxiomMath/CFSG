module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528UMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem528

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four
open CFSG.Quasithin.Vol2.Ch11.SecA CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Stmt5_2_8_U4_SL3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ : Subgroup G) (n m : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → n = 2 * m → 2 < n →
    (IsAmalgamOfGroup (sec52Alpha M L H B D L₂) (IsLieOverTwo .PSU 4 m) ∨
      IsU4ExtTwo m (sec52Alpha M L H B D L₂)) →
    IsOmega4MinusBlock L m → IsL2Quot m (oTwoQuot ↥(oTwoUpper H)) →
    IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (oTwoUpper H)) →
    ∀ Kh : Subgroup G, oTwoUpper H < Kh → quasithinIsMaximalLocal T Kh →
      ¬ pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 Kh →
      (IsPSL 3 2 m ↥(modO2Image (Kh ⊔ T) Kh) ∨ IsSL3 (2 ^ m) ↥(modO2Image (Kh ⊔ T) Kh)) →
      (∃ P : Subgroup (↥(Kh ⊔ T) ⧸ CFSG.pCore 2 ↥(Kh ⊔ T)),
        IsMaxParabolic2 (modO2Image (Kh ⊔ T) Kh) P ∧
          modO2Image (Kh ⊔ T) (oTwoUpper H) = perfectCore P) → False

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt5_2_8_U4_of_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h526 : Stmt5_2_6_F4)
    (h312 : A312ForSQTK) (hExc : FactExcParabolicO2Ne) (hExcSq : FactExcParabolicO2NeSq)
    (hAut : AutA7Fact) (hSL3 : Stmt5_2_8_U4_SL3_F4) : Stmt5_2_8_U4_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hc Kh hlt hKh
  obtain ⟨m, hnm, h2n, hαU, hLb, hKq, hsp⟩ := hc
  have h := hyp.toHyp5_0_1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨-, hL₂K, hcore, -, -, -, hKT, halt⟩ := h526 G T M L V H B D L₂ n hyp
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  have hKloc : quasithinIsLocal T K := hyp.isLocal_oTwoUpper hL₂K
  have hTN : T ≤ Subgroup.normalizer (K : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have e : Emb528 T K Kh := ⟨h.qtke, h.simple, h.nonabelian, h.sylow, hKloc, hKh.1, hlt.le, hTN⟩
  have hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh :=
    e.charTwo_Kh h37
  have hQK : Q ≤ K := pCoreOf_le 2 K
  have hST : sec52S M H ≤ T := h.pCoreOf_inf_le hyp.hStar.1.1
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 K

  obtain ⟨eK⟩ := exists_sl2_of_isL2Quot hKq
  have hFc : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hsp' : IsSpecialPow 2 (2 ^ m) 2 ↥(pCoreOf 2 (perfectCore (sec52G2 M H D L₂))) := by
    rw [← hcore]
    exact hsp
  obtain ⟨hQQ, hZq⟩ := commutator_eq_centerOf_of_isSpecialPow (by norm_num)
    (Nat.le_self_pow (by omega) 2) hsp
  have hQcard : Nat.card Q = (2 ^ m) ^ 5 := hsp.2.1

  have hG₂Q : sec52G2 M H D L₂ ≤ Subgroup.normalizer (Q : Set G) := by
    have h1 : sec52G2 M H D L₂ ≤ Subgroup.normalizer (K : Set G) := by
      rw [hcore]
      exact Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _)
    exact h1.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTN.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hKSQ : K ⊔ sec52S M H ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 K) (hST.trans hTQ)

  have hRKS : pCoreOf 2 Kh ≤ pCoreOf 2 (K ⊔ sec52S M H) := by
    have h1 := e.pCoreOf_le_pCoreOf_KT h37
    rwa [hKT] at h1

  have hcardK : Nat.card K = 2 ^ m * oSL2 m * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    congr 1
    · rw [show Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card (ModO2 K) from rfl,
        Nat.card_congr eK.toEquiv, card_SL_two hFc]
    · try with_reducible rfl
      exact (Subgroup.card_map_of_injective K.subtype_injective).symm

  have htprops : ∀ t : G, orderOf t = 2 →
      pCoreOf 2 (K ⊔ sec52S M H) = Q ⊔ Subgroup.zpowers t →
        t ∈ K ⊔ sec52S M H ∧ t ∈ Subgroup.normalizer (Q : Set G) ∧ t ^ 2 = 1 ∧
          Q.relIndex (Q ⊔ Subgroup.zpowers t) ≤ 2 := by
    intro t ht2 hKSeq
    have htO : t ∈ pCoreOf 2 (K ⊔ sec52S M H) := by
      rw [hKSeq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htKS : t ∈ K ⊔ sec52S M H := pCoreOf_le 2 _ htO
    have htN : t ∈ Subgroup.normalizer (Q : Set G) := hKSQ htKS
    refine ⟨htKS, htN, by rw [← ht2]; exact pow_orderOf_eq_one t, ?_⟩
    have h1 := Subgroup.relIndex_mul_card Q (Q ⊔ Subgroup.zpowers t)
    rw [inf_eq_left.mpr le_sup_left] at h1
    have h2 : Nat.card ↥(Q ⊔ Subgroup.zpowers t) ≤ 2 * Nat.card Q := by
      rw [sup_comm]
      refine (card_sup_le_mul_of_normalizes ((Subgroup.zpowers_le).mpr htN)).trans ?_
      rw [Nat.card_zpowers, ht2]
    have hpos : 0 < Nat.card Q := Nat.card_pos
    by_contra hgt
    have : 3 * Nat.card Q ≤ Q.relIndex (Q ⊔ Subgroup.zpowers t) * Nat.card Q :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  by_contra hKhQ
  by_cases hQR : Q ≤ pCoreOf 2 Kh
  ·
    obtain ⟨hm2', hL⟩ := a312_list_of_le h37 h312 hExc e hlt hKh hQR hm2 hFc eK
    rcases halt with ⟨-, -, -, hKSeq⟩ | ⟨m', hnm', -, hext, t, ht2, htQ, hKSeq, -⟩
    · apply hKhQ
      rw [← le_antisymm (hRKS.trans hKSeq.le) hQR]
      exact le_normalizer_pCoreOf 2 Kh
    rw [show m' = m by omega] at hext
    subst hm2'
    obtain ⟨htKS, htN, ht2', -⟩ := htprops t ht2 hKSeq
    have htR : t ∈ pCoreOf 2 Kh := by
      by_contra htR
      apply hKhQ
      have hRQ : pCoreOf 2 Kh ≤ Q := by
        intro r hr
        rcases mem_or_exists_of_mem_sup_zpowers htN ht2' (hKSeq ▸ hRKS hr) with hrQ |
            ⟨q, hq, rfl⟩
        · exact hrQ
        · exfalso
          apply htR
          have := mul_mem hr (inv_mem (hQR hq))
          rwa [mul_inv_cancel_right] at this
      rw [← le_antisymm hRQ hQR]
      exact le_normalizer_pCoreOf 2 Kh
    have hReq : pCoreOf 2 Kh = Q ⊔ Subgroup.zpowers t :=
      le_antisymm (hKSeq ▸ hRKS) (sup_le hQR ((Subgroup.zpowers_le).mpr htR))

    have htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ Q := by
      intro k hk
      have hKn : K ≤ Subgroup.normalizer
          ((K ⊓ pCoreOf 2 (K ⊔ sec52S M H) : Subgroup G) : Set G) :=
        (le_inf Subgroup.le_normalizer (le_sup_left.trans (le_normalizer_pCoreOf 2 _))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hle : K ⊓ pCoreOf 2 (K ⊔ sec52S M H) ≤ Q :=
        le_pCoreOf_of_le_normalizer 2 inf_le_left hKn
          ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
      have htKn : t ∈ Subgroup.normalizer (K : Set G) :=
        (sup_le Subgroup.le_normalizer (hST.trans hTN)) htKS
      have hkO : k ∈ Subgroup.normalizer (pCoreOf 2 (K ⊔ sec52S M H) : Set G) :=
        le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hk)
      have htO : t ∈ pCoreOf 2 (K ⊔ sec52S M H) := by
        rw [hKSeq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      refine hle (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mul_mem ((Subgroup.mem_normalizer_iff.mp htKn k).mp hk) (inv_mem hk)
      · rw [show t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) by group]
        exact mul_mem htO ((Subgroup.mem_normalizer_iff.mp hkO t⁻¹).mp (inv_mem htO))
    have htG₂ : t ∈ sec52G2 M H D L₂ := by
      have h1 : K ⊔ sec52S M H ≤ sec52G2 M H D L₂ :=
        sup_le (hL₂K ▸ le_sup_right) (le_sup_right.trans le_sup_left)
      exact h1 htKS
    have htZ : t ∈ Subgroup.centralizer (centerOf Q : Set G) := by
      have h1 := ext_center_of_amalgam U4Par.factU4ExtCenter_holds (m := 2) le_rfl hext hsp' t
        htG₂ ht2' (by rw [← hcore]; exact htQ) (by rw [← hcore]; exact htK)
      rwa [← hcore] at h1

    have hKhR : Kh ≤ Subgroup.normalizer ((Q ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [← hReq]
      exact le_normalizer_pCoreOf 2 Kh
    have hKhZ : Kh ≤ Subgroup.normalizer (centerOf Q : Set G) := by
      by_cases hnt : ∀ y ∈ Q, t * y * t⁻¹ * y⁻¹ ∈ centerOf Q
      · rw [← commutator_sup_zpowers_eq htN ht2' hQQ hnt]
        exact le_normalizer_commutator_of hKhR hKhR
      · rw [← centerOf_sup_zpowers_eq htN ht2' hQQ htZ hnt]
        exact hKhR.trans (normalizer_le_normalizer_centerOf_self _)

    obtain ⟨x, hxG₂, hx3, hxk⟩ : ∃ x ∈ sec52G2 M H D L₂, orderOf x = 3 ∧
        ∀ k ∈ perfectCore (sec52G2 M H D L₂),
          x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (sec52G2 M H D L₂)) := by
      obtain ⟨Y₀, _, Y, _, ι, hY₀, hι, hidx, T', M₁, M₂, hpair, ⟨φ⟩⟩ := hext
      exact x3_transport φ.φ2 (U4Par.factX3ParabolicU4_holds Y T' M₁ M₂
        (Or.inr ⟨Y₀, inferInstance, ι, hY₀, hι, hidx⟩) hpair (isSpecialPow_model φ.φ2 hsp'))
    rw [← hcore] at hxk
    have hR11 : Nat.card (pCoreOf 2 Kh) ≤ 2 ^ 11 := by
      rw [hReq, sup_comm]
      refine (card_sup_le_mul_of_normalizes ((Subgroup.zpowers_le).mpr htN)).trans ?_
      rw [Nat.card_zpowers, ht2, hQcard]
      norm_num
    have hZ4 : Nat.card (centerOf Q) = 4 := hZq.trans (by norm_num)
    have hZ1 : centerOf Q ≠ ⊥ := fun hZ => by
      rw [hZ, Subgroup.card_bot] at hZ4
      omega
    have hcardK60 : Nat.card K = 60 * Nat.card Q := by
      rw [hcardK]
      rfl
    exact false_of_q4_of h37 h38 h39 hAut e hKh hQR hR11 hQQ hZ4 hcardK60 hx3 hxk (centerOf Q)
      (hQ2.to_le inf_le_left) hZ1 hKhZ (hTQ.trans (normalizer_le_normalizer_centerOf_self Q))
      (normalizer_le_normalizer_centerOf_self Q (hG₂Q hxG₂)) hL
  ·
    set H' := Kh ⊔ T with hH'
    have hKH' : K ≤ H' := hlt.le.trans le_sup_left
    set R₀ := Q ⊓ pCoreOf 2 Kh with hR₀
    have hKinf : K ⊓ pCoreOf 2 H' = R₀ := by
      apply le_antisymm
      · refine le_inf e.inf_le_blockQ ?_
        rw [← e.inf_pCoreOf_eq h37]
        exact inf_le_inf_right _ hlt.le
      · exact le_inf (inf_le_left.trans hQK) (inf_le_right.trans (e.pCoreOf_le_sup h37))

    obtain ⟨hcent, hQKc, hmod⟩ := module_of_amalgam U4Par.factU4ParabolicModule_holds hm2 hαU
      hsp'
    rw [← hcore] at hcent hQKc hmod

    have hWR₀ : ⁅pCoreOf 2 H', K⁆ ≤ R₀ := e.commutator_le_inf.trans hKinf.le
    have hR₀Z : ¬ R₀ ≤ centerOf Q := by
      intro hle
      apply e.commutator_ne_bot
      rw [← e.commutator_commutator, eq_bot_iff, Subgroup.commutator_le]
      intro w hw k hk
      have hwZ : w ∈ centerOf Q := hle (hWR₀ hw)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.mp (hcent hk) w hwZ
    have hKR₀ : K ≤ Subgroup.normalizer (R₀ : Set G) :=
      (le_inf (le_normalizer_pCoreOf 2 K) (hlt.le.trans (le_normalizer_pCoreOf 2 Kh))).trans
        Subgroup.inf_normalizer_le_normalizer_inf

    have hR₀Q : R₀ ⊔ centerOf Q ≠ Q := by
      intro heq
      apply hQR
      have hZR₀ : centerOf Q ≤ R₀ := by
        rw [← hQQ]
        exact commutator_le_of_sup_center heq inf_le_right (hQK.trans hKR₀)
      exact (heq.symm.trans (sup_eq_left.mpr hZR₀)).le.trans inf_le_right
    obtain ⟨hR₀QZ, hcardR₀Z⟩ := hmod R₀ inf_le_left hKR₀ hR₀Z hR₀Q
    have hZR₀ : centerOf Q ≤ R₀ := by
      rw [← hR₀QZ]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQK.trans hKR₀)
    have hcardR₀ : Nat.card R₀ = (2 ^ m) ^ 3 := by
      rwa [sup_eq_left.mpr hZR₀] at hcardR₀Z

    set Bb := modO2Image H' K with hBb
    have hO2B : Nat.card (CFSG.pCore 2 ↥Bb) = 2 ^ (2 * m) := by
      have h1 := card_pCore_modO2Image_mul hKH'
      have h2 : Nat.card (CFSG.pCore 2 ↥K) = (2 ^ m) ^ 5 := by
        rw [← hQcard]
        exact (Subgroup.card_map_of_injective K.subtype_injective).symm
      rw [hKinf, hcardR₀, h2, show (2 ^ m) ^ 5 = 2 ^ (2 * m) * (2 ^ m) ^ 3 by ring] at h1
      exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
    obtain ⟨eKB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKH'
    have eB : ModO2 Bb ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m) := eKB.symm.trans eK
    have hD : BarData Bb m := barData_of_quot_SL2 hm2 hFc eB
    have hK4 := NQCat.exists_finset_card_four_of_card hm2 hFc
    have := Vol2Native.A312L.sl2_isSimple hK4
    have hsimp : IsSimpleGroup (ModO2 Bb) := eB.isSimpleGroup
    have hcommB : ⁅CFSG.pCore 2 ↥Bb, ⊤⁆ = CFSG.pCore 2 ↥Bb :=
      commutator_pCore_modO2Image hKH' hQKc

    have hS : IsSylowTwoOf T H' := ⟨le_sup_right, hKh.1.1, hKh.1.2.2.1⟩
    have hBl : K ∈ lFamily T := mem_lFamily_of_isLocal e.locK
    have hBL : Bb ≤ modO2Image H' Kh := Subgroup.map_mono fun x hx => hlt.le hx
    rcases lemma_1_2_4_list e.qtke e.simple e.nonab h312 hKh.1.2.2.2 hS hKH' hBl
        (cComp_of_isLocal hKh.1) hlt.le with heq | hcase | hnq
    · exact absurd (eq_of_modO2Image_eq e.locK hKh.1 hlt.le heq) hlt.ne
    swap
    · exact false_of_a312Nonquasi_of_block hD hO2B hsimp hcommB hBL hnq
    rcases rows_block hD hO2B hcase with hC2 | ⟨hm2', hMJ⟩
    ·
      obtain ⟨hL3, P, hP, hBP⟩ := a312C2_block hExcSq hD hO2B hC2
      exact hSL3 G T M L V H B D L₂ n m hyp hnm h2n hαU hLb hKq hsp Kh hlt hKh hQR hL3
        ⟨P, hP, hBP⟩

    subst hm2'
    have hR2 : IsPGroup 2 (pCoreOf 2 Kh) := pCoreOf_isPGroup 2 Kh
    have hR7 : Nat.card (pCoreOf 2 Kh) ≤ 2 ^ 7 := by
      have h1 := Subgroup.relIndex_mul_card Q (pCoreOf 2 Kh)
      have hidx : Q.relIndex (pCoreOf 2 Kh) ≤ 2 := by
        rcases halt with ⟨-, -, -, hKSeq⟩ | ⟨m', -, -, -, t, ht2, -, hKSeq, -⟩
        · have : Q.relIndex (pCoreOf 2 Kh) = 1 :=
            Subgroup.relIndex_eq_one.mpr (hRKS.trans hKSeq.le)
          omega
        · obtain ⟨-, -, -, hle2⟩ := htprops t ht2 hKSeq
          have hne : Q.relIndex (Q ⊔ Subgroup.zpowers t) ≠ 0 := by
            intro h0
            have h2 := Subgroup.relIndex_mul_card Q (Q ⊔ Subgroup.zpowers t)
            rw [h0, zero_mul] at h2
            exact (Nat.card_pos (α := ↥(Q ⊔ Subgroup.zpowers t))).ne h2
          exact (Subgroup.relIndex_le_of_le_right (hKSeq ▸ hRKS) hne).trans hle2
      rw [← h1, hcardR₀]
      calc Q.relIndex (pCoreOf 2 Kh) * (2 ^ 2) ^ 3 ≤ 2 * (2 ^ 2) ^ 3 :=
            Nat.mul_le_mul_right _ hidx
        _ = 2 ^ 7 := by norm_num
    obtain ⟨-, hcomm, hV2, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hR2
    have hVle : Nat.card (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh)) ≤
        Nat.card (pCoreOf 2 Kh) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥(pCoreOf 2 Kh))
      have hpos : 0 < Nat.card (frattini ↥(pCoreOf 2 Kh)) := Nat.card_pos
      calc Nat.card (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh))
          ≤ Nat.card (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh)) *
            Nat.card (frattini ↥(pCoreOf 2 Kh)) := Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card (pCoreOf 2 Kh) := h1.symm
    rw [hd] at hVle
    have hd9 : d ≤ 9 := by
      have h1 : 2 ^ d ≤ 2 ^ 7 := hVle.trans hR7
      have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
      omega

    have hKhH' : Kh ≤ H' := le_sup_left
    set ρ := toModO2Image hKhH' with hρ
    have hρs : Function.Surjective ρ := toModO2Image_surjective hKhH'
    have hρk : ρ.ker = (pCoreOf 2 Kh).subgroupOf Kh :=
      ker_toModO2Image hKhH' (e.inf_pCoreOf_eq h37)
    set φ := frattiniRep Kh with hφ
    have hφk : φ.ker = (pCoreOf 2 Kh).subgroupOf Kh := ker_frattiniRep hchar
    have eLφ : ↥(modO2Image H' Kh) ≃* φ.range :=
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq (hρk.trans hφk.symm)).trans
          (QuotientGroup.quotientKerEquivRange φ))
    let _ : CommGroup (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh)) :=
      { (inferInstance : Group (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh))) with
        mul_comm := hcomm.is_comm.comm }
    have hdvd : Nat.card ↥(modO2Image H' Kh) ∣ 699612310033197642547200 := by
      rw [Nat.card_congr eLφ.toEquiv]
      have h1 : Nat.card φ.range ∣
          Nat.card (MulAut (↥(pCoreOf 2 Kh) ⧸ frattini ↥(pCoreOf 2 Kh))) :=
        Subgroup.card_subgroup_dvd_card φ.range
      rw [card_mulAut_of_sq_eq_one hV2 hd] at h1
      exact h1.trans (card_GL_dvd_GL9 hd9)

    have hsp11 : ∀ {s : TauCeti.SporadicName} {N : ℕ},
        Nat.card (NativeSporadic.Carrier s) = N → IsSporadic s ↥(modO2Image H' Kh) →
          Nat.card ↥(modO2Image H' Kh) = N :=
      fun hN ⟨e'⟩ => (Nat.card_congr e'.toEquiv).trans hN
    have h11 : 11 ∣ Nat.card ↥(modO2Image H' Kh) := by
      rcases hMJ with hX | hX | hX | hX
      · rw [card_of_isSporadic_M22' hX]
        norm_num
      · rw [card_hatM22 hX]
        norm_num
      · rw [hsp11 (s := .M23) (N := 10200960) CFSG.Sporadic.Schreier.m23_card hX]
        norm_num
      · rw [hsp11 (s := .J4) (N := 86775571046077562880) CFSG.Sporadic.J4.card_J4 hX]
        norm_num
    exact absurd (h11.trans hdvd) (by norm_num)

end CFSG.Quasithin.H13
