module

public import CFSG.CGT.PushingUpLit.NineChoiceSteps

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open scoped commutatorElement

open Nine

variable {G : Type} [Group G]

theorem characteristicCoreStar_le_of_isSylowOf [Finite G] (T : Sylow 2 G) {P : Subgroup G}
    (hP : IsSylowOf 2 P ⊤) (hPM : P ≤ characteristicCoreStar (T : Subgroup G)) :
    characteristicCoreStar P ≤ characteristicCoreStar (T : Subgroup G) := by
  have hTM : (T : Subgroup G) ≤ characteristicCoreStar (T : Subgroup G) :=
    le_characteristicCoreStar _
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isPGroup T hTM hP.2.1 hPM
  have hPle : P ≤ (T : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨m * x * m⁻¹, hm ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hPT : (T : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom = P :=
    le_antisymm (le_of_isSylowOf_of_le hP (T.isPGroup'.map _) hPle le_top) hPle
  calc characteristicCoreStar P
      = characteristicCoreStar ((T : Subgroup G).map (MulAut.conj m⁻¹).toMonoidHom) := by
        rw [hPT]
    _ ≤ (characteristicCoreStar (T : Subgroup G)).map (MulAut.conj m⁻¹).toMonoidHom :=
        characteristicCoreStar_map_le _ _
    _ ≤ characteristicCoreStar (T : Subgroup G) := by
        rintro _ ⟨x, hx, rfl⟩
        have := (characteristicCoreStar (T : Subgroup G)).mul_mem
          ((characteristicCoreStar (T : Subgroup G)).mul_mem
            ((characteristicCoreStar (T : Subgroup G)).inv_mem hmM) hx) hmM
        simpa [MulAut.conj_apply] using this

theorem normalizer_le_of_normalized [Finite G] {M I S P' B : Subgroup G}
    (hmax : ∀ (H' S' : Subgroup G), IsMaximalTwoLocal H' → I ≤ H' → ¬ H' ≤ M →
      IsSylowOf 2 S' H' → I ≤ S' → Nat.card S' ≤ Nat.card S)
    (hIS : I ≤ S) (hSP : S < P') (hP2 : IsPGroup 2 P') (hB2 : IsPGroup 2 B) (hB1 : B ≠ ⊥)
    (hPB : P' ≤ Subgroup.normalizer (B : Set G)) : Subgroup.normalizer (B : Set G) ≤ M := by
  obtain ⟨H', hNH', hH'⟩ := exists_isMaximalTwoLocal_ge (isPLocal_normalizer_of_isPGroup hB2 hB1)
  by_contra hNM
  have hH'M : ¬ H' ≤ M := fun h => hNM (hNH'.trans h)
  have hPH' : P' ≤ H' := hPB.trans hNH'
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_ge hP2 hPH'
  have h1 := hmax H' S' hH' (hIS.trans (hSP.le.trans hPH')) hH'M hS' (hIS.trans (hSP.le.trans hPS'))
  have h2 := card_lt_of_lt hSP
  have h3 := Subgroup.card_le_of_le hPS'
  omega

theorem exists_nineChoice [Finite G] (hchar : CFSG.Assembly.IsCharTwoType G) (T : Sylow 2 G)
    (hM : characteristicCoreStar (T : Subgroup G) ≠ ⊤)
    (hns : ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (characteristicCoreStar (T : Subgroup G))) :
    ∃ I H S : Subgroup G, NineChoice (characteristicCoreStar (T : Subgroup G)) I H S := by
  obtain ⟨M, hMdef⟩ : ∃ M : Subgroup G, M = characteristicCoreStar (T : Subgroup G) := ⟨_, rfl⟩
  rw [← hMdef] at hM hns ⊢
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hTM : (T : Subgroup G) ≤ M := by
    rw [hMdef]
    exact le_characteristicCoreStar _
  have hT1 : (T : Subgroup G) ≠ ⊥ := by
    intro h
    refine hM (eq_top_iff.mpr fun g _ => ?_)
    rw [hMdef]
    refine centralizer_le_characteristicCoreStar (T : Subgroup G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ (⊥ : Subgroup G) := by
      rw [← h]
      exact omegaOneCenterIn_le _ hz
    rw [Subgroup.mem_bot] at hz'
    subst hz'
    simp
  have hex : ∃ I : Subgroup G, NineAdmissible M I ∧ I ≠ ⊥ := by
    by_contra hno
    push Not at hno
    refine hns (isStronglyEmbeddedOrder_of_forall_normalizer_le hM
      (even_card_of_isPGroup_le hT2 hT1 hTM) fun R hR1 hR2 hRM => ?_)
    have hJ1 : jIn R ≠ ⊥ := jIn_ne_bot hR2 hR1
    have hJ2 : IsPGroup 2 (jIn R) := isPGroup_jIn hR2
    obtain ⟨H'', hLH, hH''⟩ := exists_isMaximalTwoLocal_ge
      (isPLocal_normalizer_of_isPGroup hJ2 hJ1)
    have hH''M : H'' ≤ M := by
      by_contra hnot
      exact hJ1 (hno _ ⟨hJ2, jIn_jIn R, (jIn_le R).trans hRM, H'', hH'',
        Subgroup.le_normalizer.trans hLH, hnot⟩)
    exact (normalizer_le_normalizer_jIn R).trans (hLH.trans hH''M)
  obtain ⟨I₀, hI₀, hI₀1⟩ := hex
  obtain ⟨I₁, hI₁, hmax⟩ := Set.exists_max_image {I : Subgroup G | NineAdmissible M I}
    (fun I => toLex (pRank 2 ↥I, Nat.card ↥I)) (Set.toFinite _) ⟨I₀, hI₀⟩
  have hI₁max : NineMax M I₁ := by
    refine ⟨hI₁, fun I' hI' => ?_⟩
    have h : pRank 2 ↥I' < pRank 2 ↥I₁ ∨
        (pRank 2 ↥I' = pRank 2 ↥I₁ ∧ Nat.card ↥I' ≤ Nat.card ↥I₁) :=
      Prod.Lex.toLex_le_toLex.mp (hmax I' hI')
    exact h
  have hI₁1 : I₁ ≠ ⊥ := by
    intro h
    have h1 : pRank 2 ↥I₀ < pRank 2 ↥I₁ ∨
        (pRank 2 ↥I₀ = pRank 2 ↥I₁ ∧ Nat.card ↥I₀ ≤ Nat.card ↥I₁) :=
      Prod.Lex.toLex_le_toLex.mp (hmax I₀ hI₀)
    have h2 : 1 ≤ pRank 2 ↥I₀ := one_le_pRank hI₀.1 hI₀1
    have h3 : pRank 2 ↥I₁ = 0 := by
      rw [h]
      exact pRank_bot
    omega
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_isPGroup T hTM hI₁.1 hI₁.2.2.1
  obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = I₁.map (MulAut.conj m).toMonoidHom := ⟨_, rfl⟩
  have hImax : NineMax M I := by
    rw [hI]
    exact hI₁max.map_conj hmM
  have hIT : I ≤ T := by
    rw [hI]
    exact hm
  have hI1 : I ≠ ⊥ := fun h =>
    hI₁1 ((Subgroup.map_eq_bot_iff_of_injective I₁ (MulAut.conj m).injective).mp (hI.symm.trans h))
  have hI2 : IsPGroup 2 I := hImax.1.1
  have hN : Subgroup.normalizer (I : Set G) ≤ M := by
    rw [hMdef] at hImax ⊢
    exact normalizer_le_of_nineMax hT2 hImax hIT hI1
  obtain ⟨H₀, hH₀, hIH₀, hH₀M⟩ := hImax.1.2.2.2
  obtain ⟨S₀, hS₀, hIS₀⟩ := exists_isSylowOf_ge hI2 hIH₀
  obtain ⟨⟨H, S⟩, ⟨hHmax, hIH, hHM, hSyl, hIS⟩, hpmax⟩ := Set.exists_max_image
    {p : Subgroup G × Subgroup G | IsMaximalTwoLocal p.1 ∧ I ≤ p.1 ∧ ¬ p.1 ≤ M ∧
      IsSylowOf 2 p.2 p.1 ∧ I ≤ p.2}
    (fun p => Nat.card ↥p.2) (Set.toFinite _) ⟨(H₀, S₀), hH₀, hIH₀, hH₀M, hS₀, hIS₀⟩
  have hmaxS : ∀ (H' S' : Subgroup G), IsMaximalTwoLocal H' → I ≤ H' → ¬ H' ≤ M →
      IsSylowOf 2 S' H' → I ≤ S' → Nat.card S' ≤ Nat.card S :=
    fun H' S' hH' hIH' hH'M hS' hIS' => hpmax (H', S') ⟨hH', hIH', hH'M, hS', hIS'⟩
  have hHmax' : IsMaximalTwoLocal H := hHmax
  have hIH' : I ≤ H := hIH
  have hHM' : ¬ H ≤ M := hHM
  have hSyl' : IsSylowOf 2 S H := hSyl
  have hIS' : I ≤ S := hIS
  have hsylow_jIn : ∀ K P : Subgroup G, IsCharacteristicP 2 ↥K → I ≤ K → ¬ K ≤ M →
      IsSylowOf 2 P K → I ≤ P → jIn P = I ∧ P ≤ Subgroup.normalizer (I : Set G) :=
    fun K P hK hIK hKM hP hIP => nineMax_sylow_jIn hImax hN hI1 hK hIK hKM hP hIP
  have hHchar : IsCharacteristicP 2 ↥H := isCharacteristicP_of_isPLocal hchar hHmax'.1
  have hSM : S ≤ M := (hsylow_jIn H S hHchar hIH' hHM' hSyl' hIS').2.trans hN
  have hS2 : IsPGroup 2 S := hSyl'.2.1
  have hS1 : S ≠ ⊥ := fun h => hI1 (le_bot_iff.mp (h ▸ hIS'))
  have hSylc : ∀ P : Subgroup G, IsSylowOf 2 P ⊤ → P ≤ M →
      Subgroup.centralizer (omegaOneCenterIn P : Set G) ≤ M := by
    intro P hP hPM
    rw [hMdef] at hPM ⊢
    exact (centralizer_le_characteristicCoreStar P).trans
      (characteristicCoreStar_le_of_isSylowOf T hP hPM)
  have hcent : Subgroup.centralizer (omegaOneCenterIn S : Set G) ≤ M ∧
      ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS S →
        (B.subgroupOf (pushingUpS S)).Characteristic → Subgroup.normalizer (B : Set G) ≤ M := by
    rcases isSylowOf_top_or_exists_gt hS2 with hSG | ⟨P', hP'2, hP'N, hSP'⟩
    · have hC := hSylc S hSG hSM
      refine ⟨hC, fun B hB1 hBS hBc => ?_⟩
      have hle : characteristicCoreStar S ≤ M := by
        rw [hMdef] at hSM ⊢
        exact characteristicCoreStar_le_of_isSylowOf T hSG hSM
      exact (normalizer_le_characteristicCoreStar hB1 hBS hBc).trans hle
    · have hNS : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (pushingUpS S : Set G) :=
        normalizer_le_normalizer_of_characteristic' (pushingUpS_le S) (characteristic_pushingUpS S)
      refine ⟨?_, fun B hB1 hBS hBc => ?_⟩
      · have hE2 : IsPGroup 2 (omegaOneCenterIn S) := hS2.to_le (omegaOneCenterIn_le S)
        have hE1 : omegaOneCenterIn S ≠ ⊥ := omegaOneCenterIn_ne_bot hS2 hS1
        have hPE : P' ≤ Subgroup.normalizer (omegaOneCenterIn S : Set G) :=
          hP'N.trans (normalizer_le_normalizer_of_characteristic' (omegaOneCenterIn_le S)
            (characteristic_omegaOneCenterIn S))
        exact (Subgroup.centralizer_le_normalizer _).trans
          (normalizer_le_of_normalized hmaxS hIS' hSP' hP'2 hE2 hE1 hPE)
      · have hB2 : IsPGroup 2 B := hS2.to_le (hBS.trans (pushingUpS_le S))
        have hPB : P' ≤ Subgroup.normalizer (B : Set G) :=
          hP'N.trans (hNS.trans (normalizer_le_normalizer_of_characteristic' hBS hBc))
        exact normalizer_le_of_normalized hmaxS hIS' hSP' hP'2 hB2 hB1 hPB
  refine ⟨I, H, S, ?_⟩
  exact
    { ne_bot := hI1
      isPGroup := hI2
      jIn_self := hImax.1.2.1
      le_M := hImax.1.2.2.1
      maxLocal := hHmax'
      not_le := hHM'
      sylow := hSyl'
      I_le_S := hIS'
      max_I := hImax
      max_S := hmaxS
      normalizer_le := hN
      sylow_jIn := hsylow_jIn
      jIn_normalizer := fun K hK hIK hKM => jIn_normalizer_inf hImax hN hI1 hK hIK hKM
      centralizer_le := inf_le_left.trans hcent.1
      normalizer_char_le := fun B hB1 hBS hBc => inf_le_left.trans (hcent.2 B hB1 hBS hBc)
      sylow_centralizer := hSylc }

theorem nine_five_aux [Finite G] (hchar : CFSG.Assembly.IsCharTwoType G) {M I H S : Subgroup G}
    (h : NineChoice M I H S) {Y : Subgroup G} (hY : ¬ Y ≤ M) :
    ∀ n : ℕ, ∀ K P : Subgroup G, Nat.card G - Nat.card P = n → IsCharacteristicP 2 ↥K →
      Y ≤ K → I ≤ K → IsSylowOf 2 P K → I ≤ P → ⁅Y, omegaOneCenterIn P⁆ ≠ ⊥ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K P hn hK hYK hIK hP hIP hcomm
  have hP2 : IsPGroup 2 P := hP.2.1
  have hKM : ¬ K ≤ M := fun hKM => hY (hYK.trans hKM)
  have hPN := (h.sylow_jIn K P hK hIK hKM hP hIP).2
  have hPM : P ≤ M := hPN.trans h.normalizer_le
  have hP1 : P ≠ ⊥ := fun hb => h.ne_bot (le_bot_iff.mp (hb ▸ hIP))
  have hYC : Y ≤ Subgroup.centralizer (omegaOneCenterIn P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rcases isSylowOf_top_or_exists_gt hP2 with hPtop | ⟨P', hP'2, hP'N, hPP'⟩
  · exact hY (hYC.trans (h.sylow_centralizer P hPtop hPM))
  · have hZ2 : IsPGroup 2 (omegaOneCenterIn P) := hP2.to_le (omegaOneCenterIn_le P)
    have hZ1 : omegaOneCenterIn P ≠ ⊥ := omegaOneCenterIn_ne_bot hP2 hP1
    have hloc : IsPLocal 2 (Subgroup.normalizer (omegaOneCenterIn P : Set G)) :=
      isPLocal_normalizer_of_isPGroup hZ2 hZ1
    have hK' : IsCharacteristicP 2 ↥(Subgroup.normalizer (omegaOneCenterIn P : Set G)) :=
      isCharacteristicP_of_isPLocal hchar hloc
    have hPcent : P ≤ Subgroup.centralizer (omegaOneCenterIn P : Set G) :=
      le_centralizer_of_le_omegaOneCenterIn le_rfl
    have hCN : Subgroup.centralizer (omegaOneCenterIn P : Set G) ≤
        Subgroup.normalizer (omegaOneCenterIn P : Set G) := Subgroup.centralizer_le_normalizer _
    have hPK' := hPcent.trans hCN
    have hYK' := hYC.trans hCN
    have hIK' : I ≤ Subgroup.normalizer (omegaOneCenterIn P : Set G) := hIP.trans hPK'
    obtain ⟨Q, hQ, hPQ⟩ := exists_isSylowOf_ge hP2 hPK'
    have hPQne : P ≠ Q := by
      intro hPQeq
      have hP'Z : P' ≤ Subgroup.normalizer (omegaOneCenterIn P : Set G) :=
        hP'N.trans (normalizer_le_normalizer_of_characteristic' (omegaOneCenterIn_le P)
          (characteristic_omegaOneCenterIn P))
      have hP'Q : P' ≤ Q :=
        le_of_isSylowOf_of_le hQ hP'2 (hPQeq ▸ hPP'.le) hP'Z
      exact hPP'.not_ge (by rw [hPQeq]; exact hP'Q)
    have hlt : Nat.card P < Nat.card Q := card_lt_of_lt (lt_of_le_of_ne hPQ hPQne)
    have hQG : Nat.card Q ≤ Nat.card G := Subgroup.card_le_card_group Q
    have hind := ih (Nat.card G - Nat.card Q) (by omega) _ Q rfl hK' hYK' hIK' hQ (hIP.trans hPQ)
    refine hind ?_
    have hK'M : ¬ Subgroup.normalizer (omegaOneCenterIn P : Set G) ≤ M :=
      fun hh => hY (hYK'.trans hh)
    have hJQ := (h.sylow_jIn _ Q hK' hIK' hK'M hQ (hIP.trans hPQ)).1
    have hEI : omegaOneCenterIn Q ≤ I := (omegaOneCenterIn_le_jIn Q).trans hJQ.le
    have hEZ : omegaOneCenterIn Q ≤ omegaOneCenterIn P :=
      omegaOneCenterIn_le_omegaOneCenterIn hPQ (hEI.trans hIP)
    exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hEZ).trans hcomm.le)

theorem nine_five [Finite G] (hchar : CFSG.Assembly.IsCharTwoType G) (T : Sylow 2 G)
    {I H S : Subgroup G} (h : NineChoice (characteristicCoreStar (T : Subgroup G)) I H S)
    {Y K P : Subgroup G} (hY : ¬ Y ≤ characteristicCoreStar (T : Subgroup G))
    (hK : IsCharacteristicP 2 ↥K) (hYK : Y ≤ K) (hIK : I ≤ K) (hP : IsSylowOf 2 P K)
    (hIP : I ≤ P) : ⁅Y, omegaOneCenterIn P⁆ ≠ ⊥ :=
  nine_five_aux hchar h hY _ K P rfl hK hYK hIK hP hIP

end CFSG.CGT.PushingUpLit
