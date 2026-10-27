module

public import CFSG.CGT.PushingUpLit.NineChoice

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

open Nine

variable {G : Type} [Group G]

theorem characteristicCoreStar_le_of_isSylowOf_of_le [Finite G] (T : Sylow 2 G) {M P : Subgroup G}
    (hCM : characteristicCoreStar (T : Subgroup G) ≤ M) (hP : IsSylowOf 2 P ⊤) (hPM : P ≤ M) :
    characteristicCoreStar P ≤ M := by
  have hTM : (T : Subgroup G) ≤ M := (le_characteristicCoreStar _).trans hCM
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
    _ ≤ M := by
        rintro _ ⟨x, hx, rfl⟩
        have := M.mul_mem (M.mul_mem (M.inv_mem hmM) (hCM hx)) hmM
        simpa [MulAut.conj_apply] using this

theorem normalizer_le_of_nineMax_of_le [Finite G] {T I M : Subgroup G} (hT : IsPGroup 2 T)
    (hCM : characteristicCoreStar T ≤ M) (hI : NineMax M I) (hIT : I ≤ T) (hI1 : I ≠ ⊥) :
    Subgroup.normalizer (I : Set G) ≤ M := by
  have hTM : T ≤ M := (le_characteristicCoreStar T).trans hCM
  have hI2 : IsPGroup 2 I := hI.1.1
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = T ⊓ Subgroup.normalizer (I : Set G) := ⟨_, rfl⟩
  have hPT : P ≤ T := hP ▸ inf_le_left
  have hPN : P ≤ Subgroup.normalizer (I : Set G) := hP ▸ inf_le_right
  have hIP : I ≤ P := hP ▸ le_inf hIT Subgroup.le_normalizer
  have hP2 : IsPGroup 2 P := hT.to_le hPT
  have hI'2 : IsPGroup 2 (jIn P) := isPGroup_jIn hP2
  by_cases heq : jIn P = I
  · have hPeq : P = T := eq_of_jIn_eq_of_inf_normalizer_le hT hPT heq (hP ▸ le_rfl)
    have hT1 : T ≠ ⊥ := fun h => hI1 (le_bot_iff.mp (h ▸ hIT))
    have hIJ : I = jIn T := by rw [← heq, hPeq]
    rw [hIJ]
    exact (normalizer_jIn_le_characteristicCoreStar hT hT1).trans hCM
  · have hr : pRank 2 ↥I ≤ pRank 2 ↥(jIn P) := by
      rw [pRank_jIn]
      exact pRank_mono hIP
    have hlt : pRank 2 ↥I < pRank 2 ↥(jIn P) ∨
        (pRank 2 ↥(jIn P) = pRank 2 ↥I ∧ Nat.card I < Nat.card (jIn P)) := by
      rcases hr.lt_or_eq with h | h
      · exact Or.inl h
      · refine Or.inr ⟨h.symm, ?_⟩
        have hle : I ≤ jIn P := by
          have := jIn_mono_of_pRank_eq hIP (h.trans (pRank_jIn P))
          rwa [hI.1.2.1] at this
        exact card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm heq))
    have hle := hI.le_of_beats hI'2 (jIn_jIn P) ((jIn_le P).trans (hPT.trans hTM)) hlt
    obtain ⟨H'', hLH, hH''⟩ := exists_isMaximalTwoLocal_ge
      (isPLocal_normalizer_of_isPGroup hI2 hI1)
    exact hLH.trans (hle H'' hH'' ((jIn_le P).trans (hPN.trans hLH)))

theorem exists_nineChoice_of_le [Finite G] (hchar : CFSG.Assembly.IsCharTwoType G)
    (T : Sylow 2 G) {M : Subgroup G} (hCM : characteristicCoreStar (T : Subgroup G) ≤ M)
    (hM : M ≠ ⊤) (hns : ¬ CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M) :
    ∃ I H S : Subgroup G, NineChoice M I H S := by
  have hT2 : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hTM : (T : Subgroup G) ≤ M := (le_characteristicCoreStar _).trans hCM
  have hT1 : (T : Subgroup G) ≠ ⊥ := by
    intro h
    refine hM (eq_top_iff.mpr fun g _ => hCM ?_)
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
  have hN : Subgroup.normalizer (I : Set G) ≤ M :=
    normalizer_le_of_nineMax_of_le hT2 hCM hImax hIT hI1
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
    exact (centralizer_le_characteristicCoreStar P).trans
      (characteristicCoreStar_le_of_isSylowOf_of_le T hCM hP hPM)
  have hcent : Subgroup.centralizer (omegaOneCenterIn S : Set G) ≤ M ∧
      ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS S →
        (B.subgroupOf (pushingUpS S)).Characteristic → Subgroup.normalizer (B : Set G) ≤ M := by
    rcases isSylowOf_top_or_exists_gt hS2 with hSG | ⟨P', hP'2, hP'N, hSP'⟩
    · have hC := hSylc S hSG hSM
      refine ⟨hC, fun B hB1 hBS hBc => ?_⟩
      have hle : characteristicCoreStar S ≤ M :=
        characteristicCoreStar_le_of_isSylowOf_of_le T hCM hSG hSM
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

end CFSG.CGT.PushingUpLit.T2KR.P53
