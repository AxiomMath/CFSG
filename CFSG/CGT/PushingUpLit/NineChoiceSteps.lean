module

public import CFSG.CGT.PushingUpLit.NineChoiceJ

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.RankThree.PartOne CFSG.CGT.PushingUp

open Nine

variable {G : Type} [Group G]

@[expose] def NineAdmissible (M I : Subgroup G) : Prop :=
  IsPGroup 2 I ∧ jIn I = I ∧ I ≤ M ∧ ∃ H : Subgroup G, IsMaximalTwoLocal H ∧ I ≤ H ∧ ¬ H ≤ M

@[expose] def NineMax (M I : Subgroup G) : Prop :=
  NineAdmissible M I ∧ ∀ I' : Subgroup G, NineAdmissible M I' →
    pRank 2 ↥I' < pRank 2 ↥I ∨ (pRank 2 ↥I' = pRank 2 ↥I ∧ Nat.card I' ≤ Nat.card I)

structure NineChoice (M : Subgroup G) (I H S : Subgroup G) : Prop where
  ne_bot : I ≠ ⊥
  isPGroup : IsPGroup 2 I
  jIn_self : jIn I = I
  le_M : I ≤ M
  maxLocal : IsMaximalTwoLocal H
  not_le : ¬ H ≤ M
  sylow : IsSylowOf 2 S H
  I_le_S : I ≤ S
  max_I : NineMax M I
  max_S : ∀ (H' S' : Subgroup G), IsMaximalTwoLocal H' → I ≤ H' → ¬ H' ≤ M → IsSylowOf 2 S' H' →
    I ≤ S' → Nat.card S' ≤ Nat.card S
  normalizer_le : Subgroup.normalizer (I : Set G) ≤ M
  sylow_jIn : ∀ K P : Subgroup G, IsCharacteristicP 2 ↥K → I ≤ K → ¬ K ≤ M →
    IsSylowOf 2 P K → I ≤ P → jIn P = I ∧ P ≤ Subgroup.normalizer (I : Set G)
  jIn_normalizer : ∀ K : Subgroup G, IsCharacteristicP 2 ↥K → I ≤ K → ¬ K ≤ M →
    jIn (Subgroup.normalizer (I : Set G) ⊓ K) = I
  centralizer_le : Subgroup.centralizer (omegaOneCenterIn S : Set G) ⊓ H ≤ M
  normalizer_char_le : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS S →
    (B.subgroupOf (pushingUpS S)).Characteristic → Subgroup.normalizer (B : Set G) ⊓ H ≤ M
  sylow_centralizer : ∀ P : Subgroup G, IsSylowOf 2 P ⊤ → P ≤ M →
    Subgroup.centralizer (omegaOneCenterIn P : Set G) ≤ M

section Conj

variable {M I : Subgroup G}

theorem NineAdmissible.map_conj [Finite G] (h : NineAdmissible M I) {m : G} (hm : m ∈ M) :
    NineAdmissible M (I.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨h2, hJ, hIM, H, hH, hIH, hHM⟩ := h
  refine ⟨h2.map _, ?_, ?_, H.map (MulAut.conj m).toMonoidHom, isMaximalTwoLocal_map_conj hH m,
    Subgroup.map_mono hIH, not_map_conj_le hHM hm⟩
  · rw [jIn_map_equiv, hJ]
  · rintro _ ⟨x, hx, rfl⟩
    have := M.mul_mem (M.mul_mem hm (hIM hx)) (M.inv_mem hm)
    simpa [MulAut.conj_apply] using this

theorem NineMax.map_conj [Finite G] (h : NineMax M I) {m : G} (hm : m ∈ M) :
    NineMax M (I.map (MulAut.conj m).toMonoidHom) := by
  have hc : ∀ (g : G) (J : Subgroup G),
      pRank 2 ↥(J.map (MulAut.conj g).toMonoidHom) = pRank 2 ↥J := fun g J =>
    pRank_map_injective _ (MulAut.conj g).injective J 2
  have hk : ∀ (g : G) (J : Subgroup G),
      Nat.card ↥(J.map (MulAut.conj g).toMonoidHom) = Nat.card ↥J := fun g J =>
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  refine ⟨h.1.map_conj hm, fun I' hI' => ?_⟩
  have h1 := h.2 _ (hI'.map_conj (M.inv_mem hm))
  rw [hc, hk] at h1
  rw [hc, hk]
  exact h1

theorem NineMax.le_of_beats (h : NineMax M I) {I' : Subgroup G} (h2 : IsPGroup 2 I')
    (hJ : jIn I' = I') (hM : I' ≤ M)
    (hlt : pRank 2 ↥I < pRank 2 ↥I' ∨ (pRank 2 ↥I' = pRank 2 ↥I ∧ Nat.card I < Nat.card I')) :
    ∀ H : Subgroup G, IsMaximalTwoLocal H → I' ≤ H → H ≤ M := by
  intro H hH hI'H
  by_contra hHM
  rcases h.2 I' ⟨h2, hJ, hM, H, hH, hI'H, hHM⟩ with h1 | ⟨h1, h3⟩ <;> omega

end Conj

theorem normalizer_le_of_nineMax [Finite G] {T I : Subgroup G} (hT : IsPGroup 2 T)
    (hI : NineMax (characteristicCoreStar T) I) (hIT : I ≤ T) (hI1 : I ≠ ⊥) :
    Subgroup.normalizer (I : Set G) ≤ characteristicCoreStar T := by
  have hTM : T ≤ characteristicCoreStar T := le_characteristicCoreStar T
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
    exact normalizer_jIn_le_characteristicCoreStar hT hT1
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

theorem jIn_sylow_eq [Finite G] {M I K S₁ : Subgroup G} (hI : NineMax M I)
    (hN : Subgroup.normalizer (I : Set G) ≤ M) (hI1 : I ≠ ⊥) (hK : IsCharacteristicP 2 ↥K)
    (hIK : I ≤ K) (hKM : ¬ K ≤ M) (hS : IsSylowOf 2 S₁ (Subgroup.normalizer (I : Set G) ⊓ K)) :
    jIn S₁ = I ∧ pRank 2 ↥S₁ = pRank 2 ↥I := by
  have hIS : I ≤ S₁ := le_of_isSylowOf_of_normal hS hI.1.1
    (le_inf Subgroup.le_normalizer hIK) inf_le_left
  have hS1 : IsPGroup 2 S₁ := hS.2.1
  have hS1K' : S₁ ≤ Subgroup.normalizer (I : Set G) ⊓ K := hS.1
  have hK1 : K ≠ ⊥ := fun h => hI1 (le_bot_iff.mp (h ▸ hIK))
  obtain ⟨H₁, hKH₁, hH₁⟩ := exists_isMaximalTwoLocal_ge_of_isCharacteristicP hK hK1
  have hadm : NineAdmissible M (jIn S₁) :=
    ⟨isPGroup_jIn hS1, jIn_jIn S₁, (jIn_le S₁).trans (hS1K'.trans (inf_le_left.trans hN)), H₁,
      hH₁, (jIn_le S₁).trans (hS1K'.trans (inf_le_right.trans hKH₁)),
      fun h => hKM (hKH₁.trans h)⟩
  have hrk : pRank 2 ↥(jIn S₁) = pRank 2 ↥S₁ := pRank_jIn S₁
  have hge : pRank 2 ↥I ≤ pRank 2 ↥S₁ := pRank_mono hIS
  rcases hI.2 _ hadm with h1 | ⟨h1, h2⟩
  · omega
  · have hr : pRank 2 ↥I = pRank 2 ↥S₁ := by omega
    have hle : I ≤ jIn S₁ := by
      have := jIn_mono_of_pRank_eq hIS hr
      rwa [hI.1.2.1] at this
    exact ⟨(Subgroup.eq_of_le_of_card_ge hle h2).symm, by omega⟩

theorem jIn_normalizer_inf [Finite G] {M I K : Subgroup G} (hI : NineMax M I)
    (hN : Subgroup.normalizer (I : Set G) ≤ M) (hI1 : I ≠ ⊥) (hK : IsCharacteristicP 2 ↥K)
    (hIK : I ≤ K) (hKM : ¬ K ≤ M) : jIn (Subgroup.normalizer (I : Set G) ⊓ K) = I := by
  have hIK' : I ≤ Subgroup.normalizer (I : Set G) ⊓ K := le_inf Subgroup.le_normalizer hIK
  have key : ∀ A ∈ elemFamilyIn 2 (Subgroup.normalizer (I : Set G) ⊓ K),
      A ≤ I ∧ pRank 2 ↥(Subgroup.normalizer (I : Set G) ⊓ K) = pRank 2 ↥I := by
    intro A hA
    obtain ⟨hAK', hAe, hAc⟩ := mem_elemFamilyIn.mp hA
    have hA2 : IsPGroup 2 A := by
      have := hAe
      exact IsElementaryAbelian.isPGroup 2 ↥A
    obtain ⟨S₂, hS₂, hAS₂⟩ := exists_isSylowOf_ge hA2 hAK'
    obtain ⟨hJ₂, hr₂⟩ := jIn_sylow_eq hI hN hI1 hK hIK hKM hS₂
    have hle : pRank 2 ↥(Subgroup.normalizer (I : Set G) ⊓ K) ≤ pRank 2 ↥S₂ :=
      pRank_le_of_card_le hAS₂ hAe hAc
    have hge : pRank 2 ↥S₂ ≤ pRank 2 ↥(Subgroup.normalizer (I : Set G) ⊓ K) :=
      pRank_mono hS₂.1
    have hrr : pRank 2 ↥(Subgroup.normalizer (I : Set G) ⊓ K) = pRank 2 ↥S₂ := le_antisymm hle hge
    have hAfam : A ∈ elemFamilyIn 2 S₂ := mem_elemFamilyIn.mpr ⟨hAS₂, hAe, by rw [hAc, hrr]⟩
    have hAJ := le_elemThompsonIn hAfam
    rw [← jIn_eq_elemThompsonIn, hJ₂] at hAJ
    exact ⟨hAJ, by omega⟩
  obtain ⟨A₀, hA₀⟩ := exists_mem_elemFamilyIn (Subgroup.normalizer (I : Set G) ⊓ K)
  refine le_antisymm ?_ ?_
  · rw [jIn_eq_elemThompsonIn, elemThompsonIn_eq]
    exact sSup_le fun A hA => (key A hA).1
  · have := jIn_mono_of_pRank_eq hIK' (key A₀ hA₀).2.symm
    rwa [hI.1.2.1] at this

theorem nineMax_sylow_jIn [Finite G] {M I K P : Subgroup G} (hI : NineMax M I)
    (hN : Subgroup.normalizer (I : Set G) ≤ M) (hI1 : I ≠ ⊥) (hK : IsCharacteristicP 2 ↥K)
    (hIK : I ≤ K) (hKM : ¬ K ≤ M) (hP : IsSylowOf 2 P K) (hIP : I ≤ P) :
    jIn P = I ∧ P ≤ Subgroup.normalizer (I : Set G) := by
  have hP2 : IsPGroup 2 P := hP.2.1
  have hQP : P ⊓ Subgroup.normalizer (I : Set G) ≤ P := inf_le_left
  have hQ2 : IsPGroup 2 (P ⊓ Subgroup.normalizer (I : Set G) : Subgroup G) := hP2.to_le hQP
  have hQK' : P ⊓ Subgroup.normalizer (I : Set G) ≤ Subgroup.normalizer (I : Set G) ⊓ K :=
    le_inf inf_le_right (inf_le_left.trans hP.1)
  obtain ⟨S₁, hS₁, hQS₁⟩ := exists_isSylowOf_ge hQ2 hQK'
  obtain ⟨hJ₁, hr₁⟩ := jIn_sylow_eq hI hN hI1 hK hIK hKM hS₁
  have hIQ : I ≤ P ⊓ Subgroup.normalizer (I : Set G) := le_inf hIP Subgroup.le_normalizer
  have hrI : pRank 2 ↥I ≤ pRank 2 ↥(P ⊓ Subgroup.normalizer (I : Set G)) := pRank_mono hIQ
  have hrQ : pRank 2 ↥(P ⊓ Subgroup.normalizer (I : Set G)) ≤ pRank 2 ↥S₁ := pRank_mono hQS₁
  have hJQ : jIn (P ⊓ Subgroup.normalizer (I : Set G)) = I := by
    refine le_antisymm ?_ ?_
    · have := jIn_mono_of_pRank_eq hQS₁
        (by omega : pRank 2 ↥(P ⊓ Subgroup.normalizer (I : Set G)) = pRank 2 ↥S₁)
      rwa [hJ₁] at this
    · have := jIn_mono_of_pRank_eq hIQ
        (by omega : pRank 2 ↥I = pRank 2 ↥(P ⊓ Subgroup.normalizer (I : Set G)))
      rwa [hI.1.2.1] at this
  have hPQ : P ⊓ Subgroup.normalizer (I : Set G) = P := by
    refine eq_of_inf_normalizer_le hP2 hQP fun x hx => ?_
    refine ⟨hx.1, ?_⟩
    have := normalizer_le_normalizer_jIn (P ⊓ Subgroup.normalizer (I : Set G)) hx.2
    rwa [hJQ] at this
  refine ⟨?_, fun x hx => (hPQ.ge hx).2⟩
  calc jIn P = jIn (P ⊓ Subgroup.normalizer (I : Set G)) := by rw [hPQ]
    _ = I := hJQ

end CFSG.CGT.PushingUpLit
