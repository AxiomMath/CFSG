module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightPure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ModuleRestrict
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.ThompsonMoves

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def mModule {G : Type} [Group G] (M S : Subgroup G) : Subgroup G :=
  sInf {K : Subgroup G | Quasithin.omegaOneCenterOf S ≤ K ∧ M ≤ Subgroup.normalizer (K : Set G)}

theorem omegaOneCenterOf_le_mModule {G : Type} [Group G] (M S : Subgroup G) :
    Quasithin.omegaOneCenterOf S ≤ mModule M S :=
  le_sInf fun _ hK => hK.1

theorem normalizer_mModule {G : Type} [Group G] (M S : Subgroup G) :
    M ≤ Subgroup.normalizer (mModule M S : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [mModule, Subgroup.mem_sInf] at hx ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp (hK.2 hg) x).mp (hx K hK)
  · intro hx
    rw [mModule, Subgroup.mem_sInf] at hx ⊢
    intro K hK
    exact (Subgroup.mem_normalizer_iff.mp (hK.2 hg) x).mpr (hx K hK)

theorem mModule_le {G : Type} [Group G] {M S K : Subgroup G} (h : Quasithin.omegaOneCenterOf S ≤ K)
    (hM : M ≤ Subgroup.normalizer (K : Set G)) : mModule M S ≤ K :=
  sInf_le ⟨h, hM⟩

@[expose] def CitedFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ ⁅L, Quasithin.thompsonJ S⁆ ≤ pCoreOf 2 M →
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) ∨ IsUThreeThree ↥(barM M L)) →
    HasIrreducibleCommutatorQuotient L (mModule M S) ∧
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6)) → SocleLE L (mModule M S) 16) ∧
    (IsUThreeThree ↥(barM M L) → SocleLE L (mModule M S) 64)

section Sep

variable {G : Type} [Group G] [Finite G]

theorem hasIrr_vModule_of_mModule {P : Sylow 3 G} {M A H R : Subgroup G}
    (hctx : PairStrongCtx P M A H R) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (h : HasIrreducibleCommutatorQuotient L₁ (mModule M (pCoreOf 2 H))) :
    HasIrreducibleCommutatorQuotient L₁ (vModule (pCoreOf 2 H) L₁ L₂) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  set V' := vModule S L₁ L₂ with hV'
  set VX := mModule M S with hVX
  have hVMe : IsElemAbelian 2 (Quasithin.omegaOneCenterOf (pCoreOf 2 M)) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hMV : M ≤ Subgroup.normalizer ((Quasithin.omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_of_characteristic_pCoreOf
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hVXV : VX ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M) :=
    mModule_le hpr.omegaOneCenter_le.1 hMV
  have hV'X : V' ≤ VX :=
    vModule_le (omegaOneCenterOf_le_mModule M S)
      (hpr.twoCore_le.trans (normalizer_mModule M S))
      (h₁.le.trans (normalizer_mModule M S)) (h₂.le.trans (normalizer_mModule M S))
  have hV'V : V' ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M) := hV'X.trans hVXV
  have hV2 : ∀ y ∈ V', y ^ 2 = 1 := fun y hy => hVMe.2 y (hV'V hy)
  have hVc : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, hV'V ha⟩ ⟨b, hV'V hb⟩)
  have hVXc : ∀ a ∈ VX, ∀ b ∈ VX, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, hVXV ha⟩ ⟨b, hVXV hb⟩)
  have hLV : L₁ ≤ Subgroup.normalizer (V' : Set G) := normalizer_vModule_L₁ S L₁ L₂
  have hLX : L₁ ≤ Subgroup.normalizer (VX : Set G) := h₁.le.trans (normalizer_mModule M S)
  have hmov : ¬ L₁ ≤ Subgroup.centralizer (Quasithin.omegaOneCenterOf S : Set G) := fun h =>
    h₁.not_le_normalizer (by
      have hH : L₁ ≤ H := by
        rw [← hpr.normalizer_thompsonJ_eq.2]
        exact h.trans (Subgroup.centralizer_le_normalizer _)
      rw [← hpr.normalizer_twoCore_H] at hH
      exact hH)
  have hne : ⁅V', L₁⁆ ⊓ Subgroup.centralizer (L₁ : Set G) < ⁅V', L₁⁆ := by
    refine lt_of_le_of_ne inf_le_left (fun h => hmov ?_)
    have hle : ⁅V', L₁⁆ ≤ Subgroup.centralizer (L₁ : Set G) := h ▸ inf_le_right
    have hperf := WeakBlockModuleData.commutator_le_commutator_commutator_of_perfect h₁.perfect hLV hVc
    have hbot : ⁅⁅V', L₁⁆, L₁⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu l hl
      have hc := Subgroup.mem_centralizer_iff.mp (hle hu) l hl
      rw [Subgroup.mem_bot]
      have : l * u = u * l := hc
      simp only [commutatorElement_def]
      calc u * l * u⁻¹ * l⁻¹ = (u * l) * u⁻¹ * l⁻¹ := by group
        _ = (l * u) * u⁻¹ * l⁻¹ := by rw [this]
        _ = 1 := by group
    have hb : ⁅V', L₁⁆ = ⊥ := eq_bot_iff.2 (hperf.trans hbot.le)
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hvV' : v ∈ V' := omegaOneCenterOf_le_vModule S L₁ L₂ hv
    have h1 : v * l * v⁻¹ * l⁻¹ ∈ ⁅V', L₁⁆ := Subgroup.commutator_mem_commutator hvV' hl
    rw [hb, Subgroup.mem_bot] at h1
    calc v * l = (v * l * v⁻¹ * l⁻¹) * (l * v) := by group
      _ = l * v := by rw [h1, one_mul]
  exact HasIrreducibleCommutatorQuotient.of_le hV'X hVXc hLX h hne

theorem exists_sep_of_tightRow' (hCF : CitedFive) (hat : U33Atlas) (h86 : Asc81bEightSix)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hz₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hr₂ : 2 ≤ Open.pRank 3 L₂) (hrow : TightRow M L₁)
    (hcen : Subgroup.center ↥(barM M L₁) = ⊥)
    (hnA8 : ¬ Nonempty (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁) ≃* alternatingGroup (Fin 8))) :
    ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      L₂ ≤ Subgroup.centralizer ({x} : Set G) ∧
      3 ≤ Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  have hX : ∀ {Y : Type} [Group Y], Nonempty (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁) ≃* Y) →
      Nonempty (↥(barM M L₁) ≃* Y) := fun ⟨e⟩ => mulEquiv_of_center_eq_bot hcen e
  have hu33 : IsUThreeThree (↥(barM M L₁) ⧸ Subgroup.center ↥(barM M L₁)) →
      IsUThreeThree ↥(barM M L₁) := by
    rintro ⟨d, hd, ⟨e⟩⟩
    exact ⟨d, hd, mulEquiv_of_center_eq_bot hcen e⟩
  have hrow' : Nonempty (↥(barM M L₁) ≃* alternatingGroup (Fin 6)) ∨
      (NineThreeFive M L₁ ∧ Nonempty (↥(barM M L₁) ≃* alternatingGroup (Fin 7))) ∨
      IsUThreeThree ↥(barM M L₁) := by
    rcases hrow with h | ⟨h5, h⟩ | h | h
    · exact Or.inl (hX h)
    · exact Or.inr (Or.inl ⟨h5, hX h⟩)
    · exact absurd h hnA8
    · exact Or.inr (Or.inr (hu33 h))
  have hJ := not_commutator_thompsonJ_le hpr h₁
  have hc5 := hCF G M S L₁ hpr.isKGroup.1 hpr.asc81bHyp h₁ hJ
    (by rcases hrow' with h | ⟨-, h⟩ | h; exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr h)])
  set V' := vModule S L₁ L₂ with hV'
  set VX := mModule M S with hVX
  have hVMe : IsElemAbelian 2 (Quasithin.omegaOneCenterOf (pCoreOf 2 M)) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hMV : M ≤ Subgroup.normalizer ((Quasithin.omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_of_characteristic_pCoreOf
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hVXV : VX ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M) :=
    mModule_le hpr.omegaOneCenter_le.1 hMV
  have hV'X : V' ≤ VX :=
    vModule_le (omegaOneCenterOf_le_mModule M S)
      (hpr.twoCore_le.trans (normalizer_mModule M S))
      (h₁.le.trans (normalizer_mModule M S)) (h₂.le.trans (normalizer_mModule M S))
  have hV'V : V' ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M) := hV'X.trans hVXV
  have hV2 : ∀ y ∈ V', y ^ 2 = 1 := fun y hy => hVMe.2 y (hV'V hy)
  have hVc : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, hV'V ha⟩ ⟨b, hV'V hb⟩)
  have hVXc : ∀ a ∈ VX, ∀ b ∈ VX, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, hVXV ha⟩ ⟨b, hVXV hb⟩)
  have hLV : L₁ ≤ Subgroup.normalizer (V' : Set G) := normalizer_vModule_L₁ S L₁ L₂
  have hLX : L₁ ≤ Subgroup.normalizer (VX : Set G) := h₁.le.trans (normalizer_mModule M S)
  have hirr' : HasIrreducibleCommutatorQuotient L₁ V' := hasIrr_vModule_of_mModule hctx h₁ h₂ hc5.1
  obtain ⟨x, hxV, hx1, hxU, hxC, hxL, hrk⟩ := exists_fixedVector_of_irreducibleQuotient h86 hctx
    h₁ h₂ hne hz₁ hirr'
  have hxV' : x ∈ V' := WeakBlockModuleData.commutator_le_of_le_normalizer hLV hxU
  have hthree : 3 ∣ Nat.card (L₁ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) := by
    rcases hrow' with e | ⟨h5, -⟩ | hX3
    · exact three_dvd_of_socleLE_alt_six h₁.le hLV hV2 hVc e.some
        (SocleLE.of_le hV'X hLX hLV (hc5.2.1 e)) hxV'
    · exact fixed_of_nineThreeFive_pair h86 hpr h₁ h5 hxV
    · exact three_dvd_of_socleLE_u33 hat h₁.le hLV hV2 hVc hX3
        (SocleLE.of_le hV'X hLX hLV (hc5.2.2 hX3)) hxV'
  have hb := one_le_pRank_of_dvd Nat.prime_three hthree
  exact ⟨x, hxV, hx1, hxL, by omega⟩

end Sep

end CFSG.AGLEmbeddingD2.McLaughlin
