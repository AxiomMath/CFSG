module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.ThompsonTwoCore
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def UPrimeHyp (p : ℕ) {X : Type*} [Group X] (X₀ : Subgroup X) : Prop :=
  ∀ L : Subgroup X, IsComponentOf L ⊤ → ¬ L ≤ X₀ →
    (∀ N : Subgroup X, N ≤ X₀ ⊓ L → (N.subgroupOf (X₀ ⊓ L)).Normal →
        p.Coprime (Nat.card N) → N = ⊥) ∧
      ∀ w : X, w ∈ Subgroup.normalizer (L : Set X) →
        w ∈ Subgroup.centralizer ((X₀ ⊓ L : Subgroup X) : Set X) →
          w ∈ Subgroup.centralizer (L : Set X)

theorem primeComplementCore_eq_bot_of_forall {X : Type*} [Group X] [Finite X] {p : ℕ}
    {X₀ : Subgroup X}
    (h : ∀ W : Subgroup X, W ≤ X₀ → (W.subgroupOf X₀).Normal → p.Coprime (Nat.card W) →
      W = ⊥) :
    primeComplementCore (G := X₀) p = ⊥ := by
  have hsub : ((primeComplementCore (G := X₀) p).map X₀.subtype).subgroupOf X₀ =
      primeComplementCore (G := X₀) p :=
    Subgroup.comap_map_eq_self_of_injective X₀.subtype_injective _
  have hW := h ((primeComplementCore (G := X₀) p).map X₀.subtype) (Subgroup.map_subtype_le _)
    (by rw [hsub]; infer_instance)
    (by rw [Subgroup.card_map_of_injective X₀.subtype_injective]
        exact primeComplementCore_coprime p)
  exact (Subgroup.map_eq_bot_iff_of_injective _ X₀.subtype_injective).mp hW

theorem ReducedNongeneration.primeComplementCore_eq_bot_of_uPrimeHyp {p : ℕ} {X : Type*}
    [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hU : UPrimeHyp p X₀) : primeComplementCore (G := X₀) p = ⊥ :=
  primeComplementCore_eq_bot_of_forall (h.primeComplementCore_eq_bot
    (fun L hL hLX₀ => (hU L hL hLX₀).1) (fun L hL hLX₀ => (hU L hL hLX₀).2))

theorem isKGroup_of_catalogSimpleSections {X : Type*} [Group X]
    (hX : CatalogSimpleSections X) : Open.IsKGroup X :=
  fun K L _ hN hs hn => hX K (L.subgroupOf K) hN hs hn

theorem isElemAbelian_omegaOneCenterOf {G : Type*} [Group G] (X : Subgroup G) :
    IsElemAbelian 2 (omegaOneCenterOf X) := by
  have hle : omegaOneCenterOf X ≤ centerOf X := (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hcomm : ∀ a ∈ omegaOneCenterOf X, ∀ b ∈ omegaOneCenterOf X, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hle hb).2 a (hle ha).1
  refine ⟨isMulCommutative_subgroup_iff.mpr hcomm, fun x hx => ?_⟩
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hcomm a ha b hb) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1Escape.toPhaseThreeU (h : D1Escape p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : D1PhaseThree p P M H R :=
  { h with
    glob := hglob
    twoCore_inf := h.twoCore_inf_eq_of_primeCore_inf_eq hU }

theorem D1Escape.toPhaseThree (h : D1Escape p P M H R) (hglob : D1Global G)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : D1PhaseThree p P M H R :=
  h.toPhaseThreeU hglob.toAGLGlobal hU

theorem D1Extremal.toPhaseThreeU (h : D1Extremal p P M H R)
    (hglob : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : D1PhaseThree p P M H R :=
  h.toD1Escape.toPhaseThreeU hglob hU

theorem D1Extremal.toPhaseThree (h : D1Extremal p P M H R) (hglob : D1Global G)
    (hU : GLBPrimeCore p (H ⊓ M) = GLBPrimeCore p H) : D1PhaseThree p P M H R :=
  h.toPhaseThreeU hglob.toAGLGlobal hU

theorem D1ComponentConfig.toPhaseThree {Rbar : Sylow p (↥H ⧸ primeComplementCore (G := H) p)}
    (h : D1ComponentConfig p P M H R Rbar)
    (hU : UPrimeHyp p (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)))) :
    D1PhaseThree p P M H R :=
  h.ext.toPhaseThree h.glob
    (h.ext.primeCore_inf_eq_iff.mpr (h.red.primeComplementCore_eq_bot_of_uPrimeHyp hU))

omit [Finite G] in
theorem TwoLocalPair.isKGroup_of_isKProper (h : TwoLocalPair M H) (hK : Open.IsKProper G) :
    Open.IsKGroup ↥M ∧ Open.IsKGroup ↥H := by
  have hM : M ≠ ⊤ := fun hM => h.not_le (hM ▸ le_top)
  have hH : H ≠ ⊤ := fun hH => h.inf_lt_right.ne (by rw [hH, top_inf_eq])
  exact ⟨isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hK M hM),
    isKGroup_of_catalogSimpleSections (catalogSimpleSections_of_isKProper hK H hH)⟩

theorem D1Escape.isKGroup_of_isKProper (h : D1Escape p P M H R) (hK : Open.IsKProper G) :
    Open.IsKGroup ↥M ∧ Open.IsKGroup ↥H :=
  h.toTwoLocalPair.isKGroup_of_isKProper hK

theorem D1PhaseThree.isKGroup (h : D1PhaseThree p P M H R) :
    Open.IsKGroup ↥M ∧ Open.IsKGroup ↥H :=
  h.isKGroup_of_isKProper h.glob.kProper

theorem D1Escape.charTwo_of_isCharTwoType (h : D1Escape p P M H R)
    (hchar : Open.IsCharTwoType G) :
    CharTwo M ∧ CharTwo H :=
  ⟨hchar M h.maxTwoLocal_M.1, hchar H h.maxTwoLocal_H.1⟩

theorem D1PhaseThree.charTwo (h : D1PhaseThree p P M H R) : CharTwo M ∧ CharTwo H :=
  h.charTwo_of_isCharTwoType h.glob.charTwo

omit [Finite G] in
theorem TwoLocalPair.inf_eq_inf_normalizer_twoCore (h : TwoLocalPair M H) :
    H ⊓ M = M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  rw [h.normalizer_twoCore_H, inf_comm]

theorem D1Escape.inf_eq_inf_normalizer_twoCore (h : D1Escape p P M H R) :
    H ⊓ M = M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  h.toTwoLocalPair.inf_eq_inf_normalizer_twoCore

theorem TwoLocalPair.normalizer_thompsonJ_eq (h : TwoLocalPair M H) :
    M ⊓ Subgroup.normalizer (thompsonJ (pCoreOf 2 H) : Set G) = H ⊓ M ∧
      Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) = H := by
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  refine ⟨?_, ?_⟩
  · rw [maxTwoLocal_normalizer_char_eq h.maxTwoLocal_H (Quasithin.B6.thompsonJ_le _)
      (QuasithinUnique.Setup.thompsonJ_ne_bot h2 h.twoCore_H_ne_bot)
      (QuasithinUnique.Setup.characteristic_thompsonJ _), inf_comm]
  · exact maxTwoLocal_normalizer_char_eq h.maxTwoLocal_H
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.omegaOneCenterOf_ne_bot h2 h.twoCore_H_ne_bot)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)

theorem D1Escape.normalizer_thompsonJ_eq (h : D1Escape p P M H R) :
    M ⊓ Subgroup.normalizer (thompsonJ (pCoreOf 2 H) : Set G) = H ⊓ M ∧
      Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) = H :=
  h.toTwoLocalPair.normalizer_thompsonJ_eq

theorem D1Escape.primeCore_le_inf' (h : D1Escape p P M H R) :
    GLBPrimeCore p H ≤ H ⊓ M ∧ H ⊓ Subgroup.normalizer (pCoreOf 2 M : Set G) = H ⊓ M :=
  ⟨_root_.le_inf (glbPrimeCore_le p H) h.primeCore_le, h.inf_eq_inf_normalizer_twoCore_M.symm⟩

theorem D1PhaseThree.toTwoLocalPhaseThree (h : D1PhaseThree p P M H R) :
    TwoLocalPhaseThree M H :=
  { h.toTwoLocalPair with
    charTwo_M := h.glob.charTwo M h.maxTwoLocal_M.1
    twoCore_inf := h.twoCore_inf }

omit [Finite G] in
theorem TwoLocalPhaseThree.twoCore_inf_normalizer (h : TwoLocalPhaseThree M H) :
    pCoreOf 2 (M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) = pCoreOf 2 H := by
  rw [← h.inf_eq_inf_normalizer_twoCore, h.twoCore_inf]

omit [Finite G] in
theorem TwoLocalPhaseThree.asc81bHyp (h : TwoLocalPhaseThree M H) : Asc81bHyp M (pCoreOf 2 H) where
  twoRadical := ⟨h.twoCore_le, h.twoCore_H_ne_bot, h.twoCore_inf_normalizer.symm⟩
  charTwo := h.charTwo_M
  cgs := by rw [h.cgsIn_eq, h.normalizer_twoCore_H]

theorem TwoLocalPhaseThree.twoCore_M_lt (h : TwoLocalPhaseThree M H) : pCoreOf 2 M < pCoreOf 2 H :=
  lt_of_le_of_ne (h.twoCore_M_le h.twoCore_inf) h.twoCore_M_ne

theorem TwoLocalPhaseThree.omegaOneCenter_le (h : TwoLocalPhaseThree M H) :
    omegaOneCenterOf (pCoreOf 2 H) ≤ omegaOneCenterOf (pCoreOf 2 M) ∧
      M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) ≤ H ⊓ M := by
  have hQS := h.twoCore_M_le h.twoCore_inf
  have hZ : centerOf (pCoreOf 2 H) ≤ centerOf (pCoreOf 2 M) := fun x hx =>
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := Subgroup.centralizer_le hQS hx.2
    ⟨h.charTwo_M ⟨h.twoCore_le hx.1, hxC⟩, hxC⟩
  have hΩ : omegaOneCenterOf (pCoreOf 2 H) ≤ omegaOneCenterOf (pCoreOf 2 M) :=
    Subgroup.closure_mono fun x hx => ⟨hZ hx.1, hx.2⟩
  refine ⟨hΩ, fun x hx => ⟨?_, hx.1⟩⟩
  rw [← h.normalizer_thompsonJ_eq.2]
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hΩ hx.2)

theorem TwoLocalPhaseThree.conj_twoCore_M_le (h : TwoLocalPhaseThree M H) :
    ∀ g ∈ H, (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 H ∧
      (g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) ↔ g ∈ M) := by
  intro g hg
  refine ⟨?_, by rw [h.normalizer_twoCore_M]⟩
  rintro _ ⟨x, hx, rfl⟩
  have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [h.normalizer_twoCore_H]
    exact hg
  simpa [MulAut.conj_apply] using
    (Subgroup.mem_normalizer_iff.mp hgN x).mp (h.twoCore_M_le h.twoCore_inf hx)

theorem TwoLocalPhaseThree.inf_centralizer_le_twoCore_M (h : TwoLocalPhaseThree M H) :
    pCoreOf 2 H ⊓ (M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G)) ≤
      pCoreOf 2 M := by
  set C := M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G)
  have hCS : C ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [h.normalizer_twoCore_H]
    exact h.omegaOneCenter_le.2.trans inf_le_left
  have hnorm : ((pCoreOf 2 H ⊓ C).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      ((le_inf hCS Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have h2 : IsPGroup 2 (pCoreOf 2 H ⊓ C : Subgroup G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hle : pCoreOf 2 H ⊓ C ≤ pCoreOf 2 C :=
    normal_pGroup_le_pCoreOf 2 _ C inf_le_right hnorm h2
  have hMV : M ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) :=
    le_normalizer_of_characteristic_pCoreOf (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hMC : M ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf Subgroup.le_normalizer (hMV.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact hle.trans (pCoreOf_le_of_normal_subgroupOf 2 C M inf_le_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hMC))

theorem TwoLocalPhaseThree.exists_ffOffender (h : TwoLocalPhaseThree M H) :
    ∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 H) A ∧
      ¬ A ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) ∧
      Nat.card (omegaOneCenterOf (pCoreOf 2 M)) *
          Nat.card (A ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) :
            Subgroup G) ≤
        Nat.card A * Nat.card (omegaOneCenterOf (pCoreOf 2 M) ⊓
          Subgroup.centralizer (A : Set G) : Subgroup G) := by
  have hVS : omegaOneCenterOf (pCoreOf 2 M) ≤ pCoreOf 2 H :=
    (QuasithinUnique.Setup.omegaOneCenterOf_le _).trans (h.twoCore_M_le h.twoCore_inf)
  obtain ⟨A, hA, hAQ⟩ := h.exists_isMaxElemAbelian_not_le h.twoCore_inf
  refine ⟨A, hA, fun hAV => hAQ ?_, ?_⟩
  · exact (le_inf hA.1 (le_inf (hA.1.trans h.twoCore_le) hAV)).trans
      h.inf_centralizer_le_twoCore_M
  · have h1 := card_le_relIndex_mul_card (isElemAbelian_omegaOneCenterOf _) hVS hA
    have h2 := Subgroup.relIndex_mul_card
      (A ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G)) A
    rw [inf_of_le_left inf_le_left] at h2
    calc _ ≤ _ := Nat.mul_le_mul_right _ h1
      _ = _ := by rw [← h2]; ring

theorem D1PhaseThree.twoCore_inf_normalizer (h : D1PhaseThree p P M H R) :
    pCoreOf 2 (M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G)) = pCoreOf 2 H :=
  h.toTwoLocalPhaseThree.twoCore_inf_normalizer

theorem D1PhaseThree.asc81bHyp (h : D1PhaseThree p P M H R) : Asc81bHyp M (pCoreOf 2 H) :=
  h.toTwoLocalPhaseThree.asc81bHyp

theorem D1PhaseThree.twoCore_M_lt (h : D1PhaseThree p P M H R) : pCoreOf 2 M < pCoreOf 2 H :=
  h.toTwoLocalPhaseThree.twoCore_M_lt

theorem D1PhaseThree.omegaOneCenter_le (h : D1PhaseThree p P M H R) :
    omegaOneCenterOf (pCoreOf 2 H) ≤ omegaOneCenterOf (pCoreOf 2 M) ∧
      M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.omegaOneCenter_le

theorem D1PhaseThree.conj_twoCore_M_le (h : D1PhaseThree p P M H R) :
    ∀ g ∈ H, (pCoreOf 2 M).map (MulAut.conj g).toMonoidHom ≤ pCoreOf 2 H ∧
      (g ∈ Subgroup.normalizer (pCoreOf 2 M : Set G) ↔ g ∈ M) :=
  h.toTwoLocalPhaseThree.conj_twoCore_M_le

theorem D1PhaseThree.inf_centralizer_le_twoCore_M (h : D1PhaseThree p P M H R) :
    pCoreOf 2 H ⊓ (M ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G)) ≤
      pCoreOf 2 M :=
  h.toTwoLocalPhaseThree.inf_centralizer_le_twoCore_M

theorem D1PhaseThree.exists_ffOffender (h : D1PhaseThree p P M H R) :
    ∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 H) A ∧
      ¬ A ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) ∧
      Nat.card (omegaOneCenterOf (pCoreOf 2 M)) *
          Nat.card (A ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 M) : Set G) :
            Subgroup G) ≤
        Nat.card A * Nat.card (omegaOneCenterOf (pCoreOf 2 M) ⊓
          Subgroup.centralizer (A : Set G) : Subgroup G) :=
  h.toTwoLocalPhaseThree.exists_ffOffender

end CFSG.AGLEmbedding
