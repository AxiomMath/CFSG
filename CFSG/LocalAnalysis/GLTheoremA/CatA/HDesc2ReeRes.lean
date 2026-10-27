module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2ReeRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Lvl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res

public section


namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Blueprint TauCeti CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem twoLocalRankLE1_of_mulEquiv {S Γ : Type} [Group S] [Group Γ] (e : S ≃* Γ) {r : ℕ}
    (h : ∀ E T : Subgroup Γ, IsElemAbelian r E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set Γ) → Nat.card E ≤ r) : TwoLocalRankLE1 r S := by
  intro E T hE hT hT1 hN
  have hT'1 : T.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hT1 ((Subgroup.map_eq_bot_iff_of_injective T e.injective).mp hbot)
  have hEN : E.map e.toMonoidHom ≤ Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup Γ) : Set Γ) :=
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map e.toMonoidHom)
  have := h _ _ (CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom) (hT.map e.toMonoidHom) hT'1 hEN
  rwa [← Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv] at this

theorem exists_reeGamma_of_catalog (ctx : LvCtx) {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime), 2 * m + 1 = 2 * a + 1 ∧
      Nat.card K = 2 ^ (2 * a + 1) ∧
      Nonempty ((CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group ≃* F4.reeGamma K a) := by
  have hM : LieModel (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group .twistedF4 0 2 (2 * m + 1) :=
    model_reeF4 ctx hv (MulEquiv.refl _)
  obtain ⟨-, hR⟩ := LieModel.reeTitsModel hM (by decide)
  obtain ⟨a, K, _, _, _, -, hfa, hK, hE⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hR
  exact ⟨a, K, inferInstance, inferInstance, inferInstance, hfa, by rw [← hfa]; exact hK, hE⟩

theorem reeTitsRes_of_ctx (ctx : LvCtx) : ReeTitsRes := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨a, K, _, _, _, hfa, hK, ⟨e⟩⟩ := exists_reeGamma_of_catalog ctx hv
    have ha : a = 1 := by omega
    exact twoLocalRankLE1_of_mulEquiv e fun E T hE hT2 hT hEN =>
      reeGamma_card_le_three hK ha hE hT2 hT hEN
  · obtain ⟨a, K, _, _, _, hfa, hK, ⟨e⟩⟩ := exists_reeGamma_of_catalog ctx hv
    have ha : a = 2 := by omega
    exact twoLocalRankLE1_of_mulEquiv e fun E T hE hT2 hT hEN =>
      reeGamma_card_le_five hK ha hE hT2 hT hEN

end CFSG.LocalAnalysis.GLTheoremA.HDesc
