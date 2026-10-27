module

public import CFSG.GH74.GLS.SP.Assembly
public import CFSG.GH74.GLS.SP.GlueMap
public import CFSG.GH74.GLS.SP.SpRGD

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem ker_spProj_le_spT (F : Type) [Field F] : (spProj F).ker ≤ spT F := by
  rw [ker_spProj]
  exact center_le_spT F

theorem spGlueData_model (F : Type) [Field F] (hF : 4 ≤ Nat.card F) :
    SPGlueData (StatedProj (StatedSp 2 F)) F hF := by
  refine ⟨(spT F).map (spProj F), spProj F (weylRep 2 F 0), spProj F (weylRep 2 F 1),
    (spU F).map (spProj F), fun i => (octGroup F i).map (spProj F),
    (spRGD2 F).map (spProj F) (ker_spProj_le_spT F) (spU_inf_ker F),
    (spRGD2 F).map_gen (spProj F) (spProj_surjective F) (ker_spProj_le_spT F) (spU_inf_ker F)
      (spRGD2_gen F),
    MulEquiv.subgroupCongr (modelSystem_U F hF).symm, ?_⟩
  intro i _ _ x
  rw [modelSystem_root F hF i]
  rfl

theorem SPGlueData.of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {F : Type}
    [Field F] {hF : 4 ≤ Nat.card F} (h : SPGlueData G' F hF) : SPGlueData G F hF := by
  obtain ⟨H, r₁, r₂, U, root, R, hgen, φ, hφ⟩ := h
  have hker : (e.symm : G' →* G).ker ≤ H := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact bot_le
  have hU : U ⊓ (e.symm : G' →* G).ker = ⊥ := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.symm.injective]
    exact inf_bot_eq U
  refine ⟨H.map (e.symm : G' →* G), (e.symm : G' →* G) r₁, (e.symm : G' →* G) r₂,
    U.map (e.symm : G' →* G), fun i => (root i).map (e.symm : G' →* G),
    R.map (e.symm : G' →* G) hker hU,
    R.map_gen (e.symm : G' →* G) e.symm.surjective hker hU hgen,
    (MulEquiv.subgroupMap e.symm U).symm.trans φ, ?_⟩
  intro i h1 h4 x
  have hyx : (((MulEquiv.subgroupMap e.symm U).symm x : U) : G') = e (x : G) := by
    simp [MulEquiv.subgroupMap_symm_apply]
  have key := hφ i h1 h4 ((MulEquiv.subgroupMap e.symm U).symm x)
  rw [hyx] at key
  have hx : (x : G) ∈ (root i).map (e.symm : G' →* G) ↔ e (x : G) ∈ root i := by
    have := Subgroup.mem_map_equiv (f := e.symm) (K := root i) (x := (x : G))
    simpa using this
  rw [hx]
  exact key

theorem spGlueData_iff {G : Type} [Group G] [IsSimpleGroup G] {F : Type} [Field F]
    (hF : 4 ≤ Nat.card F) :
    SPGlueData G F hF ↔ Nonempty (G ≃* StatedProj (StatedSp 2 F)) :=
  ⟨fun h => sp_of_glueData h, fun ⟨e⟩ => SPGlueData.of_equiv e (spGlueData_model F hF)⟩

@[expose] def SPModelIso : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs] (F : Type) [Field F] [Finite F] (_ : 4 ≤ Nat.card F),
      Odd (Nat.card F) → Nonempty (Gs ≃* StatedProj (StatedSp 2 F)) →
        IsTwoCentralClassicalType G Gs → Nonempty (G ≃* StatedProj (StatedSp 2 F))

theorem spLocalGlue_iff : SPLocalGlue ↔ SPModelIso := by
  constructor
  · intro h G _ _ hK Gs _ F _ _ hF hodd e hT
    have := hK.1
    exact sp_of_glueData (h G hK Gs F hF hodd e hT)
  · intro h G _ _ hK Gs _ F _ _ hF hodd e hT
    have := hK.1
    obtain ⟨e'⟩ := h G hK Gs F hF hodd e hT
    exact SPGlueData.of_equiv e' (spGlueData_model F hF)

end CFSG.GH74.GLS.SP
