module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open scoped MatrixGroups

section Images

variable {K : Type} [Field K] {F : Type} [Field F] [CharP F 2]

theorem map_std_rootTorusSp_zero_eq (σ : K ≃+* F) :
    (((rootTorusSp K 0).map (MonoidHom.id (StatedSp 2 K))).map
        (statedSpMap (σ : K →+* F) 2)).map (spModelSL 2 F) = stdTorusSL F 0 := by
  rw [Subgroup.map_id]
  ext d
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    exact mem_stdTorusSL.2 ⟨Units.map (σ : K →+* F) κ, by rw [statedSpMap_rootTorusHom]⟩
  · intro hd
    obtain ⟨μ, rfl⟩ := mem_stdTorusSL.1 hd
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    refine ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp 0 κ, rfl⟩, ?_⟩
    change spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (rootTorusHom K 2 0 κ)) = _
    rw [statedSpMap_rootTorusHom, hμ]

theorem map_std_siegelTorus_eq [CharP K 2] (σ : K ≃+* F) :
    (((siegelTorus K 2).map (MonoidHom.id (StatedSp 2 K))).map
        (statedSpMap (σ : K →+* F) 2)).map (spModelSL 2 F) = twTorusSL F 0 := by
  rw [Subgroup.map_id]
  ext d
  constructor
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩
    refine mem_twTorusSL.2 ⟨Units.map (σ : K →+* F) s, ?_⟩
    change _ = spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => s)))
    rw [tauSp_rootTorusHom_zero, statedSpMap_diagSp]
    congr 2
    funext i
    fin_cases i <;> rfl
  · intro hd
    obtain ⟨μ, rfl⟩ := mem_twTorusSL.1 hd
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    refine ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, ?_⟩
    change spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (diagSp K 2 (fun _ => κ))) = _
    rw [tauSp_rootTorusHom_zero, statedSpMap_diagSp, hμ]
    congr 2
    funext i
    fin_cases i <;> rfl

end Images

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP K 2] in
theorem pieceCore_two_eq_of_standard (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({2} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 2) := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  refine pieceCore_eq_modelToG_of_eq_map hK e (Finset.mem_singleton_self 2) σ Φ
    (card_offPlaneSL 0) ?_
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ (MonoidHom.id _) Φ hN1
    (rootTorusSp K 0) leviTorusSp_two_le_sup map_rootTorusSp_zero_le_leviTorusSp_two
    (by rw [map_std_rootTorusSp_zero_eq]; exact perfectCore_centralizer_stdTorusSL hF4 0)

omit [Finite K] in
theorem pieceCore_one_eq_of_standard (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 0)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 0) : G) =
        ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) :
    pieceCore e ({1} : Finset (Fin 3)) =
      ((blockSpecialLinear (K := F) (twBlockSL 0) ⊔
        blockSpecialLinear (K := F) (twBlockSL 0)ᶜ).map Φ.toMonoidHom).map
          (neighbourCore e 0).subtype := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_N1 hK e (k := 0) (by decide) σ (MonoidHom.id _) Φ hN1
    (siegelTorus K 2) leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one
    (by rw [map_std_siegelTorus_eq]; exact perfectCore_centralizer_twTorusSL hF4 0)

omit [Finite K] in
theorem pieceCore_zero_eq_of_standard (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    (σ : K ≃+* F) (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e 2)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 x)) : neighbourCore e 2) : G) =
        ((e.symm (complSpEquiv 2 x : complSp K 2) : L) : G)) :
    pieceCore e ({0} : Finset (Fin 3)) =
      ((blockSpecialLinear (K := F) (twBlockSL 0) ⊔
        blockSpecialLinear (K := F) (twBlockSL 0)ᶜ).map Φ.toMonoidHom).map
          (neighbourCore e 2).subtype := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  exact pieceCore_eq_map_of_N1 hK e (k := 2) (by decide) σ (MonoidHom.id _) Φ hN1
    (siegelTorus K 2) leviTorusSp_zero_le_sup map_siegelTorus_two_le_leviTorusSp_zero
    (by rw [map_std_siegelTorus_eq]; exact perfectCore_centralizer_twTorusSL hF4 0)

end Pieces

theorem spThreeLinearEvenStandardInput_of_nodes
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin 3, RootKindSp e t f k .linearEven) → SpThreeStandard e →
          SpLinearNodeSystem e f 5) :
    SpThreeLinearEvenStandardInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  exact spGlobalCoverType_of_nodeSystem hf (by norm_num) (Or.inl ⟨rfl, rfl⟩)
    (h G L hset f K hKc hf e t ht hKt hroot hstd)

end CFSG.SeitzReduction.SymplecticPilot
