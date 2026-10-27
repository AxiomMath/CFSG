module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Abstract
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer

public section

namespace CFSG.QuasithinUnique.Setup.X3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer CFSG.SectionRank

@[expose] def SixPointQuotient : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (H : Type) [Group H] [Finite H]
    (ρ : H →* (W ≃ₗ[ZMod 2] W)), Function.Injective ρ → ∀ L A : Subgroup H, L.Normal →
    CFSG.IsQuasisimple ↥L →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) →
    Subgroup.centralizer (L : Set H) = (Subgroup.center ↥L).map L.subtype →
    Odd (Nat.card (Subgroup.center ↥L)) → A ≠ ⊥ → CFSG.IsElementaryAbelian 2 ↥A → ⁅L, A⁆ = L →
    Nat.card W ≤ weight ρ A →
    (∀ B : Subgroup H, ⊥ < B → B < A → weight ρ B < weight ρ A) →
    ∃ θ : H →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥L).map L.subtype ∧
      L.map θ = alternatingGroup (Fin 6)

theorem no_A6_component_linear (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hSix : SixPointQuotient) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {H T M E : Subgroup (W ≃ₗ[ZMod 2] W)} (hsqtk : IsSQTKCat ↥H) (hns : ¬ Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (W ≃ₗ[ZMod 2] W), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEne : E ≠ ⊥) (hEel : CFSG.IsElementaryAbelian 2 E)
    (hEoff : Nat.card W ≤ weight (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E)
    {L : Subgroup (W ≃ₗ[ZMod 2] W)} (hL : IsComponentIn L H) :
    ¬ Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) := by
  classical
  intro hA6
  have : Finite (W ≃ₗ[ZMod 2] W) := finite_linearEquiv
  have lay := Layer.Final.nonsolvable_layer hns hO2 hT hTn hTM hMH hmax hEH hEne hEel hEoff
  have hLH : L ≤ H := hL.1
  have hL₀ : CFSG.IsComponent (L.subgroupOf H) := hL.2
  have e₀ : Nonempty (↥(L.subgroupOf H) ⧸ Subgroup.center ↥(L.subgroupOf H) ≃*
      alternatingGroup (Fin 6)) := by
    obtain ⟨e⟩ := hA6
    exact ⟨(centerQuotientCongr (Subgroup.subgroupOfEquivOfLe hLH)).trans e⟩
  have hT' : IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) :=
    Layer.isSylowTwoOf_subgroupOf_top' hT
  have hTM' : T.subgroupOf H ≤ M.subgroupOf H := fun x hx => hTM hx
  have hMX' : M.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    have : H ≤ M := Subgroup.subgroupOf_eq_top.1 h
    exact hMH.not_ge this
  have hmax' : ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
    intro Y hTY hY
    have h1 : T ≤ Y.map H.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hT.1]
      exact Subgroup.map_mono hTY
    have h2 : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun h => ?_
      apply hY.ne
      have : Y.map H.subtype = (⊤ : Subgroup ↥H).map H.subtype := by
        rw [h]
        exact (map_subtype_top H).symm
      exact Subgroup.map_injective H.subtype_injective this
    have h3 := hmax _ h1 h2
    intro x hx
    exact h3 ⟨x, hx, rfl⟩
  have hKL := lay.K_eq_layer
  have hgf : CFSG.generalizedFitting ↥H = CFSG.layer ↥H := lay.K_eq_genFit.symm.trans hKL
  have hC : (Subgroup.center ↥(CFSG.layer ↥H)).map (CFSG.layer ↥H).subtype ≤ M.subgroupOf H := by
    rw [← hKL, lay.C_eq_center]
    intro x hx
    simpa using hx 1 (Subgroup.mem_top _)
  have hCodd : Odd (Nat.card (Subgroup.center ↥(CFSG.layer ↥H))) := by
    have h1 := lay.C_odd
    rw [← lay.C_eq_center, Subgroup.card_map_of_injective
      ((oddGen H).subgroupOf H).subtype_injective] at h1
    rw [← hKL]
    exact h1
  have hw : ∀ B : Subgroup ↥H, weight H.subtype B = weight (MonoidHom.id (W ≃ₗ[ZMod 2] W))
      (B.map H.subtype) := fun B => weight_comp_subtype (MonoidHom.id (W ≃ₗ[ZMod 2] W)) H B
  have hθ : (L.subgroupOf H).Normal →
      Subgroup.centralizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) =
        (Subgroup.center ↥(L.subgroupOf H)).map (L.subgroupOf H).subtype →
      Odd (Nat.card (Subgroup.center ↥(L.subgroupOf H))) →
      ∃ θ : ↥H →* Equiv.Perm (Fin 6), θ.ker = (Subgroup.center ↥(L.subgroupOf H)).map
          (L.subgroupOf H).subtype ∧ (L.subgroupOf H).map θ = alternatingGroup (Fin 6) := by
    intro hN hcen hodd
    obtain ⟨A, hA, hAL⟩ := lay.comp_offender (L.subgroupOf H) hL₀
    obtain ⟨hAH, hAne, hAel, hAoff, hAstrict⟩ := hA
    have hmapA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
    refine hSix W ↥H H.subtype H.subtype_injective (L.subgroupOf H) (A.subgroupOf H) hN hL₀.1 e₀
      hcen hodd ?_ ?_ ?_ ?_ ?_
    · intro h
      apply hAne
      rw [← hmapA, h, Subgroup.map_bot]
    · exact isElementaryAbelian_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAH) hAel
    · apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, hmapA]
      exact hAL
    · rw [hw, hmapA]
      exact hAoff
    · intro B hB0 hBA
      rw [hw B, hw (A.subgroupOf H), hmapA]
      refine hAstrict (B.map H.subtype) ?_ ?_
      · refine bot_lt_iff_ne_bot.mpr fun h => (bot_lt_iff_ne_bot.mp hB0) ?_
        exact (Subgroup.map_eq_bot_iff_of_injective B H.subtype_injective).mp h
      · rw [← hmapA]
        exact (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).mpr hBA
  exact false_of_A6_layer hcent hcat hsqtk hT' hTM' hMX' hmax' hgf hC hCodd lay.comp_trans hL₀ e₀
    hθ

theorem isSQTKCat_of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : IsSQTKCat Y) : IsSQTKCat X :=
  CFSG.SectionRank.IsSQTKCat.of_mulEquiv h e

theorem no_A6_component (hcent : OddKernelCentralization) (hcat : CatalogStepHyp)
    (hSix : SixPointQuotient) {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (hFF : Family.FFHyp V H T M E) (hns : ¬ Group.IsSolvable ↥H) (hsqtk : IsSQTKCat ↥H)
    {L : Subgroup (MulAut V)} (hL : Family.IsComp L H) :
    ¬ Nonempty (Family.CQ L ≃* alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hFF.elementary
  obtain ⟨ho2, hsyl, hnn, hmax, hE⟩ := Layer.Actor.map_hypotheses θ hFF.o2_trivial hFF.sylow
    hFF.not_normal hFF.max hFF.offender
  have hns' : ¬ Group.IsSolvable ↥(H.map (binPsi θ).toMonoidHom) := fun h =>
    hns ((solvable_map_mulEquiv_iff (binPsi θ)).1 h)
  have hsqtk' : IsSQTKCat ↥(H.map (binPsi θ).toMonoidHom) :=
    have : Finite ↥H := inferInstance
    isSQTKCat_of_mulEquiv (((binPsi θ).subgroupMap H).symm) hsqtk
  have hL' : IsComponentIn (L.map (binPsi θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) :=
    (Layer.Actor.isComponentIn_map_iff (binPsi θ)).2 ((Layer.Actor.isComp_iff L H).1 hL)
  intro hA6
  obtain ⟨e⟩ := hA6
  exact no_A6_component_linear hcent hcat hSix hsqtk' hns' ho2 hsyl hnn hmax.1 hmax.2.1 hmax.2.2
    hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hL'
    ⟨(centerQuotientCongr (L.equivMapOfInjective (binPsi θ).toMonoidHom
      (binPsi θ).injective)).symm.trans e⟩

end CFSG.QuasithinUnique.Setup.X3
