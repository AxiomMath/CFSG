module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecLin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X7a CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Model

theorem exists_cover_of_model
    {Λ : Type} [Group Λ] [Finite Λ] (hperf : Group.IsPerfect Λ)
    (hodd : Odd (Nat.card (Subgroup.center Λ))) {f : ℕ} (hf : 1 ≤ f)
    (hmodel : StatedClassicalModel (Λ ⧸ Subgroup.center Λ) .PSL 3 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL(3, F) →* Λ),
      Nat.card F = 2 ^ f ∧ Cover φ := by
  obtain ⟨-, F, iF, iFin, hFcard, ⟨e'⟩⟩ := hmodel
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hFcard
  have := hperf
  obtain ⟨φ', hsurj, hker, hmap⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
    (K := F) (n := 3) (by norm_num) hodd e'
  let ε : SL(3, F) ≃* StatedSL 3 F := specialLinearGroupEquivStatedSL 3 F
  refine ⟨F, iF, iFin, φ'.comp ε.toMonoidHom, hFcard, ?_, ?_, ?_⟩
  · exact hsurj.comp ε.surjective
  · intro x hx
    have h1 : ε x ∈ φ'.ker := hx
    have h2 : ε x ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) := hker h1
    rw [← map_center_eq_statedScalars 3 F] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    have : y = x := ε.injective hyx
    rw [scalars_eq_center]
    exact this ▸ hy
  · rw [scalars_eq_center, ← Subgroup.map_map]
    have hc := map_center_eq_statedScalars 3 F
    exact (congrArg (Subgroup.map φ') hc).trans hmap

end Model

theorem actualLinearThreeSelfDualSections
    : ActualLinearThreeSelfDualSections := by
  intro V _ _ H T M E hFF hns L hL f hf hmodel
  classical
  have hfin : Finite (MulAut V) :=
    Finite.of_injective (fun g : MulAut V => (g : V → V)) DFunLike.coe_injective
  have hLay : ActorLayer V H T M := Layer.Actor.actorLayerProp V H T M E hFF hns
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := hLay.odd_card_center hL
  have hqL : CFSG.IsQuasisimple ↥L := isQuasisimple_of_isComp hL
  obtain ⟨F, iF, iFin, φ₀, hFcard, h₀⟩ :=
    exists_cover_of_model hqL.1 hZodd (by omega : 1 ≤ f) hmodel
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hFcard
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ f := by rw [Fintype.card_eq_nat_card]; exact hFcard
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hFF.elementary
  obtain ⟨ho2, hsyl, hnn, hmax, hE⟩ := Layer.Actor.map_hypotheses θ hFF.o2_trivial hFF.sylow
    hFF.not_normal hFF.max hFF.offender
  have hns' : ¬ Group.IsSolvable ↥(H.map (binPsi θ).toMonoidHom) := fun h =>
    hns ((solvable_map_mulEquiv_iff (binPsi θ)).1 h)
  have hL' : IsComponentIn (L.map (binPsi θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) :=
    (Layer.Actor.isComponentIn_map_iff (binPsi θ)).2 ((Layer.Actor.isComp_iff L H).1 hL)
  let eψ : ↥L ≃* ↥(L.map (binPsi θ).toMonoidHom) :=
    L.equivMapOfInjective (binPsi θ).toMonoidHom (binPsi θ).injective
  have h' : Cover (eψ.toMonoidHom.comp φ₀) := h₀.congr eψ
  obtain ⟨U, iU1, iU2, iU3, ρL', A', hker, hirr, hsd, hel, hne, hint, hoffU⟩ :=
    section_linear hns' ho2 hsyl hnn hmax.1 hmax.2.1 hmax.2.2 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hL'
      hf hF h'
  exact ⟨F, iF, iFin, φ₀, U, iU1, iU2, iU3, ρL'.comp eψ.toMonoidHom, A', hFcard, hZodd,
    h₀.surjective, h₀.ker_le, h₀.map_scalars, hker, hirr, hsd, hel, hne, hint, hoffU⟩

end CFSG.QuasithinUnique.Setup.X7Sec
