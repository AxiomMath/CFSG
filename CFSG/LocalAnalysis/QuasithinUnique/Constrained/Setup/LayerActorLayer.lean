module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative commutatorElement

section Generic

theorem kerIn_top_eq_normalCore {X : Type*} [Group X] (S : Subgroup X) :
    kerIn S ⊤ = S.normalCore :=
  Subgroup.ext fun _ => ⟨fun h b => h b trivial, fun h b _ => h b⟩

variable {G : Type} [Group G]

theorem isComp_iff (L H : Subgroup G) : IsComp L H ↔ IsComponentIn L H := by
  constructor
  · intro h
    exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L H).2 h)⟩
  · intro h
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open L H).1
      ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.1).2 h.2)

theorem layerIn_eq_iSup (H : Subgroup G) :
    layerIn H = ⨆ (L : Subgroup G) (_ : IsComp L H), L := by
  unfold layerIn
  rw [layer_map_subtype_eq_iSup H]
  apply le_antisymm
  · exact iSup₂_le fun L hL => le_iSup₂_of_le L ((isComp_iff L H).2 hL) le_rfl
  · exact iSup₂_le fun L hL => le_iSup₂_of_le L ((isComp_iff L H).1 hL) le_rfl

end Generic

theorem bestJ_le {V : Type} [CommGroup V] (H : Subgroup (MulAut V)) : bestJ H ≤ H :=
  iSup₂_le fun _ hA => hA.1

section Main

variable {V : Type} [CommGroup V] [Finite V] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] (θ : V ≃* Multiplicative W)

theorem actorLayer_of_map {H T M : Subgroup (MulAut V)}
    (hN : NonsolvableLayer (H.map (binPsi θ).toMonoidHom) (T.map (binPsi θ).toMonoidHom) (M.map
        (binPsi θ).toMonoidHom)) : ActorLayer V H T M := by
  classical
  have hinj : Function.Injective (binPsi θ).toMonoidHom := (binPsi θ).injective
  have hfin : Finite (MulAut V) := Finite.of_equiv _ (binPsi θ).toEquiv.symm
  have hKH : oddGen (H.map (binPsi θ).toMonoidHom) ≤ H.map (binPsi θ).toMonoidHom :=
      (Subgroup.closure_le _).2 fun h hh => hh.1
  have hK : (oddOrderSubgroup H).map (binPsi θ).toMonoidHom = oddGen (H.map (binPsi
      θ).toMonoidHom) := map_closure_odd (binPsi θ) H
  have hJ : (bestJ H).map (binPsi θ).toMonoidHom = offenderJ (H.map (binPsi θ).toMonoidHom) := by
    unfold bestJ offenderJ
    simp only [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup₂_le fun A hA => ?_
      exact le_iSup₂_of_le (A.map (binPsi θ).toMonoidHom) ((isMinOffender_map_iff θ H A).2 hA)
          le_rfl
    · refine iSup₂_le fun A' hA' => ?_
      obtain ⟨A, rfl⟩ := exists_map_eq θ A'
      exact le_iSup₂_of_le A ((isMinOffender_map_iff θ H A).1 hA') le_rfl
  have hrad : (radIn H).map (binPsi θ).toMonoidHom = radIn (H.map (binPsi θ).toMonoidHom) :=
    (map_ambient (fun K _ => CFSG.solvableRadical K) (fun e => solvableRadical_map e)
      (binPsi θ) H).symm
  have hfit : (fittingIn H).map (binPsi θ).toMonoidHom = fittingIn (H.map (binPsi θ).toMonoidHom) :=
    (map_ambient (fun K _ => CFSG.fittingSubgroup K) (fun e => fittingSubgroup_map e)
      (binPsi θ) H).symm
  have hlay : (layerIn H).map (binPsi θ).toMonoidHom = layerIn (H.map (binPsi θ).toMonoidHom) :=
    (map_ambient (fun K _ => CFSG.layer K) (fun e => layer_map e) (binPsi θ) H).symm
  have hgf : (genFittingIn H).map (binPsi θ).toMonoidHom = genFittingIn (H.map (binPsi
      θ).toMonoidHom) :=
    (map_ambient (fun K _ => CFSG.generalizedFitting K) (fun e => generalizedFitting_map e)
      (binPsi θ) H).symm
  have hcore : (coreIn H M).map (binPsi θ).toMonoidHom = coreIn (H.map (binPsi θ).toMonoidHom)
      (M.map (binPsi θ).toMonoidHom) :=
    (map_normalCore_subgroupOf (binPsi θ) H M).symm
  have hcen : ∀ K : Subgroup (MulAut V), (Family.centerIn K).map (binPsi θ).toMonoidHom =
      Family.centerIn (K.map (binPsi θ).toMonoidHom) := fun K =>
    map_inf_centralizer (binPsi θ) K
  have hcore_rad : coreIn (H.map (binPsi θ).toMonoidHom) (M.map (binPsi θ).toMonoidHom) = radIn
      (H.map (binPsi θ).toMonoidHom) := by
    unfold coreIn radIn
    rw [← kerIn_top_eq_normalCore]
    exact congrArg (Subgroup.map (H.map (binPsi θ).toMonoidHom).subtype) hN.C_eq_rad
  have hrad_fit : radIn (H.map (binPsi θ).toMonoidHom) = fittingIn (H.map (binPsi θ).toMonoidHom)
      := by
    unfold radIn fittingIn
    rw [← hN.C_eq_rad, ← hN.C_eq_fit]
  have hfit_center : fittingIn (H.map (binPsi θ).toMonoidHom) = Family.centerIn (oddGen (H.map
      (binPsi θ).toMonoidHom)) := by
    rw [Family.centerIn, ← map_center_subgroupOf hKH, hN.C_eq_center, hN.C_eq_fit]
    rfl
  have hlay_K : layerIn (H.map (binPsi θ).toMonoidHom) = oddGen (H.map (binPsi θ).toMonoidHom) := by
    unfold layerIn
    rw [← hN.K_eq_layer, Subgroup.map_subgroupOf_eq_of_le hKH]
  have hlay_gf : layerIn (H.map (binPsi θ).toMonoidHom) = genFittingIn (H.map (binPsi
      θ).toMonoidHom) := by
    unfold layerIn genFittingIn
    rw [← hN.K_eq_layer, ← hN.K_eq_genFit]
  have hrad_odd : Odd (Nat.card ↥(radIn (H.map (binPsi θ).toMonoidHom))) := by
    unfold radIn
    rw [Subgroup.card_map_of_injective (H.map (binPsi θ).toMonoidHom).subtype_injective, ←
        hN.C_eq_rad]
    exact hN.C_odd
  have hcomp : ∀ L : Subgroup (MulAut V), IsComp L H → IsComponentIn (L.map (binPsi
      θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) :=
    fun L hL => (isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff L H).1 hL)
  have hKL : oddOrderSubgroup H = layerIn H :=
    Subgroup.map_injective hinj (by rw [hK, hlay]; exact hlay_K.symm)
  have hcommute : ∀ L L' : Subgroup (MulAut V), IsComp L H → IsComp L' H → L ≠ L' →
      ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    intro L L' hL hL' hne x hx y hy
    have h := commutator_eq_bot_of_isComponentIn_ne' ((isComp_iff L H).1 hL)
      ((isComp_iff L' H).1 hL') hne
    exact (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx) y hy).symm
  refine
    { offenders_nonempty := ?_
      J_normal := ?_
      eq_J_sup_T := ?_
      eq_K_sup_T := ?_
      K_le_J := ?_
      offender_centralizes_rad := ?_
      offender_normalizes_components := ?_
      core_eq_rad := ?_
      rad_eq_fitting := ?_
      fitting_eq_center := ?_
      rad_odd := ?_
      K_eq_layer := hKL
      layer_eq_genFitting := ?_
      exists_component := ?_
      components_generate := (layerIn_eq_iSup H).symm.trans hKL.symm
      components_commute := hcommute
      components_normal := ?_
      components_transitive := ?_
      component_commutator := ?_ }
  · obtain ⟨A', hA'⟩ := hN.parabolic.nonempty
    obtain ⟨A, rfl⟩ := exists_map_eq θ A'
    exact ⟨A, (isMinOffender_map_iff θ H A).1 hA'⟩
  · have h1 := hN.parabolic.J_normal
    rw [← hJ] at h1
    exact (normal_subgroupOf_map_iff (binPsi θ) (bestJ_le H)).1 h1
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, hJ]
    exact hN.parabolic.H_eq.symm
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_sup, hK]
    exact hN.H_eq_KT.symm
  · refine (Subgroup.map_le_map_iff_of_injective hinj).1 ?_
    rw [hK, hJ]
    exact hN.parabolic.K_le_J
  · intro A hA a ha
    have hA' := (isMinOffender_map_iff θ H A).2 hA
    have hc := hN.A_cent_rad _ hA'
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := hr
    have haH : a ∈ H := hA.1 ha
    have ha' : (⟨(binPsi θ).toMonoidHom a, ⟨a, haH, rfl⟩⟩ : ↥(H.map (binPsi θ).toMonoidHom)) ∈
        (A.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom) :=
      ⟨a, ha, rfl⟩
    have hρ' : mapEquiv (binPsi θ) H ρ ∈ CFSG.solvableRadical ↥(H.map (binPsi θ).toMonoidHom) := by
      rw [← solvableRadical_map (mapEquiv (binPsi θ) H)]
      exact ⟨ρ, hρ, rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.1 (hc ha') _ hρ'
    have h3 := congrArg (fun y : ↥(H.map (binPsi θ).toMonoidHom) => (y : W ≃ₗ[ZMod 2] W)) h2
    apply (binPsi θ).injective
    rw [map_mul, map_mul]
    exact h3
  · intro A hA L hLc
    have hA' := (isMinOffender_map_iff θ H A).2 hA
    have h1 := (hN.parabolic.comps (L.map (binPsi θ).toMonoidHom) (hcomp L hLc)).2.1
    have h2 : A.map (binPsi θ).toMonoidHom ≤ offenderJ (H.map (binPsi θ).toMonoidHom) :=
        le_offenderJ hA'
    exact (map_le_normalizer_iff (binPsi θ)).1 (h2.trans h1)
  · exact Subgroup.map_injective hinj (by rw [hcore, hrad]; exact hcore_rad)
  · exact Subgroup.map_injective hinj (by rw [hrad, hfit]; exact hrad_fit)
  · exact Subgroup.map_injective hinj (by rw [hfit, hcen, hK]; exact hfit_center)
  · rw [← Subgroup.card_map_of_injective hinj (K := radIn H), hrad]
    exact hrad_odd
  · exact Subgroup.map_injective hinj (by rw [hlay, hgf]; exact hlay_gf)
  · obtain ⟨Lc, hLc⟩ := hN.comp_ne
    have hLc' : IsComponentIn (Lc.map (H.map (binPsi θ).toMonoidHom).subtype) (H.map (binPsi
        θ).toMonoidHom) := by
      refine ⟨Subgroup.map_subtype_le Lc, ?_⟩
      have : (Lc.map (H.map (binPsi θ).toMonoidHom).subtype).subgroupOf (H.map (binPsi
          θ).toMonoidHom) = Lc :=
        Subgroup.comap_map_eq_self_of_injective (H.map (binPsi θ).toMonoidHom).subtype_injective Lc
      rw [this]
      exact hLc
    obtain ⟨L, hLeq⟩ := exists_map_eq θ (Lc.map (H.map (binPsi θ).toMonoidHom).subtype)
    refine ⟨L, (isComp_iff L H).2 ((isComponentIn_map_iff (binPsi θ)).1 ?_)⟩
    rw [hLeq]
    exact hLc'
  · intro L hL
    have hLK : L ≤ oddOrderSubgroup H := by
      rw [hKL, layerIn_eq_iSup]
      exact le_iSup₂_of_le L hL le_rfl
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLK, hKL, layerIn_eq_iSup]
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · rw [h]
      exact Subgroup.le_normalizer
    · intro x hx
      have hxc : x ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
        Subgroup.mem_centralizer_iff.2 fun y hy => (hcommute L' L hL' hL h x hx y hy).symm
      exact Subgroup.centralizer_le_normalizer (L : Set (MulAut V)) hxc
  · intro L L' hL hL'
    have hLc := hcomp L hL
    have hLc' := hcomp L' hL'
    obtain ⟨t, ht, hconj⟩ := hN.comp_trans ((L.map (binPsi θ).toMonoidHom).subgroupOf (H.map
        (binPsi θ).toMonoidHom))
      ((L'.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom)) hLc.2 hLc'.2
    obtain ⟨t1, ht1, ht1eq⟩ := ht
    refine ⟨t1, ht1, ?_⟩
    apply Subgroup.map_injective hinj
    have ht1eq' : (binPsi θ) t1 = ((t : ↥(H.map (binPsi θ).toMonoidHom)) : W ≃ₗ[ZMod 2] W) := ht1eq
    have h1 := congrArg (Subgroup.map (H.map (binPsi θ).toMonoidHom).subtype) hconj
    rw [map_conj_subtype, Subgroup.map_subgroupOf_eq_of_le hLc.1,
      Subgroup.map_subgroupOf_eq_of_le hLc'.1] at h1
    rw [map_map_conj, ht1eq']
    exact h1.symm
  · intro L hL
    have hLc := hcomp L hL
    obtain ⟨A', hA', hcomm⟩ := hN.comp_offender ((L.map (binPsi θ).toMonoidHom).subgroupOf (H.map
        (binPsi θ).toMonoidHom)) hLc.2
    rw [Subgroup.map_subgroupOf_eq_of_le hLc.1] at hcomm
    obtain ⟨A, rfl⟩ := exists_map_eq θ A'
    refine ⟨A, (isMinOffender_map_iff θ H A).1 hA', ?_⟩
    apply Subgroup.map_injective hinj
    rw [map_commutator_mulEquiv]
    exact hcomm

end Main

theorem actorLayerProp : ActorLayerProp := by
  intro V _ _ H T M E hFF hns
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hFF.elementary
  obtain ⟨ho2, hsyl, hnn, hmax, hE⟩ :=
    map_hypotheses θ hFF.o2_trivial hFF.sylow hFF.not_normal hFF.max hFF.offender
  have hns' : ¬ Group.IsSolvable ↥(H.map (binPsi θ).toMonoidHom) := fun h =>
    hns ((solvable_map_mulEquiv_iff (binPsi θ)).1 h)
  exact actorLayer_of_map θ (Final.nonsolvable_layer hns' ho2 hsyl hnn hmax.1 hmax.2.1 hmax.2.2
    hE.1 hE.2.1 hE.2.2.1 hE.2.2.2)

end CFSG.QuasithinUnique.Setup.Layer.Actor
