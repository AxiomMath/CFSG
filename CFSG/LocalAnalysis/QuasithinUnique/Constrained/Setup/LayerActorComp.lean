module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorComp1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Interface

public section

namespace CFSG.QuasithinUnique.Setup.Layer.Actor

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Offender
open CFSG.Quasithin.B6 (conjSub mem_conjSub)
open scoped Multiplicative commutatorElement

section Abstract

variable {X : Type*} [Group X] {H T M : Subgroup X}

theorem abstract_hyps [Finite X] (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup X, T ≤ Y → Y < H → Y ≤ M) :
    IsSylowOf 2 (T.subgroupOf H) (⊤ : Subgroup ↥H) ∧ T.subgroupOf H ≤ M.subgroupOf H ∧
      M.subgroupOf H < ⊤ ∧
      ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
  refine ⟨isSylowOf_top_of_isSylowTwoOf hT, fun x hx => hTM hx, ?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => ?_
    have : H ≤ M := Subgroup.subgroupOf_eq_top.1 h
    exact hMH.not_ge this
  · intro Y hTY hY
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

theorem subgroupOf_le_iff {U V' : Subgroup X} (hU : U ≤ H) :
    U.subgroupOf H ≤ V'.subgroupOf H ↔ U ≤ V' := by
  constructor
  · intro h x hx
    exact h (show (⟨x, hU hx⟩ : ↥H) ∈ U.subgroupOf H from hx)
  · intro h x hx
    exact h hx

theorem subgroupOf_lt_iff {U V' : Subgroup X} (hU : U ≤ H) (hV : V' ≤ H) :
    U.subgroupOf H < V'.subgroupOf H ↔ U < V' := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, subgroupOf_le_iff hU, subgroupOf_le_iff hV]

theorem actImg_normT_eq (T L₀ : Subgroup X) : actImg L₀ (normT T L₀) = actImg L₀ T := by
  unfold actImg
  rw [Subgroup.inf_subgroupOf_right]

theorem actImg_top_eq (L₀ : Subgroup X) : actImg L₀ ⊤ = actImg L₀ (normL L₀) := by
  unfold actImg
  rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_eq_top.2 le_top]

end Abstract

section ActorCPT

variable {V : Type} [CommGroup V] [Finite V] [Finite (MulAut V)] {H T M : Subgroup (MulAut V)}

theorem actor_cpt (hlay : ActorLayer V H T M) (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (MulAut V), T ≤ Y → Y < H → Y ≤ M) (c : Comp ↥H)
    {A : Subgroup (MulAut V)} (hA : IsBestOffender H A)
    (hAL : ⁅c.1.map H.subtype, A⁆ = c.1.map H.subtype)
    (hAn : A ≤ Subgroup.normalizer ((c.1.map H.subtype : Subgroup (MulAut V)) : Set (MulAut V))) :
    CentralProductTransfer 2 (T.subgroupOf H) (M.subgroupOf H) (fun c : Comp ↥H => c.1) c := by
  classical
  obtain ⟨hT', hTM', hMH', hmax'⟩ := abstract_hyps hT hTM hMH hmax
  have hqs : ∀ c : Comp ↥H, CFSG.IsQuasisimple ↥c.1 := fun c => c.2.1
  have hcomm : ∀ c c' : Comp ↥H, c ≠ c' → ⁅c.1, c'.1⁆ = ⊥ := by
    intro c c' hne
    rcases distinct_components_commute c.2 c'.2 with h | h
    · exact absurd (Subtype.ext h) hne
    · exact h
  have hlayer_eq : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H) = CFSG.layer ↥H :=
    (sSup_eq_iSup' _).symm
  have hKn : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H).Normal := by
    rw [hlayer_eq]
    have := layer_characteristic (G := ↥H)
    infer_instance
  have hKT : (⨆ c : Comp ↥H, c.1 : Subgroup ↥H) ⊔ T.subgroupOf H = ⊤ := by
    rw [hlayer_eq]
    have h1 : CFSG.layer ↥H = (layerIn H).subgroupOf H := by
      unfold layerIn
      exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm
    have hKH : layerIn H ≤ H := Subgroup.map_subtype_le _
    have h2 : (layerIn H ⊔ T).subgroupOf H = ⊤ := by
      rw [← hlay.K_eq_layer, ← hlay.eq_K_sup_T, Subgroup.subgroupOf_self]
    rwa [Subgroup.subgroupOf_sup hKH hT.1, ← h1] at h2
  have hperm : ∀ t ∈ T.subgroupOf H, ∀ c : Comp ↥H, ∃ c' : Comp ↥H, conjSub t c.1 = c'.1 :=
    fun t _ c => ⟨⟨_, isComponent_map_mulEquiv (MulAut.conj t) c.2⟩, rfl⟩
  have hLcomp : ∀ c : Comp ↥H, IsComp (c.1.map H.subtype) H := fun c =>
    (isComp_iff _ _).2 ⟨Subgroup.map_subtype_le c.1, by
      have : (c.1.map H.subtype).subgroupOf H = c.1 :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective c.1
      rw [this]
      exact c.2⟩
  have htrans : ∀ c c' : Comp ↥H, ∃ t ∈ T.subgroupOf H, conjSub t c.1 = c'.1 := by
    intro c c'
    obtain ⟨t, ht, h⟩ := hlay.components_transitive _ _ (hLcomp c) (hLcomp c')
    have htH : t ∈ H := hT.1 ht
    refine ⟨⟨t, htH⟩, ht, ?_⟩
    apply Subgroup.map_injective H.subtype_injective
    have e : conjSub (⟨t, htH⟩ : ↥H) c.1 = c.1.map (MulAut.conj (⟨t, htH⟩ : ↥H)).toMonoidHom := rfl
    rw [e, map_conj_subtype]
    exact h.symm
  have hpgroup : IsPGroup 2 ↥(A.subgroupOf H) := by
    intro g
    refine ⟨1, ?_⟩
    have h2 : ((g : ↥H) : MulAut V) ^ 2 = 1 := hA.2.2.1.2 _ g.2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h2
  have hnormal : A.subgroupOf H ≤ normL c.1 := fun x hx => mem_normalizer_of_map_subtype (hAn hx)
  have hEne : ⁅c.1, A.subgroupOf H⁆ ≠ ⊥ := by
    intro hbot
    have h1 := congrArg (Subgroup.map H.subtype) hbot
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1, hAL,
      Subgroup.map_bot] at h1
    have hnt := isQuasisimple_nontrivial c.2.1
    have : c.1 = ⊥ := (Subgroup.map_eq_bot_iff_of_injective c.1 H.subtype_injective).1 h1
    exact (Subgroup.nontrivial_iff_ne_bot c.1).1 hnt this
  exact central_product_transfer Nat.prime_two hT' hTM' hMH' hmax' (fun c : Comp ↥H => c.1)
    Subtype.val_injective hqs hcomm hKn hKT hperm htrans c hpgroup hnormal hEne

end ActorCPT

section Translate

variable {V : Type} [CommGroup V] [Finite (MulAut V)] {H T M L : Subgroup (MulAut V)}

theorem cpt_to_ambient (hT : IsSylowTwoOf T H) (hLH : L ≤ H)
    (hLc : CFSG.IsComponent (L.subgroupOf H))
    (hc : CentralProductTransfer 2 (T.subgroupOf H) (M.subgroupOf H) (fun c : Comp ↥H => c.1)
      ⟨L.subgroupOf H, hLc⟩) :
    IsSylowTwoOf (X1.TL T L) (X1.HL T L) ∧ ¬ ((X1.TL T L).subgroupOf (X1.HL T L)).Normal ∧
      (X1.XL M T L < X1.HL T L ∧ X1.TL T L ≤ X1.XL M T L ∧
        ∀ Y : Subgroup (MulAut V), X1.TL T L ≤ Y → Y < X1.HL T L → Y ≤ X1.XL M T L) := by
  have hTH := hT.1
  have hTL : (X1.TL T L).subgroupOf H = normT (T.subgroupOf H) (L.subgroupOf H) :=
    subgroupOf_normT hLH
  have hHL : (X1.HL T L).subgroupOf H = locL (T.subgroupOf H) (L.subgroupOf H) :=
    subgroupOf_locL hLH hTH
  have hXL : (X1.XL M T L).subgroupOf H =
      maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) := subgroupOf_maxL hLH hTH
  have hTLH : X1.TL T L ≤ H := inf_le_left.trans hTH
  have hHLH : X1.HL T L ≤ H := sup_le hLH hTLH
  have hXLH : X1.XL M T L ≤ H := sup_le (inf_le_right.trans hLH) hTLH
  have hTLHL : X1.TL T L ≤ X1.HL T L := le_sup_right
  have hsyl : IsSylowOf 2 (normT (T.subgroupOf H) (L.subgroupOf H))
      (locL (T.subgroupOf H) (L.subgroupOf H)) := hc.sylow_locL
  have hnn : ¬ ((normT (T.subgroupOf H) (L.subgroupOf H)).subgroupOf
      (locL (T.subgroupOf H) (L.subgroupOf H))).Normal := hc.T_not_normal
  have hXmax : normT (T.subgroupOf H) (L.subgroupOf H) ≤
        maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) ∧
      maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) <
        locL (T.subgroupOf H) (L.subgroupOf H) ∧
      ∀ Y : Subgroup ↥H, Y ≤ locL (T.subgroupOf H) (L.subgroupOf H) →
        normT (T.subgroupOf H) (L.subgroupOf H) ≤ Y →
        Y < locL (T.subgroupOf H) (L.subgroupOf H) →
        Y ≤ maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H) := hc.X_max
  rw [← hHL, ← hTL] at hsyl
  rw [← hHL, ← hTL] at hnn
  refine ⟨?_, ?_, ?_⟩
  · have h := (isSylowOf_map_subtype_iff (p := 2) H).2 hsyl
    rw [Subgroup.map_subgroupOf_eq_of_le hTLH, Subgroup.map_subgroupOf_eq_of_le hHLH] at h
    exact isSylowOf_iff.1 h
  · intro hn
    apply hnn
    exact (normal_subgroupOf_subgroupOf_iff hTLHL hHLH).1 hn
  · obtain ⟨h1, h2, h3⟩ := hXmax
    rw [← hTL, ← hXL] at h1
    rw [← hXL, ← hHL] at h2
    refine ⟨(subgroupOf_lt_iff hXLH hHLH).1 h2, (subgroupOf_le_iff hTLH).1 h1, ?_⟩
    intro Y hTY hYH
    have hYH' : Y ≤ H := hYH.le.trans hHLH
    have h4 := h3 (Y.subgroupOf H) (by rw [← hHL]; exact (subgroupOf_le_iff hYH').2 hYH.le)
      (by rw [← hTL]; exact (subgroupOf_le_iff hTLH).2 hTY)
      (by rw [← hHL]; exact (subgroupOf_lt_iff hYH' hHLH).2 hYH)
    rw [← hXL] at h4
    exact (subgroupOf_le_iff hYH').1 h4

theorem cpt_to_autOn (hT : IsSylowTwoOf T H) (hLH : L ≤ H)
    (hLc : CFSG.IsComponent (L.subgroupOf H))
    (hc : CentralProductTransfer 2 (T.subgroupOf H) (M.subgroupOf H) (fun c : Comp ↥H => c.1)
      ⟨L.subgroupOf H, hLc⟩) :
    IsSylowTwoOf (autOn T L) (autOn H L) ∧ ¬ ((autOn T L).subgroupOf (autOn H L)).Normal ∧
      ∃ P : Subgroup (MulAut ↥L), X35.IsUniqueMaxOver (autOn T L) P (autOn H L) := by
  have hTH := hT.1
  have eT : autOn T L =
      (actImg (L.subgroupOf H) (T.subgroupOf H)).map (autCongr hLH).toMonoidHom :=
    autOn_eq_map_actImg hLH hTH
  have eH : autOn H L = (actImg (L.subgroupOf H) ⊤).map (autCongr hLH).toMonoidHom := by
    have := autOn_eq_map_actImg (L := L) hLH (le_refl H)
    rwa [Subgroup.subgroupOf_self] at this
  have hsyl : IsSylowOf 2 (actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)))
      (actImg (L.subgroupOf H) (normL (L.subgroupOf H))) := hc.sylow_S
  have hnn : ¬ ((actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H))).subgroupOf
      (actImg (L.subgroupOf H) (normL (L.subgroupOf H)))).Normal := hc.S_not_normal
  have hPmax : actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)) ≤
        actImg (L.subgroupOf H) (maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H)) ∧
      actImg (L.subgroupOf H) (maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H)) <
        actImg (L.subgroupOf H) (normL (L.subgroupOf H)) ∧
      ∀ Y : Subgroup (MulAut ↥(L.subgroupOf H)),
        Y ≤ actImg (L.subgroupOf H) (normL (L.subgroupOf H)) →
        actImg (L.subgroupOf H) (normT (T.subgroupOf H) (L.subgroupOf H)) ≤ Y →
        Y < actImg (L.subgroupOf H) (normL (L.subgroupOf H)) →
        Y ≤ actImg (L.subgroupOf H) (maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H)) :=
    hc.P_max
  rw [actImg_normT_eq] at hsyl hnn hPmax
  rw [eT, eH, actImg_top_eq]
  have hsyl' := isSylowOf_iff.1 hsyl
  refine ⟨(isSylowTwoOf_map_mulEquiv (autCongr hLH)).2 hsyl', ?_, ?_⟩
  · rw [normal_subgroupOf_map_iff (autCongr hLH) hsyl'.1]
    exact hnn
  · refine ⟨(actImg (L.subgroupOf H)
      (maxL (T.subgroupOf H) (M.subgroupOf H) (L.subgroupOf H))).map (autCongr hLH).toMonoidHom, ?_⟩
    exact X35.IsUniqueMaxOver.map (autCongr hLH).injective
      ⟨hPmax.1, hPmax.2.1, fun Y hSY hYA => hPmax.2.2 Y hYA.le hSY hYA⟩

end Translate

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem actor_setup {H T M E : Subgroup (MulAut V)} (hFF : FFHyp V H T M E)
    (hns : ¬ Group.IsSolvable ↥H) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (θ : V ≃* Multiplicative W),
      ActualComponentTransfer (H.map (binPsi θ).toMonoidHom) (T.map (binPsi θ).toMonoidHom)
        (M.map (binPsi θ).toMonoidHom) := by
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hFF.elementary
  obtain ⟨ho2, hsyl, hnn, hmax, hE⟩ :=
    map_hypotheses θ hFF.o2_trivial hFF.sylow hFF.not_normal hFF.max hFF.offender
  have hns' : ¬ Group.IsSolvable ↥(H.map (binPsi θ).toMonoidHom) := fun h =>
    hns ((solvable_map_mulEquiv_iff (binPsi θ)).1 h)
  exact ⟨W, inferInstance, inferInstance, inferInstance, θ,
    Final.actual_component_minimal_parabolic hns' ho2 hsyl hnn hmax.1 hmax.2.1 hmax.2.2 hE.1
      hE.2.1 hE.2.2.1 hE.2.2.2⟩

theorem componentTransferProp : X1.ComponentTransferProp := by
  intro V _ _ H T M E hFF hns L hL
  obtain ⟨W, _, _, _, θ, hAct⟩ := actor_setup hFF hns
  have hfin : Finite (MulAut V) := Finite.of_equiv _ (binPsi θ).toEquiv.symm
  have hinj : Function.Injective (binPsi θ).toMonoidHom := (binPsi θ).injective
  have hlay := actorLayer_of_map θ hAct.layer
  have hLH : L ≤ H := hL.1
  have hLc : CFSG.IsComponent (L.subgroupOf H) := ((isComp_iff L H).1 hL).2
  obtain ⟨A, hA, hAL⟩ := hlay.component_commutator L hL
  have hAn := hlay.offender_normalizes_components A hA L hL
  have hmapL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hcpt := actor_cpt hlay hFF.sylow hFF.max.1 hFF.max.2.1 hFF.max.2.2
    ⟨L.subgroupOf H, hLc⟩ hA (by
      show ⁅(L.subgroupOf H).map H.subtype, A⁆ = (L.subgroupOf H).map H.subtype
      rw [hmapL]; exact hAL) (by
      show A ≤ Subgroup.normalizer (((L.subgroupOf H).map H.subtype : Subgroup (MulAut V)) :
        Set (MulAut V))
      rw [hmapL]; exact hAn)
  obtain ⟨hs, hnorm, hum⟩ := cpt_to_ambient hFF.sylow hLH hLc hcpt
  have hLc' : IsComponentIn (L.map (binPsi θ).toMonoidHom) (H.map (binPsi θ).toMonoidHom) :=
    (isComponentIn_map_iff (binPsi θ)).2 ((isComp_iff L H).1 hL)
  obtain ⟨A', hA'le, hA', hA'comm⟩ :=
    hAct.offender ⟨(L.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom),
      hLc'.2⟩
  have hTH' : T.map (binPsi θ).toMonoidHom ≤ H.map (binPsi θ).toMonoidHom :=
    Subgroup.map_mono hFF.sylow.1
  have hnormT : (normT ((T.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom))
      ((L.map (binPsi θ).toMonoidHom).subgroupOf (H.map (binPsi θ).toMonoidHom))).map
        (H.map (binPsi θ).toMonoidHom).subtype =
      T.map (binPsi θ).toMonoidHom ⊓
        Subgroup.normalizer ((L.map (binPsi θ).toMonoidHom : Subgroup _) : Set _) := by
    rw [← subgroupOf_normT hLc'.1,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hTH')]
  rw [hnormT] at hA'le
  obtain ⟨A₁, rfl⟩ := exists_map_eq θ A'
  have hA₁T : A₁ ≤ T := (Subgroup.map_le_map_iff_of_injective hinj).1 (hA'le.trans inf_le_left)
  have hA₁N : A₁ ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    (map_le_normalizer_iff (binPsi θ)).1 (hA'le.trans inf_le_right)
  obtain ⟨-, -, hel, hoff, hstrict⟩ := (isMinOffender_map_iff θ H A₁).1 hA'
  have hcomm : ⁅L, A₁⁆ = L := by
    rw [Subgroup.map_subgroupOf_eq_of_le hLc'.1] at hA'comm
    apply Subgroup.map_injective hinj
    rw [map_commutator_mulEquiv]
    exact hA'comm
  exact { sylow := hs, not_normal := hnorm, unique_max := hum
          offender := ⟨A₁, le_inf hA₁T hA₁N, hel, hcomm, hoff, hstrict⟩ }

theorem actorComponentTransfer : X35.ActorComponentTransfer := by
  intro V _ _ H T M E hB hns L hL
  have hFF : FFHyp V H T M E :=
    ⟨hB.elementary, hB.o2_trivial, hB.sylow, hB.not_normal, hB.max, hB.offender⟩
  obtain ⟨W, _, _, _, θ, hAct⟩ := actor_setup hFF hns
  have hfin : Finite (MulAut V) := Finite.of_equiv _ (binPsi θ).toEquiv.symm
  have hlay := actorLayer_of_map θ hAct.layer
  have hLH : L ≤ H := hL.1
  have hLc : CFSG.IsComponent (L.subgroupOf H) := hL.2
  have hL' : IsComp L H := (isComp_iff L H).2 hL
  obtain ⟨A, hA, hAL⟩ := hlay.component_commutator L hL'
  have hAn := hlay.offender_normalizes_components A hA L hL'
  have hmapL : (L.subgroupOf H).map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hcpt := actor_cpt hlay hFF.sylow hFF.max.1 hFF.max.2.1 hFF.max.2.2
    ⟨L.subgroupOf H, hLc⟩ hA (by
      show ⁅(L.subgroupOf H).map H.subtype, A⁆ = (L.subgroupOf H).map H.subtype
      rw [hmapL]; exact hAL) (by
      show A ≤ Subgroup.normalizer (((L.subgroupOf H).map H.subtype : Subgroup (MulAut V)) :
        Set (MulAut V))
      rw [hmapL]; exact hAn)
  exact cpt_to_autOn hFF.sylow hLH hLc hcpt

end Main

end CFSG.QuasithinUnique.Setup.Layer.Actor
