module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainKinds
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotHR8Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open E6Pilot (modelToG)

section Transport

variable {F K' : Type} [Field F] [Field K']

theorem baseChangeGL_mem_rootSpan_perpRoots_E7 (ε : F →+* K') (g : EPilot.perpLevi .E7 F) :
    baseChangeGL ε ((g : adjointGroup .E7 F) : ModGL .E7 F) ∈
      rootSpan .E7 K' (EPilot.perpRoots .E7) :=
  F4Pilot.map_rootSpan_baseChangeGL_le ε _ ⟨_, Subgroup.mem_subgroupOf.1 g.2, rfl⟩

@[expose] noncomputable def perpLeviBaseChangeE7 (ε : F →+* K') :
    EPilot.perpLevi .E7 F →* EPilot.perpLevi .E7 K' :=
  (((baseChangeGL ε).comp ((adjointGroup .E7 F).subtype.comp
      (EPilot.perpLevi .E7 F).subtype)).codRestrict (adjointGroup .E7 K') fun g =>
        (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α :
          rootSpan .E7 K' (EPilot.perpRoots .E7) ≤ adjointGroup .E7 K')
          (baseChangeGL_mem_rootSpan_perpRoots_E7 ε g)).codRestrict
    (EPilot.perpLevi .E7 K') fun g =>
      Subgroup.mem_subgroupOf.2 (baseChangeGL_mem_rootSpan_perpRoots_E7 ε g)

@[expose] noncomputable def perpLeviRingEquivE7 (ε : F ≃+* K') :
    EPilot.perpLevi .E7 F ≃* EPilot.perpLevi .E7 K' where
  toFun g := perpLeviBaseChangeE7 (ε : F →+* K') g
  invFun g := perpLeviBaseChangeE7 (ε.symm : K' →+* F) g
  left_inv g := by
    refine Subtype.ext (Subtype.ext ?_)
    change baseChangeGL (ε.symm : K' →+* F)
      (baseChangeGL (ε : F →+* K') ((g : adjointGroup .E7 F) : ModGL .E7 F)) = _
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε.symm : K' →+* F).comp (ε : F →+* K')) = RingHom.id F := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  right_inv g := by
    refine Subtype.ext (Subtype.ext ?_)
    change baseChangeGL (ε : F →+* K')
      (baseChangeGL (ε.symm : K' →+* F) ((g : adjointGroup .E7 K') : ModGL .E7 K')) = _
    rw [baseChangeGL_baseChangeGL]
    have h : ((ε : F →+* K').comp (ε.symm : K' →+* F)) = RingHom.id K' := by
      ext c
      simp
    rw [h, baseChangeGL_id]
  map_mul' g h := map_mul _ g h

end Transport

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbourCore_high_eq_centralizerPerfectCore (e : L ≃* adjointGroup .E7 K) :
    neighbourCore e .high = centralizerPerfectCore (rootTorusG e) := by
  rw [neighbourCore_high]
  rfl

theorem nonempty_levi_high_mulEquiv_neighbourCore_high {t : G} {f : ℕ} (hw : E7Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 K) (hX : HR8FieldE7 e t f) (K₂ : Type) [Field K₂]
    [Finite K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) :
    Nonempty (E7Neighbour.high.levi K₂ ≃* neighbourCore e .high) := by
  obtain ⟨htX, Kc, hKc, -, -, hlt, -, hsN, hov⟩ := hX
  obtain ⟨F, _, _, _, hF, ⟨Ψ⟩⟩ := nonempty_perpLevi_mulEquiv_centralizerPerfectCore_E7
    hw.standard.standard hw.mem_centralizer hw.orderOf_eq (hw.inf_eq e) hf hw.card_eq e
    (X := rootTorusG e) (Or.inr rfl) htX (D := rootLeviG e) rfl hKc hlt.le hsN hov
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K₂
  have hc : Fintype.card F = Fintype.card K₂ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hK₂]
  exact ⟨((MulEquiv.subgroupCongr (E7Neighbour.levi_high K₂)).trans
    (perpLeviRingEquivE7 (FiniteField.ringEquivOfCardEq hc)).symm).trans
      (Ψ.trans (MulEquiv.subgroupCongr (neighbourCore_high_eq_centralizerPerfectCore e).symm))⟩

theorem modelToG_map_subtype_levi_high (e : L ≃* adjointGroup .E7 K) :
    modelToG e ((E7Neighbour.high.levi K).map (adjointGroup .E7 K).subtype) = rootLeviG e := by
  rw [E7Neighbour.levi_high, modelToG, rootLeviG]
  congr 2
  exact Subgroup.comap_map_eq_self_of_injective (adjointGroup .E7 K).subtype_injective _

theorem perfectCore_neighbourCore_high_inf_centralizer {t : G} {f : ℕ} (hw : E7Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E7 K) :
    perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E7Neighbour.high.levi K).map (adjointGroup .E7 K).subtype) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  rw [modelToG_map_subtype_levi_high]
  set A : Subgroup (adjointGroup .E7 K) :=
    (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) with hA
  set X : Subgroup G := rootTorusG e with hXdef
  set D : Subgroup G := rootLeviG e with hDdef
  have hX : X = (A.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((EPilot.perpLevi .E7 K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hE : neighbourCore e .high = centralizerPerfectCore X :=
    neighbourCore_high_eq_centralizerPerfectCore e
  have hDperf : ⁅D, D⁆ = D := by
    rw [hDe, ← map_commutator, ← map_commutator, commutator_perpLevi_eq_E7 hq]
  have hDm : modelToG e (rootSpan .E7 K (orthRoots E7Neighbour.high.root)) = D := by
    change (((E7Neighbour.high.levi K).map e.symm.toMonoidHom).map L.subtype) = D
    rw [E7Neighbour.levi_high, hDe]
  have hDE : D ≤ neighbourCore e .high := by
    rw [← hDm]
    exact modelToG_rootSpan_orthRoots_le_neighbourCore_of_charTwo e hq .high
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.1⟩⟩
  have hPL : P ≤ L := std_perfect_le hw.standard hOut htC hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (hE ▸ F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  have hcen := E6Pilot.centralizer_eq_highTorusLine_sup_of_le (τ := .E7) (Or.inr (Or.inl rfl)) hc
    le_rfl (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c))
  rw [hX, F4Pilot.inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup, ← hX] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := by
    rw [hX, hDe]
    exact le_centralizer_iff.mp
      (F4Pilot.map_map_symm_le_centralizer e
        E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi)
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e E6Pilot.highTorusLine_subgroupOf_le_centralizer_self
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end Lift

end CFSG.SeitzReduction.E7Pilot
