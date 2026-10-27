module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GH74.GLS.Stage2.Local.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L64

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Layer

theorem commutator_layer_eq_bot_of_le {Y : Type*} [Group Y] [Finite Y] {D : Subgroup Y}
    [D.Normal] (hD : Group.IsSolvable ↥D) {Z : Subgroup Y} (h : ⁅layer Y, Z⁆ ≤ D) :
    ⁅layer Y, Z⁆ = ⊥ := by
  have hEn : (layer Y).Normal :=
    Subgroup.normal_of_characteristic _ (h := CFSG.LocalCores.layer_characteristic)
  have hcomm : ⁅layer Y, Z⁆ ≤ layer Y ⊓ D := le_inf (Subgroup.commutator_le_left _ _) h
  have hRs : Group.IsSolvable ↥(layer Y ⊓ D) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_right : layer Y ⊓ D ≤ D))
  have hcent : ⁅layer Y, layer Y ⊓ D⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hRs
      (inferInstance : (layer Y ⊓ D).Normal).isSubnormal).2
  have hdbl : ⁅⁅layer Y, Z⁆, layer Y⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅layer Y, Z⁆, layer Y⁆ ≤ ⁅layer Y ⊓ D, layer Y⁆ :=
          Subgroup.commutator_mono hcomm le_rfl
      _ = ⁅layer Y, layer Y ⊓ D⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := hcent
      _ ≤ ⊥ := le_rfl
  exact CFSG.LocalCores.perfect_double_commutator
    (CFSG.LocalCores.layer_isPerfect (G := Y)) hdbl

theorem layer_quot_le {Y Q : Type*} [Group Y] [Group Q] (π : Y →* Q)
    (hπ : Function.Surjective π) : (layer Y).map π ≤ layer Q := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  by_cases hKf : K ≤ π.ker
  · rw [(Subgroup.map_eq_bot_iff K).mpr hKf]
    exact bot_le
  · exact CFSG.LocalCores.component_le_layer
      ⟨CFSG.LocalCores.isQuasisimple_map hK.1 π hKf, hK.2.map hπ⟩

theorem commutator_layer_quot_ne_bot {Y : Type*} [Group Y] [Finite Y] {O : Subgroup Y}
    [O.Normal] (hO : Group.IsSolvable ↥O) {Z : Subgroup Y} (hZ : ⁅layer Y, Z⁆ ≠ ⊥) :
    ⁅layer (Y ⧸ O), Z.map (QuotientGroup.mk' O)⁆ ≠ ⊥ := by
  intro hbot
  apply hZ
  refine commutator_layer_eq_bot_of_le hO ?_
  have h1 : (⁅layer Y, Z⁆).map (QuotientGroup.mk' O) = ⊥ := by
    rw [Subgroup.map_commutator]
    exact le_bot_iff.mp
      (hbot ▸ Subgroup.commutator_mono (layer_quot_le _ (QuotientGroup.mk'_surjective O)) le_rfl)
  have h2 := (Subgroup.map_eq_bot_iff _).mp h1
  rwa [QuotientGroup.ker_mk'] at h2

end Layer

section Sub

variable {G : Type} [Group G]

theorem commutator_layer_ne_bot_of_Em {H X : Subgroup G} (hX : X ≤ H) (hE : ⁅Em H, X⁆ ≠ ⊥) :
    ⁅layer ↥H, X.subgroupOf H⁆ ≠ ⊥ := by
  intro hbot
  apply hE
  have h2 : ⁅(layer ↥H).map H.subtype, X⁆ = (⁅layer ↥H, X.subgroupOf H⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX]
  show ⁅(layer ↥H).map H.subtype, X⁆ = ⊥
  rw [h2, hbot, Subgroup.map_bot]

variable [Finite G]

theorem isSolvable_pCore {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    Group.IsSolvable ↥(pCore p ↥H) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite ↥(pCore p ↥H) := inferInstance
  have := (pCore_isPGroup (p := p) (G := ↥H)).isNilpotent
  infer_instance

theorem not_le_Op_of_Em {p : ℕ} (hp : p.Prime) {H X : Subgroup G} (hX : X ≤ H)
    (hE : ⁅Em H, X⁆ ≠ ⊥) : ¬ X ≤ Op p H := by
  intro hle
  have hY := commutator_layer_ne_bot_of_Em hX hE
  have hX' : X.subgroupOf H ≤ pCore p ↥H := by
    intro x hx
    have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hyx⟩ := hle hx'
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  apply hY
  refine commutator_layer_eq_bot_of_le (isSolvable_pCore hp H) ?_
  exact (Subgroup.commutator_mono le_rfl hX').trans (Subgroup.commutator_le_right _ _)

end Sub

theorem prop4_3Esub_of (h43 : Prop4_3E) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) {H X : Subgroup G} {p : ℕ}
    (h : Sig4Sub G z H p X) (hE : ⁅Em H, X⁆ ≠ ⊥) :
    Concl43E k (zSec z H h.A.z_mem (pCore p ↥H)) p (xBar p H X) :=
  h43 G z k S hctx H (pCore p ↥H) h.A.z_mem p (xBar p H X)
    (sig4B_of_sub hctx.orderOf_z h (not_le_Op_of_Em h.A.prime h.A.X_le hE))
    (commutator_layer_quot_ne_bot (isSolvable_pCore h.A.prime H)
      (commutator_layer_ne_bot_of_Em h.A.X_le hE))

end CFSG.GH74.GLS.Stage2.Signalizer.L64
