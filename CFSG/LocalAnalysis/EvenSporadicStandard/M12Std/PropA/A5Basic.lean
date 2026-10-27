module

public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

theorem alt5_card {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 5)) :
    Nat.card H = 60 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem alt5_center_trivial {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 5)) {h : H}
    (hh : ∀ h' : H, h * h' = h' * h) : h = 1 := by
  have hmem : e h ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨h', rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul, ← hh h']
  rw [alternatingGroup.center_eq_bot (by simp)] at hmem
  exact e.injective (by simpa using hmem)

theorem alt5_commutator {H : Type*} [Group H] (e : H ≃* alternatingGroup (Fin 5)) :
    commutator H = ⊤ := by
  have hrange : e.toMonoidHom.range = ⊤ := e.range_eq_top
  have h : (commutator H).map e.toMonoidHom = ⊤ := by
    rw [map_commutator_eq, hrange, ← commutator_def,
      commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)]
  refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
  rw [h, Subgroup.map_top, hrange]

theorem alt5_subgroup_center {G : Type*} [Group G] {H : Subgroup G}
    (e : H ≃* alternatingGroup (Fin 5)) {h : G} (hh : h ∈ H)
    (hc : ∀ h' ∈ H, h * h' = h' * h) : h = 1 := by
  have hcomm : ∀ h' : H, (⟨h, hh⟩ : H) * h' = h' * ⟨h, hh⟩ := by
    intro h'
    ext
    exact hc h' h'.2
  have hz := alt5_center_trivial e hcomm
  exact congrArg Subtype.val hz

theorem alt5_subgroup_perfect {G : Type*} [Group G] {H : Subgroup G}
    (e : H ≃* alternatingGroup (Fin 5)) : ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, alt5_commutator e, Subgroup.map_top,
    Subgroup.range_subtype]

theorem nonempty_alt5_of_quasisimple {H : Type*} [Group H] [Finite H]
    (hq : CFSG.IsQuasisimple H) (hc : ∀ h : H, (∀ h' : H, h * h' = h' * h) → h = 1)
    (h60 : Nat.card H = 60) : Nonempty (H ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, hsimple, -⟩ := hq
  have hcenter : Subgroup.center H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hc x fun y => (Subgroup.mem_center_iff.mp hx y).symm
  have ebot : H ⧸ Subgroup.center H ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup H :=
    @MulEquiv.isSimpleGroup H _ (H ⧸ Subgroup.center H) _ hsimple ebot.symm
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60

end CFSG.EvenSporadicStandard.M12Std.PropA
