module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionFourData
public import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentAction

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def movedCentralizerPair (L : Subgroup G) (u v : G) : Subgroup G :=
  (⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
    (⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u * v} : Set G))

theorem commuting_involution_product_square (u v : G)
    (hu : u * u = 1) (hv : v * v = 1) (hcommute : Commute u v) :
    (u * v) * (u * v) = 1 := by
  calc
    (u * v) * (u * v) = u * (v * u) * v := by group
    _ = (u * u) * (v * v) := by rw [← hcommute.eq]; group
    _ = 1 := by rw [hu, hv, one_mul]

theorem conjugation_product (u v x : G) :
    MulAut.conj (u * v) x = MulAut.conj u (MulAut.conj v x) := by
  rw [map_mul]
  rfl

theorem commuting_conjugation_product (u v x : G) (hcommute : Commute u v) :
    MulAut.conj (u * v) x = MulAut.conj v (MulAut.conj u x) := by
  rw [hcommute.eq]
  exact conjugation_product v u x

theorem rightComponent_product_of_fixed (L : Subgroup G) (u v : G)
    (hcommute : Commute u v) (hfixed : rightComponent L v = L) :
    rightComponent L (u * v) = rightComponent L u := by
  rw [hcommute.eq, ← rightComponent_mul, hfixed]

theorem cyclic_trivial_le_single_centralizer (L : Subgroup G) (u : G)
    (htrivial : ⁅L, Subgroup.zpowers u⁆ = ⊥) :
    L ≤ Subgroup.centralizer ({u} : Set G) := by
  have hcentral := (cyclic_commutator_trivial_iff L u).mp htrivial
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hcentral x hx)

variable [Finite G]

theorem moved_component_fixed_second (L : Subgroup G) (u v : G)
    (hL : IsComponentOf L ⊤) (hu : u * u = 1) (hv : v * v = 1)
    (hcommute : Commute u v) (hmoved : rightComponent L u ≠ L)
    (hfixed : rightComponent L v = L) :
    L ≤ movedCentralizerPair L u v ∨ ⁅L, Subgroup.zpowers v⁆ = ⊥ := by
  by_cases htrivial : ⁅L, Subgroup.zpowers v⁆ = ⊥
  · exact Or.inr htrivial
  left
  let B := rightComponent L u
  let T := movedCentralizerPair L u v
  have huv := commuting_involution_product_square u v hu hv hcommute
  have hproduct := rightComponent_product_of_fixed L u v hcommute hfixed
  have hproductMoved : rightComponent L (u * v) ≠ L := by
    rwa [hproduct]
  have hproductHull : ⁅L, Subgroup.zpowers (u * v)⁆ = ⁅L, Subgroup.zpowers u⁆ := by
    rw [moved_component_commutator L (u * v) hL huv hproductMoved,
      moved_component_commutator L u hL hu hmoved, hproduct]
  have hBcomponent : IsComponentOf B ⊤ := rightComponent_component L hL u
  have hBfixed : rightComponent B v = B := by
    dsimp [B]
    rw [rightComponent_mul]
    exact hproduct
  have hBnormalizes : v ∈ Subgroup.normalizer (B : Set G) :=
    (rightComponent_eq_iff_normalizer B v).mp hBfixed
  have hconjv : MulAut.conj u v = v := by
    change u * v * u⁻¹ = v
    rw [hcommute.eq]
    group
  have hcyclicMap : (Subgroup.zpowers v).map (MulAut.conj u).toMonoidHom =
      Subgroup.zpowers v := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj u v) = Subgroup.zpowers v
    rw [hconjv]
  have hcommutatorMap : (⁅L, Subgroup.zpowers v⁆).map (MulAut.conj u).toMonoidHom =
      ⁅B, Subgroup.zpowers v⁆ := by
    change _ = ⁅rightComponent L u, Subgroup.zpowers v⁆
    rw [Subgroup.map_commutator, hcyclicMap, rightComponent_involution L u hu]
  have hBnoncentral : v ∉ Subgroup.centralizer (B : Set G) := by
    intro hcentral
    have hbot := (cyclic_commutator_trivial_iff B v).mpr hcentral
    have hmapBot : (⁅L, Subgroup.zpowers v⁆).map (MulAut.conj u).toMonoidHom = ⊥ :=
      hcommutatorMap.trans hbot
    exact htrivial ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hmapBot)
  have hBcommutator : ⁅B, Subgroup.zpowers v⁆ = B :=
    QuasisimpleNormalizerCommutator.eq_factor B hBcomponent.2.2 v hBnormalizes hBnoncentral
  have hBcontained : B ≤ T := by
    rw [← hBcommutator]
    apply cyclic_involution_commutator_le B T v hv
    intro m hm
    change m ∈ rightComponent L u at hm
    rw [rightComponent_involution L u hu] at hm
    rcases hm with ⟨x, hx, rfl⟩
    have hfirst := moved_component_diagonal L u hL hu hmoved x⁻¹ (L.inv_mem hx)
    have hsecond := moved_component_diagonal L (u * v) hL huv hproductMoved x⁻¹
      (L.inv_mem hx)
    have hfirstT : x⁻¹ * MulAut.conj u x⁻¹ ∈ T :=
      (le_sup_left :
        ⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u} : Set G) ≤ T) hfirst
    have hsecondT : x⁻¹ * MulAut.conj (u * v) x⁻¹ ∈ T := by
      exact (le_sup_right :
        ⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u * v} : Set G) ≤ T)
        ⟨hproductHull ▸ hsecond.1, hsecond.2⟩
    have hidentity : ⁅MulAut.conj u x, v⁆ =
        (x⁻¹ * MulAut.conj u x⁻¹)⁻¹ *
          (x⁻¹ * MulAut.conj (u * v) x⁻¹) := by
      rw [commuting_conjugation_product u v x⁻¹ hcommute]
      simp only [MulAut.conj_apply, commutatorElement_def]
      group
    change ⁅MulAut.conj u x, v⁆ ∈ T
    rw [hidentity]
    exact T.mul_mem (T.inv_mem hfirstT) hsecondT
  intro x hx
  have hdiag : x * MulAut.conj u x ∈ T :=
    (le_sup_left :
      ⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u} : Set G) ≤ T)
      (moved_component_diagonal L u hL hu hmoved x hx)
  have hpartner : MulAut.conj u x ∈ B := by
    dsimp [B]
    rw [rightComponent_involution L u hu]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx
  have hmember := T.mul_mem hdiag (T.inv_mem (hBcontained hpartner))
  simpa only [mul_inv_cancel_right] using hmember

end CFSG.ComponentClassification.AschbacherComponentAction
