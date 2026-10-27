module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionFour

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

open CFSG.Open
open AschbacherComponentAction
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def centralizerJoin (U : Subgroup G) : Subgroup G :=
  ⨆ (w : U) (_ : (w : G) ≠ 1), Subgroup.centralizer ({(w : G)} : Set G)

theorem centralizer_le_centralizerJoin (U : Subgroup G) {w : G} (hw : w ∈ U) (hne : w ≠ 1) :
    Subgroup.centralizer ({w} : Set G) ≤ centralizerJoin U :=
  le_iSup₂_of_le (⟨w, hw⟩ : U) hne le_rfl

theorem centralizerJoin_le_gammaOne (U : Subgroup G) : centralizerJoin U ≤ gammaOne U :=
  iSup₂_le fun w hne => centralizer_le_gammaOne U w w.2 hne

theorem movedCentralizerPair_le_centralizerJoin (U L : Subgroup G) (u v : G)
    (hu : u ∈ U) (huNe : u ≠ 1) (huv : u * v ∈ U) (huvNe : u * v ≠ 1) :
    movedCentralizerPair L u v ≤ centralizerJoin U := by
  apply sup_le
  · exact inf_le_right.trans (centralizer_le_centralizerJoin U hu huNe)
  · exact inf_le_right.trans (centralizer_le_centralizerJoin U huv huvNe)

variable [Finite G]

theorem moved_component_le_centralizerJoin (U L : Subgroup G) (u v : G)
    (hL : IsComponentOf L ⊤) (huU : u ∈ U) (hvU : v ∈ U)
    (hu : u * u = 1) (hv : v * v = 1) (huNe : u ≠ 1) (hvNe : v ≠ 1)
    (hne : u ≠ v) (hcommute : Commute u v) (hmoved : rightComponent L u ≠ L) :
    L ≤ centralizerJoin U := by
  have huv := commuting_involution_product_square u v hu hv hcommute
  have huvU := U.mul_mem huU hvU
  have huvNe : u * v ≠ 1 := by
    intro hone
    exact hne ((mul_eq_one_iff_eq_inv.mp hone).trans (involution_inverse v hv))
  by_cases hvfixed : rightComponent L v = L
  · rcases moved_component_fixed_second L u v hL hu hv hcommute hmoved hvfixed with hgen | htrivial
    · exact hgen.trans (movedCentralizerPair_le_centralizerJoin U L u v huU huNe huvU huvNe)
    · exact (cyclic_trivial_le_single_centralizer L v htrivial).trans
        (centralizer_le_centralizerJoin U hvU hvNe)
  by_cases huvfixed : rightComponent L (u * v) = L
  · have hcommuteProduct : Commute u (u * v) := (Commute.refl u).mul_right hcommute
    rcases moved_component_fixed_second L u (u * v) hL hu huv hcommuteProduct hmoved huvfixed
      with hgen | htrivial
    · have huuv : u * (u * v) = v := by rw [← mul_assoc, hu, one_mul]
      have hsecondU : u * (u * v) ∈ U := U.mul_mem huU huvU
      have hsecondNe : u * (u * v) ≠ 1 := by rwa [huuv]
      exact hgen.trans (movedCentralizerPair_le_centralizerJoin U L u (u * v)
        huU huNe hsecondU hsecondNe)
    · exact (cyclic_trivial_le_single_centralizer L (u * v) htrivial).trans
        (centralizer_le_centralizerJoin U huvU huvNe)
  let B := rightComponent L u
  have hBcomponent : IsComponentOf B ⊤ := rightComponent_component L hL u
  have hBmoved : rightComponent B v ≠ B :=
    partner_moved_by_commuting_involution L u v hu hcommute hvfixed
  let : Group.IsPerfect L := ⟨hL.2.2.1⟩
  apply perfect_le_of_all_squares L (centralizerJoin U)
  intro x hx
  let b := MulAut.conj u x
  let d := MulAut.conj (u * v) x
  have hb : b ∈ B := by
    dsimp [b, B]
    rw [rightComponent_involution L u hu]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx
  have hfirst : x * b ∈ centralizerJoin U :=
    centralizer_le_centralizerJoin U huU huNe
      (moved_component_diagonal L u hL hu hmoved x hx).2
  have hsecond : b⁻¹ * d⁻¹ ∈ centralizerJoin U := by
    have hdiag := (moved_component_diagonal B v hBcomponent hv hBmoved b⁻¹ (B.inv_mem hb)).2
    have hconj : MulAut.conj v b⁻¹ = d⁻¹ := by
      calc
        MulAut.conj v b⁻¹ = (MulAut.conj v b)⁻¹ := map_inv _ _
        _ = d⁻¹ := congrArg Inv.inv
          (commuting_conjugation_product u v x hcommute).symm
    rw [hconj] at hdiag
    exact centralizer_le_centralizerJoin U hvU hvNe hdiag
  have hthird : d * x ∈ centralizerJoin U := by
    have hdiag := (moved_component_diagonal L (u * v) hL huv huvfixed x hx).2
    have hcommuteXD := moved_component_conjugate_commutes L (u * v) hL huv huvfixed x hx
    change Commute x d at hcommuteXD
    rw [hcommuteXD.eq] at hdiag
    exact centralizer_le_centralizerJoin U huvU huvNe hdiag
  have hproduct : (x * b) * (b⁻¹ * d⁻¹) * (d * x) = x ^ 2 := by
    rw [pow_two]
    group
  exact hproduct ▸ (centralizerJoin U).mul_mem ((centralizerJoin U).mul_mem hfirst hsecond) hthird

theorem lemma_2_8_centralizers (U : Subgroup G) (hU : IsElemAbelian 2 U) (_hcard : Nat.card U = 4)
    (u v : G) (huOrder : orderOf u = 2) (hvOrder : orderOf v = 2)
    (hne : u ≠ v) (hgenerate : Subgroup.zpowers u ⊔ Subgroup.zpowers v = U)
    (L : Subgroup G) (hL : IsComponentOf L ⊤) (hmoved : rightComponent L u ≠ L) :
    L ≤ ⨆ (w : U) (_ : (w : G) ≠ 1), Subgroup.centralizer ({(w : G)} : Set G) ∧
      (rightComponent L v = L →
        L ≤ (⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
          (⁅L, Subgroup.zpowers u⁆ ⊓ Subgroup.centralizer ({u * v} : Set G)) ∨
        ⁅L, Subgroup.zpowers v⁆ = ⊥) := by
  have huU : u ∈ U := hgenerate ▸
    (le_sup_left : Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
      (Subgroup.mem_zpowers u)
  have hvU : v ∈ U := hgenerate ▸
    (le_sup_right : Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
      (Subgroup.mem_zpowers v)
  have hu : u * u = 1 := by simpa only [pow_two] using hU.2 u huU
  have hv : v * v = 1 := by simpa only [pow_two] using hU.2 v hvU
  have huNe : u ≠ 1 := by
    intro hone
    subst u
    simp at huOrder
  have hvNe : v ≠ 1 := by
    intro hone
    subst v
    simp at hvOrder
  have hcommute : Commute u v := by
    have hlocal := isMulCommutative_iff.mp hU.1 (⟨u, huU⟩ : U) (⟨v, hvU⟩ : U)
    exact congrArg Subtype.val hlocal
  exact ⟨moved_component_le_centralizerJoin U L u v hL huU hvU hu hv huNe hvNe hne hcommute
    hmoved, moved_component_fixed_second L u v hL hu hv hcommute hmoved⟩

end CFSG.ComponentClassification.AschbacherToolkit
