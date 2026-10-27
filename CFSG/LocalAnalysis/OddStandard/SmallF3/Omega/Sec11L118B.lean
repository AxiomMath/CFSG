module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_lemmaB [Finite G] {z : G} {T W U : Subgroup G} (hWT : W ≤ T) (hzW : z ∈ W)
    (hW : IsElemAbelianMod z W) (hJ : JMod z T = W) (hUT : U ≤ T) (hzU : z ∈ U)
    (hU : IsElemAbelianMod z U) (hcard : Nat.card W ≤ Nat.card U) : U ≤ W := by
  set P : Set (Subgroup G) := {V | V ≤ T ∧ z ∈ V ∧ IsElemAbelianMod z V} with hP
  have hWP : W ∈ P := ⟨hWT, hzW, hW⟩
  obtain ⟨V, hVP, hVmax⟩ := Set.exists_max_image P (fun V : Subgroup G => Nat.card V)
    (Set.toFinite P) ⟨W, hWP⟩
  have hVmaxel : IsMaxElemAbelianMod z T V :=
    ⟨hVP.1, hVP.2.1, hVP.2.2, fun V' hV' hzV' hel => hVmax V' ⟨hV', hzV', hel⟩⟩
  have hVW : V ≤ W := by
    rw [← hJ]
    intro x hx
    exact Subgroup.subset_closure ⟨V, hVmaxel, hx⟩
  have hUmax : IsMaxElemAbelianMod z T U :=
    ⟨hUT, hzU, hU, fun V' hV' hzV' hel =>
      (hVmax V' ⟨hV', hzV', hel⟩).trans ((Subgroup.card_le_of_le hVW).trans hcard)⟩
  rw [← hJ]
  intro x hx
  exact Subgroup.subset_closure ⟨U, hUmax, hx⟩

end CFSG.OddStandard.SmallF3.Omega
