module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Quasithin

section Tr

variable {G : Type*} [Group G]

@[expose] def tr (S : Subgroup G) (α : S ≃* S) (g : G) (Y : Subgroup G) : Subgroup G :=
  cj (aimg S α Y) g

variable {S : Subgroup G} {α : S ≃* S} {g : G} {Y Y' : Subgroup G}

theorem tr_le : tr S α g Y ≤ cj S g := cj_mono aimg_le

theorem tr_mono (h : Y ≤ Y') : tr S α g Y ≤ tr S α g Y' := cj_mono (aimg_mono h)

theorem tr_sup (hY : Y ≤ S) (hY' : Y' ≤ S) :
    tr S α g (Y ⊔ Y') = tr S α g Y ⊔ tr S α g Y' := by
  unfold tr; rw [aimg_sup hY hY', cj_sup]

theorem tr_inf (hY : Y ≤ S) (hY' : Y' ≤ S) :
    tr S α g (Y ⊓ Y') = tr S α g Y ⊓ tr S α g Y' := by
  unfold tr; rw [aimg_inf hY hY', cj_inf]

theorem tr_commutator (hY : Y ≤ S) (hY' : Y' ≤ S) :
    tr S α g ⁅Y, Y'⁆ = ⁅tr S α g Y, tr S α g Y'⁆ := by
  unfold tr; rw [aimg_commutator hY hY', cj_commutator]

theorem tr_centralizer (hY' : Y' ≤ S) :
    tr S α g (Y ⊓ Subgroup.centralizer (Y' : Set G)) =
      tr S α g Y ⊓ Subgroup.centralizer ((tr S α g Y' : Subgroup G) : Set G) := by
  unfold tr; rw [aimg_centralizer hY', cj_inf, centralizer_cj]

theorem card_tr (hY : Y ≤ S) : Nat.card (tr S α g Y) = Nat.card Y := by
  unfold tr; rw [card_cj, card_aimg hY]

theorem tr_self : tr S α g S = cj S g := by
  unfold tr; rw [aimg_self]

theorem tr_bot : tr S α g ⊥ = ⊥ := by
  unfold tr; rw [aimg_bot, cj_bot]

@[expose] def trInv (S : Subgroup G) (α : S ≃* S) (g : G) (Y : Subgroup G) : Subgroup G :=
  aimg S α.symm (cj Y g⁻¹)

theorem trInv_le_S : trInv S α g Y ≤ S := aimg_le

theorem tr_trInv (hY : Y ≤ cj S g) : tr S α g (trInv S α g Y) = Y := by
  have h1 : cj Y g⁻¹ ≤ S := by
    intro x hx
    have := hY (mem_cj.mp hx)
    simpa [mem_cj, mul_assoc] using this
  unfold tr trInv
  rw [aimg_aimg_symm h1]
  exact cj_cj_inv

theorem trInv_tr (hY : Y ≤ S) : trInv S α g (tr S α g Y) = Y := by
  unfold tr trInv
  rw [cj_inv_cj]
  exact aimg_symm_aimg hY

theorem tr_le_tr_iff (hY : Y ≤ S) (hY' : Y' ≤ S) :
    tr S α g Y ≤ tr S α g Y' ↔ Y ≤ Y' := by
  constructor
  · intro h
    have h1 := aimg_mono (S := S) (α := α.symm) (cj_mono (g := g⁻¹) h)
    have e1 := trInv_tr (α := α) (g := g) hY
    have e2 := trInv_tr (α := α) (g := g) hY'
    unfold trInv at e1 e2
    rwa [e1, e2] at h1
  · exact tr_mono

theorem isElemAbelian_tr {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) :
    CFSG.Open.IsElemAbelian 2 (tr S α g A) :=
  isElemAbelian_cj (isElemAbelian_aimg α hA) g

theorem isMaxElemAbelian_tr [Finite G] {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    IsMaxElemAbelian (cj S g) (tr S α g A) :=
  isMaxElemAbelian_cj g (isMaxElemAbelian_aimg α hA)

theorem isMaxElemAbelian_trInv [Finite G] {A : Subgroup G} (hA : IsMaxElemAbelian (cj S g) A) :
    IsMaxElemAbelian S (trInv S α g A) := by
  have := isMaxElemAbelian_cj g⁻¹ hA
  rw [cj_inv_cj] at this
  exact isMaxElemAbelian_aimg α.symm this

theorem mem_tr {x : G} :
    x ∈ tr S α g Y ↔ ∃ y : S, (y : G) ∈ Y ∧ ((α y : S) : G) = g * x * g⁻¹ :=
  mem_cj.trans mem_aimg

theorem mem_tr_of_mem {y : S} (hy : (y : G) ∈ Y) : g⁻¹ * ((α y : S) : G) * g ∈ tr S α g Y := by
  rw [mem_tr]
  exact ⟨y, hy, by group⟩

end Tr

end CFSG.QuasithinUnique.Setup.Campbell