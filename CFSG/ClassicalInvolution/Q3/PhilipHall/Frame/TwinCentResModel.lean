module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin
import CFSG.Adapters.LieModelSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Balance

@[expose] def ModelFactSp62 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Blueprint.LieModel Q .PSp 3 2 1 →
    ∀ s : Q, orderOf s = 2 → oddCoreIn (Subgroup.centralizer ({s} : Set Q)) = ⊥

@[expose] def ModelFactD42 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1 →
    Q3NM.AutOddFree Q

@[expose] def ModelFactM12 : Prop :=
  IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) ∧
    Q3NM.AutOddFree (CFSG.Blueprint.NativeSporadic.Carrier .M12)

section Models

theorem isSimple_of_psp {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSp 3 2 1) :
    IsSimpleGroup Q :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem isSimple_of_pomegaPlus {Q : Type} [Group Q]
    (h : CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) : IsSimpleGroup Q :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem autOddFree_of_sp62 (hSp : ModelFactSp62) {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.Blueprint.LieModel Q .PSp 3 2 1) (hnab : ∃ a b : Q, a * b ≠ b * a) :
    Q3NM.AutOddFree Q := by
  have hsimp : IsSimpleGroup Q := isSimple_of_psp h
  have hinn : CFSG.ComponentClassification.OuterAutomorphisms.inner Q = ⊤ :=
    inner_eq_top_of_lieModel_psp_three_two
      (models_psp_three_two_of_blueprint (MulEquiv.refl Q) h)
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot_of_nonabelian hnab
  have hall : ∀ α : MulAut Q, α ∈ Q3NM.innSubgroup Q := fun α => by
    have : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Q :=
      hinn ▸ Subgroup.mem_top α
    exact this
  have hodd : ∀ α : MulAut Q, Odd (orderOf α) → α ∈ Q3NM.innSubgroup Q := fun α _ => hall α
  intro 𝒳 hinn' f hf
  have hf2 := Q3NM.mul_self_eq_one_of_orderOf_eq_two' hf
  refine Q3NM.involutionOddCore_eq_bot_of_fixed hZ hodd 𝒳 hinn' f hf2 ?_
  obtain ⟨s, hs⟩ := Q3NM.mem_innSubgroup_iff.mp (hall (f : MulAut Q))
  have hf2' : (f : MulAut Q) * (f : MulAut Q) = 1 := congrArg Subtype.val hf2
  have hss : s * s = 1 := by
    apply Q3NM.conj_injective_of_center_eq_bot hZ
    rw [map_mul, hs, hf2', map_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    have : f = 1 := Subtype.ext (by rw [← hs, map_one]; rfl)
    rw [this, orderOf_one] at hf
    omega
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  rw [← hs, Q3NM.fixedSubgroup_conj]
  exact hSp Q h s hs2

end Models

section Exits

variable {H : Type} [Group H] [Finite H]

@[expose] def MovedOddFreeIn (x : H) : Prop :=
  (∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, x * y ≠ y * x) → (∃ y ∈ L₂, x * y ≠ y * x) → L₁ = L₂) ∧
    ∀ L : Subgroup H, CFSG.IsComponent L → x ∈ Subgroup.normalizer (L : Set H) →
      (∃ y ∈ L, x * y ≠ y * x) → Q3NM.AutOddFreeOn ↥L (IsInducedAut L x)

theorem movedOddFreeIn_of_twinE4 (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h : TwinE4 H)
    (x : H) : MovedOddFreeIn x := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  have : Finite Q := Finite.of_surjective f hfs
  rcases hQ with hQ | hQ
  · have := isSimple_of_psp hQ
    exact atMostOne_oddFree_of_surj_simple f hfs hf2
      (fun hnab => autOddFree_of_sp62 hSp hQ hnab) x
  · have := isSimple_of_pomegaPlus hQ
    exact atMostOne_oddFree_of_surj_simple f hfs hf2 (fun _ => hD4 Q hQ) x

theorem movedOddFreeIn_of_tightE4 (hSp : ModelFactSp62) (hD4 : ModelFactD42) (h : TightE4 H)
    (x : H) : MovedOddFreeIn x :=
  movedOddFreeIn_of_twinE4 hSp hD4 (TightE4.twinE4 h) x

end Exits

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
