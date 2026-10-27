module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDKDBase

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDKD

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.HSFLit
open CFSG.OddStandard.SmallF3.L33.KD.SD

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {A : SDData t L}

@[expose] def fstHom : Multiplicative (ZMod 2 × ZMod 2) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x).1
  map_one' := rfl
  map_mul' _ _ := rfl

variable (A) in
@[expose] noncomputable def dbitT : A.T →* Multiplicative (ZMod 2) :=
  fstHom.comp (type8.comp A.ψH)

theorem dbitT_apply {g : X} (hg : g ∈ A.T) {u : (ZMod 8)ˣ} {b : ZMod 8}
    (hψ : ψX A g = aff8 u b) : dbitT A ⟨g, hg⟩ = Multiplicative.ofAdd (dbit8 b) := by
  have e1 : (A.ψH ⟨g, hg⟩) = ⟨aff8 u b, aff8_mem_H8 u b⟩ := by
    apply Subtype.ext
    rw [SDData.ψH_coe, ← ψX_of_mem hg, hψ]
  change fstHom (type8 (A.ψH ⟨g, hg⟩)) = _
  rw [e1, type8_aff8]
  rfl

variable (A) in
@[expose] noncomputable def TE : Subgroup X := (dbitT A).ker.map A.T.subtype

theorem mem_TE {g : X} : g ∈ TE A ↔ ∃ hg : g ∈ A.T, dbitT A ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

variable (C : A.CaseKD)

include C in
theorem card_T_eq_two_mul_card_TE : Nat.card A.T = 2 * Nat.card (TE A) := by
  have hd : dbitT A ⟨C.d, C.d_mem⟩ = Multiplicative.ofAdd 1 := by
    rw [dbitT_apply C.d_mem (ψX_d C)]
    rfl
  have hrange : (dbitT A).range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 := by decide
    rcases hx x with rfl | rfl
    · exact one_mem _
    · exact ⟨_, hd⟩
  have hidx : (dbitT A).ker.index = 2 := by
    rw [Subgroup.index_ker, hrange, card_top, Nat.card_eq_fintype_card]
    rfl
  have h := (dbitT A).ker.card_mul_index
  rw [hidx] at h
  have hTE : Nat.card (TE A) = Nat.card (dbitT A).ker :=
    card_map_of_injective (subtype_injective _)
  rw [hTE, ← h, mul_comm]

variable [Finite X]

end CFSG.OddStandard.SmallF3.L33.KD.SDKD
