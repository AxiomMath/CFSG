module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.GLTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.IrrQuotient

public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Quasithin.G11

variable {V : Type} [CommGroup V] [ExpTwo V] {A B : Type} [Group A] [Group B]

@[expose] def commSubOf (ρ : A →* MulAut V) (W : Subgroup V) : Subgroup V :=
  Subgroup.closure {x | ∃ a : A, ∃ w ∈ W, x = ρ a w * w⁻¹}

@[expose] def commSub (ρ : A →* MulAut V) : Subgroup V := commSubOf ρ ⊤

@[expose] def fixSubA (ρ : A →* MulAut V) : Subgroup V where
  carrier := {v | ∀ a, ρ a v = v}
  mul_mem' := fun {x y} hx hy a => by rw [map_mul, hx a, hy a]
  one_mem' := fun a => map_one (ρ a)
  inv_mem' := fun {x} hx a => by rw [map_inv, hx a]

@[expose] def IrrQuotGroup (ρ : A →* MulAut V) : Prop :=
  fixSubA ρ ⊓ commSub ρ < commSub ρ ∧
    ∀ W : Subgroup V, fixSubA ρ ⊓ commSub ρ ≤ W → W ≤ commSub ρ →
      (∀ a, ∀ w ∈ W, ρ a w ∈ W) → W = fixSubA ρ ⊓ commSub ρ ∨ W = commSub ρ

noncomputable def imageGL (ρ : A →* MulAut V) : Subgroup (GLV (Additive V)) :=
  (toGL.comp ρ).range

theorem toSubmodule_commSubOf (ρ : A →* MulAut V) (W : Subgroup V) :
    toSubmodule (commSubOf ρ W) = commSpace (imageGL ρ) (toSubmodule W) := by
  apply le_antisymm
  · suffices h : ∀ y ∈ commSubOf ρ W, Additive.ofMul y ∈ commSpace (imageGL ρ) (toSubmodule W) from
      fun x hx => h (Additive.toMul x) hx
    intro y hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, w, hw, rfl⟩ := hy
      have := sub_mem_commSpace (K := imageGL ρ) (k := toGL (ρ a)) ⟨a, rfl⟩
        (u := Additive.ofMul w) (U := toSubmodule W) hw
      have e : Additive.ofMul (ρ a w * w⁻¹) =
          toGL (ρ a) (Additive.ofMul w) - Additive.ofMul w := by
        rw [sub_eq_add_neg]; rfl
      rw [e]
      exact this
    | one => exact Submodule.zero_mem _
    | mul y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | inv y _ hy => exact Submodule.neg_mem _ hy
  · rw [commSpace_le_iff]
    rintro _ ⟨a, rfl⟩ u hu
    show Additive.toMul (toGL (ρ a) u - u) ∈ commSubOf ρ W
    exact Subgroup.subset_closure ⟨a, Additive.toMul u, hu, by
      simp [div_eq_mul_inv]; rfl⟩

theorem toSubmodule_commSub (ρ : A →* MulAut V) :
    toSubmodule (commSub ρ) = commSpace (imageGL ρ) ⊤ := by
  rw [commSub, toSubmodule_commSubOf]
  congr 1

theorem toSubmodule_fixSubA (ρ : A →* MulAut V) :
    toSubmodule (fixSubA ρ) = fixedSpace (imageGL ρ) := by
  ext u
  rw [mem_toSubmodule_iff_toMul]
  constructor
  · intro h k hk
    obtain ⟨a, rfl⟩ := hk
    exact congrArg Additive.ofMul (h a)
  · intro h a
    exact Additive.ofMul.injective (h (toGL (ρ a)) ⟨a, rfl⟩)

theorem toSubmodule_le_iff {W W' : Subgroup V} : toSubmodule W ≤ toSubmodule W' ↔ W ≤ W' :=
  ⟨fun h x hx => h (x := Additive.ofMul x) hx, fun h _ hx => h hx⟩

theorem toSubmodule_inf (W W' : Subgroup V) :
    toSubmodule (W ⊓ W') = toSubmodule W ⊓ toSubmodule W' := rfl

@[expose] def ofSubmodule (J : Submodule (ZMod 2) (Additive V)) : Subgroup V where
  carrier := {v | Additive.ofMul v ∈ J}
  mul_mem' := fun {_ _} ha hb => J.add_mem ha hb
  one_mem' := J.zero_mem
  inv_mem' := fun {_} ha => J.neg_mem ha

theorem toSubmodule_ofSubmodule (J : Submodule (ZMod 2) (Additive V)) :
    toSubmodule (ofSubmodule J) = J := by
  ext x
  exact Iff.rfl

variable [Finite V]

theorem centralizes_commSub_of_irrQuot (ρ : A →* MulAut V) (σ : B →* MulAut V)
    (hcomm : ∀ a b v, ρ a (σ b v) = σ b (ρ a v)) (hB : commutator B = ⊤)
    (hperf : commSub ρ ≤ commSubOf ρ (commSub ρ)) (hirr : IrrQuotGroup ρ) :
    ∀ b, ∀ u ∈ commSub ρ, σ b u = u := by
  set L : Subgroup (GLV (Additive V)) := imageGL ρ with hL
  set K : Subgroup (GLV (Additive V)) := (toGL.comp σ).range with hK
  have hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    ext x
    obtain ⟨v, rfl⟩ := Additive.ofMul.surjective x
    show Additive.ofMul (ρ a (σ b v)) = Additive.ofMul (σ b (ρ a v))
    rw [hcomm]
  have hKperf : commutator ↥K = ⊤ := by
    have hsurj : Function.Surjective (toGL.comp σ).rangeRestrict := MonoidHom.rangeRestrict_surjective _
    have h1 : ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = ⊤ := by rw [← commutator_def]; exact hB
    have h2 := Subgroup.map_commutator (⊤ : Subgroup B) (⊤ : Subgroup B)
      (toGL.comp σ).rangeRestrict
    rw [h1, Subgroup.map_top_of_surjective _ hsurj] at h2
    rw [commutator_def]
    exact h2.symm
  have hUL : Invariant L (commSpace L ⊤) := by
    refine invariant_commSpace (fun l' hl' l hl => L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl'))
      (invariant_top L)
  have hperfM : commSpace L (commSpace L ⊤) = commSpace L ⊤ := by
    apply le_antisymm (commSpace_le_of_invariant hUL)
    rw [← toSubmodule_commSub, ← toSubmodule_commSubOf]
    exact toSubmodule_le_iff.2 (by rw [← toSubmodule_commSub] at *; exact hperf)
  have hirrM : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := by
    rw [← toSubmodule_commSub, ← toSubmodule_fixSubA, ← toSubmodule_inf]
    refine ⟨?_, fun J hJ hCJ hJU => ?_⟩
    · exact lt_of_le_of_ne (toSubmodule_le_iff.2 inf_le_right) fun h =>
        hirr.1.ne (le_antisymm inf_le_right (toSubmodule_le_iff.1 h.ge))
    · set W : Subgroup V := ofSubmodule J with hW
      have hWJ : toSubmodule W = J := toSubmodule_ofSubmodule J
      rw [← hWJ] at hCJ hJU ⊢
      have hinv : ∀ a, ∀ w ∈ W, ρ a w ∈ W := by
        intro a w hw
        have := hJ (toGL (ρ a)) ⟨a, rfl⟩ (Additive.ofMul w) hw
        exact this
      rcases hirr.2 W (toSubmodule_le_iff.1 hCJ) (toSubmodule_le_iff.1 hJU) hinv with h | h
      · left; rw [h]
      · right; rw [h]
  have key := trivial_on_commSpace_of_irrSec hLK hKperf hperfM hirrM
  intro b u hu
  have hu' : Additive.ofMul u ∈ commSpace L ⊤ := by
    rw [← toSubmodule_commSub]; exact hu
  have := key (toGL (σ b)) ⟨b, rfl⟩ _ hu'
  exact Additive.ofMul.injective this

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
