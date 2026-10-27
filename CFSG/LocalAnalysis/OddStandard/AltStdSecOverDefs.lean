module

public import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic.Group
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Conj

variable {G : Type*} [Group G]

@[expose] def cjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cjSub {g : G} {H : Subgroup G} {x : G} : x ∈ cjSub g H ↔ g⁻¹ * x * g ∈ H := by
  unfold cjSub
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cjSub_mul (g h : G) (H : Subgroup G) : cjSub (g * h) H = cjSub g (cjSub h H) := by
  ext x
  simp only [mem_cjSub]
  have : h⁻¹ * (g⁻¹ * x * g) * h = (g * h)⁻¹ * x * (g * h) := by group
  rw [this]

theorem cjSub_one (H : Subgroup G) : cjSub 1 H = H := by
  ext x
  simp [mem_cjSub]

theorem cjSub_inv_cjSub (g : G) (H : Subgroup G) : cjSub g⁻¹ (cjSub g H) = H := by
  rw [← cjSub_mul, inv_mul_cancel, cjSub_one]

theorem cjSub_injective (g : G) : Function.Injective (cjSub g : Subgroup G → Subgroup G) :=
  fun H K h => by
    have := congrArg (cjSub g⁻¹) h
    rwa [cjSub_inv_cjSub, cjSub_inv_cjSub] at this

theorem mem_cjSub_of_mem {g : G} {H : Subgroup G} {x : G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cjSub g H :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem mem_normalizer_of_cjSub_eq {w : G} {K : Subgroup G} (h : cjSub w K = K) :
    w ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : w * x * w⁻¹ ∈ cjSub w K := mem_cjSub_of_mem hx
    rwa [h] at this
  · intro hx
    have h1 : w * x * w⁻¹ ∈ cjSub w K := by rw [h]; exact hx
    rw [mem_cjSub] at h1
    have h2 : w⁻¹ * (w * x * w⁻¹) * w = x := by group
    rwa [h2] at h1

theorem cjSub_eq_of_mem_normalizer {x : G} {K : Subgroup G} (hx : x ∈ normalizer (K : Set G)) :
    cjSub x K = K := by
  ext y
  rw [mem_cjSub]
  have h1 := (mem_normalizer_iff.1 (Subgroup.inv_mem _ hx)) y
  simpa using h1.symm

theorem card_cjSub (g : G) (H : Subgroup G) : Nat.card (cjSub g H) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

end Conj

section Stab

variable {G : Type*} [Group G]

@[expose] def subStab (P : Set (Subgroup G)) : Subgroup G where
  carrier := {g | cjSub g '' P = P}
  one_mem' := by
    show cjSub 1 '' P = P
    simp [cjSub_one]
  mul_mem' := by
    intro g h hg hh
    show cjSub (g * h) '' P = P
    have hg' : cjSub g '' P = P := hg
    have hh' : cjSub h '' P = P := hh
    have : cjSub (g * h) = cjSub g ∘ cjSub h := by
      funext K
      exact cjSub_mul g h K
    rw [this, Set.image_comp, hh', hg']
  inv_mem' := by
    intro g hg
    show cjSub g⁻¹ '' P = P
    have hg' : cjSub g '' P = P := hg
    calc cjSub g⁻¹ '' P = cjSub g⁻¹ '' (cjSub g '' P) := by rw [hg']
      _ = P := by
        rw [Set.image_image]
        simp [cjSub_inv_cjSub]

theorem mem_subStab {P : Set (Subgroup G)} {g : G} : g ∈ subStab P ↔ cjSub g '' P = P := Iff.rfl

theorem mem_subStab_pair_iff {H K : Subgroup G} (hne : H ≠ K) {g : G} :
    g ∈ subStab {H, K} ↔ (cjSub g H = H ∧ cjSub g K = K) ∨ (cjSub g H = K ∧ cjSub g K = H) := by
  rw [mem_subStab]
  constructor
  · intro h
    have h1 : cjSub g H ∈ ({H, K} : Set (Subgroup G)) := by
      rw [← h]; exact ⟨H, by simp, rfl⟩
    have h2 : cjSub g K ∈ ({H, K} : Set (Subgroup G)) := by
      rw [← h]; exact ⟨K, by simp, rfl⟩
    have hne' : cjSub g H ≠ cjSub g K := fun e => hne (cjSub_injective g e)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne'
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [Set.image_pair, h1, h2]
    · rw [Set.image_pair, h1, h2, Set.pair_comm]

end Stab

section Char

variable {G : Type*} [Group G]

open Classical in
@[expose] noncomputable def pairCharFun (H : Subgroup G) (g : G) : Multiplicative (ZMod 2) :=
  if cjSub g H = H then 1 else Multiplicative.ofAdd 1

theorem pairCharFun_mul {H K : Subgroup G} (hne : H ≠ K) {g h : G}
    (hg : g ∈ subStab ({H, K} : Set (Subgroup G))) (hh : h ∈ subStab ({H, K} : Set (Subgroup G))) :
    pairCharFun H (g * h) = pairCharFun H g * pairCharFun H h := by
  classical
  have hg' := (mem_subStab_pair_iff hne).1 hg
  have hh' := (mem_subStab_pair_iff hne).1 hh
  have hgh : cjSub (g * h) H = cjSub g (cjSub h H) := cjSub_mul _ _ _
  have hne' : K ≠ H := Ne.symm hne
  unfold pairCharFun
  rw [hgh]
  rcases hg' with ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩ <;> rcases hh' with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
  · simp [hh1, hg1]
  · simp [hh1, hg1, hg2, hne']
  · simp [hh1, hg1, hne']
  · have h4 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
      decide
    simp [hh1, hg1, hg2, hne', h4]

@[expose] noncomputable def pairChar (H K : Subgroup G) (hne : H ≠ K) :
    subStab ({H, K} : Set (Subgroup G)) →* Multiplicative (ZMod 2) where
  toFun g := pairCharFun H (g : G)
  map_one' := by
    classical
    simp [pairCharFun, cjSub_one]
  map_mul' g h := pairCharFun_mul hne g.2 h.2

theorem pairCharFun_eq_one_iff {H : Subgroup G} {g : G} : pairCharFun H g = 1 ↔ cjSub g H = H := by
  classical
  unfold pairCharFun
  by_cases h : cjSub g H = H
  · simp [h]
  · simp only [h, ite_false, iff_false]
    decide

theorem pairChar_eq_one_iff {H K : Subgroup G} (hne : H ≠ K)
    {g : subStab ({H, K} : Set (Subgroup G))} :
    pairChar H K hne g = 1 ↔ cjSub (g : G) H = H :=
  pairCharFun_eq_one_iff

end Char

end CFSG.OddStandard.AltStdSec
