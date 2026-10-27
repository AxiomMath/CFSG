module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutECore
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem autE_conclusion {G : Type*} [Group G] {E : Subgroup G} (hE : AutEFact ↥E) {β y : G}
    (hβN : β ∈ Subgroup.normalizer (E : Set G)) (hβ3 : β ^ 3 = 1)
    (hβne : ∃ e ∈ E, β * e ≠ e * β)
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) (hyβ : y * β = β * y)
    (hin : ∃ d ∈ E ⊓ Subgroup.centralizer ({β} : Set G),
      ∀ e ∈ E ⊓ Subgroup.centralizer ({β} : Set G), y * e * y⁻¹ = d * e * d⁻¹) :
    ∃ d ∈ E ⊓ Subgroup.centralizer ({β} : Set G), ∃ j : ℤ,
      ∀ e ∈ E, y * e * y⁻¹ = (d * β ^ j) * e * (d * β ^ j)⁻¹ := by
  set nβ : Subgroup.normalizer (E : Set G) := ⟨β, hβN⟩ with hnβ
  set ny : Subgroup.normalizer (E : Set G) := ⟨y, hyN⟩ with hny
  set b : MulAut E := E.normalizerMonoidHom nβ with hb
  set a : MulAut E := E.normalizerMonoidHom ny with ha
  have hbapp : ∀ (c : Subgroup.normalizer (E : Set G)) (e : E),
      ((E.normalizerMonoidHom c e : E) : G) = c * e * (c : G)⁻¹ := fun c e => rfl
  have hfix : ∀ e : E, b e = e ↔ β * e = e * β := by
    intro e
    rw [Subtype.ext_iff, hb, hbapp, hnβ]
    exact mul_inv_eq_iff_eq_mul.trans (by rw [eq_comm])
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← map_pow]
    convert map_one E.normalizerMonoidHom
    exact Subtype.ext (by simpa using hβ3)
  have hb1 : b ≠ 1 := by
    intro h1
    obtain ⟨e, he, hne⟩ := hβne
    apply hne
    have : b ⟨e, he⟩ = ⟨e, he⟩ := by rw [h1]; rfl
    exact (hfix ⟨e, he⟩).1 this
  have hab : a * b = b * a := by
    rw [ha, hb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hyβ
  obtain ⟨d, hdD, hd⟩ := hin
  obtain ⟨d', hd'fix, j, hj⟩ := hE b a hb3 hb1 hab ⟨⟨d, hdD.1⟩, (hfix _).2 (by
      have := mem_centralizer_iff.1 hdD.2 β rfl
      exact this), fun e he => by
      have hec : (e : G) ∈ E ⊓ Subgroup.centralizer ({β} : Set G) :=
        ⟨e.2, mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact
          ((hfix e).1 he)⟩
      apply Subtype.ext
      show y * e * y⁻¹ = d * e * d⁻¹
      exact hd e hec⟩
  have hd'c : (d' : G) ∈ Subgroup.centralizer ({β} : Set G) :=
    mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact (hfix d').1 hd'fix
  refine ⟨d', ⟨d'.2, hd'c⟩, (j : ℤ), fun e he => ?_⟩
  have h1 := congrArg Subtype.val (hj ⟨e, he⟩)
  have hpow : ∀ e : E, (((b ^ j) e : E) : G) = β ^ (j : ℤ) * e * (β ^ (j : ℤ))⁻¹ := by
    intro e
    rw [hb, ← map_pow, hbapp, hnβ]
    simp
  have h2 : y * e * y⁻¹ = (d' : G) * (β ^ (j : ℤ) * e * (β ^ (j : ℤ))⁻¹) * (d' : G)⁻¹ := by
    have h3 : ((a ⟨e, he⟩ : E) : G) = y * e * y⁻¹ := rfl
    rw [← h3, h1, ← hpow ⟨e, he⟩]
    rfl
  rw [h2]
  simp only [mul_inv_rev, mul_assoc]

end CFSG.EvenSporadicStandard.Fin76b
