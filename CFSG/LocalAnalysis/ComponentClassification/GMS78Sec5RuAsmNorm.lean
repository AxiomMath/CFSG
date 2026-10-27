module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmDefs

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.ComponentClassification.GMS78.RuPi7

structure RuAlignFacts : Prop where
  M2_le : ruM2 ≤ normalizer (ruA0 : Set Pi7)
  trans_A0 : ∀ a ∈ ruA0, a ≠ 1 → ∃ m ∈ ruM2, m * ruZ0 * m⁻¹ = a

theorem ruM12_le_ruM1 : ruM12 ≤ ruM1 := letterSub_mono (by decide)

theorem ruM12_le_ruM2 : ruM12 ≤ ruM2 := letterSub_mono (by decide)

variable {G : Type} [Group G] {z : G} {A : Subgroup G}

theorem exists_aligned (hF : RuAlignFacts) (hzA : z ∈ A) (hz1 : z ≠ 1)
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G)))
    (h₂ : ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂ m : ↥(normalizer (A : Set G))) : G) ∈ A) :
    ∃ f₂' : ↥ruM2 ≃* ↥(normalizer (A : Set G)),
      (∀ m : ↥ruM2, (m : Pi7) = ruZ0 → ((f₂' m : ↥(normalizer (A : Set G))) : G) = z) ∧
      ∀ m : ↥ruM2, (m : Pi7) ∈ ruA0 ↔ ((f₂' m : ↥(normalizer (A : Set G))) : G) ∈ A := by
  obtain ⟨a, ha⟩ := f₂.surjective ⟨z, le_normalizer hzA⟩
  have haA : (a : Pi7) ∈ ruA0 := (h₂ a).mpr (by rw [ha]; exact hzA)
  have ha1 : (a : Pi7) ≠ 1 := fun h => hz1 (by
    have h1 : a = 1 := Subtype.ext h
    rw [h1, map_one] at ha
    exact (congrArg Subtype.val ha).symm)
  obtain ⟨m, hm, hmz⟩ := hF.trans_A0 _ haA ha1
  refine ⟨(MulAut.conj (⟨m, hm⟩ : ↥ruM2)).trans f₂, fun x hx => ?_, fun x => ?_⟩
  · have e : (MulAut.conj (⟨m, hm⟩ : ↥ruM2)) x = a := by
      rw [MulAut.conj_apply]
      exact Subtype.ext (by rw [coe_mul, coe_mul, coe_inv, hx]; exact hmz)
    rw [MulEquiv.trans_apply, e, ha]
  · rw [MulEquiv.trans_apply, ← h₂, MulAut.conj_apply, coe_mul, coe_mul, coe_inv]
    have hmN := hF.M2_le hm
    constructor
    · intro hx
      exact (mem_normalizer_iff.mp hmN _).mp hx
    · intro hx
      have h3 := (mem_normalizer_iff.mp (inv_mem hmN) _).mp hx
      simpa [mul_assoc] using h3

@[expose] def RuEdgeAgree (f₁ : ↥ruM1 ≃* ↥(centralizer ({z} : Set G)))
    (f₂ : ↥ruM2 ≃* ↥(normalizer (A : Set G))) (β : ↥ruM12 →* ↥ruM12) : Prop :=
  ∀ m : ↥ruM12, ((f₁ (inclusion ruM12_le_ruM1 m) : ↥(centralizer ({z} : Set G))) : G) =
    ((f₂ (inclusion ruM12_le_ruM2 (β m)) : ↥(normalizer (A : Set G))) : G)

end CFSG.ComponentClassification.GMS78.RuAsm
