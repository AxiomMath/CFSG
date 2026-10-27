module

public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup
open scoped MatrixGroups

theorem quaternion_eq_or_sq_eq (g : QuaternionGroup 2) :
    g = 1 ∨ g = QuaternionGroup.a 2 ∨ g ^ 2 = QuaternionGroup.a 2 := by
  revert g
  decide

theorem injective_of_quaternion_a_two {G : Type*} [Group G] (q : QuaternionGroup 2 →* G)
    (hq : q (QuaternionGroup.a 2) ≠ 1) : Function.Injective q := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases quaternion_eq_or_sq_eq g with h | h | h
  · exact h
  · exact absurd (h ▸ hg) hq
  · exact absurd (by rw [← h, map_pow, hg, one_pow]) hq

theorem not_injective_quaternion_perm_six (φ : QuaternionGroup 2 →* Equiv.Perm (Fin 6)) :
    ¬ Function.Injective φ := by
  intro hφ
  have hz : φ (QuaternionGroup.a 2) ≠ 1 := fun h =>
    absurd (hφ (h.trans (map_one φ).symm)) (by decide)
  obtain ⟨x, hx⟩ : ∃ x, φ (QuaternionGroup.a 2) x ≠ x := by
    by_contra h
    push Not at h
    exact hz (Equiv.ext h)
  have hinj : Function.Injective fun g : QuaternionGroup 2 => φ g x := by
    intro g h hgh
    have hgh' : φ g x = φ h x := hgh
    have h1 : φ (h⁻¹ * g) x = x := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, hgh', ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
    rcases quaternion_eq_or_sq_eq (h⁻¹ * g) with h2 | h2 | h2
    · exact (inv_mul_eq_one.mp h2).symm
    · rw [h2] at h1
      exact absurd h1 hx
    · have h3 : φ ((h⁻¹ * g) ^ 2) x = x := by
        rw [map_pow, sq, Equiv.Perm.mul_apply, h1, h1]
      rw [h2] at h3
      exact absurd h3 hx
  have h86 := Fintype.card_le_of_injective _ hinj
  rw [QuaternionGroup.card, Fintype.card_fin] at h86
  omega

theorem false_of_quaternion_noncentral {L : Type*} [Group L]
    (eA : L ⧸ center L ≃* alternatingGroup (Fin 6)) (q : QuaternionGroup 2 →* L)
    (hq : q (QuaternionGroup.a 2) ∉ center L) : False := by
  let ψ : QuaternionGroup 2 →* Equiv.Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (eA.toMonoidHom.comp ((QuotientGroup.mk' _).comp q))
  refine not_injective_quaternion_perm_six ψ (injective_of_quaternion_a_two ψ fun h => hq ?_)
  have h1 : eA (QuotientGroup.mk' (center L) (q (QuaternionGroup.a 2))) = 1 := Subtype.ext h
  have h2 : QuotientGroup.mk' (center L) (q (QuaternionGroup.a 2)) = 1 :=
    eA.injective (h1.trans (map_one eA).symm)
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem false_of_sl2_hom_noncentral {L : Type*} [Group L]
    (eA : L ⧸ center L ≃* alternatingGroup (Fin 6)) {F : Type*} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (φ : SL(2, F) →* L) (hz : φ (-1) ∉ center L) : False := by
  obtain ⟨a, b, hab⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hF (-1)
  have hQa : LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab
      (QuaternionGroup.a 2) = -1 :=
    Subtype.ext (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom_a_two hab)
  refine false_of_quaternion_noncentral eA
    (φ.comp (LocalAnalysis.ComponentInitial.QuaternionMatrices.quatHom hab)) ?_
  rw [MonoidHom.comp_apply, hQa]
  exact hz

end CFSG.ComponentClassification.CatLeafProof
