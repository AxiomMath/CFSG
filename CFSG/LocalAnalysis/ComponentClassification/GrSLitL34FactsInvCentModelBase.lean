
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsElem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLift

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

section Witness

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

private theorem spec_mem {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ}
    (h : s ∈ [(FreeGroup.invRev witnessF ++ alphaF witnessF, 0, 0, 0),
      (wpow witnessF 2, 0, 0, 0),
      (FreeGroup.invRev witnessG ++ alphaG witnessG, 0, 0, 1),
      (wpow witnessG 2, 0, 0, 2),
      (FreeGroup.invRev witnessU ++ alphaU witnessU, 0, 0, 0),
      (wpow witnessU 2, 0, 0, 0)]) : s ∈ coverSpecs := by
  unfold coverSpecs
  exact List.mem_append_right _ h

theorem abTab_ne_of_witnessOK {w : List (Fin 2 × Bool)} {ρT : Tab} (h : witnessOK w ρT = true) :
    abTab w ≠ idTab 42 := by
  simp only [witnessOK, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  exact h.1.2

end Witness

variable {G : Type} [Group G]

theorem betaHat_congr (J : Subgroup G) {x y : G} (hx : x ∈ normalizer (J : Set G))
    (hy : y ∈ normalizer (J : Set G)) (h : x = y) (e : Jhat J) :
    betaHat J hx e = betaHat J hy e := by
  subst h
  rfl

theorem betaHat_of_mem {J : Subgroup G} {j : G} (hj : j ∈ J) (hjN : j ∈ normalizer (J : Set G))
    (e : Jhat J) : betaHat J hjN e = (jq J ⟨j, hj⟩)⁻¹ * e * jq J ⟨j, hj⟩ := by
  obtain ⟨i, rfl⟩ := jq_surjective J e
  rw [betaHat_jq, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem exists_fixed_involution_lift [Finite G] {J : Subgroup G} {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) {w : Jhat J} (hw2 : w * w = 1)
    (hwfix : betaHat J hxN w = w) :
    ∃ v ∈ J, v * v = 1 ∧ v * x = x * v ∧ ∀ hv : v ∈ J, jq J ⟨v, hv⟩ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 (zpowers w) := fun f => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    rcases eq_one_or_eq_of_mem_zpowers hw2 f.2 with h | h
    · rw [h, mul_one]
      rfl
    · rw [h, hw2]
      rfl)⟩
  have hfix : ∀ e ∈ zpowers w, betaHat J hxN e = e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    rw [map_zpow, hwfix]
  obtain ⟨E, hEJ, θ, hθ⟩ := exists_lift_fixed hxN hx2 hF2 hfix
  set v := θ.symm ⟨w, mem_zpowers w⟩ with hv
  have hvw : jq J ⟨v, (hEJ v.2).1⟩ = w := by
    rw [← hθ v, hv, MulEquiv.apply_symm_apply]
  have hvv : v * v = 1 := by
    apply θ.injective
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, hv, MulEquiv.apply_symm_apply, map_one]
    exact hw2
  refine ⟨v, (hEJ v.2).1, congrArg Subtype.val hvv,
    (mem_centralizer_singleton_iff.mp (hEJ v.2).2), fun _ => hvw⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
