module

public import CFSG.ClassicalInvolution.Uniform.U8Shape
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpClassical

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Abstract

variable {K : Type*} [Group K]

theorem false_of_universalPartner_of_layer3 {Fund : Set (Subgroup K)}
    (hconj : ∀ R ∈ Fund, ∀ g : K, conjSub g R ∈ Fund) (hgen : ∀ R ∈ Fund, ModelFacts.Gen3 R)
    (hnab : ∀ R ∈ Fund, ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) {R₀ R₁ : Subgroup K}
    (hP : NonClassical.UniversalPartner Fund R₀ R₁)
    (hlayer : ∃ L : Subgroup K, CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (R₀ : Set K) ∧
      (∀ x ∈ Subgroup.centralizer (R₀ : Set K), x ^ 3 = 1 → x ∈ L) ∧ L ∉ Fund) : False := by
  obtain ⟨hR₁, -, hc, huniv⟩ := hP
  obtain ⟨L, hLqs, hLC, hL3, hLfund⟩ := hlayer
  have hR₁C : R₁ ≤ Subgroup.centralizer (R₀ : Set K) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have hR₁L : R₁ ≤ L := by
    obtain ⟨S, hSR, hS3, hRS⟩ := hgen R₁ hR₁
    exact hRS.trans ((Subgroup.closure_le _).2 fun s hs => hL3 s (hR₁C (hSR hs)) (hS3 s hs))
  obtain ⟨g, hgL, hg1, hg2⟩ := exists_conj_not_commutes_of_le hLqs hR₁L (hnab R₁ hR₁)
    (fun hLR => hLfund (le_antisymm hLR hR₁L ▸ hR₁))
  have hSL : conjSub g R₁ ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hgL (hR₁L hy)) (L.inv_mem hgL)
  have hcS : Commutes (conjSub g R₁) R₀ := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hLC (hSL hx)) y hy).symm
  rcases huniv _ (hconj R₁ hR₁ g) hcS with h | h
  · exact hg1 h
  · exact hg2 h

end Abstract

set_option linter.unusedSectionVars false


theorem noTE6Config3_of_hasLayer3 {t : StatedLieTag} {n : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hlayer : Uniform.HasLayer3 t n) :
    NonClassical.NoTE6Config
      (Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D) := by
  intro R₀ hR₀ R₁ hP _
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hsl2 : ∀ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR
  refine false_of_universalPartner_of_layer3
    (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => (hsl2 R hR).elim fun φ => ModelFacts.gen3_of_equiv_sl2 φ)
    (fun R hR hab => ?_) hP (hlayer R₀ hR₀)
  obtain ⟨φ⟩ := hsl2 R hR
  apply Uniform.sl2_exists_not_comm (GaloisField 3 1)
  intro A B
  apply φ.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext (hab _ (φ.symm A).2 _ (φ.symm B).2)

end CFSG.ClassicalInvolution.Q3.Q3W
