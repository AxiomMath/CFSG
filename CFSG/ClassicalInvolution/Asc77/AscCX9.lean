module

public import CFSG.ClassicalInvolution.Asc77.AscCX8F

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ParityE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ d₁ d₂ : G,
        d₁ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        d₂ ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        d₁ * d₁ = 1 → d₂ * d₂ = 1 → d₁ * d₂ = d₂ * d₁ →
        d₁ ≠ 1 → d₂ ≠ 1 → d₁ ≠ d₂ → z ≠ d₁ → z ≠ d₂ → z ≠ d₁ * d₂ →
        z ∉ zStarOf (Subgroup.centralizer ({d₁, d₂} : Set G)) →
        (∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G),
          z ∉ zStarOf (Subgroup.centralizer ({d} : Set G)) ∧
            z ∉ zStarOf (Subgroup.centralizer ({d * z} : Set G))) →
        (∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G),
          (LayerOrthType p f Ω d 5 true ∨ LayerOrthType p f Ω d 6 (!piSign p f)) ∧
            (LayerOrthType p f Ω (d * z) 5 true ∨
              LayerOrthType p f Ω (d * z) 6 (!piSign p f))) →
        False

end Residual

section Reduction

variable {p f : ℕ} [Fact p.Prime]


theorem noMixParity_of_parityE4 (h : ParityE4 p f) : NoMixParity p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp D hDA hDbad hcov h4 hsq hcomm hnomix htyp
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzD : z ∉ D := not_mem_of_badSub hyp hDA hDbad
  have hbadD : ∀ x ∈ D, z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) := fun x hx =>
    C25W.not_mem_zStarOf_of_mem_badSub hx (fun y hy => hzS y (hDA hy).1) hDbad
  obtain ⟨d₁, hd₁D, hd₁1⟩ : ∃ d₁ ∈ D, d₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (a := 1) (b := 1) fun x hx => Or.inl (hcon x hx)
    omega
  obtain ⟨d₂, hd₂D, hd₂1, hd₂₁⟩ : ∃ d₂ ∈ D, d₂ ≠ 1 ∧ d₂ ≠ d₁ := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (a := 1) (b := d₁) fun x hx => by
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · exact Or.inr (hcon x hx hx1)
    omega
  have hd₁₂D : d₁ * d₂ ∈ D := D.mul_mem hd₁D hd₂D
  have hmemD : ∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G), d ∈ D := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd₁D
    · exact hd₂D
    · exact hd₁₂D
  have hzne : ∀ d ∈ D, z ≠ d := fun d hd h => hzD (h ▸ hd)
  have hgood : ∀ d ∈ D, d ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({d} : Set G)) ∧
      z ∉ zStarOf (Subgroup.centralizer ({d * z} : Set G)) := by
    intro d hd hd1
    refine ⟨hbadD d hd, hnomix d (hDA hd) ?_ (hbadD d hd)⟩
    intro hdz
    rcases mem_zpowers_of_sq hz2 hdz with h1 | h1
    · exact hd1 h1
    · exact hzne d hd h1.symm
  have hne1 : ∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G), d ≠ 1 := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd₁1
    · exact hd₂1
    · intro h1
      apply hd₂₁
      calc d₂ = d₁⁻¹ * (d₁ * d₂) := by group
        _ = d₁ := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (hsq d₁ hd₁D)]
  refine h G Ω K K' W S R R' z t u₁ u₂ hyp d₁ d₂ (hDA hd₁D) (hDA hd₂D) (hsq d₁ hd₁D)
    (hsq d₂ hd₂D) (hcomm d₁ hd₁D d₂ hd₂D) hd₁1 hd₂1 hd₂₁.symm (hzne d₁ hd₁D) (hzne d₂ hd₂D)
    (hzne _ hd₁₂D) ?_ (fun d hd => hgood d (hmemD d hd) (hne1 d hd)) fun d hd => ?_
  ·
    intro hz
    apply hDbad
    refine T7T.mem_zStarOf_of_le ?_ hz ?_
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      rintro x (rfl | rfl)
      · exact hg _ hd₁D
      · exact hg _ hd₂D
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hDA hg).1
  ·
    have hdD := hmemD d hd
    have hdA := hDA hdD
    have hdz : d * z = z * d := hzS d hdA.1
    have hdzA : d * z ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ hdA (T7T.z_mem_centralizer_of_hyp hyp)
    refine ⟨htyp d hdA (hsq d hdD) (hne1 d hd) (hgood d hdD (hne1 d hd)).1, ?_⟩
    refine htyp (d * z) hdzA ?_ ?_ (hgood d hdD (hne1 d hd)).2
    · calc d * z * (d * z) = (d * d) * (z * z) := by
            rw [show d * z * (d * z) = d * (z * d) * z by group, ← hdz]
            group
        _ = 1 := by rw [hsq d hdD, hz2, one_mul]
    · intro h1
      apply hzne d hdD
      calc z = d⁻¹ * (d * z) := by group
        _ = d := by rw [h1, mul_one, inv_eq_of_mul_eq_one_right (hsq d hdD)]

theorem centExt_of_parityE4 (h : ParityE4 p f) : C25W.CentExt p f :=
  centExt_of_noMixParity' (noMixParity_of_parityE4 h)

end Reduction

end CFSG.ClassicalInvolution.Asc77.CX
