module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X3
public import CFSG.ClassicalInvolution.Asc77.AscCX9U

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Asc77.CX (centralizer_pair_comm centralizer_pair_mul)


section Pair

theorem centralizer_pair_eq_of {G : Type} [Group G] {a b c : G} (h : c = a * b) :
    Subgroup.centralizer ({a, c} : Set G) = Subgroup.centralizer ({a, b} : Set G) := by
  rw [h]
  exact centralizer_pair_mul a b

end Pair

section Face

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def NoFaceAt (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) : Prop :=
  ∀ {w₁ w₂ w₃ : G}, w₁ ∈ cA S R R' → w₂ ∈ cA S R R' → w₃ ∈ cA S R R' →
    w₁ * w₁ = 1 → w₂ * w₂ = 1 → w₃ * w₃ = 1 → w₁ ≠ 1 → w₂ ≠ 1 → w₃ ≠ 1 →
    w₁ * w₂ = w₂ * w₁ → w₁ * w₃ = w₃ * w₁ → w₂ * w₃ = w₃ * w₂ → w₁ * w₂ * w₃ = z →
    BadElt z w₁ → BadElt z w₂ → BadElt z w₃ →
    z ∉ zStarOf (Subgroup.centralizer ({w₁, w₂} : Set G)) →
    z ∉ zStarOf (Subgroup.centralizer ({w₁, w₃} : Set G)) →
    z ∉ zStarOf (Subgroup.centralizer ({w₂, w₃} : Set G)) → False

@[expose] def P25X_NoFace : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G)
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂), NoFaceAt hyp

theorem parityE4_of (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp) (hF : NoFaceAt hyp)
    {d₁ d₂ : G} (hd₁A : d₁ ∈ cA S R R') (hd₂A : d₂ ∈ cA S R R') (hs₁ : d₁ * d₁ = 1)
    (hs₂ : d₂ * d₂ = 1) (hc₁₂ : d₁ * d₂ = d₂ * d₁) (hn₁ : d₁ ≠ 1) (hn₂ : d₂ ≠ 1) (hne : d₁ ≠ d₂)
    (hz₁ : z ≠ d₁) (hz₂ : z ≠ d₂) (hz₁₂ : z ≠ d₁ * d₂)
    (hD₀ : z ∉ zStarOf (Subgroup.centralizer ({d₁, d₂} : Set G)))
    (hbad : ∀ d ∈ ({d₁, d₂, d₁ * d₂} : Set G), BadElt z d ∧ BadElt z (d * z)) : False := by
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have m₁ : d₁ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert _ _
  have m₂ : d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have m₃ : d₁ * d₂ ∈ ({d₁, d₂, d₁ * d₂} : Set G) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  have C₁ : Commute d₁ z := hzS d₁ hd₁A.1
  have C₂ : Commute d₂ z := hzS d₂ hd₂A.1
  have C₁₂ : Commute d₁ d₂ := hc₁₂
  have cm : ∀ {x w : G}, Commute x w → x ∈ Subgroup.centralizer ({w} : Set G) := fun h =>
    Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  have hA₃ : d₁ * d₂ ∈ cA S R R' := Subgroup.mul_mem _ hd₁A hd₂A
  have hB₁ : d₁ * z ∈ cA S R R' := Subgroup.mul_mem _ hd₁A hzA
  have hB₂ : d₂ * z ∈ cA S R R' := Subgroup.mul_mem _ hd₂A hzA
  have hB₃ : d₁ * d₂ * z ∈ cA S R R' := Subgroup.mul_mem _ hA₃ hzA
  have sq : ∀ {a b : G}, Commute a b → a * a = 1 → b * b = 1 → a * b * (a * b) = 1 :=
    fun {a b} h ha hb => by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [h.eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  have sa₃ : d₁ * d₂ * (d₁ * d₂) = 1 := sq C₁₂ hs₁ hs₂
  have sb₁ : d₁ * z * (d₁ * z) = 1 := sq C₁ hs₁ hz2
  have sb₂ : d₂ * z * (d₂ * z) = 1 := sq C₂ hs₂ hz2
  have sb₃ : d₁ * d₂ * z * (d₁ * d₂ * z) = 1 := sq (C₁.mul_left C₂) sa₃ hz2
  have ne : ∀ {a b : G}, a * a = 1 → a ≠ b → a * b ≠ 1 := fun {a b} ha hab h => by
    apply hab
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, ha, one_mul]
  have na₃ : d₁ * d₂ ≠ 1 := ne hs₁ hne
  have nb₁ : d₁ * z ≠ 1 := ne hs₁ (Ne.symm hz₁)
  have nb₂ : d₂ * z ≠ 1 := ne hs₂ (Ne.symm hz₂)
  have nb₃ : d₁ * d₂ * z ≠ 1 := ne sa₃ (Ne.symm hz₁₂)
  obtain ⟨bd₁, bb₁⟩ := hbad d₁ m₁
  obtain ⟨bd₂, bb₂⟩ := hbad d₂ m₂
  obtain ⟨ba₃, bb₃⟩ := hbad _ m₃
  have L₁ := not_good_and_good (hQ hB₁ sb₁ nb₁ bb₁) hB₁ hd₂A (cm (C₁₂.symm.mul_right C₂))
  have L₂ := not_good_and_good (hQ hB₂ sb₂ nb₂ bb₂) hB₂ hd₁A (cm (C₁₂.mul_right C₁))
  have L₃ := not_good_and_good (hQ hB₃ sb₃ nb₃ bb₃) hB₃ hd₁A
    (cm (((Commute.refl d₁).mul_right C₁₂).mul_right C₁))
  rw [centralizer_pair_comm (d₂ * z), centralizer_pair_comm (d₂ * z)] at L₂
  have r₁ : d₁ * d₂ * z = d₁ * (d₂ * z) := mul_assoc _ _ _
  have r₂ : d₁ * d₂ * z = d₁ * z * d₂ := by
    rw [mul_assoc d₁ z, ← C₂.eq, ← mul_assoc]
  rw [centralizer_pair_comm (d₁ * d₂ * z), centralizer_pair_comm (d₁ * d₂ * z),
    centralizer_pair_eq_of r₁, centralizer_pair_eq_of r₂] at L₃
  by_cases G1 : z ∈ zStarOf (Subgroup.centralizer ({d₁, d₂ * z} : Set G))
  · have nG2 := fun h => L₃ ⟨G1, h⟩
    have nG3 := fun h => L₂ ⟨G1, h⟩
    have r₃ : d₁ * d₂ = d₁ * z * (d₂ * z) := by
      calc d₁ * d₂ = d₁ * d₂ * (z * z) := by rw [hz2, mul_one]
        _ = d₁ * (d₂ * z) * z := by group
        _ = d₁ * (z * d₂) * z := by rw [C₂.eq]
        _ = d₁ * z * (d₂ * z) := by group
    refine hF hd₂A hA₃ hB₁ hs₂ sa₃ sb₁ hn₂ na₃ nb₁
      (C₁₂.symm.mul_right (Commute.refl d₂)).eq (C₁₂.symm.mul_right C₂).eq
      (Commute.mul_left ((Commute.refl d₁).mul_right C₁) (C₁₂.symm.mul_right C₂)).eq ?_
      bd₂ ba₃ bb₁ ?_ ?_ ?_
    · calc d₂ * (d₁ * d₂) * (d₁ * z) = d₂ * (d₂ * d₁) * (d₁ * z) := by rw [C₁₂.eq]
        _ = (d₂ * d₂) * (d₁ * d₁) * z := by group
        _ = z := by rw [hs₂, hs₁, one_mul, one_mul]
    · rw [centralizer_pair_eq_of C₁₂.eq, centralizer_pair_comm]
      exact hD₀
    · rw [centralizer_pair_comm]
      exact nG2
    · rw [centralizer_pair_comm, centralizer_pair_eq_of r₃]
      exact nG3
  · by_cases G2 : z ∈ zStarOf (Subgroup.centralizer ({d₁ * z, d₂} : Set G))
    · have nG3 := fun h => L₁ ⟨G2, h⟩
      have r₄ : d₁ * d₂ = d₂ * z * (d₁ * z) := by
        calc d₁ * d₂ = d₂ * d₁ * (z * z) := by rw [hz2, mul_one, C₁₂.eq]
          _ = d₂ * (d₁ * z) * z := by group
          _ = d₂ * (z * d₁) * z := by rw [C₁.eq]
          _ = d₂ * z * (d₁ * z) := by group
      refine hF hd₁A hA₃ hB₂ hs₁ sa₃ sb₂ hn₁ na₃ nb₂
        ((Commute.refl d₁).mul_right C₁₂).eq (C₁₂.mul_right C₁).eq
        (Commute.mul_left (C₁₂.mul_right C₁) ((Commute.refl d₂).mul_right C₂)).eq ?_
        bd₁ ba₃ bb₂ ?_ G1 ?_
      · calc d₁ * (d₁ * d₂) * (d₂ * z) = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_mul]
        exact hD₀
      · rw [centralizer_pair_comm, centralizer_pair_eq_of r₄, centralizer_pair_comm]
        exact nG3
    · have r₅ : d₁ * d₂ * z = d₂ * (d₁ * z) := by rw [C₁₂.eq, mul_assoc]
      refine hF hd₁A hd₂A hB₃ hs₁ hs₂ sb₃ hn₁ hn₂ nb₃ C₁₂.eq
        (((Commute.refl d₁).mul_right C₁₂).mul_right C₁).eq
        ((C₁₂.symm.mul_right (Commute.refl d₂)).mul_right C₂).eq ?_
        bd₁ bd₂ bb₃ hD₀ ?_ ?_
      · calc d₁ * d₂ * (d₁ * d₂ * z) = d₁ * (d₂ * d₁) * d₂ * z := by group
          _ = d₁ * (d₁ * d₂) * d₂ * z := by rw [← C₁₂.eq]
          _ = (d₁ * d₁) * (d₂ * d₂) * z := by group
          _ = z := by rw [hs₁, hs₂, one_mul, one_mul]
      · rw [centralizer_pair_eq_of r₁]
        exact G1
      · rw [centralizer_pair_eq_of r₅, centralizer_pair_comm]
        exact G2

theorem noMixParity_of_leaves (hQ : P25X_QTF) (hF : P25X_NoFace) : NoMixParity := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp D hDA hDbad hcov h4 hsq hcomm hnomix
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hzD : z ∉ D := notMem_of_badSub hDA hyp hDbad
  have hbadD : ∀ x ∈ D, BadElt z x := fun x hx => badElt_of_mem hDA hyp hDbad hx
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
  have hgood : ∀ d ∈ D, d ≠ 1 → BadElt z d ∧ BadElt z (d * z) := by
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
  refine parityE4_of hyp (hQ G Ω K K' W S R R' z t u₁ u₂ hyp) (hF G Ω K K' W S R R' z t u₁ u₂ hyp)
    (hDA hd₁D) (hDA hd₂D) (hsq d₁ hd₁D) (hsq d₂ hd₂D) (hcomm d₁ hd₁D d₂ hd₂D) hd₁1 hd₂1
    hd₂₁.symm (hzne d₁ hd₁D) (hzne d₂ hd₂D) (hzne _ hd₁₂D) ?_
    (fun d hd => hgood d (hmemD d hd) (hne1 d hd))
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

end Face

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
