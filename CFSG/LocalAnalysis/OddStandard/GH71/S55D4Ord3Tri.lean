module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Rk3

public noncomputable section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KGD CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def d4Orb : Fin 3 → (Fin TwistTag.D4.tag.rank → ℤ) × (Fin TwistTag.D4.tag.rank → ℤ) ×
    (Fin TwistTag.D4.tag.rank → ℤ)
  | 0 => (![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 0, 1])
  | 1 => (![1, 0, 1, 0], ![0, -1, -1, 0], ![0, 0, 1, 1])
  | 2 => (![1, 1, 1, 0], ![0, -1, -1, -1], ![1, 0, 1, 1])

theorem d4Orb_check : ∀ i : Fin 3,
    List.ofFn (d4Orb i).1 ∈ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn (d4Orb i).2.1 ∈ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn (d4Orb i).2.2 ∈ TwistTag.D4.tag.artifactRoots ∧
    iform (d4Orb i).1 (d4Orb i).2.1 = 0 ∧ iform (d4Orb i).1 (d4Orb i).2.2 = 0 ∧
    iform (d4Orb i).2.1 (d4Orb i).2.2 = 0 ∧
    List.ofFn ((d4Orb i).1 + (d4Orb i).2.1) ∉ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn ((d4Orb i).1 - (d4Orb i).2.1) ∉ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn ((d4Orb i).1 + (d4Orb i).2.2) ∉ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn ((d4Orb i).1 - (d4Orb i).2.2) ∉ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn ((d4Orb i).2.1 + (d4Orb i).2.2) ∉ TwistTag.D4.tag.artifactRoots ∧
    List.ofFn ((d4Orb i).2.1 - (d4Orb i).2.2) ∉ TwistTag.D4.tag.artifactRoots ∧
    permLattice TwistTag.D4.perm (d4Orb i).1 = -(d4Orb i).2.1 ∧
    permLattice TwistTag.D4.perm (d4Orb i).2.1 = -(d4Orb i).2.2 ∧
    permLattice TwistTag.D4.perm (d4Orb i).2.2 = (d4Orb i).1 := by
  decide +kernel

@[expose] def d4E2 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 0]

theorem d4_e2_check : List.ofFn d4E2 ∈ TwistTag.D4.tag.artifactRoots ∧
    permLattice TwistTag.D4.perm d4E2 = d4E2 := by
  decide +kernel

theorem cube_root_eq_or_inv {L : Type} [Field L] {A B : Lˣ} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hA1 : A ≠ 1) (hB1 : B ≠ 1) : B = A ∨ B = A⁻¹ := by
  have prim : ∀ C : Lˣ, C ^ 3 = 1 → C ≠ 1 → (C : L) ^ 2 + C + 1 = 0 := fun C hC hC1 => by
    have h : ((C : L) - 1) * ((C : L) ^ 2 + C + 1) = 0 := by
      have := congrArg Units.val hC
      push_cast at this
      linear_combination this
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (Units.ext (by simpa [sub_eq_zero] using h)) hC1
    · exact h
  have hA2 := prim A hA hA1
  have hB2 := prim B hB hB1
  have h : ((B : L) - A) * ((B : L) + A + 1) = 0 := by linear_combination hB2 - hA2
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (Units.ext (sub_eq_zero.1 h))
  · refine Or.inr (eq_inv_of_mul_eq_one_left (Units.ext ?_))
    push_cast
    linear_combination (A : L) * h - hA2


variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] [IsAlgClosed L]

theorem d4Orb_pElt (hf : 1 ≤ f) (i : Fin 3) :
    ∃ u : ModGL TwistTag.D4.tag L, u ∈ adjointGroup TwistTag.D4.tag L ∧ u ≠ 1 ∧ u ^ p = 1 ∧
      trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) u *
        (trialityOpposition L)⁻¹ = u ∧
      ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, rootChar a (d4Orb i).1 = 1 →
        rootChar a (d4Orb i).2.1 = 1 → rootChar a (d4Orb i).2.2 = 1 →
          rootDiagUnit TwistTag.D4.tag a * u = u * rootDiagUnit TwistTag.D4.tag a := by
  obtain ⟨m₁, m₂, m₃, o₁₂, o₁₃, o₂₃, p₁₂, n₁₂, p₁₃, n₁₃, p₂₃, n₂₃, e₁, e₂, e₃⟩ := d4Orb_check i
  have h₁ := isRoot_iff_mem_artifactRoots.2 m₁
  have h₂ := isRoot_iff_mem_artifactRoots.2 m₂
  have h₃ := isRoot_iff_mem_artifactRoots.2 m₃
  exact d4_rk3_pElt hf h₁ h₂ h₃ e₁ e₂ e₃
    (rootSL2_commute_of_orth h₁ h₂ o₁₂ (d4Q_not_isRoot p₁₂) (d4Q_not_isRoot n₁₂))
    (rootSL2_commute_of_orth h₁ h₃ o₁₃ (d4Q_not_isRoot p₁₃) (d4Q_not_isRoot n₁₃))
    (rootSL2_commute_of_orth h₂ h₃ o₂₃ (d4Q_not_isRoot p₂₃) (d4Q_not_isRoot n₂₃))

theorem d4_toral3_pElt (hf : 1 ≤ f) {A B : Lˣ} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (h1 : ¬ (A = 1 ∧ B = 1)) :
    ∃ u : ModGL TwistTag.D4.tag L, u ∈ adjointGroup TwistTag.D4.tag L ∧ u ≠ 1 ∧ u ^ p = 1 ∧
      trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) u *
        (trialityOpposition L)⁻¹ = u ∧
      rootDiagUnit TwistTag.D4.tag ![A, A, B, A] * u =
        u * rootDiagUnit TwistTag.D4.tag ![A, A, B, A] := by
  have hc : ∀ v : Fin TwistTag.D4.tag.rank → ℤ, rootChar (τ := TwistTag.D4.tag) (![A, A, B, A] :
      Fin TwistTag.D4.tag.rank → Lˣ) v = A ^ v 0 * A ^ v 1 * B ^ v 2 * A ^ v 3 := fun v =>
    Fin.prod_univ_four _
  by_cases hB1 : B = 1
  · obtain ⟨u, hu, hu1, hup, huF, huc⟩ :=
      d4_rk1_pElt (L := L) hf (isRoot_iff_mem_artifactRoots.2 d4_e2_check.1) d4_e2_check.2
    refine ⟨u, hu, hu1, hup, huF, huc _ ?_⟩
    rw [hc]
    simp [d4E2, hB1]
  by_cases hA1 : A = 1
  · obtain ⟨u, hu, hu1, hup, huF, huc⟩ := d4Orb_pElt (L := L) hf 0
    refine ⟨u, hu, hu1, hup, huF, huc _ ?_ ?_ ?_⟩ <;> rw [hc] <;> simp [d4Orb, hA1]
  rcases cube_root_eq_or_inv hA hB hA1 hB1 with rfl | rfl
  · obtain ⟨u, hu, hu1, hup, huF, huc⟩ := d4Orb_pElt (L := L) hf 2
    refine ⟨u, hu, hu1, hup, huF, huc _ ?_ ?_ ?_⟩ <;> rw [hc] <;> simp [d4Orb] <;>
      first
      | (rw [← pow_three']; exact hA)
      | rw [← pow_three', inv_pow, hA, inv_one]
  · obtain ⟨u, hu, hu1, hup, huF, huc⟩ := d4Orb_pElt (L := L) hf 1
    refine ⟨u, hu, hu1, hup, huF, huc _ ?_ ?_ ?_⟩ <;> rw [hc] <;> simp [d4Orb]

end CFSG.OddStandard.GH71.S55
