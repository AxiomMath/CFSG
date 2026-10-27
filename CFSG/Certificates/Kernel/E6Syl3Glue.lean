module

public import CFSG.Certificates.Kernel.E6Syl3Sound
public import CFSG.Certificates.Kernel.E7PlaneGlue
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem isA2Pair_smul {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair (τ := Tag.E6) α β)
    (g : WeylGroup Tag.E6) : IsA2Pair (τ := Tag.E6) (g • α) (g • β) := by
  refine ⟨IsRoot.smul h.isRoot_fst g, IsRoot.smul h.isRoot_snd g, ?_, ?_, ?_⟩
  · rw [← smul_add]
    exact IsRoot.smul h.isRoot_add g
  · rw [iform_smul, iform_smul]
    exact h.iform_snd
  · rw [iform_smul, iform_smul]
    exact h.two_iform

theorem a2Roots_smul {α β γ : Fin Tag.E6.rank → ℤ} (h : γ ∈ a2Roots α β) (g : WeylGroup Tag.E6) :
    g • γ ∈ a2Roots (g • α) (g • β) := by
  simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [smul_neg, smul_add]

theorem kindA2_conj {y : WeylGroup Tag.E6} (h : E6KindA2 y) (g : WeylGroup Tag.E6) :
    E6KindA2 (g * y * g⁻¹) := by
  obtain ⟨α, β, hp, rfl⟩ := h
  refine ⟨g • α, g • β, isA2Pair_smul hp g, ?_⟩
  rw [rootReflection_smul_root g hp.isRoot_fst, rootReflection_smul_root g hp.isRoot_snd]
  group

theorem kind3_conj {y : WeylGroup Tag.E6} (h : E6Kind3A2 y) (g : WeylGroup Tag.E6) :
    E6Kind3A2 (g * y * g⁻¹) := by
  intro v
  have e : v + (g * y * g⁻¹) • v + (g * y * g⁻¹) • (g * y * g⁻¹) • v =
      g • (g⁻¹ • v + y • g⁻¹ • v + y • y • g⁻¹ • v) := by
    simp only [mul_smul, smul_add, smul_inv_smul, inv_smul_smul]
  rw [e, h (g⁻¹ • v), smul_zero]

theorem norm_span {y : WeylGroup Tag.E6} {γ₁ γ₂ : Fin Tag.E6.rank → ℤ}
    (h : ∀ j : Fin Tag.E6.rank, ∃ m n : ℤ,
      (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + y • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
          y • y • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = m • γ₁ + n • γ₂)
    (v : Fin Tag.E6.rank → ℤ) : ∃ m n : ℤ, v + y • v + y • y • v = m • γ₁ + n • γ₂ := by
  choose m n hmn using h
  refine ⟨∑ j, v j * m j, ∑ j, v j * n j, ?_⟩
  have hv : v = ∑ j : Fin Tag.E6.rank, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have key : v + y • v + y • y • v = ∑ j : Fin Tag.E6.rank, v j •
      ((Pi.single j 1 : Fin Tag.E6.rank → ℤ) + y • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
        y • y • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    conv_lhs => rw [hv]
    simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_comm y]
  rw [key]
  simp only [hmn, smul_add, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]

theorem kind2_conj {y : WeylGroup Tag.E6} {γ₁ γ₂ : Fin Tag.E6.rank → ℤ} (h : E6Kind2A2 y γ₁ γ₂)
    (g : WeylGroup Tag.E6) : E6Kind2A2 (g * y * g⁻¹) (g • γ₁) (g • γ₂) := by
  obtain ⟨hp, h1, h2, hfix, ⟨μ, hμ⟩, hrng⟩ := h
  refine ⟨isA2Pair_smul hp g, ?_, ?_, ?_, ⟨g • μ, ?_⟩, ?_⟩
  · simp only [mul_smul, inv_smul_smul, h1]
  · simp only [mul_smul, inv_smul_smul, h2]
  · intro γ hγ hwγ
    have hfix' : y • (g⁻¹ • γ) = g⁻¹ • γ := by
      have e := congrArg (fun x => g⁻¹ • x) hwγ
      simpa only [mul_smul, inv_smul_smul] using e
    have hm := a2Roots_smul (hfix _ (IsRoot.smul hγ g⁻¹) hfix') g
    rwa [smul_inv_smul] at hm
  · have e := congrArg (fun x => g • x) hμ
    simp only [two_nsmul, smul_add] at e ⊢
    simpa only [mul_smul, inv_smul_smul] using e
  · intro j
    obtain ⟨m, n, hmn⟩ := norm_span hrng (g⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))
    refine ⟨m, n, ?_⟩
    have e := congrArg (fun x => g • x) hmn
    simp only [smul_add, smul_inv_smul, smul_comm g m, smul_comm g n] at e
    simpa only [mul_smul, inv_smul_smul] using e

theorem factorization_E6 : (51840 : ℕ).factorization 3 = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e3 : (51840 : ℕ) = 3 ^ 4 * 640 := by norm_num
  rw [Nat.factorization_def _ Nat.prime_three, e3, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem e6Order3Kinds_of_checks {gw W : List (List ℕ)} (hq : qCheckWith gw (qTups gw) = true)
    (hk : kindsCheck (qTups gw) W = true) : E6Order3Kinds := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, hcov⟩ := exists_subgroup_of_qCheck hq
  have hS : Nat.card (qSub gw) = 3 ^ (Nat.card (WeylGroup Tag.E6)).factorization 3 := by
    rw [hcard, CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6, factorization_E6]
    norm_num
  intro w hw3 hw1
  obtain ⟨g, hg⟩ :=
    CFSG.KC.E7Plane.exists_conj_mem_of_orderOf (qSub gw) hS (orderOf_eq_prime hw3 hw1)
  obtain ⟨t, ht, hrep⟩ := hcov _ hg
  obtain ⟨c, hc⟩ := kindOK_of_mem hk ht
  have hw : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
  have hy3 : (g⁻¹ * w * g) ^ 3 = 1 := by
    have e : (g⁻¹ * w * g) ^ 3 = g⁻¹ * w ^ 3 * g := by
      have e' := conj_pow (a := g⁻¹) (b := w) (i := 3)
      rwa [inv_inv] at e'
    rw [e, hw3]
    group
  have hy1 : g⁻¹ * w * g ≠ 1 := by
    intro h1
    apply hw1
    rw [hw, h1]
    group
  rcases kindOK_sound hrep hy3 hy1 hc with hA | ⟨γ₁, γ₂, h2⟩ | h3
  · rw [hw]
    exact Or.inl (kindA2_conj hA g)
  · rw [hw]
    exact Or.inr (Or.inl ⟨_, _, kind2_conj h2 g⟩)
  · rw [hw]
    exact Or.inr (Or.inr (kind3_conj h3 g))

end CFSG.KC.E6Syl3
