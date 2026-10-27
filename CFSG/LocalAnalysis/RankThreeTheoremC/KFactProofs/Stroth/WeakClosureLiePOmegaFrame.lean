module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslQuot
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureVacuous

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

section Lines

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem exists_zpow_eq_of_card_prime [Fact p.Prime] {A : Subgroup K} (hA : Nat.card A = p)
    {y z : K} (hy : y ∈ A) (hy1 : y ≠ 1) (hz : z ∈ A) : ∃ k : ℤ, y ^ k = z := by
  have hord : orderOf y = p := by
    have h1 : orderOf y ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hy
    rw [hA] at h1
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hle : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.2 hy
  have heq : Subgroup.zpowers y = A := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hA, Nat.card_zpowers, hord]
  rw [← heq] at hz
  exact Subgroup.mem_zpowers_iff.1 hz

theorem normalizerMovesLines_range_perm_diag [Fact p.Prime] {a r : ℕ}
    (Ψ : (Fin r → Multiplicative (ZMod (p ^ a))) →* K) (hΨ : Function.Injective Ψ)
    (hperm : ∀ j k : Fin r, j ≠ k → ∃ (g : K) (τ : Equiv.Perm (Fin r)), τ j = k ∧
      ∀ c, g * Ψ c * g⁻¹ = Ψ (c ∘ ⇑τ⁻¹))
    (hdiag : ∃ (g : K) (μ : Fin r → ℤ), (∃ i j, ¬ (p : ℤ) ∣ μ i - μ j) ∧
      ∀ c, g * Ψ c * g⁻¹ = Ψ (fun k => c k ^ μ k)) :
    NormalizerMovesLines p Ψ.range := by
  intro A hAP hA
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ g : K, (∀ c, ∃ d, g * Ψ c * g⁻¹ = Ψ d) →
      g ∈ Subgroup.normalizer (Ψ.range : Set K) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hg c
    rw [hd]
    exact ⟨d, rfl⟩
  have hconjA : ∀ g : K, (∀ c, ∃ d, g * Ψ c * g⁻¹ = Ψ d) → ∀ y ∈ A, g * y * g⁻¹ ∈ A := by
    intro g hg y hy
    rw [← hcon g (hnorm g hg)]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hexp : ∀ y ∈ A, y ^ p = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := A) (x := ⟨y, hy⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  obtain ⟨y₁, hy₁A, hy₁⟩ : ∃ y ∈ A, y ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨c₁, hc₁⟩ : ∃ c, Ψ c = y₁ := hAP hy₁A
  have hc₁ne : c₁ ≠ 1 := by
    rintro rfl
    exact hy₁ (by rw [← hc₁, map_one])
  have hpow : ∀ x ∈ A, ∃ m : ℤ, Ψ (c₁ ^ m) = x := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_zpow_eq_of_card_prime hA hy₁A hy₁ hx
    exact ⟨m, by rw [map_zpow, hc₁]; exact hm⟩
  have hcp : ∀ j, c₁ j ^ p = 1 := by
    intro j
    have h1 : Ψ (c₁ ^ p) = 1 := by rw [map_pow, hc₁]; exact hexp _ hy₁A
    have h2 : c₁ ^ p = 1 := hΨ (by rw [h1, map_one])
    simpa using congrFun h2 j
  have hall : ∀ j, c₁ j ≠ 1 := by
    intro k hk
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc₁ne
    have hjk : j ≠ k := fun h => hj (h ▸ hk)
    obtain ⟨g, τ, hτ, hg⟩ := hperm j k hjk
    have hmem : g * y₁ * g⁻¹ ∈ A :=
      hconjA g (fun c => ⟨_, hg c⟩) y₁ hy₁A
    obtain ⟨m, hm⟩ := hpow _ hmem
    rw [← hc₁, hg c₁] at hm
    have h3 : c₁ ∘ ⇑τ⁻¹ = c₁ ^ m := (hΨ hm).symm
    have h4 := congrFun h3 k
    have hτk : τ⁻¹ k = j := by rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]; exact hτ.symm
    simp only [Function.comp_apply, hτk, Pi.pow_apply, hk, one_zpow] at h4
    exact hj h4
  obtain ⟨g, μ, ⟨i, j, hij⟩, hg⟩ := hdiag
  have hmem : g * y₁ * g⁻¹ ∈ A := hconjA g (fun c => ⟨_, hg c⟩) y₁ hy₁A
  obtain ⟨m, hm⟩ := hpow _ hmem
  rw [← hc₁, hg c₁] at hm
  have h3 : c₁ ^ m = fun k => c₁ k ^ μ k := hΨ hm
  have hmod : ∀ k, (p : ℤ) ∣ m - μ k := by
    intro k
    have h4 : c₁ k ^ m = c₁ k ^ μ k := by simpa using congrFun h3 k
    have hord : orderOf (c₁ k) = p := orderOf_eq_prime (hcp k) (hall k)
    rw [← hord]
    refine orderOf_dvd_iff_zpow_eq_one.2 ?_
    rw [zpow_sub, h4, mul_inv_cancel]
  apply hij
  have h5 := dvd_sub (hmod j) (hmod i)
  have h6 : m - μ j - (m - μ i) = μ i - μ j := by ring
  rwa [h6] at h5

end Lines

structure OFrame (p : ℕ) (C : Type) [Group C] (r : ℕ) (G : Type) [Group G] where
  T : (Fin r → C) →* G
  T_injective : Function.Injective T
  perm : ∀ j k : Fin r, j ≠ k → ∃ (g : G) (τ : Equiv.Perm (Fin r)), τ j = k ∧
    ∀ c, g * T c * g⁻¹ = T (c ∘ ⇑τ⁻¹)
  diag : 2 ≤ r → ∃ (g : G) (μ : Fin r → ℤ), (∃ i j, ¬ (p : ℤ) ∣ μ i - μ j) ∧
    ∀ c, g * T c * g⁻¹ = T (fun k => c k ^ μ k)

namespace OFrame

variable {p : ℕ} {C : Type} [Group C] {r : ℕ} {G G' : Type} [Group G] [Group G']

@[expose] def map (F : OFrame p C r G) (h : G →* G') (hinj : Function.Injective (h.comp F.T)) :
    OFrame p C r G' where
  T := h.comp F.T
  T_injective := hinj
  perm j k hjk := by
    obtain ⟨g, τ, hτ, hg⟩ := F.perm j k hjk
    refine ⟨h g, τ, hτ, fun c => ?_⟩
    change h g * h (F.T c) * (h g)⁻¹ = h (F.T (c ∘ ⇑τ⁻¹))
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  diag hr := by
    obtain ⟨g, μ, hμ, hg⟩ := F.diag hr
    refine ⟨h g, μ, hμ, fun c => ?_⟩
    change h g * h (F.T c) * (h g)⁻¹ = h (F.T (fun k => c k ^ μ k))
    rw [← map_inv, ← map_mul, ← map_mul, hg]

theorem wcOn [Fact p.Prime] [Finite G] {a : ℕ}
    (F : OFrame p (Multiplicative (ZMod (p ^ a))) r G)
    (hcard : (Nat.card G).factorization p = a * r) : WCOn p G := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hT : Nat.card (Fin r → Multiplicative (ZMod (p ^ a))) =
      p ^ (Nat.card G).factorization p := by
    rw [hcard, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, ← pow_mul]
  by_cases hr0 : r = 0
  · subst hr0
    refine WCOn.of_factorization_le_one ?_
    simp [hcard]
  by_cases hr1 : r = 1
  · subst hr1
    haveI : IsCyclic (Fin 1 → Multiplicative (ZMod (p ^ a))) :=
      isCyclic_of_surjective (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm
        (MulEquiv.funUnique (Fin 1) (Multiplicative (ZMod (p ^ a)))).symm.surjective
    exact wcOn_of_range_cyclic F.T F.T_injective hT
  · have hr2 : 2 ≤ r := by omega
    exact wcOn_of_range_nml F.T F.T_injective hT
      (normalizerMovesLines_range_perm_diag F.T F.T_injective F.perm (F.diag hr2))

end OFrame

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
