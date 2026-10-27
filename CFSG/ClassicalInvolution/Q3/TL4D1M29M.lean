module

public import CFSG.ClassicalInvolution.Q3.TL4D1MAME
public import CFSG.ClassicalInvolution.Q3.TL4D1MAGLF

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Equiv Matrix

theorem rank_one_of_sq_zero : ∀ N : Matrix (Fin 3) (Fin 3) (ZMod 2), N * N = 0 → N ≠ 0 →
    ∃ a : Fin 3 → ZMod 2, a ≠ 0 ∧ ∀ y : Fin 3 → ZMod 2, N *ᵥ y = 0 ↔ a ⬝ᵥ y = 0 := by
  decide +kernel

theorem hplane_card : ∀ a : Fin 3 → ZMod 2, a ≠ 0 → ∀ γ, (hplane a γ).card = 4 := by
  decide

theorem mem_affinePlanes_of_fixed {σ : Perm (Fin 8)} (hσ : σ ∈ agl32) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) {c : Fin 8} (hc : σ c = c) {O : Finset (Fin 8)} (hO : O.card = 4)
    (hmov : ∀ x ∈ O, σ x ≠ x) : O ∈ affinePlanes := by
  obtain ⟨A, b, rfl⟩ := exists_aperm_eq hσ
  have hAA : A.1 * A.1 = 1 := by
    have h := aperm_inj ((aperm_mul A A b b).symm.trans (h2.trans aperm_one_zero.symm))
    exact congrArg Subtype.val h.1
  have hb : A.1 *ᵥ bin c + b = bin c := by
    have := congrArg bin hc
    rwa [aperm_apply, bin_aapply] at this
  have hfix : ∀ x, aperm A b x = x ↔ (1 + A.1) *ᵥ (bin x + bin c) = 0 := by
    intro x
    rw [← bin_injective.eq_iff, aperm_apply, bin_aapply, add_mulVec, one_mulVec, mulVec_add]
    constructor
    · intro h
      funext i
      have h' := congrFun h i
      have hb' := congrFun hb i
      revert h' hb'
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize (A.1 *ᵥ bin x) i = p
      generalize (A.1 *ᵥ bin c) i = q
      generalize b i = r
      generalize bin x i = e
      generalize bin c i = f
      revert p q r e f
      decide
    · intro h
      funext i
      have h' := congrFun h i
      have hb' := congrFun hb i
      revert h' hb'
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize (A.1 *ᵥ bin x) i = p
      generalize (A.1 *ᵥ bin c) i = q
      generalize b i = r
      generalize bin x i = e
      generalize bin c i = f
      revert p q r e f
      decide
  have hNN : (1 + A.1) * (1 + A.1) = 0 := by
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hAA]
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    generalize (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j = p
    generalize A.1 i j = q
    revert p q
    decide
  have hN0 : (1 + A.1) ≠ 0 := by
    intro h0
    apply h1
    refine Equiv.ext fun x => ?_
    rw [Perm.one_apply]
    exact (hfix x).mpr (by rw [h0, zero_mulVec])
  obtain ⟨a, ha, hker⟩ := rank_one_of_sq_zero _ hNN hN0
  have hsub : O ⊆ hplane a (a ⬝ᵥ bin c + 1) := by
    intro x hx
    rw [hplane, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hne : ¬ (a ⬝ᵥ (bin x + bin c) = 0) := fun h =>
      hmov x hx ((hfix x).mpr ((hker _).mpr h))
    rw [dotProduct_add] at hne
    generalize a ⬝ᵥ bin x = p at hne ⊢
    generalize a ⬝ᵥ bin c = q at hne ⊢
    revert p q
    decide
  rw [Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hplane_card a ha, hO]))]
  exact hplane_mem a ha _

theorem e29_regular : ∀ s ∈ agl32, ∀ t ∈ agl32, s * s = 1 → t * t = 1 → s * t = t * s → ∀ a,
    s a ≠ a → t a ≠ a → s (t a) ≠ a → ({a, s a, t a, s (t a)} : Finset (Fin 8)) ∈ e29Sets ∨
      ∃ c, OffOrb s t a c ∧ s c ≠ c ∧ t c ≠ c ∧ s (t c) ≠ c := by
  intro s hs t ht hs2 ht2 hst a hsa hta hsta
  have hss := apply_apply_of_mul_self hs2
  have hts : ∀ i, t (s i) = s (t i) := fun i => by rw [← Perm.mul_apply, ← hst, Perm.mul_apply]
  have e5 : t a ≠ s a := fun h => hsta (by rw [h, hss])
  have e6 : s (t a) ≠ s a := fun h => hta (s.injective h)
  have e7 : s (t a) ≠ t a := fun h => hsa (t.injective (by rw [hts, h]))
  have hO4 : ({a, s a, t a, s (t a)} : Finset (Fin 8)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm e7
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm e5, Ne.symm e6⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hsa, Ne.symm hta, Ne.symm hsta⟩
  have hreg : ∀ y ∈ ({a, s a, t a, s (t a)} : Finset (Fin 8)),
      s y ≠ y ∧ t y ≠ y ∧ s (t y) ≠ y := fun y hy =>
    regular_orbit hs2 ht2 hst hsa hta hsta (by simpa using hy)
  have hu2 : s * t * (s * t) = 1 := by
    calc s * t * (s * t) = s * (t * s) * t := by group
      _ = s * s * (t * t) := by rw [← hst]; group
      _ = 1 := by rw [hs2, ht2, one_mul]
  by_cases hfree : ∀ x, s x ≠ x ∧ t x ≠ x ∧ s (t x) ≠ x
  · right
    obtain ⟨c, hc⟩ : ∃ c, OffOrb s t a c := exists_ne_four (by norm_num) a (s a) (t a) (s (t a))
    exact ⟨c, hc, hfree c⟩
  · left
    push Not at hfree
    obtain ⟨x, hx⟩ := hfree
    show _ ∈ affinePlanes
    by_cases hsx : s x = x
    · exact mem_affinePlanes_of_fixed hs hs2 (fun h => hsa (by rw [h, Perm.one_apply])) hsx hO4
        fun y hy => (hreg y hy).1
    by_cases htx : t x = x
    · exact mem_affinePlanes_of_fixed ht ht2 (fun h => hta (by rw [h, Perm.one_apply])) htx hO4
        fun y hy => (hreg y hy).2.1
    exact mem_affinePlanes_of_fixed (agl32.mul_mem hs ht) hu2
      (fun h => hsta (by rw [← Perm.mul_apply, h, Perm.one_apply])) (hx hsx htx) hO4
      fun y hy => (hreg y hy).2.2

theorem e29_members : ModelMembers e29Sets e29Sub :=
  modelMembers_of_regular (by norm_num) agl32_sign e29_regular

theorem e29_facts : ModelFacts e29Sets e29Sub :=
  ⟨e29_normal, e29_perfect, e29_three, e29_members⟩

end CFSG.ClassicalInvolution.Q3.TL4
