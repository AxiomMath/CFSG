module

public import CFSG.GH74.GLS.Balance.Step4Split
public import CFSG.GH74.GLS.Balance.Step4Orbit

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace Step4

theorem exists_cj_pow_inv {X : Type} [Group X] [Finite X] (w : X) (K : Subgroup X) :
    ∃ m : ℕ, cj (w ^ m) (cj w K) = K := by
  refine ⟨orderOf w - 1, ?_⟩
  have hpos : 0 < orderOf w := orderOf_pos w
  rw [← cj_mul, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one, cj_one]

theorem mem_normalizer_of_normal {X : Type} [Group X] {H : Subgroup X} (hH : H.Normal) (g : X) :
    g ∈ normalizer (H : Set X) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr hH]
  exact mem_top g

variable {X : Type} [Group X] {x : X} {V : Subgroup X}

structure SetGood (A : SolvAPI x V) (S : Set (Subgroup X)) : Prop where
  comp : ∀ K ∈ S, IsComponent K ∧ x ∈ normalizer (K : Set X)
  wS : ∀ K ∈ S, cj A.w K ∈ S
  P_le : A.P ≤ compProd S

theorem setGood_top (A : SolvAPI x V)
    (hRL : A.P ≤ compProd {K : Subgroup X | IsComponent K ∧ x ∈ normalizer (K : Set X)}) :
    SetGood A {K : Subgroup X | IsComponent K ∧ x ∈ normalizer (K : Set X)} where
  comp K hK := hK
  wS K hK := by
    refine ⟨isComponent_cj hK.1, ?_⟩
    rw [mem_normalizer_iff_cj_eq]
    have h1 : cj (x * A.w) K = cj (A.w * x) K := by rw [A.w_mul_x.symm]
    rw [cj_mul, cj_mul, mem_normalizer_iff_cj_eq.mp hK.2] at h1
    exact h1
  P_le := hRL

theorem SetGood.orbit_mem {A : SolvAPI x V} {S : Set (Subgroup X)} (hS : SetGood A S)
    {K₀ : Subgroup X} (hK₀ : K₀ ∈ S) (n : ℕ) : cj (A.w ^ n) K₀ ∈ S := by
  induction n with
  | zero => rwa [pow_zero, cj_one]
  | succ n ih => rw [cj_pow_succ]; exact hS.wS _ ih

section Fin

variable [Finite X]

theorem exists_component_of_minimal (hx : orderOf x = 2) (hO : pPrimeCore 2 X = ⊥) (A : SolvAPI x V)
    {S : Set (Subgroup X)} (hS : SetGood A S) (hmin : ∀ S' : Set (Subgroup X), SetGood A S' → ¬ S' < S) :
    ∃ K ∈ S, A.P ≤ K := by
  have hZn : (layerZ X).Normal := layerZ_normal
  have hZ2 := layerZ_isPGroup hO
  have hne : S.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hP : A.P ≤ ⊥ := by simpa [hemp, compProd_empty] using hS.P_le
    obtain ⟨a, ha, b, hb, hab⟩ := A.P_nonab
    have h1 : a = 1 := Subgroup.mem_bot.mp (hP ha)
    have h2 : b = 1 := Subgroup.mem_bot.mp (hP hb)
    exact hab (by rw [h1, h2])
  obtain ⟨K₀, hK₀⟩ := hne
  set S₁ : Set (Subgroup X) := {K | ∃ n : ℕ, K = cj (A.w ^ n) K₀} with hS₁def
  have hS₁S : S₁ ⊆ S := by
    rintro _ ⟨n, rfl⟩
    exact hS.orbit_mem hK₀ n
  have hK₀S₁ : K₀ ∈ S₁ := ⟨0, by rw [pow_zero, cj_one]⟩
  have hS₁w : ∀ K ∈ S₁, cj A.w K ∈ S₁ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, (cj_pow_succ A.w n K₀).symm⟩
  have hS₁w' : ∀ K : Subgroup X, cj A.w K ∈ S₁ → K ∈ S₁ := by
    rintro K ⟨n, hn⟩
    obtain ⟨m, hm⟩ := exists_cj_pow_inv A.w K
    refine ⟨m + n, ?_⟩
    rw [pow_add, cj_mul, ← hn, hm]
  set S₂ : Set (Subgroup X) := S \ S₁ with hS₂def
  have hS₂S : S₂ ⊆ S := Set.sdiff_subset
  have hS₂w : ∀ K ∈ S₂, cj A.w K ∈ S₂ := fun K hK =>
    ⟨hS.wS K hK.1, fun h => hK.2 (hS₁w' K h)⟩
  have hdisj : Disjoint S₁ S₂ := Set.disjoint_sdiff_right
  have hcomp₁ : ∀ K ∈ S₁, IsComponent K := fun K hK => (hS.comp K (hS₁S hK)).1
  have hcomp₂ : ∀ K ∈ S₂, IsComponent K := fun K hK => (hS.comp K (hS₂S hK)).1
  have hsplit : SplitHyp A (compProd S₁) (compProd S₂) (layerZ X) := by
    refine ⟨compProd_commute hcomp₁ hcomp₂ hdisj, compProd_inf_le_layerZ hcomp₁ hcomp₂ hdisj,
      ?_, ?_, ?_, ?_, ?_, hZ2, ?_⟩
    · exact mem_normalizer_compProd fun K hK k hk =>
        le_compProd (hS₁w K hK) (conj_mem_cj hk)
    · exact mem_normalizer_compProd fun K hK k hk =>
        le_compProd (hS₂w K hK) (conj_mem_cj hk)
    · exact mem_normalizer_compProd fun K hK k hk =>
        le_compProd hK ((mem_normalizer_iff.mp (hS.comp K (hS₁S hK)).2 k).mp hk)
    · exact mem_normalizer_compProd fun K hK k hk =>
        le_compProd hK ((mem_normalizer_iff.mp (hS.comp K (hS₂S hK)).2 k).mp hk)
    · rw [← compProd_union, Set.union_sdiff_cancel hS₁S]
      exact hS.P_le
    · exact A.abelian hx (layerZ X) hZ2 (fun a ha b hb => layerZ_comm ha hb)
        (mem_normalizer_of_normal hZn A.w) (mem_normalizer_of_normal hZn x)
  have hPS₁ : A.P ≤ compProd S₁ := by
    rcases split_lemma hsplit (fun a ha b hb => layerZ_comm ha hb) with h | h
    · exact h
    · exfalso
      refine hmin S₂ ⟨fun K hK => hS.comp K (hS₂S hK), hS₂w, h⟩ ?_
      exact lt_of_le_of_ne hS₂S fun heq => by
        have : K₀ ∈ S₂ := heq ▸ hK₀
        exact this.2 hK₀S₁
  have hS₁good : SetGood A S₁ :=
    ⟨fun K hK => hS.comp K (hS₁S hK), hS₁w, hPS₁⟩
  have hSS₁ : S₁ = S := by
    by_contra hne
    exact hmin S₁ hS₁good (lt_of_le_of_ne hS₁S hne)
  by_cases hone : ∃ K ∈ S, K ≠ K₀
  · exfalso
    refine orbit_lemma hx hO (A := A) (S := S) (K₀ := K₀) ⟨hK₀, fun K hK => (hS.comp K hK).1,
      fun K hK => (hS.comp K hK).2, hS.wS, fun K hK => ?_, hone, hS.P_le⟩
    rw [← hSS₁] at hK
    exact hK
  · push Not at hone
    refine ⟨K₀, hK₀, hS.P_le.trans (compProd_le fun K hK => le_of_eq (hone K hK))⟩

end Fin

end Step4

open Step4 in
theorem step4 {X : Type} [Group X] [Finite X] {x : X} {V : Subgroup X} (hx : orderOf x = 2)
    (hO : pPrimeCore 2 X = ⊥)
    (A : SolvAPI x V)
    (hRn : ∀ K : Subgroup X, IsComponent K → oPrimeResidualOf 2 V ≤ normalizer (K : Set X))
    (hRL : A.P ≤ ⨆ K ∈ {K : Subgroup X | IsComponent K ∧ x ∈ normalizer (K : Set X)}, K) :
    ∃ K : Subgroup X, IsComponent K ∧ x ∈ normalizer (K : Set X) ∧ oPrimeResidualOf 2 V ≤ K := by
  obtain ⟨S, hS, hmin⟩ := (wellFounded_lt (α := Set (Subgroup X))).has_min
    {S : Set (Subgroup X) | SetGood A S} ⟨_, setGood_top A hRL⟩
  obtain ⟨K, hK, hPK⟩ := exists_component_of_minimal hx hO A hS fun S' hS' => hmin S' hS'
  exact ⟨K, (hS.comp K hK).1, (hS.comp K hK).2, A.R_gen K (hRn K (hS.comp K hK).1) hPK⟩

end CFSG.GH74.GLS.Balance
