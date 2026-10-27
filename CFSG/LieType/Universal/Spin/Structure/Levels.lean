module

public import CFSG.LieType.Steinberg.Extras
public import Mathlib.LinearAlgebra.Matrix.IsDiag

public section

namespace CFSG.LieType.Universal.Spin

open CFSG.LieType.Steinberg

section Level

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R] (lev : σ → ℤ)

@[expose] def IdBelow (h : ℤ) (M : Matrix σ σ R) : Prop :=
  ∀ a b, lev a - lev b < h → M a b = (1 : Matrix σ σ R) a b

omit [Fintype σ] in
theorem IdBelow.mono {lev : σ → ℤ} {h h' : ℤ} (hh : h ≤ h') {M : Matrix σ σ R}
    (hM : IdBelow lev h' M) : IdBelow lev h M :=
  fun a b hab => hM a b (by omega)

omit [Fintype σ] in
theorem idBelow_one (h : ℤ) : IdBelow lev h (1 : Matrix σ σ R) := fun _ _ _ => rfl

theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h) {M N : Matrix σ σ R}
    (hM : IdBelow lev h M) (hN : IdBelow lev h N) {a b : σ} (hab : a ≠ b)
    (hlev : lev a - lev b ≤ h) : (M * N) a b = M a b + N a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM a a (by simpa using hh), hN b b (by simpa using hh)]
    simp [add_comm]
  · intro c _ ⟨hca, hcb⟩
    by_cases hc : lev a - lev c < h
    · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · rw [hN c b (by omega), Matrix.one_apply_ne hcb, mul_zero]
  · simp
  · simp

theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix σ σ R}
    (hM : IdBelow lev h M) (hN : IdBelow lev h N) : IdBelow lev h (M * N) := by
  intro a b hab
  by_cases hab' : a = b
  · subst hab'
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hM a a (by simpa using hh), hN a a (by simpa using hh)]
      simp
    · intro c _ hca
      by_cases hc : lev a - lev c < h
      · rw [hM a c hc, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
      · rw [hN c a (by omega), Matrix.one_apply_ne hca, mul_zero]
    · simp
  · rw [mul_apply_of_idBelow lev hh hM hN hab' hab.le, hM a b hab, hN a b hab,
      Matrix.one_apply_ne hab', add_zero]

theorem idBelow_list_prod {ι : Type*} {h : ℤ} (hh : 0 < h) (L : List ι)
    (f : ι → Matrix σ σ R) (hf : ∀ x ∈ L, IdBelow lev h (f x)) :
    IdBelow lev h (L.map f).prod ∧ ∀ a b, a ≠ b → lev a - lev b ≤ h →
      (L.map f).prod a b = (L.map fun x => f x a b).sum := by
  induction L with
  | nil => exact ⟨by simpa using idBelow_one lev h, fun a b hab _ => by
      simp [Matrix.one_apply_ne hab]⟩
  | cons x L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun y hy => hf y (List.mem_cons_of_mem x hy)
    have hx := hf x List.mem_cons_self
    refine ⟨?_, fun a b hab hlev => ?_⟩
    · simpa using idBelow_mul lev hh hx ih1
    · simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [mul_apply_of_idBelow lev hh hx ih1 hab hlev, ih2 a b hab hlev]

omit [Fintype σ] in
theorem eq_one_of_idBelow_of_idBelow_neg {M : Matrix σ σ R} (h₁ : IdBelow lev 1 M)
    (h₂ : IdBelow (fun a => -lev a) 1 M) : M = 1 := by
  ext a b
  rcases le_or_gt (lev a - lev b) 0 with h | h
  · exact h₁ a b (by omega)
  · exact h₂ a b (by show -lev a - -lev b < 1; omega)

omit [Fintype σ] in
theorem eq_one_of_idBelow_one_of_idBelow_neg_one {M : Matrix σ σ R}
    (h₁ : IdBelow (fun a => (1 : ℤ) * lev a) 1 M) (h₂ : IdBelow (fun a => (-1 : ℤ) * lev a) 1 M) :
    M = 1 := by
  ext a b
  rcases le_or_gt (lev a - lev b) 0 with h | h
  · exact h₁ a b (by show 1 * lev a - 1 * lev b < 1; omega)
  · exact h₂ a b (by show -1 * lev a - -1 * lev b < 1; omega)

omit [Fintype σ] in
theorem eq_one_of_isDiag_of_idBelow {M : Matrix σ σ R} (hd : M.IsDiag) (h : IdBelow lev 1 M) :
    M = 1 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    exact h a a (by simp)
  · rw [hd hab, Matrix.one_apply_ne hab]

variable {G : Type*} [Group G]

theorem eq_of_list_prod_eq_of_idBelow {κ : Type*} (ρ : G →* Matrix σ σ R)
    (X : κ → Subgroup G) (h : κ → ℤ) (L : List κ) (hL : L.Nodup)
    (hh : ∀ γ ∈ L, 0 < h γ)
    (hidb : ∀ γ ∈ L, ∀ x ∈ X γ, IdBelow lev (h γ) (ρ x))
    (hpos : ∀ γ ∈ L, ∃ a b, a ≠ b ∧ lev a - lev b ≤ h γ ∧
      (∀ δ ∈ L, δ ≠ γ → ∀ x ∈ X δ, ρ x a b = 0) ∧
      ∀ x ∈ X γ, ∀ y ∈ X γ, ρ x a b = ρ y a b → x = y)
    (hsort : L.Pairwise fun γ δ => h γ ≤ h δ)
    (f g : κ → G) (hf : ∀ γ ∈ L, f γ ∈ X γ) (hg : ∀ γ ∈ L, g γ ∈ X γ)
    (hfg : (L.map f).prod = (L.map g).prod) : ∀ γ ∈ L, f γ = g γ := by
  induction L with
  | nil => simp
  | cons γ L ih =>
    rw [List.nodup_cons] at hL
    rw [List.pairwise_cons] at hsort
    obtain ⟨a, b, hab, hlev, hzero, hinj⟩ := hpos γ List.mem_cons_self
    have hγ := hh γ List.mem_cons_self
    have htail : ∀ e : κ → G, (∀ δ ∈ L, e δ ∈ X δ) →
        IdBelow lev (h γ) (ρ (L.map e).prod) ∧ ρ (L.map e).prod a b = 0 := by
      intro e he
      rw [map_list_prod, List.map_map]
      obtain ⟨h1, h2⟩ := idBelow_list_prod lev hγ L (ρ ∘ e)
        (fun δ hδ => (hidb δ (List.mem_cons_of_mem γ hδ) (e δ) (he δ hδ)).mono (hsort.1 δ hδ))
      refine ⟨h1, ?_⟩
      rw [h2 a b hab hlev]
      refine List.sum_eq_zero fun z hz => ?_
      obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hz
      exact hzero δ (List.mem_cons_of_mem γ hδ) (fun e => hL.1 (e ▸ hδ)) (e δ) (he δ hδ)
    have hentry : ∀ e : κ → G, e γ ∈ X γ → (∀ δ ∈ L, e δ ∈ X δ) →
        ρ (e γ * (L.map e).prod) a b = ρ (e γ) a b := by
      intro e heγ he
      obtain ⟨h1, h2⟩ := htail e he
      rw [map_mul, mul_apply_of_idBelow lev hγ (hidb γ List.mem_cons_self _ heγ) h1 hab hlev, h2,
        add_zero]
    simp only [List.map_cons, List.prod_cons] at hfg
    have hf' : ∀ δ ∈ L, f δ ∈ X δ := fun δ hδ => hf δ (List.mem_cons_of_mem γ hδ)
    have hg' : ∀ δ ∈ L, g δ ∈ X δ := fun δ hδ => hg δ (List.mem_cons_of_mem γ hδ)
    have hfγ := hf γ List.mem_cons_self
    have hgγ := hg γ List.mem_cons_self
    have hcx : f γ = g γ := hinj _ hfγ _ hgγ (by
      rw [← hentry f hfγ hf', ← hentry g hgγ hg', hfg])
    intro δ hδ
    rcases List.mem_cons.mp hδ with rfl | hδ
    · exact hcx
    · refine ih hL.2 (fun δ hδ => hh δ (List.mem_cons_of_mem γ hδ))
        (fun δ hδ => hidb δ (List.mem_cons_of_mem γ hδ)) ?_ hsort.2 hf' hg' ?_ δ hδ
      · intro δ hδ
        obtain ⟨a, b, h1, h2, h3, h4⟩ := hpos δ (List.mem_cons_of_mem γ hδ)
        exact ⟨a, b, h1, h2, fun ε hε => h3 ε (List.mem_cons_of_mem γ hε), h4⟩
      · rw [hcx] at hfg
        exact mul_left_cancel hfg

theorem prodInjectiveFor_of_idBelow {ι : Type*} (ρ : G →* Matrix σ σ R)
    (X : (ι → ℤ) → Subgroup G) (h : (ι → ℤ) → ℤ) (L : List (ι → ℤ)) (hL : L.Nodup)
    (hh : ∀ γ ∈ L, 0 < h γ)
    (hidb : ∀ γ ∈ L, ∀ x ∈ X γ, IdBelow lev (h γ) (ρ x))
    (hpos : ∀ γ ∈ L, ∃ a b, a ≠ b ∧ lev a - lev b ≤ h γ ∧
      (∀ δ ∈ L, δ ≠ γ → ∀ x ∈ X δ, ρ x a b = 0) ∧
      ∀ x ∈ X γ, ∀ y ∈ X γ, ρ x a b = ρ y a b → x = y)
    (hsort : L.Pairwise fun γ δ => h γ ≤ h δ) : ProdInjectiveFor X L :=
  fun f g hf hg hfg => eq_of_list_prod_eq_of_idBelow lev ρ X h L hL hh hidb hpos hsort f g hf hg hfg

end Level

section Diagonal

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {R : Type*} [CommRing R]

theorem isDiag_mul {M N : Matrix σ σ R} (hM : M.IsDiag) (hN : N.IsDiag) : (M * N).IsDiag := by
  rw [← hM.diagonal_diag, ← hN.diagonal_diag, Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

theorem mul_apply_self_of_isDiag {M N : Matrix σ σ R} (hM : M.IsDiag) (hN : N.IsDiag) (a : σ) :
    (M * N) a a = M a a * N a a := by
  rw [← hM.diagonal_diag, ← hN.diagonal_diag, Matrix.diagonal_mul_diagonal]
  simp

theorem prod_diag_mul_of_isDiag {ι : Type*} (S : Finset ι) (e : ι → σ) {M N : Matrix σ σ R}
    (hM : M.IsDiag) (hN : N.IsDiag) :
    ∏ m ∈ S, (M * N) (e m) (e m) = (∏ m ∈ S, M (e m) (e m)) * ∏ m ∈ S, N (e m) (e m) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => mul_apply_self_of_isDiag hM hN (e m)

end Diagonal

theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]

end CFSG.LieType.Universal.Spin
