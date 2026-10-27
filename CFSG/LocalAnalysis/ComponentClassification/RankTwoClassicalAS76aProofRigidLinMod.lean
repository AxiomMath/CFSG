module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidLinX

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Columns

variable {K : Type} [Field K] {k : ℕ}

@[expose] def IsBlockOne (k : ℕ) (x : Fin (2 + k)) : Prop := x = idxW k ∨ x = idxW' k

@[expose] def BlockOneShape (hk : 2 ≤ k) (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) : Prop :=
  ∀ x y : Fin (2 + k), x ≠ idxU hk → x ≠ idxV hk → y ≠ idxU hk → y ≠ idxV hk →
    ¬ (IsBlockOne k x ∧ IsBlockOne k y) → M x y = (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y

theorem isBlockOne_ne_idxU (hk : 2 ≤ k) {x : Fin (2 + k)} (hx : IsBlockOne k x) :
    x ≠ idxU hk := by
  rcases hx with rfl | rfl
  exacts [idxW_ne_idxU hk, idxW'_ne_idxU hk]

theorem isBlockOne_ne_idxV (hk : 2 ≤ k) {x : Fin (2 + k)} (hx : IsBlockOne k x) :
    x ≠ idxV hk := by
  rcases hx with rfl | rfl
  exacts [idxW_ne_idxV hk, idxW'_ne_idxV hk]

theorem stdX_apply_u (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ stdX K hk)
    (x : Fin (2 + k)) : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxU hk) =
      (Pi.single (idxU hk) (1 : K) : Fin (2 + k) → K) x := by
  have := congrFun hg.1 x
  rwa [mulVec_single_one, col_apply] at this

theorem stdX_apply_v (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ stdX K hk)
    (y : Fin (2 + k)) : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxV hk) y =
      (Pi.single (idxV hk) (1 : K) : Fin (2 + k) → K) y := by
  have := congrFun hg.2 y
  rwa [single_one_vecMul, row_apply] at this

theorem mulVec_single_other (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hs : BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {j : Fin (2 + k)} (hju : j ≠ idxU hk) (hjv : j ≠ idxV hk) (hj : ¬ IsBlockOne k j) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single j 1 =
      Pi.single j 1 + (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) j •
        Pi.single (idxU hk) 1 := by
  ext x
  rw [mulVec_single_one, col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hxu : x = idxU hk
  · subst hxu
    rw [Pi.single_eq_of_ne (Ne.symm hju), Pi.single_eq_same, mul_one, zero_add]
  rw [Pi.single_eq_of_ne hxu, mul_zero, add_zero]
  by_cases hxv : x = idxV hk
  · subst hxv
    rw [stdX_apply_v hk hg, Pi.single_eq_of_ne hjv, Pi.single_eq_of_ne (Ne.symm hjv)]
  rw [hs x j hxu hxv hju hjv (fun h => hj h.2), one_apply, Pi.single_apply]

end Columns

section Perfect

theorem eq_zero_of_map_mul_eq_add {G A : Type*} [Group G] [AddCommGroup A] {W : Subgroup G}
    (hW : ⁅W, W⁆ = W) (f : G → A) (hf : ∀ g ∈ W, ∀ h ∈ W, f (g * h) = f g + f h) {g : G}
    (hg : g ∈ W) : f g = 0 := by
  let φ : ↥W →* Multiplicative A :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun g h => by
      rw [← ofAdd_add]
      exact congrArg _ (hf g g.2 h h.2)
  have hle : ⁅W, W⁆ ≤ φ.ker.map W.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥W), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  rw [hW] at hle
  obtain ⟨g', hg', he⟩ := hle hg
  obtain rfl : g' = ⟨g, hg⟩ := Subtype.ext he
  have h1 : Multiplicative.ofAdd (f g) = 1 := hg'
  exact ofAdd_eq_one.mp h1

theorem mulVec_eq_self_of_perfect {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    {W : Subgroup (SpecialLinearGroup n K)} (hW : ⁅W, W⁆ = W) (P : (n → K) → Prop) (f : n → K)
    (hP : ∀ g ∈ W, P ((g : Matrix n n K) *ᵥ f - f))
    (hfix : ∀ g ∈ W, ∀ x, P x → (g : Matrix n n K) *ᵥ x = x) {g : SpecialLinearGroup n K}
    (hg : g ∈ W) : (g : Matrix n n K) *ᵥ f = f := by
  refine sub_eq_zero.mp (eq_zero_of_map_mul_eq_add hW
    (fun g : SpecialLinearGroup n K => (g : Matrix n n K) *ᵥ f - f) (fun g hg h hh => ?_) hg)
  change ((g * h : SpecialLinearGroup n K) : Matrix n n K) *ᵥ f - f =
    ((g : Matrix n n K) *ᵥ f - f) + ((h : Matrix n n K) *ᵥ f - f)
  have e := hfix g hg _ (hP h hh)
  rw [mulVec_sub] at e
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
  calc (g : Matrix n n K) *ᵥ ((h : Matrix n n K) *ᵥ f) - f =
      ((g : Matrix n n K) *ᵥ ((h : Matrix n n K) *ᵥ f) - (g : Matrix n n K) *ᵥ f) +
        ((g : Matrix n n K) *ᵥ f - f) := by abel
    _ = _ := by rw [e, add_comm]

end Perfect

section Fixed

variable {K : Type} [Field K] {k : ℕ}

theorem mulVec_single_other_eq_self (hk : 2 ≤ k)
    {W : Subgroup (SpecialLinearGroup (Fin (2 + k)) K)} (hW : ⁅W, W⁆ = W) (hWX : W ≤ stdX K hk)
    (hWs : ∀ g ∈ W, BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {j : Fin (2 + k)} (hju : j ≠ idxU hk) (hjv : j ≠ idxV hk) (hj : ¬ IsBlockOne k j)
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ W) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single j 1 = Pi.single j 1 := by
  refine mulVec_eq_self_of_perfect hW (fun x => ∀ t, t ≠ idxU hk → x t = 0) _
    (fun g hg => ?_) (fun g hg x hx => ?_) hg
  · intro t ht
    rw [mulVec_single_other hk (hWX hg) (hWs g hg) hju hjv hj, add_sub_cancel_left,
      Pi.smul_apply, Pi.single_eq_of_ne ht, smul_zero]
  · ext t
    simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single (idxU hk) (fun s _ hs => by rw [hx s hs, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), stdX_apply_u hk (hWX hg)]
    by_cases ht : t = idxU hk
    · subst ht
      rw [Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne ht, zero_mul, hx t ht]

end Fixed

section Torus

variable {K : Type} [Field K] {k : ℕ}

@[expose] def FixesStdEnds (hk : 2 ≤ k) (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) : Prop :=
  M *ᵥ Pi.single (idxU hk) 1 = Pi.single (idxU hk) 1 ∧
    Pi.single (idxV hk) 1 ᵥ* M = Pi.single (idxV hk) 1

theorem FixesStdEnds.apply_u {hk : 2 ≤ k} {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (h : FixesStdEnds hk M) (x : Fin (2 + k)) :
    M x (idxU hk) = (Pi.single (idxU hk) (1 : K) : Fin (2 + k) → K) x := by
  have := congrFun h.1 x
  rwa [mulVec_single_one, col_apply] at this

theorem FixesStdEnds.apply_v {hk : 2 ≤ k} {M : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (h : FixesStdEnds hk M) (y : Fin (2 + k)) :
    M (idxV hk) y = (Pi.single (idxV hk) (1 : K) : Fin (2 + k) → K) y := by
  have := congrFun h.2 y
  rwa [single_one_vecMul, row_apply] at this

@[expose] def TorusOneShape (hk : 2 ≤ k) (μ : K) (M : Matrix (Fin (2 + k)) (Fin (2 + k)) K) :
    Prop :=
  ∀ x y : Fin (2 + k), x ≠ idxU hk → x ≠ idxV hk → y ≠ idxU hk → y ≠ idxV hk →
    (IsBlockOne k x ∨ IsBlockOne k y) → M x y = if x = y then μ else 0

theorem sum_eq_add_add_of_ne {f : Fin (2 + k) → K} (a b c : Fin (2 + k)) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : ∀ x, x ≠ a → x ≠ b → x ≠ c → f x = 0) :
    ∑ x, f x = f a + f b + f c := by
  have ha : a ∉ ({b, c} : Finset (Fin (2 + k))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab, hac⟩
  have hsub : ∀ x ∈ (Finset.univ : Finset (Fin (2 + k))), x ∉ ({a, b, c} : Finset _) →
      f x = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact h x hx.1 hx.2.1 hx.2.2
  rw [← Finset.sum_subset (Finset.subset_univ {a, b, c}) hsub, Finset.sum_insert ha,
    Finset.sum_pair hbc, add_assoc]

theorem eq_of_commute_torus_u (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    {z : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hs : BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (hz : FixesStdEnds hk z) {μ : K} (hzs : TorusOneShape hk μ z)
    (hzg : z * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z)
    {i : Fin (2 + k)} (hi : IsBlockOne k i) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) i +
      (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxW k) *
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) i +
      (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxW' k) *
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) i =
      (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) i +
        (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) i * μ := by
  have hiu := isBlockOne_ne_idxU hk hi
  have hiv := isBlockOne_ne_idxV hk hi
  have h := congrFun (congrFun hzg (idxU hk)) i
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  rw [sum_eq_add_add_of_ne (idxU hk) (idxW k) (idxW' k) (idxW_ne_idxU hk).symm
    (idxW'_ne_idxU hk).symm (idxW_ne_idxW' k) (fun x hxu hxw hxw' => ?_),
    Fintype.sum_eq_add (idxU hk) i hiu.symm (fun x hx => ?_)] at h
  · have hzu := congrFun hz.1 (idxU hk)
    rw [mulVec_single_one, col_apply, Pi.single_eq_same] at hzu
    have hgu := congrFun hg.1 (idxU hk)
    rw [mulVec_single_one, col_apply, Pi.single_eq_same] at hgu
    have hzi : (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) i i = μ := by
      rw [hzs i i hiu hiv hiu hiv (Or.inl hi)]
      simp
    rw [hzu, hgu, hzi, one_mul, one_mul] at h
    exact h
  · have hzx : (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x i = 0 := by
      by_cases hxv : x = idxV hk
      · rw [hxv, hz.apply_v, Pi.single_eq_of_ne hiv]
      rw [hzs x i hx.1 hxv hiu hiv (Or.inr hi)]
      simp [hx.2]
    rw [hzx, mul_zero]
  · have hgx : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x i = 0 := by
      by_cases hxv : x = idxV hk
      · rw [hxv, stdX_apply_v hk hg, Pi.single_eq_of_ne hiv]
      have hxB : ¬ IsBlockOne k x := fun h => h.elim hxw hxw'
      rw [hs x i hxu hxv hiu hiv (fun h => hxB h.1), one_apply_ne]
      rintro rfl
      exact hxB hi
    rw [hgx, mul_zero]

theorem eq_of_commute_torus_v (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    {z : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hs : BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (hz : FixesStdEnds hk z) {μ : K} (hzs : TorusOneShape hk μ z)
    (hzg : z * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z)
    {x : Fin (2 + k)} (hx : IsBlockOne k x) :
    μ * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxV hk) +
      (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxV hk) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxW k) *
        (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) (idxV hk) +
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxW' k) *
        (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) (idxV hk) +
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x (idxV hk) := by
  have hxu := isBlockOne_ne_idxU hk hx
  have hxv := isBlockOne_ne_idxV hk hx
  have h := congrFun (congrFun hzg x) (idxV hk)
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  rw [Fintype.sum_eq_add x (idxV hk) hxv (fun y hy => ?_),
    sum_eq_add_add_of_ne (idxW k) (idxW' k) (idxV hk) (idxW_ne_idxW' k) (idxW_ne_idxV hk)
      (idxW'_ne_idxV hk) (fun y hyw hyw' hyv => ?_)] at h
  · have hzv := congrFun hz.2 (idxV hk)
    rw [single_one_vecMul, row_apply, Pi.single_eq_same] at hzv
    have hgv := congrFun hg.2 (idxV hk)
    rw [single_one_vecMul, row_apply, Pi.single_eq_same] at hgv
    have hzx : (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x x = μ := by
      rw [hzs x x hxu hxv hxu hxv (Or.inl hx)]
      simp
    rw [hzv, hgv, hzx, mul_one, mul_one] at h
    exact h
  · have hgy : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y = 0 := by
      by_cases hyu : y = idxU hk
      · rw [hyu, stdX_apply_u hk hg, Pi.single_eq_of_ne hxu]
      have hyB : ¬ IsBlockOne k y := fun h => h.elim hyw hyw'
      rw [hs x y hxu hxv hyu hyv (fun h => hyB h.2), one_apply_ne]
      rintro rfl
      exact hyB hx
    rw [hgy, zero_mul]
  · have hzy : (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y = 0 := by
      by_cases hyu : y = idxU hk
      · rw [hyu, hz.apply_u, Pi.single_eq_of_ne hxu]
      rw [hzs x y hxu hxv hyu hy.2 (Or.inl hx)]
      simp [Ne.symm hy.1]
    rw [hzy, zero_mul]

theorem mulVec_eps_of_torus (hk : 2 ≤ k) {g : SpecialLinearGroup (Fin (2 + k)) K}
    {z : Matrix (Fin (2 + k)) (Fin (2 + k)) K}
    (hg : g ∈ stdX K hk) (hs : BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (hz : FixesStdEnds hk z) {μ m : K} (hm : (μ - 1) * m = 1) (hzs : TorusOneShape hk μ z)
    (hzg : z * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z)
    {i : Fin (2 + k)} (hi : IsBlockOne k i) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ (Pi.single i 1 +
      ((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) i * m) • Pi.single (idxU hk) 1) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) i • (Pi.single (idxW k) 1 +
        ((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxW k) * m) •
          Pi.single (idxU hk) 1) +
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) i • (Pi.single (idxW' k) 1 +
        ((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) (idxW' k) * m) •
          Pi.single (idxU hk) 1) := by
  have hC := eq_of_commute_torus_u hk hg hs hz hzs hzg hi
  have hiu := isBlockOne_ne_idxU hk hi
  have hiv := isBlockOne_ne_idxV hk hi
  ext t
  rw [mulVec_add, mulVec_smul, mulVec_single_one, mulVec_single_one]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]
  rw [stdX_apply_u hk hg]
  by_cases htu : t = idxU hk
  · subst htu
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (idxW_ne_idxU hk).symm,
      Pi.single_eq_of_ne (idxW'_ne_idxU hk).symm]
    linear_combination (-m) * hC -
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxU hk) i * hm
  rw [Pi.single_eq_of_ne htu, mul_zero, mul_zero, mul_zero, add_zero, add_zero, add_zero]
  by_cases htw : t = idxW k
  · subst htw
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (idxW_ne_idxW' k), mul_one, mul_zero, add_zero]
  by_cases htw' : t = idxW' k
  · subst htw'
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (idxW_ne_idxW' k).symm, mul_one, mul_zero,
      zero_add]
  rw [Pi.single_eq_of_ne htw, Pi.single_eq_of_ne htw', mul_zero, mul_zero, add_zero]
  by_cases htv : t = idxV hk
  · rw [htv, stdX_apply_v hk hg, Pi.single_eq_of_ne hiv]
  have htB : ¬ IsBlockOne k t := fun h => h.elim htw htw'
  rw [hs t i htu htv hiu hiv (fun h => htB h.1), one_apply_ne]
  rintro rfl
  exact htB hi

theorem mulVec_delta_of_torus (hk : 2 ≤ k) {W : Subgroup (SpecialLinearGroup (Fin (2 + k)) K)}
    (hW : ⁅W, W⁆ = W) (hWX : W ≤ stdX K hk)
    (hWs : ∀ g ∈ W, BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {z : Matrix (Fin (2 + k)) (Fin (2 + k)) K} (hz : FixesStdEnds hk z) {μ m : K}
    (hm : (μ - 1) * m = 1) (hzs : TorusOneShape hk μ z)
    (hzW : ∀ g ∈ W, z * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z)
    {g : SpecialLinearGroup (Fin (2 + k)) K} (hg : g ∈ W) :
    (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ (Pi.single (idxV hk) 1 +
      (-((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) (idxV hk) * m)) •
        Pi.single (idxW k) 1 +
      (-((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) (idxV hk) * m)) •
        Pi.single (idxW' k) 1) =
      Pi.single (idxV hk) 1 +
        (-((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) (idxV hk) * m)) •
          Pi.single (idxW k) 1 +
        (-((z : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) (idxV hk) * m)) •
          Pi.single (idxW' k) 1 := by
  refine mulVec_eq_self_of_perfect hW (fun x => ∀ t, (IsBlockOne k t ∨ t = idxV hk) → x t = 0)
    _ (fun g hg => ?_) (fun g hg x hx => ?_) hg
  · intro t ht
    rw [Pi.sub_apply, sub_eq_zero, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul,
      mulVec_single_one, mulVec_single_one, mulVec_single_one]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, col_apply]
    rcases ht with ht | rfl
    · have hC := eq_of_commute_torus_v hk (hWX hg) (hWs g hg) hz hzs (hzW g hg) ht
      rcases ht with rfl | rfl
      · rw [Pi.single_eq_of_ne (idxW_ne_idxV hk), Pi.single_eq_same,
          Pi.single_eq_of_ne (idxW_ne_idxW' k)]
        linear_combination m * hC -
          (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW k) (idxV hk) * hm
      · rw [Pi.single_eq_of_ne (idxW'_ne_idxV hk), Pi.single_eq_same,
          Pi.single_eq_of_ne (idxW_ne_idxW' k).symm]
        linear_combination m * hC -
          (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (idxW' k) (idxV hk) * hm
    · simp only [stdX_apply_v hk (hWX hg), Pi.single_eq_same,
        Pi.single_eq_of_ne (idxW_ne_idxV hk), Pi.single_eq_of_ne (idxW'_ne_idxV hk),
        Pi.single_eq_of_ne (idxW_ne_idxV hk).symm, Pi.single_eq_of_ne (idxW'_ne_idxV hk).symm,
        mul_zero]
  · have hent : ∀ t s, (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) t s * x s =
        (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) t s * x s := by
      intro t s
      by_cases hs : IsBlockOne k s ∨ s = idxV hk
      · rw [hx s hs, mul_zero, mul_zero]
      obtain ⟨hsB, hsv⟩ := not_or.mp hs
      by_cases hsu : s = idxU hk
      · rw [hsu, stdX_apply_u hk (hWX hg), Pi.single_apply, one_apply]
      · have hcol := congrFun (mulVec_single_other_eq_self hk hW hWX hWs hsu hsv hsB hg) t
        rw [mulVec_single_one, col_apply] at hcol
        rw [hcol, Pi.single_apply, one_apply]
    ext t
    conv_rhs => rw [← one_mulVec x]
    simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun s _ => hent t s

end Torus


section Conj

variable {K : Type} [Field K] {k : ℕ}

theorem mulVec_trSL {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : K) (f : Fin n → K) :
    (trSL i j hij c : Matrix (Fin n) (Fin n) K) *ᵥ f = f + (c * f j) • Pi.single i 1 := by
  rw [coe_trSL, add_mulVec, one_mulVec, single_mulVec_eq]

theorem mulVec_trSL_of_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : K) {f : Fin n → K}
    (hf : f j = 0) : (trSL i j hij c : Matrix (Fin n) (Fin n) K) *ᵥ f = f := by
  rw [mulVec_trSL, hf, mul_zero, zero_smul, add_zero]

theorem inv_mulVec_mulVec {n : ℕ} (s : SpecialLinearGroup (Fin n) K) (f : Fin n → K) :
    ((s⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((s : Matrix (Fin n) (Fin n) K) *ᵥ f) = f := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

variable (K) in
@[expose] noncomputable def stdNormU (hk : 2 ≤ k) (a a' c c' : K) :
    SpecialLinearGroup (Fin (2 + k)) K :=
  trSL (idxW k) (idxV hk) (idxW_ne_idxV hk) c * trSL (idxW' k) (idxV hk) (idxW'_ne_idxV hk) c' *
    (trSL (idxU hk) (idxW k) (idxW_ne_idxU hk).symm a *
      trSL (idxU hk) (idxW' k) (idxW'_ne_idxU hk).symm a')

theorem stdNormU_mulVec (hk : 2 ≤ k) (a a' c c' : K) (f : Fin (2 + k) → K) :
    (stdNormU K hk a a' c c' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ f =
      (trSL (idxW k) (idxV hk) (idxW_ne_idxV hk) c : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ
        ((trSL (idxW' k) (idxV hk) (idxW'_ne_idxV hk) c' :
          Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ
        ((trSL (idxU hk) (idxW k) (idxW_ne_idxU hk).symm a :
          Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ
        ((trSL (idxU hk) (idxW' k) (idxW'_ne_idxU hk).symm a' :
          Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ f))) := by
  rw [stdNormU, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

theorem stdNormU_mulVec_single_of_ne (hk : 2 ≤ k) (a a' c c' : K) {j : Fin (2 + k)}
    (hjv : j ≠ idxV hk) (hjw : j ≠ idxW k) (hjw' : j ≠ idxW' k) :
    (stdNormU K hk a a' c c' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single j 1 =
      Pi.single j 1 := by
  rw [stdNormU_mulVec,
    mulVec_trSL_of_eq_zero (idxW'_ne_idxU hk).symm a' (Pi.single_eq_of_ne' hjw' (1 : K)),
    mulVec_trSL_of_eq_zero (idxW_ne_idxU hk).symm a (Pi.single_eq_of_ne' hjw (1 : K)),
    mulVec_trSL_of_eq_zero (idxW'_ne_idxV hk) c' (Pi.single_eq_of_ne' hjv (1 : K)),
    mulVec_trSL_of_eq_zero (idxW_ne_idxV hk) c (Pi.single_eq_of_ne' hjv (1 : K))]


theorem stdNormU_mulVec_single_w (hk : 2 ≤ k) (a a' c c' : K) :
    (stdNormU K hk a a' c c' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxW k) 1 =
      Pi.single (idxW k) 1 + a • Pi.single (idxU hk) 1 := by
  have hv : (Pi.single (idxW k) (1 : K) + a • Pi.single (idxU hk) 1 : Fin (2 + k) → K)
      (idxV hk) = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' (idxW_ne_idxV hk),
      Pi.single_eq_of_ne' (idxU_ne_idxV hk), smul_zero, add_zero]
  rw [stdNormU_mulVec, mulVec_trSL_of_eq_zero (idxW'_ne_idxU hk).symm a'
      (Pi.single_eq_of_ne' (idxW_ne_idxW' k) (1 : K)),
    mulVec_trSL (idxU hk) (idxW k) (idxW_ne_idxU hk).symm a (Pi.single (idxW k) 1),
    Pi.single_eq_same, mul_one, mulVec_trSL_of_eq_zero (idxW'_ne_idxV hk) c' hv,
    mulVec_trSL_of_eq_zero (idxW_ne_idxV hk) c hv]

theorem stdNormU_mulVec_single_w' (hk : 2 ≤ k) (a a' c c' : K) :
    (stdNormU K hk a a' c c' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxW' k) 1 =
      Pi.single (idxW' k) 1 + a' • Pi.single (idxU hk) 1 := by
  have hw : (Pi.single (idxW' k) (1 : K) + a' • Pi.single (idxU hk) 1 : Fin (2 + k) → K)
      (idxW k) = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' (idxW_ne_idxW' k).symm,
      Pi.single_eq_of_ne' (idxW_ne_idxU hk).symm, smul_zero, add_zero]
  have hv : (Pi.single (idxW' k) (1 : K) + a' • Pi.single (idxU hk) 1 : Fin (2 + k) → K)
      (idxV hk) = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' (idxW'_ne_idxV hk),
      Pi.single_eq_of_ne' (idxU_ne_idxV hk), smul_zero, add_zero]
  rw [stdNormU_mulVec,
    mulVec_trSL (idxU hk) (idxW' k) (idxW'_ne_idxU hk).symm a' (Pi.single (idxW' k) 1),
    Pi.single_eq_same, mul_one, mulVec_trSL_of_eq_zero (idxW_ne_idxU hk).symm a hw,
    mulVec_trSL_of_eq_zero (idxW'_ne_idxV hk) c' hv, mulVec_trSL_of_eq_zero (idxW_ne_idxV hk) c hv]

theorem stdNormU_mulVec_single_v (hk : 2 ≤ k) (a a' c c' : K) :
    (stdNormU K hk a a' c c' : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxV hk) 1 =
      Pi.single (idxV hk) 1 + c • Pi.single (idxW k) 1 + c' • Pi.single (idxW' k) 1 := by
  have hv1 : (Pi.single (idxV hk) (1 : K) + c' • Pi.single (idxW' k) 1 : Fin (2 + k) → K)
      (idxV hk) = 1 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne' (idxW'_ne_idxV hk),
      smul_zero, add_zero]
  rw [stdNormU_mulVec, mulVec_trSL_of_eq_zero (idxW'_ne_idxU hk).symm a'
      (Pi.single_eq_of_ne' (idxW'_ne_idxV hk).symm (1 : K)),
    mulVec_trSL_of_eq_zero (idxW_ne_idxU hk).symm a
      (Pi.single_eq_of_ne' (idxW_ne_idxV hk).symm (1 : K)),
    mulVec_trSL (idxW' k) (idxV hk) (idxW'_ne_idxV hk) c' (Pi.single (idxV hk) 1),
    Pi.single_eq_same, mul_one, mulVec_trSL (idxW k) (idxV hk) (idxW_ne_idxV hk) c, hv1, mul_one]
  exact add_right_comm _ _ _


theorem mem_range_blkSL₁_of_apply {g : SpecialLinearGroup (Fin (2 + k)) K}
    (hg : ∀ x y : Fin (2 + k), ¬ (IsBlockOne k x ∧ IsBlockOne k y) →
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y =
        (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y) :
    g ∈ (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range := by
  obtain ⟨A, B, C, D, hABCD⟩ := eq_reindex_fromBlocks (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  have hent : ∀ a b, (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (finSumFinEquiv a)
      (finSumFinEquiv b) = fromBlocks A B C D a b := by
    intro a b
    rw [hABCD, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  have hone : ∀ a b, (1 : Matrix (Fin (2 + k)) (Fin (2 + k)) K) (finSumFinEquiv a)
      (finSumFinEquiv b) = fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0
        (1 : Matrix (Fin k) (Fin k) K) a b := by
    intro a b
    rw [fromBlocks_one, one_apply, one_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  have hR : ∀ b : Fin k, ¬ IsBlockOne k (finSumFinEquiv (Sum.inr b)) := by
    intro b h
    rcases h with h | h <;> exact Sum.inr_ne_inl (finSumFinEquiv.injective h)
  have hBz : B = 0 := by
    ext a b
    have h := hg (finSumFinEquiv (Sum.inl a)) (finSumFinEquiv (Sum.inr b)) (fun h => hR b h.2)
    rwa [hent, hone, fromBlocks_apply₁₂, fromBlocks_apply₁₂] at h
  have hCz : C = 0 := by
    ext a b
    have h := hg (finSumFinEquiv (Sum.inr a)) (finSumFinEquiv (Sum.inl b)) (fun h => hR a h.1)
    rwa [hent, hone, fromBlocks_apply₂₁, fromBlocks_apply₂₁] at h
  have hDz : D = 1 := by
    ext a b
    have h := hg (finSumFinEquiv (Sum.inr a)) (finSumFinEquiv (Sum.inr b)) (fun h => hR a h.1)
    rwa [hent, hone, fromBlocks_apply₂₂, fromBlocks_apply₂₂] at h
  have hgA : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) = blk A 1 := by
    rw [hABCD, hBz, hCz, hDz]
    rfl
  have hA : A.det = 1 := by
    have h := g.2
    rw [hgA, det_blk, det_one, mul_one] at h
    exact h
  let X : SpecialLinearGroup (Fin 2) K := ⟨A, hA⟩
  refine ⟨X, Subtype.ext ?_⟩
  change blk A 1 = (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  exact hgA.symm


theorem stdNormU_mem_stdX (hk : 2 ≤ k) (a a' c c' : K) : stdNormU K hk a a' c c' ∈ stdX K hk :=
  mul_mem (mul_mem (trSL_mem_stdX hk _ (idxW_ne_idxV hk) (idxU_ne_idxV hk).symm c)
      (trSL_mem_stdX hk _ (idxW'_ne_idxV hk) (idxU_ne_idxV hk).symm c'))
    (mul_mem (trSL_mem_stdX hk _ (idxU_ne_idxV hk) (idxW_ne_idxU hk) a)
      (trSL_mem_stdX hk _ (idxU_ne_idxV hk) (idxW'_ne_idxU hk) a'))

theorem exists_conj_mem_range_blkSL₁_of_matrix (hk : 2 ≤ k)
    {W : Subgroup (SpecialLinearGroup (Fin (2 + k)) K)} (hW : ⁅W, W⁆ = W) (hWX : W ≤ stdX K hk)
    (hWs : ∀ g ∈ W, BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {z : Matrix (Fin (2 + k)) (Fin (2 + k)) K} (hz : FixesStdEnds hk z) {μ : K} (hμ : μ ≠ 1)
    (hzs : TorusOneShape hk μ z)
    (hzW : ∀ g ∈ W, z * (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) =
      (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) * z) :
    ∃ u₀ : SpecialLinearGroup (Fin (2 + k)) K, u₀ ∈ stdX K hk ∧ ∀ g ∈ W, u₀⁻¹ * g * u₀ ∈
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range := by
  have hm : (μ - 1) * (μ - 1)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hμ)
  set m := (μ - 1)⁻¹
  set Z := (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K)
  obtain ⟨u₀, hu₀X, hw, hw', hv, hj⟩ : ∃ u₀ : SpecialLinearGroup (Fin (2 + k)) K,
      u₀ ∈ stdX K hk ∧
      (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxW k) 1 =
        Pi.single (idxW k) 1 + (Z (idxU hk) (idxW k) * m) • Pi.single (idxU hk) 1 ∧
      (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxW' k) 1 =
        Pi.single (idxW' k) 1 + (Z (idxU hk) (idxW' k) * m) • Pi.single (idxU hk) 1 ∧
      (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single (idxV hk) 1 =
        Pi.single (idxV hk) 1 + (-(Z (idxW k) (idxV hk) * m)) • Pi.single (idxW k) 1 +
          (-(Z (idxW' k) (idxV hk) * m)) • Pi.single (idxW' k) 1 ∧
      ∀ j, j ≠ idxV hk → j ≠ idxW k → j ≠ idxW' k →
        (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single j 1 = Pi.single j 1 :=
    ⟨stdNormU K hk _ _ _ _, stdNormU_mem_stdX hk _ _ _ _, stdNormU_mulVec_single_w hk _ _ _ _,
      stdNormU_mulVec_single_w' hk _ _ _ _, stdNormU_mulVec_single_v hk _ _ _ _,
      fun j hjv hjw hjw' => stdNormU_mulVec_single_of_ne hk _ _ _ _ hjv hjw hjw'⟩
  refine ⟨u₀, hu₀X, fun g hg => mem_range_blkSL₁_of_apply fun x y hxy => ?_⟩
  have hentry : ((u₀⁻¹ * g * u₀ : SpecialLinearGroup (Fin (2 + k)) K) :
      Matrix (Fin (2 + k)) (Fin (2 + k)) K) x y =
      (((u₀⁻¹ * g * u₀ : SpecialLinearGroup (Fin (2 + k)) K) :
        Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single y 1) x := by
    rw [mulVec_single_one, col_apply]
  rw [hentry, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← mulVec_mulVec, ← mulVec_mulVec]
  by_cases hy : IsBlockOne k y
  · have hx : ¬ IsBlockOne k x := fun h => hxy ⟨h, hy⟩
    have hε : (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single y 1 =
        Pi.single y 1 + (Z (idxU hk) y * m) • Pi.single (idxU hk) 1 := by
      rcases hy with rfl | rfl
      exacts [hw, hw']
    rw [hε, mulVec_eps_of_torus hk (hWX hg) (hWs g hg) hz hm hzs (hzW g hg) hy, ← hw, ← hw',
      ← mulVec_smul, ← mulVec_smul, ← mulVec_add, inv_mulVec_mulVec, Pi.add_apply,
      Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hx (Or.inl h)),
      Pi.single_eq_of_ne (fun h => hx (Or.inr h)), smul_zero, smul_zero, add_zero,
      one_apply_ne (by rintro rfl; exact hx hy)]
  · have hfix : (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ
        ((u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single y 1) =
          (u₀ : Matrix (Fin (2 + k)) (Fin (2 + k)) K) *ᵥ Pi.single y 1 := by
      by_cases hyv : y = idxV hk
      · rw [hyv, hv]
        exact mulVec_delta_of_torus hk hW hWX hWs hz hm hzs hzW hg
      rw [hj y hyv (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))]
      by_cases hyu : y = idxU hk
      · rw [hyu]
        exact (hWX hg).1
      exact mulVec_single_other_eq_self hk hW hWX hWs hyu hyv hy hg
    rw [hfix, inv_mulVec_mulVec, Pi.single_apply, one_apply]

theorem exists_conj_mem_range_blkSL₁ (hk : 2 ≤ k)
    {W : Subgroup (SpecialLinearGroup (Fin (2 + k)) K)} (hW : ⁅W, W⁆ = W) (hWX : W ≤ stdX K hk)
    (hWs : ∀ g ∈ W, BlockOneShape hk (g : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    {z : SpecialLinearGroup (Fin (2 + k)) K} (hz : z ∈ stdX K hk) {μ : K} (hμ : μ ≠ 1)
    (hzs : TorusOneShape hk μ (z : Matrix (Fin (2 + k)) (Fin (2 + k)) K))
    (hzW : ∀ g ∈ W, z * g = g * z) :
    ∃ u₀ : SpecialLinearGroup (Fin (2 + k)) K, ∀ g ∈ W, u₀⁻¹ * g * u₀ ∈
      (blkSL₁ : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin (2 + k)) K).range :=
  (exists_conj_mem_range_blkSL₁_of_matrix hk hW hWX hWs hz hμ hzs fun g hg => by
    have h := congrArg Subtype.val (hzW g hg)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h).imp
      fun _ h => h.2

end Conj

end CFSG.ComponentClassification.RankTwoClassical
