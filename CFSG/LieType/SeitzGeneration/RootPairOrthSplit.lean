module

public import CFSG.LieType.SeitzGeneration.RootPairOrthRat
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap

namespace RootPairOrth

structure SplitCoord {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) where
  star : Fin d → Fin d
  star_star : ∀ a, star (star a) = a
  star_ne : ∀ a, star a ≠ a
  Q_single : ∀ a, Q (Pi.single a 1) = 0
  polar_single : ∀ a w, polar Q (Pi.single a 1) w = w (star a)

section Pairs

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

abbrev IsRat (k : Subfield K) (v : Fin d → K) : Prop := ∀ i, v i ∈ k

@[expose] def IsTS (Q : QuadraticForm K (Fin d → K)) (x y : Fin d → K) : Prop :=
  Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 0

@[expose] def Phi (Q : QuadraticForm K (Fin d → K)) (g : Matrix (Fin d) (Fin d) K) (μ : K)
    (x y x₀ y₀ : Fin d → K) : K :=
  μ⁻¹ * (polar Q x (g *ᵥ x₀) * polar Q y (g *ᵥ y₀) - polar Q x (g *ᵥ y₀) * polar Q y (g *ᵥ x₀))

theorem isRat_single (k : Subfield K) (a : Fin d) : IsRat k (Pi.single a 1 : Fin d → K) := by
  intro i
  by_cases h : i = a
  · subst h; simp [k.one_mem]
  · simp [h, k.zero_mem]

theorem IsRat.add {k : Subfield K} {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) :
    IsRat k (x + y) := fun i => k.add_mem (hx i) (hy i)

theorem IsRat.sub {k : Subfield K} {x y : Fin d → K} (hx : IsRat k x) (hy : IsRat k y) :
    IsRat k (x - y) := fun i => k.sub_mem (hx i) (hy i)

omit [Field K] in
theorem Fin.exists_notMem (s : Finset (Fin d)) (hs : s.card < d) : ∃ i, i ∉ s := by
  by_contra h
  push Not at h
  have : s = Finset.univ := Finset.eq_univ_iff_forall.mpr h
  rw [this, Finset.card_univ, Fintype.card_fin] at hs
  omega

end Pairs

section Split

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : SplitCoord Q)

theorem SplitCoord.polar_single_single (a b : Fin d) :
    polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) = if S.star a = b then 1 else 0 := by
  rw [S.polar_single, Pi.single_apply]

theorem SplitCoord.isTS_single {a b : Fin d} (hb : b ≠ S.star a) :
    IsTS Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) :=
  ⟨S.Q_single a, S.Q_single b, by rw [S.polar_single_single]; simp [Ne.symm hb]⟩

theorem SplitCoord.isTS_plane {a j : Fin d} (hj : j ≠ a) :
    IsTS Q ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
      (Pi.single j 1 - Pi.single (S.star a) 1) := by
  have hne : S.star j ≠ S.star a := fun h => hj (by
    have := congrArg S.star h
    rwa [S.star_star, S.star_star] at this)
  have h1 : polar Q (Pi.single a 1 : Fin d → K) (Pi.single (S.star j) 1) = 0 := by
    rw [S.polar_single_single]; simp [Ne.symm hne]
  have h2 : polar Q (Pi.single j 1 : Fin d → K) (Pi.single (S.star a) 1) = 0 := by
    rw [S.polar_single_single]; simp [hne]
  refine ⟨?_, ?_, ?_⟩
  · rw [QuadraticMap.map_add Q, S.Q_single, S.Q_single, h1]; ring
  · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, S.Q_single, S.Q_single,
      polar_neg_right, h2]; ring
  · simp only [polar_add_left, polar_sub_right, S.polar_single_single, S.star_star]
    by_cases h : S.star a = j
    · simp [h]
    · simp [h, Ne.symm h]

inductive IsBasic : (Fin d → K) → (Fin d → K) → Prop
  | single {a b : Fin d} : b ≠ S.star a → IsBasic (Pi.single a 1) (Pi.single b 1)
  | plane {a j : Fin d} : j ≠ a → j ≠ S.star a →
      IsBasic ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
        (Pi.single j 1 - Pi.single (S.star a) 1)

theorem IsBasic.isTS {S : SplitCoord Q} {x y : Fin d → K} (h : IsBasic S x y) : IsTS Q x y := by
  cases h with
  | single hb => exact S.isTS_single hb
  | plane hj _ => exact S.isTS_plane hj

theorem IsBasic.isRat {S : SplitCoord Q} (k : Subfield K) {x y : Fin d → K} (h : IsBasic S x y) :
    IsRat k x ∧ IsRat k y := by
  cases h with
  | single _ => exact ⟨isRat_single k _, isRat_single k _⟩
  | plane _ _ =>
    exact ⟨(isRat_single k _).add (isRat_single k _), (isRat_single k _).sub (isRat_single k _)⟩

variable (k : Subfield K) in
@[expose] def PairsRational (g : Matrix (Fin d) (Fin d) K) (μ : K) : Prop :=
  ∀ x y x₀ y₀ : Fin d → K, IsBasic S x y → IsBasic S x₀ y₀ → Phi Q g μ x y x₀ y₀ ∈ k

theorem SplitCoord.phi_single (g : Matrix (Fin d) (Fin d) K) (μ : K) (a b c c' : Fin d) :
    Phi Q g μ (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) (Pi.single c' 1) =
      μ⁻¹ * (g (S.star a) c * g (S.star b) c' - g (S.star a) c' * g (S.star b) c) := by
  simp [Phi, S.polar_single]

theorem phi_self_left (g : Matrix (Fin d) (Fin d) K) (μ : K) (x x₀ y₀ : Fin d → K) :
    Phi Q g μ x x x₀ y₀ = 0 := by
  simp only [Phi]; ring

theorem SplitCoord.phi_row_identity (g : Matrix (Fin d) (Fin d) K) (μ : K) (a j : Fin d)
    (x₀ y₀ : Fin d → K) :
    Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ +
        Phi Q g μ (Pi.single j 1) (Pi.single (S.star j) 1) x₀ y₀ =
      Phi Q g μ (Pi.single a 1) (Pi.single j 1) x₀ y₀ -
        Phi Q g μ (Pi.single (S.star j) 1) (Pi.single (S.star a) 1) x₀ y₀ -
        Phi Q g μ ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
          (Pi.single j 1 - Pi.single (S.star a) 1) x₀ y₀ := by
  simp only [Phi, polar_add_left, polar_sub_left, S.polar_single, S.star_star]
  ring

theorem SplitCoord.phi_col_identity (g : Matrix (Fin d) (Fin d) K) (μ : K) (x y : Fin d → K)
    (c l : Fin d) :
    Phi Q g μ x y (Pi.single c 1) (Pi.single (S.star c) 1) +
        Phi Q g μ x y (Pi.single l 1) (Pi.single (S.star l) 1) =
      Phi Q g μ x y (Pi.single c 1) (Pi.single l 1) -
        Phi Q g μ x y (Pi.single (S.star l) 1) (Pi.single (S.star c) 1) -
        Phi Q g μ x y ((Pi.single c 1 : Fin d → K) + Pi.single (S.star l) 1)
          (Pi.single l 1 - Pi.single (S.star c) 1) := by
  simp only [Phi, Matrix.mulVec_add, Matrix.mulVec_sub, polar_add_right, polar_sub_right]
  ring

end Split

section Half

variable {K : Type} [Field K]

theorem half_trick {k : Subfield K} (h2 : (2 : K) ≠ 0) {e₁ e₂ e₃ : K} (h12 : e₁ + e₂ ∈ k)
    (h13 : e₁ + e₃ ∈ k) (h23 : e₂ + e₃ ∈ k) : e₁ ∈ k := by
  have h2k : (2 : K) ∈ k := by
    rw [← one_add_one_eq_two]; exact k.add_mem k.one_mem k.one_mem
  have : e₁ = (2 : K)⁻¹ * ((e₁ + e₂) + (e₁ + e₃) - (e₂ + e₃)) := by
    field_simp; ring
  rw [this]
  exact k.mul_mem (k.inv_mem h2k) (k.sub_mem (k.add_mem h12 h13) h23)

end Half

section Chain

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : SplitCoord Q)
  {k : Subfield K} {g : Matrix (Fin d) (Fin d) K} {μ : K}

theorem SplitCoord.exists_three (hd : 5 < d) (a : Fin d) :
    ∃ j l : Fin d, j ≠ a ∧ j ≠ S.star a ∧ l ≠ a ∧ l ≠ S.star a ∧ l ≠ j ∧ l ≠ S.star j := by
  obtain ⟨j, hj⟩ := Fin.exists_notMem ({a, S.star a} : Finset (Fin d))
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  obtain ⟨l, hl⟩ := Fin.exists_notMem ({a, S.star a, j, S.star j} : Finset (Fin d))
    (lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hl
  exact ⟨j, l, hj.1, hj.2, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2⟩

theorem SplitCoord.phi_dual_row (h2 : (2 : K) ≠ 0) (hd : 5 < d) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasic S x y → Phi Q g μ x y x₀ y₀ ∈ k) (a : Fin d) :
    Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ ∈ k := by
  obtain ⟨j, l, hja, hjs, hla, hls, hlj, hljs⟩ := S.exists_three hd a
  have pair : ∀ a j : Fin d, j ≠ a → j ≠ S.star a →
      Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ +
        Phi Q g μ (Pi.single j 1) (Pi.single (S.star j) 1) x₀ y₀ ∈ k := by
    intro a j hja hjs
    rw [S.phi_row_identity]
    exact k.sub_mem (k.sub_mem (hcol _ _ (IsBasic.single hjs))
      (hcol _ _ (IsBasic.single (by rw [S.star_star]; exact Ne.symm hjs))))
      (hcol _ _ (IsBasic.plane hja hjs))
  exact half_trick h2 (pair a j hja hjs) (pair a l hla hls) (pair j l hlj hljs)

theorem SplitCoord.phi_dual_col (h2 : (2 : K) ≠ 0) (hd : 5 < d) {x y : Fin d → K}
    (hrow : ∀ x₀ y₀ : Fin d → K, IsBasic S x₀ y₀ → Phi Q g μ x y x₀ y₀ ∈ k) (c : Fin d) :
    Phi Q g μ x y (Pi.single c 1) (Pi.single (S.star c) 1) ∈ k := by
  obtain ⟨j, l, hjc, hjs, hlc, hls, hlj, hljs⟩ := S.exists_three hd c
  have pair : ∀ c l : Fin d, l ≠ c → l ≠ S.star c →
      Phi Q g μ x y (Pi.single c 1) (Pi.single (S.star c) 1) +
        Phi Q g μ x y (Pi.single l 1) (Pi.single (S.star l) 1) ∈ k := by
    intro c l hlc hls
    rw [S.phi_col_identity]
    exact k.sub_mem (k.sub_mem (hrow _ _ (IsBasic.single hls))
      (hrow _ _ (IsBasic.single (by rw [S.star_star]; exact Ne.symm hls))))
      (hrow _ _ (IsBasic.plane hlc hls))
  exact half_trick h2 (pair c j hjc hjs) (pair c l hlc hls) (pair j l hlj hljs)

theorem SplitCoord.phi_coord_mem (hP : PairsRational S k g μ) (h2 : (2 : K) ≠ 0) (hd : 5 < d)
    (a b c c' : Fin d) :
    Phi Q g μ (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) (Pi.single c' 1) ∈ k := by
  by_cases hab : b = S.star a <;> by_cases hcc : c' = S.star c
  · subst hab hcc
    exact S.phi_dual_col h2 hd (fun x₀ y₀ hx₀ => S.phi_dual_row h2 hd
      (fun x y hxy => hP x y x₀ y₀ hxy hx₀) a) c
  · subst hab
    exact S.phi_dual_row h2 hd (fun x y hxy => hP x y _ _ hxy (IsBasic.single hcc)) a
  · subst hcc
    exact S.phi_dual_col h2 hd (fun x₀ y₀ hx₀ => hP _ _ x₀ y₀ (IsBasic.single hab) hx₀) c
  · exact hP _ _ _ _ (IsBasic.single hab) (IsBasic.single hcc)

theorem SplitCoord.rational_of_pairs (hP : PairsRational S k g μ) (h2 : (2 : K) ≠ 0)
    (hd : 5 < d) {σ : K →+* K} (hσ : ∀ x, σ x = x ↔ x ∈ k) (hμ : μ ≠ 0) (hg : g.det ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  refine rational_of_minors (by rw [Fintype.card_fin]; omega) hσ hμ hg (fun r s c c' => ?_)
  have := S.phi_coord_mem hP h2 hd (S.star r) (S.star s) c c'
  rwa [S.phi_single, S.star_star, S.star_star] at this

end Chain

end RootPairOrth

end CFSG.LieType.SeitzGeneration
