module

public import CFSG.LieType.SeitzGeneration.RootPairOrthSplit

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix QuadraticMap

namespace RootPairOrth

structure HypCoord {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K)) where
  hyp : Finset (Fin d)
  star : Fin d → Fin d
  star_mem : ∀ a ∈ hyp, star a ∈ hyp
  star_star : ∀ a ∈ hyp, star (star a) = a
  star_ne : ∀ a ∈ hyp, star a ≠ a
  Q_single : ∀ a ∈ hyp, Q (Pi.single a 1) = 0
  polar_single : ∀ a ∈ hyp, ∀ w, polar Q (Pi.single a 1) w = w (star a)
  card_hyp : 5 < hyp.card

section Basic

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem phi_add_snd (g : Matrix (Fin d) (Fin d) K) (μ : K) (x y y' x₀ y₀ : Fin d → K) :
    Phi Q g μ x (y + y') x₀ y₀ = Phi Q g μ x y x₀ y₀ + Phi Q g μ x y' x₀ y₀ := by
  simp only [Phi, polar_add_left]; ring

theorem phi_sub_snd (g : Matrix (Fin d) (Fin d) K) (μ : K) (x y y' x₀ y₀ : Fin d → K) :
    Phi Q g μ x (y - y') x₀ y₀ = Phi Q g μ x y x₀ y₀ - Phi Q g μ x y' x₀ y₀ := by
  simp only [Phi, polar_sub_left]; ring

theorem phi_smul_snd (g : Matrix (Fin d) (Fin d) K) (μ c : K) (x y x₀ y₀ : Fin d → K) :
    Phi Q g μ x (c • y) x₀ y₀ = c * Phi Q g μ x y x₀ y₀ := by
  simp only [Phi, polar_smul_left, smul_eq_mul]; ring

theorem phi_swap (g : Matrix (Fin d) (Fin d) K) (μ : K) (x y x₀ y₀ : Fin d → K) :
    Phi Q g μ y x x₀ y₀ = - Phi Q g μ x y x₀ y₀ := by
  simp only [Phi]; ring

end Basic

section Hyp

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)

theorem HypCoord.polar_single_single {a : Fin d} (ha : a ∈ S.hyp) (b : Fin d) :
    polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) = if S.star a = b then 1 else 0 := by
  rw [S.polar_single a ha, Pi.single_apply]

theorem HypCoord.polar_single_right {a : Fin d} (ha : a ∈ S.hyp) (x : Fin d → K) :
    polar Q x (Pi.single a 1) = x (S.star a) := by
  rw [polar_comm, S.polar_single a ha]

theorem HypCoord.star_injective {a b : Fin d} (ha : a ∈ S.hyp) (hb : b ∈ S.hyp)
    (h : S.star a = S.star b) : a = b := by
  rw [← S.star_star a ha, h, S.star_star b hb]

inductive IsBasicT (S : HypCoord Q) : (Fin d → K) → (Fin d → K) → Prop
  | single {a b : Fin d} : a ∈ S.hyp → b ∈ S.hyp → b ≠ S.star a →
      IsBasicT S (Pi.single a 1) (Pi.single b 1)
  | plane {a j : Fin d} : a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a →
      IsBasicT S ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
        (Pi.single j 1 - Pi.single (S.star a) 1)
  | tail1 {a j t : Fin d} : a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a → t ∉ S.hyp →
      IsBasicT S (Pi.single a 1)
        ((Pi.single j 1 : Fin d → K) + Pi.single t 1 - Q (Pi.single t 1) • Pi.single (S.star j) 1)

theorem HypCoord.Q_tail {j : Fin d} (hj : j ∈ S.hyp) {w : Fin d → K} (hw1 : w (S.star j) = 0)
    (hw2 : w j = 0) :
    Q ((Pi.single j 1 : Fin d → K) + w - Q w • Pi.single (S.star j) 1) = 0 := by
  have hjs := S.star_mem j hj
  have e1 : (Pi.single j 1 : Fin d → K) + w - Q w • Pi.single (S.star j) 1 =
      ((Pi.single j 1 : Fin d → K) + w) + (-(Q w)) • Pi.single (S.star j) 1 := by module
  have p1 : polar Q (Pi.single j 1 : Fin d → K) w = 0 := by rw [S.polar_single j hj, hw1]
  have p2 : polar Q (Pi.single j 1 : Fin d → K) (Pi.single (S.star j) 1) = 1 := by
    rw [S.polar_single_single hj]; simp
  have p3 : polar Q w (Pi.single (S.star j) 1) = 0 := by
    rw [S.polar_single_right hjs, S.star_star j hj, hw2]
  rw [e1, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul, S.Q_single j hj,
    S.Q_single _ hjs]
  simp only [polar_add_left, polar_smul_right, smul_eq_mul, p1, p2, p3]
  ring

theorem IsBasicT.isTS {S : HypCoord Q} {x y : Fin d → K} (h : IsBasicT S x y) : IsTS Q x y := by
  cases h with
  | single ha hb hbs =>
    rename_i a b
    refine ⟨S.Q_single a ha, S.Q_single b hb, ?_⟩
    rw [S.polar_single_single ha]
    simp [Ne.symm hbs]
  | plane ha hj hja hjs =>
    rename_i a j
    have has := S.star_mem a ha
    have hjst := S.star_mem j hj
    have hne : S.star j ≠ S.star a := fun h => hja (S.star_injective hj ha h)
    have h1 : polar Q (Pi.single a 1 : Fin d → K) (Pi.single (S.star j) 1) = 0 := by
      rw [S.polar_single_single ha]; simp [Ne.symm hne]
    have h2 : polar Q (Pi.single j 1 : Fin d → K) (Pi.single (S.star a) 1) = 0 := by
      rw [S.polar_single_single hj]; simp [hne]
    refine ⟨?_, ?_, ?_⟩
    · rw [QuadraticMap.map_add Q, S.Q_single a ha, S.Q_single _ hjst, h1]; ring
    · rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, S.Q_single j hj,
        S.Q_single _ has, polar_neg_right, h2]; ring
    · simp only [polar_add_left, polar_sub_right, S.polar_single_single ha,
        S.polar_single_single hjst, S.star_star j hj]
      by_cases h : S.star a = j
      · simp [h]
      · simp [h, Ne.symm h]
  | tail1 ha hj hja hjs ht =>
    rename_i a j t
    have hw1 : (Pi.single t 1 : Fin d → K) (S.star j) = 0 := by
      have : S.star j ≠ t := fun h => ht (h ▸ S.star_mem j hj)
      simp [this]
    have hw2 : (Pi.single t 1 : Fin d → K) j = 0 := by
      have : j ≠ t := fun h => ht (h ▸ hj)
      simp [this]
    refine ⟨S.Q_single a ha, S.Q_tail hj hw1 hw2, ?_⟩
    rw [S.polar_single a ha]
    have has : S.star a ≠ t := fun h => ht (h ▸ S.star_mem a ha)
    have hsj : S.star a ≠ S.star j := fun h => hja (S.star_injective hj ha h.symm)
    simp [has, hsj, Ne.symm hjs]

theorem IsBasicT.isRat (k : Subfield K) (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    {S : HypCoord Q} {x y : Fin d → K} (h : IsBasicT S x y) : IsRat k x ∧ IsRat k y := by
  cases h with
  | single => exact ⟨isRat_single k _, isRat_single k _⟩
  | plane =>
    exact ⟨(isRat_single k _).add (isRat_single k _), (isRat_single k _).sub (isRat_single k _)⟩
  | tail1 =>
    rename_i a j t _ _ _ _ _
    exact ⟨isRat_single k _, ((isRat_single k _).add (isRat_single k _)).sub
      (fun i => k.mul_mem (hQk t) (isRat_single k _ i))⟩

end Hyp

section Chain

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K} {g : Matrix (Fin d) (Fin d) K} {μ : K}

theorem HypCoord.exists_three_T {a : Fin d} (_ha : a ∈ S.hyp) :
    ∃ j l : Fin d, j ∈ S.hyp ∧ l ∈ S.hyp ∧ j ≠ a ∧ j ≠ S.star a ∧ l ≠ a ∧ l ≠ S.star a ∧ l ≠ j ∧
      l ≠ S.star j := by
  classical
  obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, S.star a} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_two (by have := S.card_hyp; omega))
  obtain ⟨l, hl, hl'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, S.star a, j, S.star j} : Finset (Fin d))) (t := S.hyp)
    (lt_of_le_of_lt Finset.card_le_four (by have := S.card_hyp; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj' hl'
  exact ⟨j, l, hj, hl, hj'.1, hj'.2, hl'.1, hl'.2.1, hl'.2.2.1, hl'.2.2.2⟩

theorem HypCoord.phi_row_identity_T (g : Matrix (Fin d) (Fin d) K) (μ : K) {a j : Fin d}
    (ha : a ∈ S.hyp) (hj : j ∈ S.hyp) (x₀ y₀ : Fin d → K) :
    Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ +
        Phi Q g μ (Pi.single j 1) (Pi.single (S.star j) 1) x₀ y₀ =
      Phi Q g μ (Pi.single a 1) (Pi.single j 1) x₀ y₀ -
        Phi Q g μ (Pi.single (S.star j) 1) (Pi.single (S.star a) 1) x₀ y₀ -
        Phi Q g μ ((Pi.single a 1 : Fin d → K) + Pi.single (S.star j) 1)
          (Pi.single j 1 - Pi.single (S.star a) 1) x₀ y₀ := by
  have has := S.star_mem a ha
  have hjs := S.star_mem j hj
  simp only [Phi, polar_add_left, polar_sub_left, S.polar_single a ha, S.polar_single j hj,
    S.polar_single _ has, S.polar_single _ hjs, S.star_star a ha, S.star_star j hj]
  ring

theorem HypCoord.phi_dual_row_T (h2 : (2 : K) ≠ 0) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k) {a : Fin d}
    (ha : a ∈ S.hyp) : Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ ∈ k := by
  obtain ⟨j, l, hj, hl, hja, hjs, hla, hls, hlj, hljs⟩ := S.exists_three_T ha
  have pair : ∀ a j : Fin d, a ∈ S.hyp → j ∈ S.hyp → j ≠ a → j ≠ S.star a →
      Phi Q g μ (Pi.single a 1) (Pi.single (S.star a) 1) x₀ y₀ +
        Phi Q g μ (Pi.single j 1) (Pi.single (S.star j) 1) x₀ y₀ ∈ k := by
    intro a j ha hj hja hjs
    rw [S.phi_row_identity_T g μ ha hj]
    refine k.sub_mem (k.sub_mem (hcol _ _ (IsBasicT.single ha hj hjs))
      (hcol _ _ (IsBasicT.single (S.star_mem j hj) (S.star_mem a ha) ?_)))
      (hcol _ _ (IsBasicT.plane ha hj hja hjs))
    rw [S.star_star j hj]
    exact Ne.symm hjs
  exact half_trick h2 (pair a j ha hj hja hjs) (pair a l ha hl hla hls) (pair j l hj hl hlj hljs)

theorem HypCoord.phi_hyp_tail (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k) {x₀ y₀ : Fin d → K}
    (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k)
    (hHH : ∀ a b, a ∈ S.hyp → b ∈ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single b 1) x₀ y₀ ∈ k)
    {a t : Fin d} (ha : a ∈ S.hyp) (ht : t ∉ S.hyp) :
    Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ ∈ k := by
  obtain ⟨j, -, hj, -, hja, hjs, -, -, -, -⟩ := S.exists_three_T ha
  have h1 := hcol _ _ (IsBasicT.tail1 ha hj hja hjs ht)
  have h2 : Phi Q g μ (Pi.single a 1) ((Pi.single j 1 : Fin d → K) + Pi.single t 1 -
        Q (Pi.single t 1) • Pi.single (S.star j) 1) x₀ y₀ =
      Phi Q g μ (Pi.single a 1) (Pi.single j 1) x₀ y₀ +
        Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ -
        Q (Pi.single t 1) * Phi Q g μ (Pi.single a 1) (Pi.single (S.star j) 1) x₀ y₀ := by
    rw [phi_sub_snd, phi_add_snd, phi_smul_snd]
  have h3 : Phi Q g μ (Pi.single a 1) (Pi.single t 1) x₀ y₀ =
      Phi Q g μ (Pi.single a 1) ((Pi.single j 1 : Fin d → K) + Pi.single t 1 -
        Q (Pi.single t 1) • Pi.single (S.star j) 1) x₀ y₀ -
        Phi Q g μ (Pi.single a 1) (Pi.single j 1) x₀ y₀ +
        Q (Pi.single t 1) * Phi Q g μ (Pi.single a 1) (Pi.single (S.star j) 1) x₀ y₀ := by
    rw [h2]; ring
  rw [h3]
  exact k.add_mem (k.sub_mem h1 (hHH a j ha hj))
    (k.mul_mem (hQk t) (hHH a (S.star j) ha (S.star_mem j hj)))

theorem HypCoord.phi_row_ext (h2 : (2 : K) ≠ 0) (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    {x₀ y₀ : Fin d → K} (hcol : ∀ x y : Fin d → K, IsBasicT S x y → Phi Q g μ x y x₀ y₀ ∈ k)
    {r s : Fin d} (hrs : r ∈ S.hyp ∨ s ∈ S.hyp) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := by
  have hHH : ∀ a b, a ∈ S.hyp → b ∈ S.hyp →
      Phi Q g μ (Pi.single a 1) (Pi.single b 1) x₀ y₀ ∈ k := by
    intro a b ha hb
    by_cases hbs : b = S.star a
    · subst hbs
      exact S.phi_dual_row_T h2 hcol ha
    · exact hcol _ _ (IsBasicT.single ha hb hbs)
  rcases hrs with hr | hs
  · by_cases hs : s ∈ S.hyp
    · exact hHH r s hr hs
    · exact S.phi_hyp_tail hQk hcol hHH hr hs
  · by_cases hr : r ∈ S.hyp
    · exact hHH r s hr hs
    · have : Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ =
          -Phi Q g μ (Pi.single s 1) (Pi.single r 1) x₀ y₀ :=
        phi_swap g μ (Pi.single s 1) (Pi.single r 1) x₀ y₀
      rw [this]
      exact k.neg_mem (S.phi_hyp_tail hQk hcol hHH hs hr)

end Chain

section Symm

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem polar_mulVec_sim {g : Matrix (Fin d) (Fin d) K} {μ : K}
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (a b : Fin d → K) :
    polar Q (g *ᵥ a) (g *ᵥ b) = μ * polar Q a b := by
  unfold QuadraticMap.polar
  rw [← Matrix.mulVec_add, hg, hg, hg]
  ring

theorem phi_symm {g : Matrix (Fin d) (Fin d) K} {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (hdet : IsUnit g.det) (x y x₀ y₀ : Fin d → K) :
    Phi Q g μ x y x₀ y₀ = Phi Q g⁻¹ μ⁻¹ x₀ y₀ x y := by
  have hinv : ∀ v, g *ᵥ (g⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet, Matrix.one_mulVec]
  have hp : ∀ (x z : Fin d → K), polar Q x (g *ᵥ z) = μ * polar Q z (g⁻¹ *ᵥ x) := fun x z => by
    conv_lhs => rw [← hinv x]
    rw [polar_mulVec_sim hg, polar_comm]
  simp only [Phi, hp]
  field_simp

end Symm

section Coord

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K}

@[expose] def TailPairs (S : HypCoord Q) (k : Subfield K) : Prop :=
  ∀ (g' : Matrix (Fin d) (Fin d) K) (μ' : K) (x₀ y₀ : Fin d → K),
    (∀ x y : Fin d → K, IsBasicT S x y → Phi Q g' μ' x y x₀ y₀ ∈ k) →
      ∀ t t' : Fin d, t ∉ S.hyp → t' ∉ S.hyp →
        Phi Q g' μ' (Pi.single t 1) (Pi.single t' 1) x₀ y₀ ∈ k

include S in
theorem HypCoord.phi_coord_mem_T (h2 : (2 : K) ≠ 0) (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hTT : TailPairs S k) {g : Matrix (Fin d) (Fin d) K} {μ : K} (hμ : μ ≠ 0)
    (hg : ∀ v, Q (g *ᵥ v) = μ * Q v) (hdet : IsUnit g.det)
    (hP : ∀ x y x₀ y₀ : Fin d → K, IsBasicT S x y → IsBasicT S x₀ y₀ →
      Phi Q g μ x y x₀ y₀ ∈ k) (r s c c' : Fin d) :
    Phi Q g μ (Pi.single r 1) (Pi.single s 1) (Pi.single c 1) (Pi.single c' 1) ∈ k := by
  have full : ∀ (g' : Matrix (Fin d) (Fin d) K) (μ' : K) (x₀ y₀ : Fin d → K),
      (∀ x y : Fin d → K, IsBasicT S x y → Phi Q g' μ' x y x₀ y₀ ∈ k) →
      ∀ r s : Fin d, Phi Q g' μ' (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := by
    intro g' μ' x₀ y₀ hcol r s
    by_cases hrs : r ∈ S.hyp ∨ s ∈ S.hyp
    · exact S.phi_row_ext h2 hQk hcol hrs
    · push Not at hrs
      exact hTT g' μ' x₀ y₀ hcol r s hrs.1 hrs.2
  have stepA : ∀ x₀ y₀ : Fin d → K, IsBasicT S x₀ y₀ → ∀ r s : Fin d,
      Phi Q g μ (Pi.single r 1) (Pi.single s 1) x₀ y₀ ∈ k := fun x₀ y₀ hb r s =>
    full g μ x₀ y₀ (fun x y hxy => hP x y x₀ y₀ hxy hb) r s
  rw [phi_symm hμ hg hdet]
  refine full g⁻¹ μ⁻¹ (Pi.single r 1) (Pi.single s 1) (fun x y hxy => ?_) c c'
  rw [← phi_symm hμ hg hdet]
  exact stepA x y hxy r s

end Coord

section Rational

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (S : HypCoord Q)
  {k : Subfield K}

@[expose] def gramMat (Q : QuadraticForm K (Fin d → K)) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun r c => polar Q (Pi.single r 1) (Pi.single c 1)

theorem polar_expand_left (w v : Fin d → K) :
    polar Q w v = ∑ r, w r * polar Q (Pi.single r 1 : Fin d → K) v := by
  have hw : w = ∑ r, w r • (Pi.single r 1 : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [← polarBilin_apply_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul]

theorem polar_expand_right (v w : Fin d → K) :
    polar Q v w = ∑ c, w c * polar Q v (Pi.single c 1 : Fin d → K) := by
  have hw : w = ∑ c, w c • (Pi.single c 1 : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  rw [← polarBilin_apply_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, polarBilin_apply_apply, smul_eq_mul]

theorem gramMat_mulVec (v : Fin d → K) (r : Fin d) :
    (gramMat Q *ᵥ v) r = polar Q (Pi.single r 1) v := by
  rw [polar_expand_right]
  simp only [Matrix.mulVec, dotProduct, gramMat, Matrix.of_apply]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem gramMat_det_ne (hnd : (polarBilin Q).Nondegenerate) : (gramMat Q).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv0
  refine hnd.2 v fun w => ?_
  rw [polarBilin_apply_apply, polar_expand_left]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [← gramMat_mulVec, hv]
  simp

include S in
theorem HypCoord.rational_of_pairs_T (h2 : (2 : K) ≠ 0)
    (hQk : ∀ a, Q (Pi.single a 1 : Fin d → K) ∈ k)
    (hPk : ∀ a b, polar Q (Pi.single a 1 : Fin d → K) (Pi.single b 1) ∈ k) (hTT : TailPairs S k)
    (hnd : (polarBilin Q).Nondegenerate) {σ : K →+* K} (hσ : ∀ x, σ x = x ↔ x ∈ k)
    {g : Matrix (Fin d) (Fin d) K} {μ : K} (hμ : μ ≠ 0) (hg : ∀ v, Q (g *ᵥ v) = μ * Q v)
    (hdet : g.det ≠ 0)
    (hP : ∀ x y x₀ y₀ : Fin d → K, IsBasicT S x y → IsBasicT S x₀ y₀ →
      Phi Q g μ x y x₀ y₀ ∈ k) :
    ∃ a : K, a ≠ 0 ∧ ∀ r c, σ (g r c) = a * g r c := by
  set G := gramMat Q with hGdef
  have hGdet : G.det ≠ 0 := gramMat_det_ne hnd
  have hG' : ∀ r c, (G * g) r c = polar Q (Pi.single r 1) (g *ᵥ Pi.single c 1) := by
    intro r c
    rw [← gramMat_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hdetG' : (G * g).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hGdet hdet
  have hmin : ∀ r s c c', μ⁻¹ * ((G * g) r c * (G * g) s c' - (G * g) r c' * (G * g) s c) ∈ k := by
    intro r s c c'
    have h := S.phi_coord_mem_T h2 hQk hTT hμ hg (isUnit_iff_ne_zero.mpr hdet) hP r s c c'
    simp only [Phi] at h
    simpa only [hG'] using h
  have hcard : 3 ≤ Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    have h1 := S.card_hyp
    have h2' := S.hyp.card_le_univ
    rw [Fintype.card_fin] at h2'
    omega
  obtain ⟨a, ha, heig⟩ := rational_of_minors hcard hσ hμ hdetG' hmin
  refine ⟨a, ha, fun r c => ?_⟩
  have hGfix : ∀ r e, σ (G r e) = G r e := fun r e => (hσ _).mpr (hPk r e)
  have key : ∀ c, G *ᵥ (fun e => σ (g e c) - a * g e c) = 0 := by
    intro c
    funext r
    have h1 := heig r c
    rw [Matrix.mul_apply, map_sum] at h1
    simp only [map_mul, hGfix] at h1
    show ∑ e, G r e * (σ (g e c) - a * g e c) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [h1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun e _ => by ring
  have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hGdet (key c)) r
  exact sub_eq_zero.mp this

end Rational

end RootPairOrth

end CFSG.LieType.SeitzGeneration
