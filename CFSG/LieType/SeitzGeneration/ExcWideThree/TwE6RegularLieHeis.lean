module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLieFrame

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

section Abstract

open scoped commutatorElement

theorem mul_pow_of_commute_commutator {G : Type*} [Group G] {A B : G}
    (hA : Commute ⁅A, B⁆ A) (hB : Commute ⁅A, B⁆ B) (n : ℕ) :
    (A * B) ^ n = A ^ n * B ^ n * (⁅A, B⁆⁻¹) ^ (n.choose 2) := by
  obtain ⟨D, hD⟩ : ∃ D : G, D = ⁅A, B⁆⁻¹ := ⟨_, rfl⟩
  rw [← hD]
  have hDA : Commute D A := by rw [hD]; exact hA.inv_left
  have hDB : Commute D B := by rw [hD]; exact hB.inv_left
  have hBA : B * A = D * A * B := by
    rw [hD, commutatorElement_def]
    group
  have hDnA : ∀ k : ℕ, D ^ k * A = A * D ^ k := fun k => (hDA.pow_left k).eq
  have hDnB : ∀ k : ℕ, D ^ k * B = B * D ^ k := fun k => (hDB.pow_left k).eq
  have hDnBi : ∀ k i : ℕ, D ^ k * B ^ i = B ^ i * D ^ k := fun k i => (hDB.pow_pow k i).eq
  have hBnA : ∀ k : ℕ, B ^ k * A = D ^ k * A * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc B ^ (k + 1) * A = B * (B ^ k * A) := by rw [pow_succ']; group
        _ = B * (D ^ k * A * B ^ k) := by rw [ih]
        _ = (B * D ^ k) * A * B ^ k := by group
        _ = (D ^ k * B) * A * B ^ k := by rw [← hDnB k]
        _ = D ^ k * (B * A) * B ^ k := by group
        _ = D ^ k * (D * A * B) * B ^ k := by rw [hBA]
        _ = D ^ (k + 1) * A * B ^ (k + 1) := by group
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [hc]
    calc (A * B) ^ (n + 1) = (A * B) ^ n * (A * B) := by rw [pow_succ]
      _ = A ^ n * B ^ n * D ^ n.choose 2 * (A * B) := by rw [ih]
      _ = A ^ n * B ^ n * ((D ^ n.choose 2 * A) * B) := by group
      _ = A ^ n * B ^ n * ((A * D ^ n.choose 2) * B) := by rw [hDnA]
      _ = A ^ n * B ^ n * (A * (D ^ n.choose 2 * B)) := by group
      _ = A ^ n * B ^ n * (A * (B * D ^ n.choose 2)) := by rw [hDnB]
      _ = A ^ n * (B ^ n * A) * B * D ^ n.choose 2 := by group
      _ = A ^ n * (D ^ n * A * B ^ n) * B * D ^ n.choose 2 := by rw [hBnA n]
      _ = A ^ n * (D ^ n * A) * (B ^ n * B) * D ^ n.choose 2 := by group
      _ = A ^ n * (A * D ^ n) * (B ^ n * B) * D ^ n.choose 2 := by rw [hDnA n]
      _ = A ^ (n + 1) * (D ^ n * B ^ (n + 1)) * D ^ n.choose 2 := by group
      _ = A ^ (n + 1) * (B ^ (n + 1) * D ^ n) * D ^ n.choose 2 := by rw [hDnBi n (n + 1)]
      _ = A ^ (n + 1) * B ^ (n + 1) * D ^ (n + n.choose 2) := by group

end Abstract

section Heis

open scoped commutatorElement

variable {G : Type*} [Group G] {L : Type*} [Field L]

theorem family_zero {X : L → G} (h : ∀ c d, X (c + d) = X c * X d) : X 0 = 1 := by
  have h2 : X 0 * X 0 = X 0 * 1 := by rw [mul_one, ← h, add_zero]
  exact mul_left_cancel h2

theorem family_inv {X : L → G} (h : ∀ c d, X (c + d) = X c * X d) (c : L) :
    (X c)⁻¹ = X (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← h, add_neg_cancel, family_zero h]

theorem family_pow {X : L → G} (h : ∀ c d, X (c + d) = X c * X d) (c : L) (n : ℕ) :
    X c ^ n = X ((n : L) * c) := by
  induction n with
  | zero => simp [family_zero h]
  | succ n ih => rw [pow_succ, ih, ← h]; congr 1; push_cast; ring

theorem family_comm {X : L → G} (h : ∀ c d, X (c + d) = X c * X d) (c d : L) :
    X c * X d = X d * X c := by
  rw [← h, ← h, add_comm]

theorem exists_fixed_heis [IsAlgClosed L] (X₁ X₂ X₃ : L → G)
    (h₁ : ∀ c d, X₁ (c + d) = X₁ c * X₁ d) (h₂ : ∀ c d, X₂ (c + d) = X₂ c * X₂ d)
    (h₃ : ∀ c d, X₃ (c + d) = X₃ c * X₃ d)
    (hc₁₃ : ∀ c d, Commute (X₁ c) (X₃ d)) (hc₂₃ : ∀ c d, Commute (X₂ c) (X₃ d))
    (N : L) (hcom : ∀ c d, ⁅X₁ c, X₂ d⁆ = X₃ (N * c * d))
    (ψ : G →* G) (q : ℕ) (hq : 2 ≤ q) (a₁ a₂ a₃ : L) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (ha₃ : a₃ ≠ 0) (hψ₁ : ∀ c, ψ (X₁ c) = X₂ (a₁ * c ^ q))
    (hψ₂ : ∀ c, ψ (X₂ c) = X₁ (a₂ * c ^ q)) (hψ₃ : ∀ c, ψ (X₃ c) = X₃ (a₃ * c ^ q)) :
    ∃ s t u : L, s ≠ 0 ∧ ψ (X₁ s * X₂ t * X₃ u) = X₁ s * X₂ t * X₃ u := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have hn : 0 < q ^ 2 - 1 := by omega
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (a₂ * a₁ ^ q)⁻¹ hn
  have hne : a₂ * a₁ ^ q ≠ 0 := mul_ne_zero ha₂ (pow_ne_zero _ ha₁)
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne'] at hs
    exact (inv_ne_zero hne) hs.symm
  obtain ⟨t, ht⟩ : ∃ t : L, t = a₁ * s ^ q := ⟨_, rfl⟩
  have hst : a₂ * t ^ q = s := by
    have e1 : t ^ q = a₁ ^ q * s ^ (q ^ 2) := by
      rw [ht, mul_pow, ← pow_mul, sq]
    have e2 : s ^ (q ^ 2) = s ^ (q ^ 2 - 1) * s := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e1, e2, hs]
    field_simp
  obtain ⟨u, hu⟩ : ∃ u : L, a₃ * u ^ q - u - N * s * t = 0 := by
    have hdeg : (Polynomial.C a₃ * Polynomial.X ^ q -
        (Polynomial.X + Polynomial.C (N * s * t))).degree ≠ 0 := by
      have h1 : (Polynomial.X + Polynomial.C (N * s * t)).degree = 1 :=
        Polynomial.degree_X_add_C _
      have h2 : (Polynomial.C a₃ * Polynomial.X ^ q).degree = (q : WithBot ℕ) :=
        Polynomial.degree_C_mul_X_pow q ha₃
      rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rw [h1, h2]; exact_mod_cast hq), h2]
      exact_mod_cast (by omega : q ≠ 0)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨u, ?_⟩
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add] at hu
    linear_combination hu
  refine ⟨s, t, u, hs0, ?_⟩
  have hswap : X₂ t * X₁ s = X₃ (-(N * s * t)) * (X₁ s * X₂ t) := by
    have e : X₁ s * X₂ t = X₃ (N * s * t) * (X₂ t * X₁ s) := by
      have := hcom s t
      rw [commutatorElement_def] at this
      rw [← this]
      group
    rw [← family_inv h₃, e]
    group
  have hcent : ∀ c, X₃ c * (X₁ s * X₂ t) = (X₁ s * X₂ t) * X₃ c := fun c =>
    ((hc₁₃ s c).mul_left (hc₂₃ t c)).symm.eq
  calc ψ (X₁ s * X₂ t * X₃ u) = ψ (X₁ s) * ψ (X₂ t) * ψ (X₃ u) := by simp only [map_mul]
    _ = X₂ (a₁ * s ^ q) * X₁ (a₂ * t ^ q) * X₃ (a₃ * u ^ q) := by rw [hψ₁, hψ₂, hψ₃]
    _ = X₂ t * X₁ s * X₃ (a₃ * u ^ q) := by rw [← ht, hst]
    _ = X₃ (-(N * s * t)) * (X₁ s * X₂ t) * X₃ (a₃ * u ^ q) := by rw [hswap]
    _ = X₁ s * X₂ t * (X₃ (-(N * s * t)) * X₃ (a₃ * u ^ q)) := by rw [hcent]; group
    _ = X₁ s * X₂ t * X₃ (-(N * s * t) + a₃ * u ^ q) := by rw [← h₃]
    _ = X₁ s * X₂ t * X₃ u := by
      congr 2
      linear_combination hu

theorem heis_not_mem_range (X₁ X₂ X₃ : L → G)
    (h₂ : ∀ c d, X₂ (c + d) = X₂ c * X₂ d) (h₃ : ∀ c d, X₃ (c + d) = X₃ c * X₃ d)
    (hc₂₃ : ∀ c d, Commute (X₂ c) (X₃ d)) (hX₃inj : Function.Injective X₃)
    (N : L) (hN : N ≠ 0) (hcom : ∀ c d, ⁅X₁ c, X₂ d⁆ = X₃ (N * c * d)) {s t u : L} (hs : s ≠ 0) :
    ¬ ∃ e, X₃ e = X₁ s * X₂ t * X₃ u := by
  rintro ⟨e, he⟩
  obtain ⟨y, hy⟩ : ∃ y, y = X₁ s * X₂ t * X₃ u := ⟨_, rfl⟩
  rw [← hy] at he
  have hyc : y * X₂ 1 = X₂ 1 * y := by rw [← he]; exact (hc₂₃ 1 e).symm.eq
  have hA : X₁ s * X₂ 1 = X₃ (N * s * 1) * (X₂ 1 * X₁ s) := by
    have := hcom s 1
    rw [commutatorElement_def] at this
    rw [← this]
    group
  have h3 : X₃ u * X₂ 1 = X₂ 1 * X₃ u := (hc₂₃ 1 u).symm.eq
  have hyX : y * X₂ 1 = X₃ (N * s * 1) * (X₂ 1 * y) := by
    calc y * X₂ 1 = X₁ s * X₂ t * (X₃ u * X₂ 1) := by rw [hy]; group
      _ = X₁ s * X₂ t * (X₂ 1 * X₃ u) := by rw [h3]
      _ = X₁ s * (X₂ t * X₂ 1) * X₃ u := by group
      _ = X₁ s * (X₂ 1 * X₂ t) * X₃ u := by rw [family_comm h₂ t 1]
      _ = (X₁ s * X₂ 1) * X₂ t * X₃ u := by group
      _ = X₃ (N * s * 1) * (X₂ 1 * X₁ s) * X₂ t * X₃ u := by rw [hA]
      _ = X₃ (N * s * 1) * (X₂ 1 * y) := by rw [hy]; group
  have h4 : X₃ (N * s * 1) * (X₂ 1 * y) = 1 * (X₂ 1 * y) := by
    rw [← hyX, hyc, one_mul]
  have h5 : X₃ (N * s * 1) = X₃ 0 := by
    rw [family_zero h₃]
    exact mul_right_cancel h4
  have h6 := hX₃inj h5
  exact mul_ne_zero hN hs (by simpa using h6)

end Heis

section E6

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement


theorem heis_root_facts {δ₁ δ₂ : Fin TwistTag.E6.tag.rank → ℤ} (h₁ : IsRoot TwistTag.E6.tag δ₁)
    (h₂ : IsRoot TwistTag.E6.tag δ₂) (h₁₂ : IsRoot TwistTag.E6.tag (δ₁ + δ₂)) :
    δ₁ ≠ δ₂ ∧ δ₁ ≠ -δ₂ ∧ δ₁ ≠ δ₁ + δ₂ ∧ δ₁ ≠ -(δ₁ + δ₂) ∧ δ₂ ≠ δ₁ + δ₂ ∧
      δ₂ ≠ -(δ₁ + δ₂) ∧ ¬ IsRoot TwistTag.E6.tag (δ₁ + (δ₁ + δ₂)) ∧
      ¬ IsRoot TwistTag.E6.tag (δ₂ + (δ₁ + δ₂)) := by
  have hsl : TwistTag.E6.tag = Tag.D4 ∨ TwistTag.E6.tag = Tag.E6 ∨ TwistTag.E6.tag = Tag.E7 ∨
      TwistTag.E6.tag = Tag.E8 := Or.inr (Or.inl rfl)
  have e1 := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
    hsl h₁
  have e2 := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
    hsl h₂
  have eθ := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
    hsl h₁₂
  have e12 := iform_eq_neg_one_of_isRoot_add h₁ h₂ h₁₂
  have e21 : iform δ₂ δ₁ = -1 := by rw [iform_comm]; exact e12
  have p1 : iform δ₁ (δ₁ + δ₂) = 1 := by rw [iform_add_right, e1, e12]; norm_num
  have p2 : iform δ₂ (δ₁ + δ₂) = 1 := by rw [iform_add_right, e21, e2]; norm_num
  have p1' : iform (δ₁ + δ₂) δ₁ = 1 := by rw [iform_comm]; exact p1
  have p2' : iform (δ₁ + δ₂) δ₂ = 1 := by rw [iform_comm]; exact p2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at e12
    omega
  · intro h
    rw [h, iform_neg_left] at e12
    omega
  · intro h
    rw [← h] at p1
    omega
  · intro h
    have := congrArg (fun x => iform x (δ₁ + δ₂)) h
    simp only [iform_neg_left] at this
    omega
  · intro h
    rw [← h] at p2
    omega
  · intro h
    have := congrArg (fun x => iform x (δ₁ + δ₂)) h
    simp only [iform_neg_left] at this
    omega
  · intro hr
    have := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
      hsl hr
    simp only [iform_add_left, iform_add_right] at this
    omega
  · intro hr
    have := CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two (τ := TwistTag.E6.tag)
      hsl hr
    simp only [iform_add_left, iform_add_right] at this
    omega

theorem exists_fixed_rootSpan_heis {L : Type} [Field L] [IsAlgClosed L] (p f : ℕ) [Fact p.Prime]
    [CharP L p] (hf : 1 ≤ f) {δ₁ δ₂ : Fin TwistTag.E6.tag.rank → ℤ}
    (h₁ : IsRoot TwistTag.E6.tag δ₁) (h₂ : IsRoot TwistTag.E6.tag δ₂)
    (h₁₂ : IsRoot TwistTag.E6.tag (δ₁ + δ₂))
    (ψ : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L) (a₁ a₂ a₃ : L) (ha₁ : a₁ ≠ 0)
    (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hψ₁ : ∀ c, ψ (pinnedX TwistTag.E6.tag L δ₁ c) =
      pinnedX TwistTag.E6.tag L δ₂ (a₁ * c ^ (p ^ f)))
    (hψ₂ : ∀ c, ψ (pinnedX TwistTag.E6.tag L δ₂ c) =
      pinnedX TwistTag.E6.tag L δ₁ (a₂ * c ^ (p ^ f)))
    (hψ₃ : ∀ c, ψ (pinnedX TwistTag.E6.tag L (δ₁ + δ₂) c) =
      pinnedX TwistTag.E6.tag L (δ₁ + δ₂) (a₃ * c ^ (p ^ f))) :
    ∃ y : ModGL TwistTag.E6.tag L,
      y ∈ rootSpan TwistTag.E6.tag L {δ₁, δ₂, δ₁ + δ₂} ∧ ψ y = y ∧ y ^ (p ^ 2) = 1 ∧
        y ∉ rootSubgroup TwistTag.E6.tag L (δ₁ + δ₂) := by
  obtain ⟨hne12, hne12', hne1θ, hne1θ', hne2θ, hne2θ', hnr1, hnr2⟩ := heis_root_facts h₁ h₂ h₁₂
  have hsl : TwistTag.E6.tag = Tag.D4 ∨ TwistTag.E6.tag = Tag.E6 ∨ TwistTag.E6.tag = Tag.E7 ∨
      TwistTag.E6.tag = Tag.E8 := Or.inr (Or.inl rfl)
  have hp := (Fact.out : p.Prime)
  have hpL : (p : L) = 0 := CharP.cast_eq_zero L p
  have hq : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨hNc, hcomm⟩ := (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag hsl h₁ h₂ hne12
    hne12').1 h₁₂
  have hcomm13 : ∀ c d : L, Commute (pinnedX TwistTag.E6.tag L δ₁ c)
      (pinnedX TwistTag.E6.tag L (δ₁ + δ₂) d) := fun c d =>
    ((simply_laced_root_commutator_unit.{0} TwistTag.E6.tag hsl h₁ h₁₂ hne1θ hne1θ').2 hnr1 L _
      (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩))
  have hcomm23 : ∀ c d : L, Commute (pinnedX TwistTag.E6.tag L δ₂ c)
      (pinnedX TwistTag.E6.tag L (δ₁ + δ₂) d) := fun c d =>
    ((simply_laced_root_commutator_unit.{0} TwistTag.E6.tag hsl h₂ h₁₂ hne2θ hne2θ').2 hnr2 L _
      (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩))
  obtain ⟨N, hN⟩ : ∃ N : L, N = ((commConst TwistTag.E6.tag δ₁ δ₂ (1, 1) : ℤ) : L) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    rcases hNc with h | h <;> rw [h] <;> simp
  have hcomN : ∀ c d : L, ⁅pinnedX TwistTag.E6.tag L δ₁ c, pinnedX TwistTag.E6.tag L δ₂ d⁆ =
      pinnedX TwistTag.E6.tag L (δ₁ + δ₂) (N * c * d) := fun c d => by
    rw [hcomm L c d, hN]
  have hadd : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, ∀ c d : L,
      pinnedX TwistTag.E6.tag L γ (c + d) =
        pinnedX TwistTag.E6.tag L γ c * pinnedX TwistTag.E6.tag L γ d :=
    fun γ c d => pinnedX_add TwistTag.E6.tag L γ c d
  obtain ⟨s, t, u, hs, hfix⟩ := exists_fixed_heis (pinnedX TwistTag.E6.tag L δ₁)
    (pinnedX TwistTag.E6.tag L δ₂) (pinnedX TwistTag.E6.tag L (δ₁ + δ₂)) (hadd δ₁) (hadd δ₂)
    (hadd (δ₁ + δ₂)) hcomm13 hcomm23 N hcomN ψ (p ^ f) hq a₁ a₂ a₃ ha₁ ha₂ ha₃ hψ₁ hψ₂ hψ₃
  refine ⟨pinnedX TwistTag.E6.tag L δ₁ s * pinnedX TwistTag.E6.tag L δ₂ t *
    pinnedX TwistTag.E6.tag L (δ₁ + δ₂) u, ?_, hfix, ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (pinnedX_mem_rootSpan ?_ s)
      (pinnedX_mem_rootSpan ?_ t)) (pinnedX_mem_rootSpan ?_ u)
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  ·
    set A := pinnedX TwistTag.E6.tag L δ₁ s with hA
    set B := pinnedX TwistTag.E6.tag L δ₂ t with hB
    set Z := pinnedX TwistTag.E6.tag L (δ₁ + δ₂) u with hZ
    have hcAB : ⁅A, B⁆ = pinnedX TwistTag.E6.tag L (δ₁ + δ₂) (N * s * t) := hcomN s t
    have hAB1 : Commute ⁅A, B⁆ A := by rw [hcAB]; exact (hcomm13 s _).symm
    have hAB2 : Commute ⁅A, B⁆ B := by rw [hcAB]; exact (hcomm23 t _).symm
    have hcZ : Commute (A * B) Z := (hcomm13 s u).mul_left (hcomm23 t u)
    have hp2 : ((p ^ 2 : ℕ) : L) = 0 := by rw [Nat.cast_pow, hpL]; norm_num
    have hA1 : A ^ (p ^ 2) = 1 := by
      rw [hA, family_pow (hadd δ₁) s, hp2, zero_mul, family_zero (hadd δ₁)]
    have hB1 : B ^ (p ^ 2) = 1 := by
      rw [hB, family_pow (hadd δ₂) t, hp2, zero_mul, family_zero (hadd δ₂)]
    have hZ1 : Z ^ (p ^ 2) = 1 := by
      rw [hZ, family_pow (hadd (δ₁ + δ₂)) u, hp2, zero_mul, family_zero (hadd (δ₁ + δ₂))]
    have hdvd : p ∣ (p ^ 2).choose 2 := by
      refine Nat.Prime.dvd_choose_pow hp two_ne_zero ?_
      intro h
      have := hp.two_le
      nlinarith
    have hchoose : (((p ^ 2).choose 2 : ℕ) : L) = 0 := (CharP.cast_eq_zero_iff L p _).2 hdvd
    have hD1 : (pinnedX TwistTag.E6.tag L (δ₁ + δ₂) (N * s * t))⁻¹ ^ (p ^ 2).choose 2 = 1 := by
      rw [family_inv (hadd (δ₁ + δ₂)), family_pow (hadd (δ₁ + δ₂)), hchoose, zero_mul,
        family_zero (hadd (δ₁ + δ₂))]
    rw [hcZ.mul_pow, mul_pow_of_commute_commutator hAB1 hAB2, hcAB, hA1, hB1, hD1, hZ1]
    simp
  · rintro hmem
    obtain ⟨e, he⟩ := mem_rootSubgroup.1 hmem
    exact heis_not_mem_range (pinnedX TwistTag.E6.tag L δ₁) (pinnedX TwistTag.E6.tag L δ₂)
      (pinnedX TwistTag.E6.tag L (δ₁ + δ₂)) (hadd δ₂) (hadd (δ₁ + δ₂)) hcomm23
      (pinnedX_injective TwistTag.E6.tag L (δ₁ + δ₂)) N hN0 hcomN hs ⟨e, he⟩

end E6



end CFSG.LieType.SeitzGeneration.ExcWideThree
