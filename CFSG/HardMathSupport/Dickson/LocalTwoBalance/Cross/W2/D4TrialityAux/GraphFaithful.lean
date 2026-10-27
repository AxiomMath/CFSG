module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4Outer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.ExtendProps
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Descent
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.NormalPi

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

section GraphFaithful


theorem graphFixedInclusion_injective (K : Type) [Field K] (σ : K ≃+* K) :
    Function.Injective (graphFixedInclusion K σ) := by
  intro y₁ y₂ h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact h'

theorem faithfulAt_graphOne {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα3 : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) ^ 3 = 1) :
    FaithfulAt 3 (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) := by
  classical
  intro Ξ hcop hΞα hfix
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨f, hf, hKf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = ringChar K ^ f := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hℓ3 : ringChar K ≠ 3 := fun h => hK3 (by rw [hKf, h]; exact dvd_pow_self 3 (by omega))
  have hKcard : Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨c, b, σ, hΞ⟩ := exists_normalAut_of_commute_graphOne g a Ξ hcop hΞα
  have hcomm : (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) *
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
        (MulAut.conj c * exactNormalAut Tag.D4 K b σ 0) := by
    rw [hΞ] at hΞα
    exact hΞα
  have hstar := star_identity hKcard g c a b σ hcomm
  obtain ⟨K₃, hF₃, hFin₃, hAlg, Fr, hK₃, hFr, ψ, φ, hψβ, hφ3, hφo, hFrψ, -, hfix2, hx4fix,
    hx4range⟩ := dual_data_one hf K hKf
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) hα3 g a rfl
  have hchar : CharP K₃ (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K K₃).injective (ringChar K)
  obtain ⟨σt, hσt, k, hσtk⟩ := exists_ringEquiv_lift (ℓ := ringChar K) (K₃ := K₃) σ
  generalize algebraMap K K₃ = ι at hσt hψβ hfix2
  have hFrι : ∀ x : K, Fr (ι x) = ι x := fun x => by
    rw [hFr, ← map_pow]
    congr 1
    have : Fintype K := Fintype.ofFinite K
    rw [← hKf, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hFrσt : ∀ y, Fr (σt y) = σt (Fr y) := fun y => by
    rw [hFr (σt y), hσtk y, hσtk (Fr y), hFr y, ← pow_mul, ← pow_mul, mul_comm]
  have hFr3 : ∀ c, Fr (Fr (Fr c)) = c := fun c => by
    have : Fintype K₃ := Fintype.ofFinite K₃
    rw [hFr, hFr, hFr, ← pow_mul, ← pow_mul,
      show ringChar K ^ f * (ringChar K ^ f * ringChar K ^ f) = (ringChar K ^ f) ^ 3 by ring,
      ← hK₃, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨Ξt₀, hΞt₀⟩ : ∃ Ξt₀ : MulAut (adjointGroup Tag.D4 K₃),
      Ξt₀ = MulAut.conj (baseChangeAdj ι c) *
        exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (b i)) σt 0 := ⟨_, rfl⟩
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : MulAut (adjointGroup Tag.D4 K₃), β₀ = MulAut.conj (baseChangeAdj ι g) *
      (exactNormalAut Tag.D4 K₃ (fun i => Units.map ι.toMonoidHom (a i)) Fr 0 *
        d4Graph K₃ 1) := ⟨_, rfl⟩
  have hN1 : Ξt₀ * β₀ = β₀ * Ξt₀ := by
    rw [hΞt₀, hβ₀]
    exact ext_commute_graph ι c g a b σ σt Fr hσt hFrι hFrσt hstar
  have hN2 : Ξt₀ * entrywiseAdjointAut Tag.D4 Fr = entrywiseAdjointAut Tag.D4 Fr * Ξt₀ := by
    rw [hΞt₀]
    exact ext_commute_entrywise ι c b σt Fr hFrι hFrσt
  have hE1 : ∀ u, Ξt₀ (baseChangeAdj ι u) = baseChangeAdj ι (Ξ u) := fun u => by
    rw [hΞt₀, hΞ]
    exact ext_apply_baseChange ι c b σ σt hσt u
  have hinjA : Function.Injective (baseChangeAdj ι) := fun u u' h =>
    Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))
  have hEn : ∀ (n : ℕ) (u : adjointGroup Tag.D4 K),
      (Ξt₀ ^ n) (baseChangeAdj ι u) = baseChangeAdj ι ((Ξ ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih, hE1]
  have hdvd : orderOf Ξ ∣ orderOf Ξt₀ := by
    refine orderOf_dvd_of_pow_eq_one (MulEquiv.ext fun u => hinjA ?_)
    rw [← hEn, pow_orderOf_eq_one]
    try rfl
  obtain ⟨m, hm1, hm3⟩ := exists_pow_coprime_three Ξt₀ (orderOf Ξ) hcop hdvd
  obtain ⟨Ξt, hΞt⟩ : ∃ Ξt : MulAut (adjointGroup Tag.D4 K₃), Ξt = Ξt₀ ^ m := ⟨_, rfl⟩
  have hΞt3 : Nat.Coprime 3 (orderOf Ξt) := hΞt ▸ hm3
  have hΞt1 : ∀ u, Ξt (baseChangeAdj ι u) = baseChangeAdj ι (Ξ u) := fun u => by
    rw [hΞt, hEn]
    have h : Ξ ^ m = Ξ ^ 1 := (pow_eq_pow_iff_modEq).2 hm1
    rw [h, pow_one]
  have hNβ : Ξt * β₀ = β₀ * Ξt := by
    rw [hΞt]
    exact Commute.pow_left (show Commute Ξt₀ β₀ from hN1) m
  have hNT : Ξt * entrywiseAdjointAut Tag.D4 Fr = entrywiseAdjointAut Tag.D4 Fr * Ξt := by
    rw [hΞt]
    exact Commute.pow_left (show Commute Ξt₀ (entrywiseAdjointAut Tag.D4 Fr) from hN2) m
  have hθ3 : Nat.Coprime 3 (orderOf (ψ * Ξt * ψ⁻¹)) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ?_) hΞt3
    rw [conj_pow, pow_orderOf_eq_one]
    group
  obtain ⟨x, hx⟩ : ∃ x : MulAut (adjointGroup Tag.D4 K₃),
      x = twistedEntrywiseAut TwistTag.D4 1 Fr := ⟨_, rfl⟩
  have hψβx : ψ * β₀ * ψ⁻¹ = x := by
    rw [hβ₀, hx]
    exact hψβ
  have hθx : (ψ * Ξt * ψ⁻¹) * x = x * (ψ * Ξt * ψ⁻¹) := by
    rw [← hψβx]
    calc ψ * Ξt * ψ⁻¹ * (ψ * β₀ * ψ⁻¹) = ψ * (Ξt * β₀) * ψ⁻¹ := by group
      _ = ψ * (β₀ * Ξt) * ψ⁻¹ := by rw [hNβ]
      _ = ψ * β₀ * ψ⁻¹ * (ψ * Ξt * ψ⁻¹) := by group
  have hθΘ : (ψ * Ξt * ψ⁻¹) * (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) =
      (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) * (ψ * Ξt * ψ⁻¹) :=
    calc ψ * Ξt * ψ⁻¹ * (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹)
        = ψ * (Ξt * entrywiseAdjointAut Tag.D4 Fr) * ψ⁻¹ := by group
      _ = ψ * (entrywiseAdjointAut Tag.D4 Fr * Ξt) * ψ⁻¹ := by rw [hNT]
      _ = ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹ * (ψ * Ξt * ψ⁻¹) := by group
  have hθ1 : ψ * Ξt * ψ⁻¹ = 1 := by
    refine faithfulAt_of_descent x
      (graphFixedInclusion K₃ Fr) (graphFixedInclusion_injective K₃ Fr)
      (fun y => by rw [hx]; exact hx4fix y)
      (fun w hw => by rw [hx] at hw; exact hx4range w hw)
      φ (ψ * entrywiseAdjointAut Tag.D4 Fr * ψ⁻¹) (fun y => (hFrψ y).symm)
      (coreFreeAt_three_D4_outer (Fact.out) hℓ3 hf hK₃ Fr hFr φ hφ3 hφo).2
      (by rw [hx]; exact faithfulAt_x4_one Fr hFr3) (ψ * Ξt * ψ⁻¹) hθ3 hθx hθΘ ?_
    intro y hy
    obtain ⟨u, hu⟩ := hfix2 y hy
    have hu' : Ξ u.1 = u.1 := hfix u.1 (mem_fixSub.2 u.2)
    have h1 : (ψ * Ξt * ψ⁻¹) (ψ (baseChangeAdj ι u.1)) = ψ (baseChangeAdj ι u.1) := by
      change ψ (Ξt (ψ⁻¹ (ψ (baseChangeAdj ι u.1)))) = _
      rw [MulAut.inv_apply_self, hΞt1, hu']
    exact (congrArg (ψ * Ξt * ψ⁻¹) hu).trans (h1.trans hu.symm)
  have hΞt1' : Ξt = 1 := by
    have h : Ξt = ψ⁻¹ * (ψ * Ξt * ψ⁻¹) * ψ := by group
    rw [h, hθ1]
    group
  refine MulEquiv.ext fun u => hinjA ?_
  rw [← hΞt1, hΞt1']
  rfl

end GraphFaithful

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
