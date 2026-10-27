module

public import CFSG.ClassicalInvolution.Balance.BootstrapFrameFacts
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Weyl

abbrev g2i0 : Fin Tag.G2.rank := ⟨0, by decide⟩

abbrev g2i1 : Fin Tag.G2.rank := ⟨1, by decide⟩

theorem simple_inv_eq' (τ : Tag) (i : Fin τ.rank) : (simple τ i)⁻¹ = simple τ i := by
  unfold simple
  exact (coxeterSystem τ).inv_simple i

theorem prod_univ_g2 {M : Type*} [CommMonoid M] (f : Fin Tag.G2.rank → M) :
    ∏ i, f i = f g2i0 * f g2i1 :=
  Fin.prod_univ_two f

variable {K : Type} [Field K]

theorem weylTuple_simple_g0_zero (b : Fin Tag.G2.rank → Kˣ) :
    weylTuple (simple Tag.G2 g2i0) b g2i0 = (b g2i0)⁻¹ := by
  rw [weylTuple, simple_inv_eq', simple_smul]
  have : reflect Tag.G2 g2i0 (Pi.single g2i0 1) = fun i => if i = g2i0 then -1 else 0 := by
    funext i
    fin_cases i <;> simp [reflect, Tag.cartan, g2i0]
    all_goals decide
  rw [this, rootChar, prod_univ_g2]
  simp [g2i0, g2i1]

theorem weylTuple_simple_g0_one (b : Fin Tag.G2.rank → Kˣ) :
    weylTuple (simple Tag.G2 g2i0) b g2i1 = b g2i0 * b g2i1 := by
  rw [weylTuple, simple_inv_eq', simple_smul]
  have : reflect Tag.G2 g2i0 (Pi.single g2i1 1) = fun _ => 1 := by
    funext i
    fin_cases i <;> simp [reflect, Tag.cartan, g2i0, g2i1]
    all_goals decide
  rw [this, rootChar, prod_univ_g2]
  simp [g2i0, g2i1]

theorem weylTuple_simple_g1_zero (b : Fin Tag.G2.rank → Kˣ) :
    weylTuple (simple Tag.G2 g2i1) b g2i0 = b g2i0 * b g2i1 ^ 3 := by
  rw [weylTuple, simple_inv_eq', simple_smul]
  have : reflect Tag.G2 g2i1 (Pi.single g2i0 1) = fun i => if i = g2i0 then 1 else 3 := by
    funext i
    fin_cases i <;> simp [reflect, Tag.cartan, g2i0, g2i1]
    all_goals decide
  rw [this, rootChar, prod_univ_g2]
  simp [g2i0, g2i1]

theorem weylTuple_simple_g1_one (b : Fin Tag.G2.rank → Kˣ) :
    weylTuple (simple Tag.G2 g2i1) b g2i1 = (b g2i1)⁻¹ := by
  rw [weylTuple, simple_inv_eq', simple_smul]
  have : reflect Tag.G2 g2i1 (Pi.single g2i1 1) = fun i => if i = g2i1 then -1 else 0 := by
    funext i
    fin_cases i <;> simp [reflect, Tag.cartan, g2i1]
    all_goals decide
  rw [this, rootChar, prod_univ_g2]
  simp [g2i0, g2i1]

theorem g2_funext {M : Type*} {f g : Fin Tag.G2.rank → M} (h0 : f g2i0 = g g2i0)
    (h1 : f g2i1 = g g2i1) : f = g := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem g2_signTuple_to_neg_one {b : Fin Tag.G2.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hne : b ≠ 1) :
    ∃ w : WeylGroup Tag.G2, weylTuple w b = fun _ => -1 := by
  rcases hb g2i0 with h0 | h0 <;> rcases hb g2i1 with h1 | h1
  · exact absurd (g2_funext h0 h1) hne
  · refine ⟨simple Tag.G2 g2i1, g2_funext ?_ ?_⟩
    · rw [weylTuple_simple_g1_zero, h0, h1]
      simp [Odd.neg_one_pow (show Odd 3 by decide)]
    · rw [weylTuple_simple_g1_one, h1]
      simp
  · refine ⟨simple Tag.G2 g2i0, g2_funext ?_ ?_⟩
    · rw [weylTuple_simple_g0_zero, h0]
      simp
    · rw [weylTuple_simple_g0_one, h0, h1]
      simp
  · exact ⟨1, by rw [weylTuple_one]; exact g2_funext h0 h1⟩

theorem g2_signTuple_conj {b b' : Fin Tag.G2.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb' : ∀ i, b' i = 1 ∨ b' i = -1) (hne : b ≠ 1)
    (hne' : b' ≠ 1) : ∃ w : WeylGroup Tag.G2, weylTuple w b = b' := by
  obtain ⟨w, hw⟩ := g2_signTuple_to_neg_one hb hne
  obtain ⟨w', hw'⟩ := g2_signTuple_to_neg_one hb' hne'
  refine ⟨w'⁻¹ * w, ?_⟩
  rw [← weylTuple_weylTuple, hw, ← hw', weylTuple_weylTuple, inv_mul_cancel, weylTuple_one]

end Weyl

section Involutions

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem ne_one_of_conj_eq_rootDiagUnit {x c : ↥(adjointGroup Tag.G2 K)}
    {d : Fin Tag.G2.rank → Kˣ} (h : ((c * x * c⁻¹ : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      rootDiagUnit Tag.G2 d) (hx : x ≠ 1) : d ≠ 1 := by
  intro hd
  apply hx
  rw [hd, rootDiagUnit_one] at h
  have h1 : c * x * c⁻¹ = 1 := Subtype.ext h
  calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
    _ = 1 := by rw [h1]; group

theorem g2_involutions_conj (hK : Odd (Nat.card K)) {z z' : ↥(adjointGroup Tag.G2 K)}
    (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1) (hz1' : z' ≠ 1) :
    ∃ h : ↥(adjointGroup Tag.G2 K), h * z * h⁻¹ = z' := by
  obtain ⟨g, b, hb, hgz⟩ := exists_conj_eq_rootDiagUnit_of_involution (Or.inl rfl) hK z hz
  obtain ⟨g', b', hb', hgz'⟩ := exists_conj_eq_rootDiagUnit_of_involution (Or.inl rfl) hK z' hz'
  obtain ⟨w, hw⟩ := g2_signTuple_conj hb hb' (ne_one_of_conj_eq_rootDiagUnit hgz hz1)
    (ne_one_of_conj_eq_rootDiagUnit hgz' hz1')
  set N : ↥(adjointGroup Tag.G2 K) :=
    ⟨canonicalRep (coxeterSystem Tag.G2) K w, canonicalRep_mem_adjointGroup _ K w⟩ with hN
  have hconj : N * (g * z * g⁻¹) * N⁻¹ = g' * z' * g'⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hgz, hgz', ← hw]
    exact canonicalRep_conj_rootDiagUnit w b
  refine ⟨g'⁻¹ * N * g, ?_⟩
  calc g'⁻¹ * N * g * z * (g'⁻¹ * N * g)⁻¹ = g'⁻¹ * (N * (g * z * g⁻¹) * N⁻¹) * g' := by group
    _ = z' := by rw [hconj]; group

end Involutions

section Model

variable {p : ℕ} [Fact p.Prime]

theorem fundInvolutionsConj_g2 {n e : ℕ} (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .G2 n p e) :
    FundInvolutionsConj p .G2 n e := by
  have hK : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  intro _ _ _ _ r _ r' _ hrr hrr' hr1 hr1' _ _
  exact g2_involutions_conj hK hrr hrr' hr1 hr1'

@[expose] def TrialityD4InvolutionsConj (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ n e : ℕ, p ≠ 2 → StatedLieAdmissible .trialityD4 n p e → FundInvolutionsConj p .trialityD4 n e

theorem twoClassInvolutionsConj_of_trialityD4 (h : TrialityD4InvolutionsConj p) :
    TwoClassInvolutionsConj p := by
  intro t n e hp2 ht hadm
  rcases ht with rfl | rfl
  · exact fundInvolutionsConj_g2 hp2 hadm
  · exact h n e hp2 hadm

end Model

end CFSG.ClassicalInvolution.Balance.Bootstrap
