module

public import CFSG.LieType.SeitzGeneration.SpF2.Quot
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open Matrix CFSG.RankThree.PartOne.CTP CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.Assembly.LowTwoRank

variable {r : ℕ} {K : Type} [Field K]

@[expose] def stdQuad (x : Fin r ⊕ Fin r → K) : K :=
  ∑ i : Fin r, x (Sum.inl i) * x (Sum.inr i)

@[expose] noncomputable def twistQuad (z x : Fin r ⊕ Fin r → K) : K :=
  stdQuad x + spForm r K x z ^ 2

theorem spForm_eq_sum_inl_inr (x y : Fin r ⊕ Fin r → K) :
    spForm r K x y =
      ∑ i : Fin r, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  rw [Finset.sum_sub_distrib, spForm_apply]
  simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.fromBlocks_mulVec,
    dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, sub_eq_add_neg]

theorem stdQuad_add [CharP K 2] (x y : Fin r ⊕ Fin r → K) :
    stdQuad (x + y) = stdQuad x + stdQuad y + spForm r K x y := by
  rw [spForm_eq_sum_inl_inr, stdQuad, stdQuad, stdQuad, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, CharTwo.sub_eq_add]
  ring

theorem stdQuad_smul (c : K) (x : Fin r ⊕ Fin r → K) : stdQuad (c • x) = c ^ 2 * stdQuad x := by
  simp only [stdQuad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem twistQuad_add [CharP K 2] (z x y : Fin r ⊕ Fin r → K) :
    twistQuad z (x + y) = twistQuad z x + twistQuad z y + spForm r K x y := by
  simp only [twistQuad, stdQuad_add, map_add, LinearMap.add_apply, CharTwo.add_sq]
  ring

theorem twistQuad_smul (z : Fin r ⊕ Fin r → K) (c : K) (x : Fin r ⊕ Fin r → K) :
    twistQuad z (c • x) = c ^ 2 * twistQuad z x := by
  simp only [twistQuad, stdQuad_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem twistQuad_spTransvection [CharP K 2] {z v : Fin r ⊕ Fin r → K} (hv : twistQuad z v = 1)
    (x : Fin r ⊕ Fin r → K) :
    twistQuad z (spEnd (spTransvection v 1) x) = twistQuad z x := by
  rw [spEnd_spTransvection, twistQuad_add, twistQuad_smul, hv, map_smul, smul_eq_mul, one_mul]
  linear_combination spForm r K x v ^ 2 * (CharTwo.two_eq_zero (R := K))

theorem twistQuad_closure {z : Fin r ⊕ Fin r → K} {s : Set (StatedSp r K)}
    (hs : ∀ g ∈ s, ∀ x, twistQuad z (spEnd g x) = twistQuad z x) :
    ∀ g ∈ Subgroup.closure s, ∀ x, twistQuad z (spEnd g x) = twistQuad z x := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hs g hg
  | one => intro x; rw [spEnd_one, Module.End.one_apply]
  | mul a b _ _ ha hb => intro x; rw [spEnd_mul, Module.End.mul_apply, ha, hb]
  | inv a _ ha => intro x; rw [← ha (spEnd a⁻¹ x), spEnd_spEnd_inv]

theorem Frame.exists_spForm_eq {e f r₀ : Fin r ⊕ Fin r → K} (h : Frame e f r₀) (hr₀ : r₀ ≠ 0)
    (s₁ s₂ s₃ : K) :
    ∃ z, spForm r K e z = s₁ ∧ spForm r K f z = s₂ ∧ spForm r K r₀ z = s₃ := by
  obtain ⟨v, hv⟩ := CFSG.RankThree.PartOne.KCSpComm.exists_spForm_eq_one hr₀
  have hA := spForm_isAlt (r := r) (K := K)
  have hee : spForm r K e e = 0 := hA.self_eq_zero e
  have hff : spForm r K f f = 0 := hA.self_eq_zero f
  have hfe : spForm r K f e = -1 := by rw [← hA.neg_eq e f, h.ef]
  have hre : spForm r K r₀ e = 0 := by rw [← hA.neg_eq e r₀, h.er, neg_zero]
  have hrf : spForm r K r₀ f = 0 := by rw [← hA.neg_eq f r₀, h.fr, neg_zero]
  have hrv : spForm r K r₀ v = -1 := by rw [← hA.neg_eq v r₀, hv]
  refine ⟨(-s₂) • e + s₁ • f - s₃ • (v + spForm r K f v • e - spForm r K e v • f), ?_, ?_, ?_⟩ <;>
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hee, hff, hfe, h.ef, hre, hrf, hrv] <;>
    ring

end CFSG.LieType.SeitzGeneration.SpF2
