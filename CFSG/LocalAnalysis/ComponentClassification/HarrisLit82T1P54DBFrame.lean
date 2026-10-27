module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DA

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup CliffordAlgebra Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem negOne_mem_center (hQ : Q ≠ 0) : spinGroup.negOne Q hQ ∈ center (spinGroup Q) := by
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, spinGroup.coe_negOne, mul_neg_one, neg_one_mul]

variable {m : ℕ} (F : HypFrame Q m)

theorem centralizer_longSL2_neg_one (hQ : Q ≠ 0) {i j : Fin m} (hij : i ≠ j) (s : Bool) :
    centralizer {F.longSL2 hij true s (-1)} = centralizer {F.longSL2 hij true true (-1)} := by
  cases s
  · have h : F.longSL2 hij true false (-1) =
        spinGroup.negOne Q hQ * F.longSL2 hij true true (-1) :=
      T1.longSL2_neg_one_not F hij hQ true true
    rw [h]
    exact T1.centralizer_mul_of_mem_center (negOne_mem_center hQ)
  · rfl

theorem conclZ_of_frame [Finite K] {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (hZ : ∀ x ∈ center (spinGroup Q), ∃ c : K, ∀ v, spinAction Q x v = c • v) (hQ : Q ≠ 0)
    {t : spinGroup Q} {J : Subgroup (spinGroup Q)}
    (hJc : IsTwoComponentIn J (centralizer {F.longSL2 hij true true (-1)}))
    (hJu : ∀ s, F.longSL2 hij true s (-1) ∉ J) (hJq : IsQuasisimple J)
    (hJx : ∃ x ∈ J, orderOf x = 2 ∧ x ∉ center (spinGroup Q))
    (hJl : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel (J ⧸ center J) τ' n' p f)
    {s : Bool} (ht : t * F.longSL2 hij true s (-1) ∈ J) : ConclZ p f (spinGroup Q) t := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  set u := F.longSL2 hij true s (-1) with hu
  have hu2 : orderOf u = 2 := T1.orderOf_longSL2_neg_one F hij hodd true s
  have huZ : u ∉ center (spinGroup Q) :=
    DA.longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true s
  have := T1.finite_range_longSL2 F hij true s
  have hZ₁ : (center ↥(F.longSL2 hij true s).range).map (F.longSL2 hij true s).range.subtype =
      zpowers u :=
    T1.map_center_range_longSL2 F hij hp hp2 hK h5 true s
  have hJc' : IsTwoComponentIn J (centralizer {u}) := by
    rw [hu, centralizer_longSL2_neg_one F hQ hij s]
    exact hJc
  have huJ₁ : u ∈ (F.longSL2 hij true s).range := MonoidHom.mem_range.mpr ⟨-1, rfl⟩
  refine ⟨u, hu2, huZ, (F.longSL2 hij true s).range, J,
    T1.isTwoComponentIn_range_longSL2 F hij hp hp2 hK h5 hrange true s, hJc',
    fun h => hJu s (by rw [← h]; exact huJ₁), huJ₁, ?_,
    T1.isSLTwoOver_range_longSL2 F hij hK true s, hJq, hJx, hJl, .inr ht⟩
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_inf] at ha
  have h1 : a ∈ (center ↥(F.longSL2 hij true s).range).map (F.longSL2 hij true s).range.subtype :=
    Subgroup.mem_map.mpr ⟨⟨a, ha.1⟩,
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp ha.2 g), rfl⟩
  rw [hZ₁] at h1
  rcases eq_one_or_eq_of_mem_zpowers hu2 h1 with h2 | h2
  · rw [h2]
    exact one_mem _
  · exact absurd (h2 ▸ ha.2) huZ

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
