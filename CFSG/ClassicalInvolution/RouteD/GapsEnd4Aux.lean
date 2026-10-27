module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Model
public import CFSG.ClassicalInvolution.RouteD.GapsD4A
public import CFSG.ClassicalInvolution.RouteD.TypeAChain

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

theorem blockSL2_range_eq_Lc {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {m a : ℕ} (ha : a < m) :
    (blockSL2 F m ⟨a, ha⟩).range = Lc F (nodePair m a ha) :=
  range_blockSL_eq_Lc h2 (by omega : a + 2 ≤ m + 1)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem unique_involution_of_isClassicalMember (h2 : (2 : GaloisField p f) ≠ 0) {L : Subgroup G}
    (hL : classicalInvolutionOddCore L = ⊥) {a b : G} (ha : IsClassicalMember p f L a)
    (hb : IsClassicalMember p f L b) : a = b := by
  obtain ⟨e⟩ := ha.nonempty_equiv_sl2 hL
  have key : ∀ {y : G} (hy : IsClassicalMember p f L y), e ⟨y, hy.mem⟩ = -1 := by
    intro y hy
    have hyy : y * y = 1 := by
      rw [← pow_two]
      have := pow_orderOf_eq_one y
      rwa [hy.orderOf_eq_two] at this
    have h1 : (⟨y, hy.mem⟩ : ↥L) * ⟨y, hy.mem⟩ = 1 := Subtype.ext hyy
    have h3 : e ⟨y, hy.mem⟩ * e ⟨y, hy.mem⟩ = 1 := by rw [← map_mul, h1, map_one]
    rcases sl2_sq_eq_one h2 h3 with h | h
    · exfalso
      have : (⟨y, hy.mem⟩ : ↥L) = 1 := e.injective (by rw [h, map_one])
      have h4 : y = 1 := congrArg Subtype.val this
      have := hy.orderOf_eq_two
      rw [h4, orderOf_one] at this
      omega
    · exact h
  have := e.injective ((key ha).trans (key hb).symm)
  exact congrArg Subtype.val this

theorem eq_block_neg_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    {θ : SL(3, F) →* X} (hker : θ.ker ≤ Subgroup.center SL(3, F)) {j : ℕ} (hj : j + 2 ≤ 3)
    {a : X} (ha : a ∈ (blockSL F 3 2 j hj).range.map θ) (ha2 : orderOf a = 2) :
    a = θ (blockSL F 3 2 j hj (-1)) := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
  have hinj := comp_blockSL_injective hker hj (by omega : 2 < 3)
  have haa : θ (blockSL F 3 2 j hj A) * θ (blockSL F 3 2 j hj A) = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one (θ (blockSL F 3 2 j hj A))
    rwa [ha2] at this
  have hAA : A * A = 1 := by
    apply hinj
    simp only [MonoidHom.comp_apply, map_mul, map_one]
    exact haa
  rcases sl2_sq_eq_one h2 hAA with h | h
  · exfalso
    subst h
    rw [map_one, map_one, orderOf_one] at ha2
    omega
  · rw [h]

theorem standardPair_involutions_commute {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {X : Type}
    [Group X] {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) {a b : X} (ha : a ∈ U)
    (hb : b ∈ V) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a * b = b * a := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  rw [← hU] at ha
  rw [← hV] at hb
  rw [eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) ha ha2,
    eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) hb hb2, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_neg_one,
    coe_blockSL_neg_one, negBlock_eq_diagonal, negBlock_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem conj_partnerDiag_four_neg {F : Type} [Field F] (x : SL(4 + 1, F)) :
    slConjugation (4 + 1) F (partnerDiag 4 (-1)) x =
      zElt F (nodePair 4 1 (by norm_num)) * x * (zElt F (nodePair 4 1 (by norm_num)))⁻¹ := by
  set T := nodePair 4 1 (by norm_num) with hT
  let v : Fin (4 + 1) → Fˣ := fun i => if i.val = 1 ∨ i.val = 2 then -1 else 1
  have hc : ∀ i, partnerEnt 4 (-1 : Fˣ) i = (-1) * v i := by
    intro i
    simp only [partnerEnt, v]
    fin_cases i <;> simp
  have hmem : ∀ i : Fin (4 + 1), i ∈ T.1 ↔ (i.val = 1 ∨ i.val = 2) := by
    intro i
    simp only [hT, nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have hvz : ∀ i, (v i : F) = if i ∈ T.1 then -1 else 1 := by
    intro i
    by_cases hi : i ∈ T.1
    · have := (hmem i).mp hi
      simp [v, this, hi]
    · have := (not_congr (hmem i)).mp hi
      simp [v, this, hi]
  have hvz' : ∀ i, (((v i)⁻¹ : Fˣ) : F) = if i ∈ T.1 then -1 else 1 := by
    intro i
    by_cases hi : i ∈ T.1
    · have := (hmem i).mp hi
      simp [v, this, hi]
    · have := (not_congr (hmem i)).mp hi
      simp [v, this, hi]
  unfold partnerDiag
  rw [slConjugation_diagGL_congr (partnerEnt 4 (-1)) v (-1) hc x]
  have hinv : (zElt F T)⁻¹ = zElt F T := inv_eq_of_mul_eq_one_right (zElt_mul_self T)
  rw [hinv]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [slConjugation_diagGL_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_zElt, zMat, Matrix.mul_diagonal, Matrix.diagonal_mul,
    hvz, hvz']

end CFSG.ClassicalInvolution.RouteD.Gaps
