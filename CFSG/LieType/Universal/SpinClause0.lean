module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Commutator

private theorem mul_mul_mul_mul_eq_neg_one {R : Type*} [Ring R] {a b c : R} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hab : b * a = -(a * b)) (hac : c * a = -(a * c))
    (hbc : b * c = -(c * b)) : a * b * (b * c) * (b * a) * (c * b) = -1 := by
  have e1 : a * b * (b * c) = a * c := by rw [mul_assoc, ← mul_assoc b, hb, one_mul]
  have e2 : a * c * (b * a) = c * b := by
    calc a * c * (b * a) = a * (c * (b * a)) := by rw [mul_assoc]
    _ = a * (c * -(a * b)) := by rw [hab]
    _ = -(a * (c * a) * b) := by noncomm_ring
    _ = -(a * -(a * c) * b) := by rw [hac]
    _ = a * a * (c * b) := by noncomm_ring
    _ = c * b := by rw [ha, one_mul]
  have e3 : c * b * (c * b) = -1 := by
    calc c * b * (c * b) = c * (b * c) * b := by noncomm_ring
    _ = c * -(c * b) * b := by rw [hbc]
    _ = -((c * c) * (b * b)) := by noncomm_ring
    _ = -1 := by rw [hc, hb, one_mul]
  rw [e1, e2, e3]

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem coe_inv_spinGroup (z : spinGroup Q) :
    ((z⁻¹ : spinGroup Q) : CliffordAlgebra Q) = star (z : CliffordAlgebra Q) := by
  rw [← spinGroup.star_eq_inv, spinGroup.coe_star]

theorem exists_commutator_eq_neg_one {a b c : V} (ha : Q a = 1) (hb : Q b = 1) (hc : Q c = 1)
    (hab : polar Q a b = 0) (hac : polar Q a c = 0) (hbc : polar Q b c = 0) :
    ∃ x y : spinGroup Q, ((⁅x, y⁆ : spinGroup Q) : CliffordAlgebra Q) = -1 := by
  refine ⟨⟨ι Q a * ι Q b, ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one a b (by
      rw [ha, hb, one_mul])⟩,
    ⟨ι Q b * ι Q c, ι_mul_ι_mem_spinGroup_of_norm_mul_norm_eq_one b c (by
      rw [hb, hc, one_mul])⟩, ?_⟩
  have hsq : ∀ v : V, Q v = 1 → ι Q v * ι Q v = 1 := fun v hv => by
    rw [ι_sq_scalar, hv, map_one]
  have hanti : ∀ u v : V, polar Q u v = 0 → ι Q v * ι Q u = -(ι Q u * ι Q v) := fun u v huv =>
    ι_mul_ι_comm_of_isOrtho (isOrtho_polarBilin.mp (by
      rw [polarBilin_apply_apply, polar_comm, huv]))
  rw [commutatorElement_def, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    coe_inv_spinGroup, coe_inv_spinGroup]
  simp only [star_mul, star_ι, neg_mul_neg]
  exact mul_mul_mul_mul_eq_neg_one (hsq a ha) (hsq b hb) (hsq c hc) (hanti a b hab)
    (hanti a c hac) (hanti c b (by rw [polar_comm]; exact hbc))

private theorem map_add_hypPair (P : HypPair Q) : Q (P.e + P.f) = 1 := by
  rw [QuadraticMap.map_add Q, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]

private theorem polar_add_hypPair {P P' : HypPair Q} (h : P.Orth P') :
    polar Q (P.e + P.f) (P'.e + P'.f) = 0 := by
  rw [polar_add_left, polar_add_right, polar_add_right, h.ee, h.ef, h.fe, h.ff, add_zero,
    add_zero]

theorem exists_commutator_eq_neg_one_of_hypPairs {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    ∃ x y : spinGroup Q, ((⁅x, y⁆ : spinGroup Q) : CliffordAlgebra Q) = -1 :=
  exists_commutator_eq_neg_one (map_add_hypPair P₁) (map_add_hypPair P₂) (map_add_hypPair P₃)
    (polar_add_hypPair h₁₂) (polar_add_hypPair h₁₃) (polar_add_hypPair h₂₃)

end Commutator

section Perfect

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
  {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K}

theorem isPerfect_spinGroup (hR : (spinMatrix Q).range = StatedOmega Q₀)
    [Group.IsPerfect (StatedOmega Q₀)]
    (hker : ∀ x ∈ (spinMatrix Q).ker, x = 1 ∨ (x : CliffordAlgebra Q) = -1)
    {x y : spinGroup Q} (hxy : ((⁅x, y⁆ : spinGroup Q) : CliffordAlgebra Q) = -1) :
    Group.IsPerfect (spinGroup Q) := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro g _
  let φ : spinGroup Q →* StatedOmega Q₀ :=
    (spinMatrix Q).codRestrict (StatedOmega Q₀) (spinMatrix_mem_of_range_eq Q hR)
  have hsurj : Function.Surjective φ := by
    rintro ⟨A, hA⟩
    obtain ⟨z, hz⟩ : A ∈ (spinMatrix Q).range := hR ▸ hA
    exact ⟨z, Subtype.ext hz⟩
  have hmap : (commutator (spinGroup Q)).map φ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsurj, ← commutator_def, Group.IsPerfect.commutator_eq_top]
  obtain ⟨h, hh, hφ⟩ : φ g ∈ (commutator (spinGroup Q)).map φ := hmap ▸ Subgroup.mem_top _
  have hk : g * h⁻¹ ∈ (spinMatrix Q).ker := by
    have hφ' : spinMatrix Q h = spinMatrix Q g := congrArg Subtype.val hφ
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ', mul_inv_cancel]
  rcases hker _ hk with h1 | hneg
  · rw [mul_inv_eq_one] at h1
    rw [h1]
    exact hh
  · have hc : g * h⁻¹ = ⁅x, y⁆ := Subtype.ext (hneg.trans hxy.symm)
    have hg : g = ⁅x, y⁆ * h := by rw [← hc, inv_mul_cancel_right]
    rw [hg]
    exact mul_mem (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
      hh

private theorem exists_mul_ne_mul_of_mulEquiv {G : Type*} [Group G] {ι : Type} [Fintype ι]
    [DecidableEq ι] {H : Subgroup (GL ι K)} [Group.IsPerfect H] [IsSimpleGroup (StatedProj H)]
    (e : G ≃* StatedProj H) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := exists_mul_ne_mul_statedProj (H := H)
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

theorem isQuasisimple_spinGroup_of_mulEquiv [Group.IsPerfect (spinGroup Q)]
    [Group.IsPerfect (StatedOmega Q₀)] [IsSimpleGroup (StatedProj (StatedOmega Q₀))]
    (e : spinGroup Q ⧸ Subgroup.center (spinGroup Q) ≃* StatedProj (StatedOmega Q₀)) :
    IsQuasisimple (spinGroup Q) :=
  CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient _ le_rfl inferInstance
    e.isSimpleGroup (exists_mul_ne_mul_of_mulEquiv e)

end Perfect

section Odd

variable {n : ℕ} {K : Type} [Field K]

private theorem oddPairs (hn : 3 ≤ n) :
    (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨1, by omega⟩) ∧
      (oddPair K (⟨0, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) ∧
      (oddPair K (⟨1, by omega⟩ : Fin n)).Orth (oddPair K ⟨2, by omega⟩) :=
  ⟨oddPair_orth (by simp [Fin.ext_iff]), oddPair_orth (by simp [Fin.ext_iff]),
    oddPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_spinGroup_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Group.IsPerfect (spinGroup (quadOdd n K)) := by
  have := isPerfect_statedOmega_quadOdd h2 hn
  obtain ⟨x, y, hxy⟩ := exists_commutator_eq_neg_one_of_hypPairs (oddPairs (K := K) hn).1
    (oddPairs hn).2.1 (oddPairs hn).2.2
  exact isPerfect_spinGroup (range_spinMatrix_quadOdd h2 hn)
    (fun x hx => (mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx) hxy

theorem isQuasisimple_spinGroup_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    IsQuasisimple (spinGroup (quadOdd n K)) := by
  have := isPerfect_spinGroup_quadOdd h2 hn
  have := isPerfect_statedOmega_quadOdd h2 hn
  have := isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero h2 hn
  exact isQuasisimple_spinGroup_of_mulEquiv (spinQuotientCenterEquivQuadOdd h2 hn)

theorem statedClassicalModel_spin_quadOdd [Finite K] {p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) (hK : Nat.card K = p ^ f) :
    StatedClassicalModel (spinGroup (quadOdd n K) ⧸ Subgroup.center (spinGroup (quadOdd n K)))
      .POmegaOdd n p f := by
  obtain ⟨hp, hf, hn, hp2⟩ := hadm
  have hq : (ringChar K).Prime := by rw [ringChar_eq_of_card_eq hp hf hK]; exact hp
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two hq, ringChar_eq_of_card_eq hp hf hK]
    exact hp2
  exact ⟨⟨hp, hf, hn, hp2⟩, K, inferInstance, inferInstance, hK,
    ⟨spinQuotientCenterEquivQuadOdd h2 hn⟩⟩

end Odd

section Plus

variable {n : ℕ} {K : Type} [Field K]

private theorem plusPairs (hn : 3 ≤ n) :
    (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨1, by omega⟩) ∧
      (plusPair K (⟨0, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) ∧
      (plusPair K (⟨1, by omega⟩ : Fin n)).Orth (plusPair K ⟨2, by omega⟩) :=
  ⟨plusPair_orth (by simp [Fin.ext_iff]), plusPair_orth (by simp [Fin.ext_iff]),
    plusPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_spinGroup_quadPlus (hn : 3 ≤ n) :
    Group.IsPerfect (spinGroup (quadPlus n K)) := by
  have := isPerfect_statedOmega_quadPlus (K := K) hn
  obtain ⟨x, y, hxy⟩ := exists_commutator_eq_neg_one_of_hypPairs (plusPairs (K := K) hn).1
    (plusPairs hn).2.1 (plusPairs hn).2.2
  exact isPerfect_spinGroup (range_spinMatrix_quadPlus hn)
    (fun x hx => (mem_ker_spinMatrix_quadPlus_iff x).mp hx) hxy

theorem isQuasisimple_spinGroup_quadPlus (hn : 3 ≤ n) :
    IsQuasisimple (spinGroup (quadPlus n K)) := by
  have := isPerfect_spinGroup_quadPlus (K := K) hn
  have := isPerfect_statedOmega_quadPlus (K := K) hn
  have := isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hn
  exact isQuasisimple_spinGroup_of_mulEquiv (spinQuotientCenterEquivQuadPlus hn)

theorem statedClassicalModel_spin_quadPlus [Finite K] {p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (hK : Nat.card K = p ^ f) :
    StatedClassicalModel (spinGroup (quadPlus n K) ⧸ Subgroup.center (spinGroup (quadPlus n K)))
      .POmegaPlus n p f :=
  ⟨hadm, K, inferInstance, inferInstance, hK,
    ⟨spinQuotientCenterEquivQuadPlus (by have := hadm.2.2; omega)⟩⟩

end Plus

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K}

private theorem minusPairs (hn : 4 ≤ n) :
    (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨1, by omega⟩) ∧
      (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) ∧
      (minusPair K b c (⟨1, by omega⟩ : Fin (n - 1))).Orth (minusPair K b c ⟨2, by omega⟩) :=
  ⟨minusPair_orth (by simp [Fin.ext_iff]), minusPair_orth (by simp [Fin.ext_iff]),
    minusPair_orth (by simp [Fin.ext_iff])⟩

theorem isPerfect_spinGroup_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Group.IsPerfect (spinGroup (quadMinus n K b c)) := by
  have := isPerfect_statedOmega_quadMinus hn hirr
  obtain ⟨x, y, hxy⟩ := exists_commutator_eq_neg_one_of_hypPairs (minusPairs (b := b) (c := c)
    (K := K) hn).1 (minusPairs hn).2.1 (minusPairs hn).2.2
  exact isPerfect_spinGroup (range_spinMatrix_quadMinus hn hirr)
    (fun x hx => (mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx) hxy

theorem isQuasisimple_spinGroup_quadMinus [Finite K] (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsQuasisimple (spinGroup (quadMinus n K b c)) := by
  have := isPerfect_spinGroup_quadMinus hn hirr
  have := isPerfect_statedOmega_quadMinus hn hirr
  have := isSimpleGroup_statedProj_statedOmega_quadMinus hn hirr
  exact isQuasisimple_spinGroup_of_mulEquiv (spinQuotientCenterEquivQuadMinus hn hirr)

theorem statedClassicalModel_spin_quadMinus [Finite K] {p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hK : Nat.card K = p ^ f)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedClassicalModel
      (spinGroup (quadMinus n K b c) ⧸ Subgroup.center (spinGroup (quadMinus n K b c)))
      .POmegaMinus n p f :=
  ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr,
    ⟨spinQuotientCenterEquivQuadMinus hadm.2.2 hirr⟩⟩

end Minus

end CFSG.LieType.Universal.Spin
