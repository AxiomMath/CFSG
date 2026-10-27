module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

@[expose] def q2CoordFun (N ε : ℕ) : (Fin N ⊕ Fin N) ⊕ Fin ε → Fin (2 * N + ε) :=
  Sum.elim (Sum.elim (fun p => ⟨2 * p.1, by have := p.2; omega⟩)
    (fun p => ⟨2 * p.1 + 1, by have := p.2; omega⟩)) (fun i => ⟨2 * N + i.1, by
      have := i.2; omega⟩)

theorem q2CoordFun_injective (N ε : ℕ) : Function.Injective (q2CoordFun N ε) := by
  intro w w' h
  have hv := congrArg Fin.val h
  rcases w with (p | p) | i <;> rcases w' with (p' | p') | i' <;>
    simp only [q2CoordFun, Sum.elim_inl, Sum.elim_inr] at hv <;>
    first
    | (have := p.2; have := p'.2; omega)
    | (have := p.2; have := i'.2; omega)
    | (have := i.2; have := p'.2; omega)
    | (congr 2; ext; omega)

@[expose] noncomputable def q2Coord (N ε : ℕ) : (Fin N ⊕ Fin N) ⊕ Fin ε ≃ Fin (2 * N + ε) :=
  Equiv.ofBijective (q2CoordFun N ε) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨q2CoordFun_injective N ε, by simp only [Fintype.card_sum, Fintype.card_fin]; ring⟩)

variable {N ε : ℕ}

@[simp] theorem q2Coord_inl_inl (p : Fin N) :
    ((q2Coord N ε (Sum.inl (Sum.inl p))) : ℕ) = 2 * p.1 := rfl

@[simp] theorem q2Coord_inl_inr (p : Fin N) :
    ((q2Coord N ε (Sum.inl (Sum.inr p))) : ℕ) = 2 * p.1 + 1 := rfl

@[simp] theorem q2Coord_inr (i : Fin ε) :
    ((q2Coord N ε (Sum.inr i)) : ℕ) = 2 * N + i.1 := rfl

@[expose] def InPlanes (R : Finset (Fin N)) : (Fin N ⊕ Fin N) ⊕ Fin ε → Prop :=
  Sum.elim (fun u => planeOf u ∈ R) (fun _ => False)

instance (R : Finset (Fin N)) : DecidablePred (InPlanes (ε := ε) R) := fun w => by
  unfold InPlanes
  rcases w with u | i
  · exact inferInstanceAs (Decidable (planeOf u ∈ R))
  · exact inferInstanceAs (Decidable False)

@[simp] theorem inPlanes_inl (R : Finset (Fin N)) (u : Fin N ⊕ Fin N) :
    InPlanes (ε := ε) R (Sum.inl u) ↔ planeOf u ∈ R := Iff.rfl

@[simp] theorem not_inPlanes_inr (R : Finset (Fin N)) (i : Fin ε) :
    ¬ InPlanes (ε := ε) R (Sum.inr i) := id

@[expose] noncomputable def planeCoordsQ2 (ε : ℕ) (R : Finset (Fin N)) : Finset (Fin (2 * N + ε)) :=
  Finset.univ.filter fun a => InPlanes R ((q2Coord N ε).symm a)

theorem q2Coord_mem_planeCoordsQ2 {R : Finset (Fin N)} {w : (Fin N ⊕ Fin N) ⊕ Fin ε} :
    q2Coord N ε w ∈ planeCoordsQ2 ε R ↔ InPlanes R w := by
  simp [planeCoordsQ2]

theorem planeCoordsQ2_mono {R R' : Finset (Fin N)} (h : R ⊆ R') :
    planeCoordsQ2 ε R ⊆ planeCoordsQ2 ε R' := by
  intro a ha
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [q2Coord_mem_planeCoordsQ2] at ha ⊢
  rcases w with u | i
  · exact h ha
  · exact ha.elim

theorem mem_planeCoordsQ2_iff {R : Finset (Fin N)} {a : Fin (2 * N + ε)} :
    a ∈ planeCoordsQ2 ε R ↔ ∃ h : a.1 < 2 * N, (⟨a.1 / 2, by omega⟩ : Fin N) ∈ R := by
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [q2Coord_mem_planeCoordsQ2]
  rcases w with (p | p) | i
  · have hp := p.2
    have hlt : (q2Coord N ε (Sum.inl (Sum.inl p))).1 < 2 * N := by
      simp only [q2Coord_inl_inl]; omega
    have e : ∀ h : (q2Coord N ε (Sum.inl (Sum.inl p))).1 < 2 * N,
        (⟨(q2Coord N ε (Sum.inl (Sum.inl p))).1 / 2, by omega⟩ : Fin N) = p :=
      fun _ => Fin.ext (by simp only [q2Coord_inl_inl]; omega)
    rw [inPlanes_inl, planeOf_inl]
    exact ⟨fun h => ⟨hlt, by rw [e hlt]; exact h⟩, fun ⟨h, h'⟩ => by rwa [e h] at h'⟩
  · have hp := p.2
    have hlt : (q2Coord N ε (Sum.inl (Sum.inr p))).1 < 2 * N := by
      simp only [q2Coord_inl_inr]; omega
    have e : ∀ h : (q2Coord N ε (Sum.inl (Sum.inr p))).1 < 2 * N,
        (⟨(q2Coord N ε (Sum.inl (Sum.inr p))).1 / 2, by omega⟩ : Fin N) = p :=
      fun _ => Fin.ext (by simp only [q2Coord_inl_inr]; omega)
    rw [inPlanes_inl, planeOf_inr]
    exact ⟨fun h => ⟨hlt, by rw [e hlt]; exact h⟩, fun ⟨h, h'⟩ => by rwa [e h] at h'⟩
  · refine ⟨fun h => (not_inPlanes_inr R i h).elim, fun ⟨h, _⟩ => ?_⟩
    simp only [q2Coord_inr] at h
    omega

section Embed

variable {K : Type} [Field K]

@[expose] noncomputable def q2EmbedMat (ε : ℕ) (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
  reindex (q2Coord N ε) (q2Coord N ε) (fromBlocks y 0 0 1)

theorem q2EmbedMat_apply (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K)
    (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    q2EmbedMat ε y (q2Coord N ε w) (q2Coord N ε w') = fromBlocks y 0 0 1 w w' := by
  simp [q2EmbedMat, reindex_apply]

theorem q2EmbedMat_mul (y z : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    q2EmbedMat ε (y * z) = q2EmbedMat ε y * q2EmbedMat ε z := by
  simp only [q2EmbedMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem q2EmbedMat_one : q2EmbedMat ε (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) = 1 := by
  rw [q2EmbedMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

theorem q2EmbedMat_transpose (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    (q2EmbedMat ε y)ᵀ = q2EmbedMat ε yᵀ := by
  rw [q2EmbedMat, q2EmbedMat, transpose_reindex, fromBlocks_transpose]
  simp

theorem det_q2EmbedMat (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K) :
    (q2EmbedMat ε y).det = y.det := by
  rw [q2EmbedMat, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

end Embed

section SL

variable {K : Type} [Field K]

theorem q2_eq_one_of_ne_zero (hK : Nat.card K = 2) {c : K} (hc : c ≠ 0) : c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  exact mul_left_cancel₀ hc (h.trans (mul_one c).symm)

theorem det_eq_one_of_card_two (hK : Nat.card K = 2) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : GL ι K) : (y : Matrix ι ι K).det = 1 :=
  q2_eq_one_of_ne_zero hK (Matrix.GeneralLinearGroup.det_ne_zero y)

variable (ε) in
@[expose] noncomputable def q2Embed (hK : Nat.card K = 2) :
    StatedSp N K →* SpecialLinearGroup (Fin (2 * N + ε)) K where
  toFun y := ⟨q2EmbedMat ε (mat N K y), by
    rw [det_q2EmbedMat, mat_apply]; exact det_eq_one_of_card_two hK _⟩
  map_one' := Subtype.ext (by
    change q2EmbedMat ε (mat N K 1) = 1
    rw [map_one, q2EmbedMat_one])
  map_mul' y z := Subtype.ext (by
    change q2EmbedMat ε (mat N K (y * z)) = q2EmbedMat ε (mat N K y) * q2EmbedMat ε (mat N K z)
    rw [map_mul, q2EmbedMat_mul])

theorem coe_q2Embed (hK : Nat.card K = 2) (y : StatedSp N K) :
    ((q2Embed ε hK y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = q2EmbedMat ε (mat N K y) := rfl

theorem q2Embed_apply_q2Coord (hK : Nat.card K = 2) (y : StatedSp N K)
    (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ((q2Embed ε hK y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε w) (q2Coord N ε w') =
        fromBlocks (mat N K y) 0 0 1 w w' := by
  rw [coe_q2Embed, q2EmbedMat_apply]

theorem q2Embed_injective (hK : Nat.card K = 2) :
    Function.Injective (q2Embed (N := N) ε hK) := by
  intro y z h
  apply mat_injective
  ext u v
  have := congrArg (fun A : SpecialLinearGroup (Fin (2 * N + ε)) K =>
    (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε (Sum.inl u))
      (q2Coord N ε (Sum.inl v))) h
  simpa only [q2Embed_apply_q2Coord, fromBlocks_apply₁₁] using this

variable (K ε) in
@[expose] noncomputable def q2Block (R : Finset (Fin N)) :
    Subgroup (SpecialLinearGroup (Fin (2 * N + ε)) K) :=
  blockSpecialLinear (planeCoordsQ2 ε R)ᶜ

theorem q2Block_anti {R R' : Finset (Fin N)} (h : R ⊆ R') :
    q2Block ε K R' ≤ q2Block ε K R :=
  LinearPilot.blockSpecialLinear_mono (Finset.compl_subset_compl.2 (planeCoordsQ2_mono h))

theorem q2Embed_mem_q2Block_iff (hK : Nat.card K = 2) {R : Finset (Fin N)} {y : StatedSp N K} :
    q2Embed ε hK y ∈ q2Block ε K R ↔ y ∈ spBlock K Rᶜ := by
  rw [q2Block, mem_blockSpecialLinear, mem_spBlock]
  constructor
  · intro h u v huv
    have h1 := h (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) (by
      simp only [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      by_contra hc
      push Not at hc
      exact huv ⟨by simpa [mem_planeCoords] using hc.1, by simpa [mem_planeCoords] using hc.2⟩)
    rw [q2Embed_apply_q2Coord, fromBlocks_apply₁₁] at h1
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    simp only [(q2Coord N ε).injective.eq_iff, Sum.inl.injEq]
  · intro h a b hab
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
    obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
    rw [q2Embed_apply_q2Coord, Matrix.one_apply]
    simp only [(q2Coord N ε).injective.eq_iff]
    simp only [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2] at hab
    rcases w with u | i <;> rcases w' with v | j
    · have hu : ¬(u ∈ planeCoords Rᶜ ∧ v ∈ planeCoords Rᶜ) := by
        simp only [mem_planeCoords, Finset.mem_compl]
        rcases hab with h1 | h1
        · exact fun h2 => h2.1 h1
        · exact fun h2 => h2.2 h1
      rw [fromBlocks_apply₁₁, h u v hu, Matrix.one_apply]
      simp only [Sum.inl.injEq]
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
      simp
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
      simp
    · simp at hab

end SL

section Graph

variable {K : Type} [Field K]

@[expose] noncomputable def q2Par (N ε : ℕ) : Fin (2 * N + ε) → Fin (2 * N + ε) :=
  fun a => q2Coord N ε (Sum.map par id ((q2Coord N ε).symm a))

theorem q2Par_q2Coord (w : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    q2Par N ε (q2Coord N ε w) = q2Coord N ε (Sum.map par id w) := by
  simp [q2Par]

theorem q2Par_q2Par (a : Fin (2 * N + ε)) : q2Par N ε (q2Par N ε a) = a := by
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [q2Par_q2Coord, q2Par_q2Coord]
  rcases w with u | i <;> simp

theorem q2Par_mem_planeCoordsQ2 {R : Finset (Fin N)} {a : Fin (2 * N + ε)} :
    q2Par N ε a ∈ planeCoordsQ2 ε R ↔ a ∈ planeCoordsQ2 ε R := by
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  rw [q2Par_q2Coord, q2Coord_mem_planeCoordsQ2, q2Coord_mem_planeCoordsQ2]
  rcases w with u | i
  · simp
  · simp

@[expose] noncomputable def q2GramMat (ε : ℕ) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
  q2EmbedMat ε (gram K N)

theorem q2GramMat_apply [CharP K 2] (a b : Fin (2 * N + ε)) :
    q2GramMat (K := K) ε a b = if b = q2Par N ε a then 1 else 0 := by
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [q2GramMat, q2EmbedMat_apply, q2Par_q2Coord]
  simp only [(q2Coord N ε).injective.eq_iff]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
    rcases u with u | u <;> simp [sgn, Sum.map, CharTwo.neg_eq]
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, Matrix.one_apply]
    simp [eq_comm]

theorem q2GramMat_mul_mul_apply [CharP K 2] (M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)
    (a b : Fin (2 * N + ε)) :
    (q2GramMat ε * M * q2GramMat ε : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a b =
      M (q2Par N ε a) (q2Par N ε b) := by
  have h1 : ∀ d, (q2GramMat ε * M : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) a d =
      M (q2Par N ε a) d := by
    intro d
    rw [Matrix.mul_apply, Finset.sum_eq_single (q2Par N ε a)]
    · rw [q2GramMat_apply, ite_eq_left rfl, one_mul]
    · intro c _ hc
      rw [q2GramMat_apply, ite_eq_right hc, zero_mul]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (q2Par N ε b)]
  · rw [h1, q2GramMat_apply, ite_eq_left (q2Par_q2Par b).symm, mul_one]
  · intro c _ hc
    rw [q2GramMat_apply, ite_eq_right (fun h => hc (by rw [h, q2Par_q2Par])), mul_zero]
  · simp

theorem neg_one_matrix_eq_one [CharP K 2] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (-1 : Matrix ι ι K) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

theorem q2GramMat_mul_self [CharP K 2] :
    q2GramMat (K := K) (N := N) ε * q2GramMat ε = 1 := by
  rw [q2GramMat, ← q2EmbedMat_mul, gram_mul_gram, neg_one_matrix_eq_one, q2EmbedMat_one]

theorem q2GramMat_transpose [CharP K 2] :
    (q2GramMat (K := K) (N := N) ε)ᵀ = q2GramMat ε := by
  ext a b
  rw [transpose_apply, q2GramMat_apply, q2GramMat_apply]
  by_cases hab : b = q2Par N ε a
  · rw [ite_eq_left hab, ite_eq_left (by rw [hab, q2Par_q2Par])]
  · rw [ite_eq_right (fun h => hab (by rw [h, q2Par_q2Par])), ite_eq_right hab]

@[expose] noncomputable def q2SpJ : StatedSp N K :=
  ofSymplecticMat (gram K N) (by
    have hT : (gram K N)ᵀ = -gram K N := by
      rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose]
      simp [fromBlocks_neg]
    rw [hT, Matrix.neg_mul, gram_mul_gram, neg_neg, Matrix.one_mul])

theorem mat_q2SpJ : mat N K q2SpJ = gram K N := rfl

variable (ε) in
@[expose] noncomputable def q2Graph (hK : Nat.card K = 2) :
    MulAut (SpecialLinearGroup (Fin (2 * N + ε)) K) :=
  MulAut.conj (q2Embed ε hK q2SpJ) * CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut
    (2 * N + ε) K

theorem q2Embed_q2SpJ_inv [CharP K 2] (hK : Nat.card K = 2) :
    (q2Embed ε hK (q2SpJ (N := N)))⁻¹ = q2Embed ε hK q2SpJ := by
  rw [← map_inv]
  congr 1
  apply mat_injective
  have h1 : mat N K q2SpJ⁻¹ * mat N K q2SpJ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc mat N K q2SpJ⁻¹ = mat N K q2SpJ⁻¹ * (mat N K q2SpJ * mat N K q2SpJ) := by
        rw [mat_q2SpJ, gram_mul_gram, neg_one_matrix_eq_one, Matrix.mul_one]
    _ = mat N K q2SpJ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem coe_q2Graph [CharP K 2] (hK : Nat.card K = 2) (x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
    ((q2Graph ε hK x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
        q2GramMat ε * ((x⁻¹ : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)ᵀ * q2GramMat ε := by
  have h : q2Graph ε hK x = q2Embed ε hK q2SpJ *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (2 * N + ε) K x *
        (q2Embed ε hK q2SpJ)⁻¹ := rfl
  rw [h, q2Embed_q2SpJ_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
  rfl

theorem q2Graph_eq_self_iff [CharP K 2] (hK : Nat.card K = 2)
    (x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
    q2Graph ε hK x = x ↔ (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)ᵀ * q2GramMat ε *
      (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = q2GramMat ε := by
  set X : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
    (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) with hX
  set Y : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
    ((x⁻¹ : SpecialLinearGroup (Fin (2 * N + ε)) K) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)
    with hY
  have hXY : X * Y = 1 := by
    rw [hX, hY, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hYX : Y * X = 1 := by
    rw [hX, hY, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hP := q2GramMat_mul_self (K := K) (N := N) (ε := ε)
  have hext : q2Graph ε hK x = x ↔ ((q2Graph ε hK x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = X :=
    ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  rw [hext, coe_q2Graph]
  constructor
  · intro h
    change q2GramMat ε * Yᵀ * q2GramMat ε = X at h
    calc Xᵀ * q2GramMat ε * X = Xᵀ * q2GramMat ε * (q2GramMat ε * Yᵀ * q2GramMat ε) := by rw [h]
      _ = Xᵀ * (q2GramMat ε * q2GramMat ε) * Yᵀ * q2GramMat ε := by
          simp only [Matrix.mul_assoc]
      _ = (Y * X)ᵀ * q2GramMat ε := by rw [hP, Matrix.mul_one, Matrix.transpose_mul]
      _ = q2GramMat ε := by rw [hYX, Matrix.transpose_one, Matrix.one_mul]
  · intro h
    change q2GramMat ε * Yᵀ * q2GramMat ε = X
    calc q2GramMat ε * Yᵀ * q2GramMat ε = q2GramMat ε * (Yᵀ * (Xᵀ * q2GramMat ε * X)) := by
          rw [h, Matrix.mul_assoc]
      _ = q2GramMat ε * ((X * Y)ᵀ * q2GramMat ε * X) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = X := by
          rw [hXY, Matrix.transpose_one, Matrix.one_mul, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem q2Graph_q2Embed [CharP K 2] (hK : Nat.card K = 2) (y : StatedSp N K) :
    q2Graph ε hK (q2Embed ε hK y) = q2Embed ε hK y := by
  rw [q2Graph_eq_self_iff, coe_q2Embed, q2EmbedMat_transpose, q2GramMat, ← q2EmbedMat_mul,
    ← q2EmbedMat_mul, mat_transpose_mul_gram_mul]

theorem q2Graph_mem_q2Block [CharP K 2] (hK : Nat.card K = 2) {R : Finset (Fin N)}
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ q2Block ε K R) :
    q2Graph ε hK x ∈ q2Block ε K R := by
  have hx' : x⁻¹ ∈ q2Block ε K R := inv_mem hx
  rw [q2Block, mem_blockSpecialLinear] at hx' ⊢
  intro a b hab
  rw [coe_q2Graph, q2GramMat_mul_mul_apply, transpose_apply,
    hx' _ _ (by
      simp only [Finset.mem_compl, not_not] at hab ⊢
      rcases hab with h | h
      · exact Or.inr (q2Par_mem_planeCoordsQ2.2 h)
      · exact Or.inl (q2Par_mem_planeCoordsQ2.2 h)),
    Matrix.one_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (by rw [← q2Par_q2Par a, ← h', q2Par_q2Par])), ite_eq_right h]

theorem q2Graph_mul_self [CharP K 2] (hK : Nat.card K = 2) :
    q2Graph (N := N) ε hK * q2Graph ε hK = 1 := by
  ext1 x
  rw [MulAut.mul_apply, MulAut.one_apply]
  apply Subtype.ext
  rw [coe_q2Graph, ← map_inv, coe_q2Graph, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    q2GramMat_transpose, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [q2GramMat_mul_self, Matrix.one_mul, Matrix.mul_assoc, q2GramMat_mul_self, Matrix.mul_one]

end Graph

end CFSG.SeitzReduction.SymplecticPilot
