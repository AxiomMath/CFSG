module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {N ε : ℕ} {K : Type} [Field K]

theorem det_mat_statedSp_of_charTwo [CharP K 2] (y : StatedSp N K) : (mat N K y).det = 1 := by
  have hJ : (gram K N).det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det (gram_mul_gram (K := K) (n := N))
    rw [det_mul, h0, zero_mul, det_neg, det_one, mul_one] at h
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h.symm
  exact CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical.det_eq_one_of_mem hJ
    (g := (y : GL (Fin N ⊕ Fin N) K)) (mat_transpose_mul_gram_mul y)

variable (ε) in
@[expose] noncomputable def ctEmbed [CharP K 2] :
    StatedSp N K →* SpecialLinearGroup (Fin (2 * N + ε)) K where
  toFun y := ⟨q2EmbedMat ε (mat N K y), by rw [det_q2EmbedMat]; exact det_mat_statedSp_of_charTwo y⟩
  map_one' := Subtype.ext (by
    change q2EmbedMat ε (mat N K 1) = 1
    rw [map_one, q2EmbedMat_one])
  map_mul' y z := Subtype.ext (by
    change q2EmbedMat ε (mat N K (y * z)) = q2EmbedMat ε (mat N K y) * q2EmbedMat ε (mat N K z)
    rw [map_mul, q2EmbedMat_mul])

theorem coe_ctEmbed [CharP K 2] (y : StatedSp N K) :
    ((ctEmbed ε y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = q2EmbedMat ε (mat N K y) := rfl

theorem ctEmbed_apply_q2Coord [CharP K 2] (y : StatedSp N K) (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ((ctEmbed ε y : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε w) (q2Coord N ε w') =
        fromBlocks (mat N K y) 0 0 1 w w' := by
  rw [coe_ctEmbed, q2EmbedMat_apply]

theorem ctEmbed_injective [CharP K 2] : Function.Injective (ctEmbed (N := N) (K := K) ε) := by
  intro y z h
  apply mat_injective
  ext u v
  have := congrArg (fun A : SpecialLinearGroup (Fin (2 * N + ε)) K =>
    (A : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) (q2Coord N ε (Sum.inl u))
      (q2Coord N ε (Sum.inl v))) h
  simpa only [ctEmbed_apply_q2Coord, fromBlocks_apply₁₁] using this

theorem ctEmbed_mem_q2Block_iff [CharP K 2] {R : Finset (Fin N)} {y : StatedSp N K} :
    ctEmbed ε y ∈ q2Block ε K R ↔ y ∈ spBlock K Rᶜ := by
  rw [q2Block, mem_blockSpecialLinear, mem_spBlock]
  constructor
  · intro h u v huv
    have h1 := h (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) (by
      simp only [Finset.mem_compl, not_not, q2Coord_mem_planeCoordsQ2, inPlanes_inl]
      by_contra hc
      push Not at hc
      exact huv ⟨by simpa [mem_planeCoords] using hc.1, by simpa [mem_planeCoords] using hc.2⟩)
    rw [ctEmbed_apply_q2Coord, fromBlocks_apply₁₁] at h1
    rw [h1, Matrix.one_apply, Matrix.one_apply]
    simp only [(q2Coord N ε).injective.eq_iff, Sum.inl.injEq]
  · intro h a b hab
    obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
    obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
    rw [ctEmbed_apply_q2Coord, Matrix.one_apply]
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

variable (ε) in
@[expose] noncomputable def ctGraph [CharP K 2] : MulAut (SpecialLinearGroup (Fin (2 * N + ε)) K) :=
  MulAut.conj (ctEmbed ε (q2SpJ (N := N) (K := K))) *
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (2 * N + ε) K

theorem ctEmbed_q2SpJ_inv [CharP K 2] :
    (ctEmbed ε (q2SpJ (N := N) (K := K)))⁻¹ = ctEmbed ε q2SpJ := by
  rw [← map_inv]
  congr 1
  apply mat_injective
  have h1 : mat N K q2SpJ⁻¹ * mat N K q2SpJ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc mat N K q2SpJ⁻¹ = mat N K q2SpJ⁻¹ * (mat N K q2SpJ * mat N K q2SpJ) := by
        rw [mat_q2SpJ, gram_mul_gram, neg_one_matrix_eq_one, Matrix.mul_one]
    _ = mat N K q2SpJ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem coe_ctGraph [CharP K 2] (x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
    ((ctGraph ε x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) =
        q2GramMat ε * ((x⁻¹ : SpecialLinearGroup (Fin (2 * N + ε)) K) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)ᵀ * q2GramMat ε := by
  have h : ctGraph ε x = ctEmbed ε (q2SpJ (N := N) (K := K)) *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut (2 * N + ε) K x *
        (ctEmbed ε q2SpJ)⁻¹ := rfl
  rw [h, ctEmbed_q2SpJ_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
  rfl

theorem ctGraph_eq_self_iff [CharP K 2] (x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
    ctGraph ε x = x ↔ (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K)ᵀ * q2GramMat ε *
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
  have hext : ctGraph ε x = x ↔ ((ctGraph ε x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) = X :=
    ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
  rw [hext, coe_ctGraph]
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

theorem ctGraph_ctEmbed [CharP K 2] (y : StatedSp N K) : ctGraph ε (ctEmbed ε y) = ctEmbed ε y := by
  rw [ctGraph_eq_self_iff, coe_ctEmbed, q2EmbedMat_transpose, q2GramMat, ← q2EmbedMat_mul,
    ← q2EmbedMat_mul, mat_transpose_mul_gram_mul]

theorem ctGraph_mem_q2Block [CharP K 2] {R : Finset (Fin N)}
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : x ∈ q2Block ε K R) :
    ctGraph ε x ∈ q2Block ε K R := by
  have hx' : x⁻¹ ∈ q2Block ε K R := inv_mem hx
  rw [q2Block, mem_blockSpecialLinear] at hx' ⊢
  intro a b hab
  rw [coe_ctGraph, q2GramMat_mul_mul_apply, transpose_apply,
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

theorem ctGraph_mul_self [CharP K 2] : ctGraph (N := N) (K := K) ε * ctGraph ε = 1 := by
  ext1 x
  rw [MulAut.mul_apply, MulAut.one_apply]
  apply Subtype.ext
  rw [coe_ctGraph, ← map_inv, coe_ctGraph, inv_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    q2GramMat_transpose, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [q2GramMat_mul_self, Matrix.one_mul, Matrix.mul_assoc, q2GramMat_mul_self, Matrix.mul_one]

theorem ctGraph_ctGraph [CharP K 2] (x : SpecialLinearGroup (Fin (2 * N + ε)) K) :
    ctGraph ε (ctGraph ε x) = x := by
  rw [← MulAut.mul_apply, ctGraph_mul_self, MulAut.one_apply]

theorem exists_eq_ctEmbed_of_ctGraph_eq [CharP K 2] (hε : ε ≤ 1)
    {x : SpecialLinearGroup (Fin (2 * N + ε)) K} (hx : ctGraph ε x = x) :
    ∃ y : StatedSp N K, ctEmbed ε y = x := by
  have hE := (ctGraph_eq_self_iff x).1 hx
  set X : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K :=
    (x : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) K) with hX
  have hEa : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε,
      ∑ c, X (q2Coord N ε (Sum.map par id c)) (q2Coord N ε w) * X (q2Coord N ε c)
        (q2Coord N ε w') = q2GramMat ε (q2Coord N ε w) (q2Coord N ε w') := by
    intro w w'
    rw [← transpose_mul_q2GramMat_mul_apply, hE]
  have hP : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε, q2GramMat (K := K) ε (q2Coord N ε w)
      (q2Coord N ε w') = if w' = Sum.map par id w then 1 else 0 := by
    intro w w'
    rw [q2GramMat_apply, q2Par_q2Coord]
    simp only [(q2Coord N ε).injective.eq_iff]
  have hsplit : ∀ w w' : (Fin N ⊕ Fin N) ⊕ Fin ε,
      ∑ c, X (q2Coord N ε (Sum.map par id c)) (q2Coord N ε w) * X (q2Coord N ε c)
        (q2Coord N ε w') =
      ∑ u, X (q2Coord N ε (Sum.inl (par u))) (q2Coord N ε w) *
          X (q2Coord N ε (Sum.inl u)) (q2Coord N ε w') +
        ∑ e, X (q2Coord N ε (Sum.inr e)) (q2Coord N ε w) *
          X (q2Coord N ε (Sum.inr e)) (q2Coord N ε w') := by
    intro w w'
    rw [Fintype.sum_sum_type]
    rfl
  have hC : ∀ (e : Fin ε) (v : Fin N ⊕ Fin N),
      X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inl v)) = 0 := by
    intro e v
    have h1 := hEa (Sum.inl v) (Sum.inl v)
    rw [hsplit, hP, ite_eq_right (by
      simp only [Sum.map_inl, Sum.inl.injEq]
      rcases v with v | v <;> simp [par]), sum_fin_le_one hε _ e] at h1
    have h0 : ∑ u, X (q2Coord N ε (Sum.inl (par u))) (q2Coord N ε (Sum.inl v)) *
        X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) = 0 := by
      have := sum_mul_par_eq_zero (K := K)
        (fun u => X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)))
      rw [← this]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [h0, zero_add, ← sq] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  set A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) K :=
    fun u v => X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inl v)) with hA
  have hAsp : Aᵀ * gram K N * A = gram K N := by
    ext u v
    rw [transpose_mul_gram_mul_apply, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
    have h1 := hEa (Sum.inl u) (Sum.inl v)
    rw [hsplit, hP] at h1
    simp only [hC, zero_mul, Finset.sum_const_zero, add_zero] at h1
    have hsgn : ∀ c : Fin N ⊕ Fin N, sgn K c = 1 := by
      intro c
      rcases c with c | c
      · rfl
      · simp [sgn, CharTwo.neg_eq]
    simp only [hsgn, one_mul]
    rw [← (Equiv.sumComm (Fin N) (Fin N)).sum_comp]
    have hsw : ∀ c : Fin N ⊕ Fin N, (Equiv.sumComm (Fin N) (Fin N)) c = par c := fun _ => rfl
    simp only [hsw, par_par]
    rw [show (∑ c, A (par c) u * A c v) = ∑ c, X (q2Coord N ε (Sum.inl (par c)))
      (q2Coord N ε (Sum.inl u)) * X (q2Coord N ε (Sum.inl c)) (q2Coord N ε (Sum.inl v)) from rfl,
      h1]
    simp only [Sum.map_inl, Sum.inl.injEq]
  set y : StatedSp N K := ofSymplecticMat A hAsp with hy
  have hmy : mat N K y = A := mat_ofSymplecticMat A hAsp
  have hB : ∀ (u : Fin N ⊕ Fin N) (e : Fin ε),
      X (q2Coord N ε (Sum.inl u)) (q2Coord N ε (Sum.inr e)) = 0 := by
    intro u e
    set b : Fin N ⊕ Fin N → K := fun c => X (q2Coord N ε (Sum.inl (par c)))
      (q2Coord N ε (Sum.inr e)) with hb
    have hbA : b ᵥ* A = 0 := by
      ext v
      have h1 := hEa (Sum.inl v) (Sum.inr e)
      rw [hsplit, hP, ite_eq_right (by simp)] at h1
      simp only [hC, zero_mul, Finset.sum_const_zero, add_zero] at h1
      rw [vecMul, dotProduct, Pi.zero_apply, ← (Equiv.sumComm (Fin N) (Fin N)).sum_comp]
      have hsw : ∀ c : Fin N ⊕ Fin N, (Equiv.sumComm (Fin N) (Fin N)) c = par c := fun _ => rfl
      simp only [hsw, hb, hA, par_par]
      rw [← h1]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hAA : A * mat N K y⁻¹ = 1 := by rw [← hmy, ← map_mul, mul_inv_cancel, map_one]
    have hb0 : b = 0 := by
      rw [← vecMul_one b, ← hAA, ← vecMul_vecMul, hbA, zero_vecMul]
    have := congrFun hb0 (par u)
    simpa [hb, par_par] using this
  have hD : ∀ e : Fin ε, X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inr e)) = 1 := by
    intro e
    have h1 := hEa (Sum.inr e) (Sum.inr e)
    rw [hsplit, hP, ite_eq_left (by simp)] at h1
    simp only [hB, mul_zero, Finset.sum_const_zero, zero_add] at h1
    rw [sum_fin_le_one hε _ e, ← sq] at h1
    have h2 : (X (q2Coord N ε (Sum.inr e)) (q2Coord N ε (Sum.inr e)) + 1) ^ 2 = 0 := by
      rw [add_sq, h1, mul_one, one_pow, CharTwo.two_eq_zero, zero_mul, add_zero,
        CharTwo.add_self_eq_zero]
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
    rw [← CharTwo.neg_eq (X _ _), ← add_eq_zero_iff_neg_eq]
    exact h3
  refine ⟨y, Subtype.ext ?_⟩
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [ctEmbed_apply_q2Coord, hmy]
  rcases w with u | e <;> rcases w' with v | e'
  · rfl
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    exact (hB u e').symm
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    exact (hC e v).symm
  · obtain rfl : e = e' := Fin.ext (by have := e.2; have := e'.2; omega)
    rw [fromBlocks_apply₂₂, Matrix.one_apply_eq]
    exact (hD e).symm

theorem ctPlaneNe (p : Fin N) :
    q2Coord N ε (Sum.inl (Sum.inl p)) ≠ q2Coord N ε (Sum.inl (Sum.inr p)) := fun h =>
  Sum.inl_ne_inr (Sum.inl.inj ((q2Coord N ε).injective h))

theorem ctEmbed_longBlock [CharP K 2] (p : Fin N) (A : SL(2, K)) :
    ctEmbed ε (longBlock K N p A) = LinearPilot.pairEmbed (ctPlaneNe (ε := ε) p) A := by
  apply Subtype.ext
  ext a b
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [ctEmbed_apply_q2Coord, mat_longBlock, LinearPilot.pairEmbed_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton, (q2Coord N ε).injective.eq_iff]
  rcases w with (u | u) | e <;> rcases w' with (v | v) | e' <;>
    simp [CFSG.LieType.Steinberg.Sp.blockMat, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq] <;>
    by_cases h1 : u = p <;> by_cases h2 : v = p <;> simp_all [eq_comm]

theorem ctEmbed_mem_blockSpecialLinear_planeCoordsQ2 [CharP K 2] {R : Finset (Fin N)}
    {y : StatedSp N K} (hy : y ∈ spBlock K R) :
    ctEmbed ε y ∈ blockSpecialLinear (planeCoordsQ2 ε R) := by
  rw [mem_blockSpecialLinear]
  intro a b hab
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [ctEmbed_apply_q2Coord, Matrix.one_apply]
  simp only [(q2Coord N ε).injective.eq_iff]
  simp only [q2Coord_mem_planeCoordsQ2] at hab
  rcases w with u | i <;> rcases w' with v | j
  · have hu : ¬(u ∈ planeCoords R ∧ v ∈ planeCoords R) := by
      simp only [mem_planeCoords]
      simp only [inPlanes_inl] at hab
      rintro ⟨h1, h2⟩
      rcases hab with h | h
      · exact h h1
      · exact h h2
    rw [fromBlocks_apply₁₁, mem_spBlock.1 hy u v hu, Matrix.one_apply]
    simp only [Sum.inl.injEq]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, Matrix.one_apply]
    simp only [Sum.inr.injEq]

variable (ε) in
@[expose] noncomputable def ctGraphBlock [CharP K 2] (R : Finset (Fin N)) :
    MulAut (q2Block ε K R) where
  toFun x := ⟨ctGraph (N := N) ε (x : SpecialLinearGroup (Fin (2 * N + ε)) K),
    ctGraph_mem_q2Block x.2⟩
  invFun x := ⟨ctGraph (N := N) ε (x : SpecialLinearGroup (Fin (2 * N + ε)) K),
    ctGraph_mem_q2Block x.2⟩
  left_inv _ := Subtype.ext (ctGraph_ctGraph _)
  right_inv _ := Subtype.ext (ctGraph_ctGraph _)
  map_mul' x y := Subtype.ext (map_mul (ctGraph (N := N) (K := K) ε)
    (x : SpecialLinearGroup (Fin (2 * N + ε)) K) y)

theorem coe_ctGraphBlock [CharP K 2] {R : Finset (Fin N)} (x : q2Block ε K R) :
    ((ctGraphBlock ε R x : q2Block ε K R) : SpecialLinearGroup (Fin (2 * N + ε)) K) =
      ctGraph ε (x : SpecialLinearGroup (Fin (2 * N + ε)) K) := rfl

variable (ε K) in
@[expose] noncomputable def ctSpBlock [CharP K 2] (R : Finset (Fin N)) : Subgroup (q2Block ε K R) :=
  ((spBlock K Rᶜ).map (ctEmbed ε)).subgroupOf (q2Block ε K R)

theorem mem_ctSpBlock [CharP K 2] {R : Finset (Fin N)} {x : q2Block ε K R} :
    x ∈ ctSpBlock ε K R ↔ ∃ y ∈ spBlock K Rᶜ, ctEmbed ε y = x :=
  Iff.rfl

theorem ctGraphBlock_fix [CharP K 2] {R : Finset (Fin N)} {x : q2Block ε K R}
    (hx : x ∈ ctSpBlock ε K R) : ctGraphBlock ε R x = x := by
  obtain ⟨y, -, hy⟩ := mem_ctSpBlock.1 hx
  apply Subtype.ext
  rw [coe_ctGraphBlock, ← hy, ctGraph_ctEmbed]

end CFSG.SeitzReduction.SymplecticPilot
