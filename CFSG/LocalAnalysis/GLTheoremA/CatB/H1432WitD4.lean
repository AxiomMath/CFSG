module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.WitD4

open Matrix CFSG.Open CFSG.LieType.Universal.Spin CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def gBlk (x y c d : K) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  Matrix.fromBlocks !![1, 0, 0, 0; y, 1, 0, 0; 0, 0, 1, 0; 0, 0, d, 1]
    !![0, -x, 0, 0; x, -(x * y), 0, 0; 0, 0, 0, -c; 0, 0, c, -(c * d)]
    0 !![1, -y, 0, 0; 0, 1, 0, 0; 0, 0, 1, -d; 0, 0, 0, 1]

@[expose] def tBlk : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  Matrix.fromBlocks !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] 0 0
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def aBlk : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  Matrix.fromBlocks !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] 0 0
    !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def bBlk : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  Matrix.fromBlocks !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
    !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
    !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem gBlk_mul (x y c d x' y' c' d' : K) :
    gBlk x y c d * gBlk x' y' c' d' = gBlk (x + x') (y + y') (c + c') (d + d') := by
  unfold gBlk
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gBlk_zero : gBlk (0 : K) 0 0 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gBlk, Matrix.one_apply]

theorem gBlk_mul_neg (x y c d : K) : gBlk x y c d * gBlk (-x) (-y) (-c) (-d) = 1 := by
  rw [gBlk_mul]; simp only [add_neg_cancel]; exact gBlk_zero

theorem gBlk_neg_mul (x y c d : K) : gBlk (-x) (-y) (-c) (-d) * gBlk x y c d = 1 := by
  rw [gBlk_mul]; simp only [neg_add_cancel]; exact gBlk_zero

theorem tBlk_mul_self : tBlk * tBlk = (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tBlk, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem aBlk_mul_self : aBlk * aBlk = (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [aBlk, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem bBlk_mul_self : bBlk * bBlk = (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [bBlk, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem aBlk_bBlk_comm : aBlk (K := K) * bBlk (K := K) * aBlk (K := K) * bBlk (K := K) =
    tBlk (K := K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [aBlk, bBlk, tBlk, Matrix.mul_apply, Fin.sum_univ_four]

theorem gBlk_mul_tBlk (x y c d : K) : gBlk x y c d * tBlk = tBlk * gBlk x y c d := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [gBlk, tBlk, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem gBlk_isom (x y c d : K) (v : Fin 4 ⊕ Fin 4 → K) :
    ∑ i, (gBlk x y c d *ᵥ v) (Sum.inl i) * (gBlk x y c d *ᵥ v) (Sum.inr i) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i) := by
  simp [gBlk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    Matrix.fromBlocks]
  ring

theorem tBlk_isom (v : Fin 4 ⊕ Fin 4 → K) :
    ∑ i, (tBlk *ᵥ v) (Sum.inl i) * (tBlk *ᵥ v) (Sum.inr i) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i) := by
  simp [tBlk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    Matrix.fromBlocks]

theorem aBlk_isom (v : Fin 4 ⊕ Fin 4 → K) :
    ∑ i, (aBlk *ᵥ v) (Sum.inl i) * (aBlk *ᵥ v) (Sum.inr i) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i) := by
  simp [aBlk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    Matrix.fromBlocks]

theorem bBlk_isom (v : Fin 4 ⊕ Fin 4 → K) :
    ∑ i, (bBlk *ᵥ v) (Sum.inl i) * (bBlk *ᵥ v) (Sum.inr i) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i) := by
  simp [bBlk, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_four,
    Matrix.fromBlocks]
  ring

@[expose] def gU (x y c d : K) : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K :=
  ⟨gBlk x y c d, gBlk (-x) (-y) (-c) (-d), gBlk_mul_neg x y c d, gBlk_neg_mul x y c d⟩

@[expose] def tU : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K := ⟨tBlk, tBlk, tBlk_mul_self, tBlk_mul_self⟩

@[expose] def aU : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K := ⟨aBlk, aBlk, aBlk_mul_self, aBlk_mul_self⟩

@[expose] def bU : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K := ⟨bBlk, bBlk, bBlk_mul_self, bBlk_mul_self⟩

theorem gU_mul (x y c d x' y' c' d' : K) :
    gU x y c d * gU x' y' c' d' = gU (x + x') (y + y') (c + c') (d + d') :=
  Units.ext (gBlk_mul x y c d x' y' c' d')

theorem gU_zero : gU (0 : K) 0 0 0 = 1 := Units.ext gBlk_zero

theorem tU_mul_self : tU (K := K) * tU = 1 := Units.ext tBlk_mul_self

theorem aU_mul_self : aU (K := K) * aU = 1 := Units.ext aBlk_mul_self

theorem bU_mul_self : bU (K := K) * bU = 1 := Units.ext bBlk_mul_self

theorem aU_bU_comm : ⁅aU (K := K), bU (K := K)⁆ = tU := by
  rw [commutatorElement_def, inv_eq_of_mul_eq_one_right aU_mul_self,
    inv_eq_of_mul_eq_one_right bU_mul_self]
  exact Units.ext aBlk_bBlk_comm

theorem gU_pow_three [CharP K 3] (x y c d : K) : gU x y c d ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [pow_three, gU_mul, gU_mul]
  have e1 : x + (x + x) = 0 := by linear_combination x * h3
  have e2 : y + (y + y) = 0 := by linear_combination y * h3
  have e3 : c + (c + c) = 0 := by linear_combination c * h3
  have e4 : d + (d + d) = 0 := by linear_combination d * h3
  rw [e1, e2, e3, e4, gU_zero]

theorem statedQuadPlus_apply' (w : Fin 4 ⊕ Fin 4 → K) :
    StatedQuadPlus 4 K w = ∑ i, w (Sum.inl i) * w (Sum.inr i) :=
  (congrFun (coe_quadPlus 4 K) w).symm.trans (quadPlus_apply 4 K w)

@[expose] def tsT : Submodule K (Fin 4 ⊕ Fin 4 → K) :=
  Submodule.span K (Set.range fun i : Fin 3 => (Pi.single (Sum.inl (Fin.castLE (show 3 ≤ 4 by decide) i)) (1 : K) : Fin 4 ⊕ Fin 4 → K))

theorem tsT_finrank : Module.finrank K (tsT (K := K)) = 3 := by
  have hli : LinearIndependent K
      (fun i : Fin 3 => (Pi.single (Sum.inl (Fin.castLE (show 3 ≤ 4 by decide) i)) (1 : K) : Fin 4 ⊕ Fin 4 → K)) := by
    have h0 := (Pi.basisFun K (Fin 4 ⊕ Fin 4)).linearIndependent.comp
      (fun i : Fin 3 => Sum.inl (Fin.castLE (show 3 ≤ 4 by decide) i))
      (fun i j h => Fin.castLE_injective (show 3 ≤ 4 by decide) (Sum.inl_injective h))
    simpa [Function.comp_def] using h0
  unfold tsT
  rw [finrank_span_eq_card hli]
  simp

theorem tsT_le : tsT (K := K) ≤
    LinearMap.ker (LinearMap.pi fun j : Fin 4 => (LinearMap.proj (Sum.inr j) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] K)) := by
  unfold tsT
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  ext j
  simp [Pi.single_apply]

theorem tsT_singular (x : Fin 4 ⊕ Fin 4 → K) (hx : x ∈ tsT (K := K)) : quadPlus 4 K x = 0 := by
  have hy := LinearMap.mem_ker.1 (tsT_le hx)
  rw [quadPlus_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : x (Sum.inr i) = 0 := by simpa using congrFun hy i
  simp [this]

theorem gU_mem_omega [Finite K] [CharP K 3] (x y c d : K) :
    gU x y c d ∈ StatedOmega (StatedQuadPlus 4 K) := by
  refine CFSG.ComponentClassification.CatFC.DS81.ClOmega.mem_statedOmega_of_odd_order
    (coe_quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K)
    ⟨tsT, tsT_finrank, fun v hv => tsT_singular v hv⟩ (fun v => ?_) (m := 3) (by decide)
    (gU_pow_three x y c d)
  rw [statedQuadPlus_apply', statedQuadPlus_apply']
  exact gBlk_isom x y c d v

theorem aU_mem_isometry : aU (K := K) ∈
    CFSG.MatrixModel.isometryCore (StatedQuadPlus 4 K) :=
  Subgroup.subset_closure fun v => by
    rw [statedQuadPlus_apply', statedQuadPlus_apply']
    exact aBlk_isom v

theorem bU_mem_isometry : bU (K := K) ∈
    CFSG.MatrixModel.isometryCore (StatedQuadPlus 4 K) :=
  Subgroup.subset_closure fun v => by
    rw [statedQuadPlus_apply', statedQuadPlus_apply']
    exact bBlk_isom v

theorem tU_mem_omega : tU (K := K) ∈ StatedOmega (StatedQuadPlus 4 K) := by
  have := Subgroup.commutator_mem_commutator (aU_mem_isometry (K := K)) (bU_mem_isometry (K := K))
  rw [aU_bU_comm] at this
  exact this

theorem two_ne_zero_of_charThree [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h2
  omega

theorem scalar_entry (c : Kˣ) (i j : Fin 4 ⊕ Fin 4) :
    (Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 4) c :
      Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) i j = if i = j then (c : K) else 0 := by
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem tU_not_scalar [CharP K 3] : tU (K := K) ∉ StatedScalars (Fin 4 ⊕ Fin 4) K := by
  rintro ⟨c, hc⟩
  have h1 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K =>
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (Sum.inl 0) (Sum.inl 0)) hc
  have h2 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K =>
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) (Sum.inl 2) (Sum.inl 2)) hc
  simp only [scalar_entry, tU, tBlk, Matrix.fromBlocks_apply₁₁, if_true, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Units.val_mk,
    Sum.inl.injEq, Fin.isValue, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    Matrix.head_fin_const, Matrix.vecCons_const, Matrix.cons_val_succ, Fin.reduceEq,
    Sum.inl_ne_inr, if_false, reduceCtorEq] at h1 h2
  apply two_ne_zero_of_charThree (K := K)
  linear_combination h1 - h2

theorem gBlk_entry_01 (x y c d : K) : gBlk x y c d (Sum.inl 0) (Sum.inr 1) = -x := rfl

theorem gBlk_entry_YY01 (x y c d : K) : gBlk x y c d (Sum.inr 0) (Sum.inr 1) = -y := rfl

theorem gBlk_entry_23 (x y c d : K) : gBlk x y c d (Sum.inl 2) (Sum.inr 3) = -c := rfl

theorem gBlk_entry_YY23 (x y c d : K) : gBlk x y c d (Sum.inr 2) (Sum.inr 3) = -d := rfl

theorem gU_mem_scalars {x y c d : K}
    (h : gU x y c d ∈ StatedScalars (Fin 4 ⊕ Fin 4) K) : x = 0 ∧ y = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨c₀, hc⟩ := h
  have hent : ∀ i j : Fin 4 ⊕ Fin 4, i ≠ j → gBlk x y c d i j = 0 := by
    intro i j hij
    have := congrFun (congrFun (congrArg (fun g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K =>
      (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) hc) i) j
    rw [scalar_entry, if_neg hij] at this
    exact this.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact neg_eq_zero.1 (gBlk_entry_01 x y c d ▸ hent (Sum.inl 0) (Sum.inr 1) (by simp))
  · exact neg_eq_zero.1 (gBlk_entry_YY01 x y c d ▸ hent (Sum.inr 0) (Sum.inr 1) (by simp))
  · exact neg_eq_zero.1 (gBlk_entry_23 x y c d ▸ hent (Sum.inl 2) (Sum.inr 3) (by simp))
  · exact neg_eq_zero.1 (gBlk_entry_YY23 x y c d ▸ hent (Sum.inr 2) (Sum.inr 3) (by simp))

@[expose] def gHom [Finite K] [CharP K 3] :
    Multiplicative (K × K × K × K) →* StatedOmega (StatedQuadPlus 4 K) where
  toFun p := ⟨gU p.toAdd.1 p.toAdd.2.1 p.toAdd.2.2.1 p.toAdd.2.2.2, gU_mem_omega _ _ _ _⟩
  map_one' := Subtype.ext (by
    show gU (0 : K) 0 0 0 = 1
    exact gU_zero)
  map_mul' p q := Subtype.ext (by
    show gU (p.toAdd.1 + q.toAdd.1) (p.toAdd.2.1 + q.toAdd.2.1) (p.toAdd.2.2.1 + q.toAdd.2.2.1)
        (p.toAdd.2.2.2 + q.toAdd.2.2.2) =
      gU p.toAdd.1 p.toAdd.2.1 p.toAdd.2.2.1 p.toAdd.2.2.2 *
        gU q.toAdd.1 q.toAdd.2.1 q.toAdd.2.2.1 q.toAdd.2.2.2
    rw [gU_mul])

theorem pow_three_eq_one_mult [CharP K 3] (p : Multiplicative (K × K × K × K)) : p ^ 3 = 1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  ext <;> simp [h3]

theorem hasTwoLocalWitness_statedProj [Finite K] (f : ℕ) (hK : Nat.card K = 3 ^ f) :
    HasTwoLocalWitness (StatedProj (StatedOmega (StatedQuadPlus 4 K))) (4 * f) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let π : StatedOmega (StatedQuadPlus 4 K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    QuotientGroup.mk' _
  let ψ : Multiplicative (K × K × K × K) →* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    π.comp gHom
  let tS : StatedOmega (StatedQuadPlus 4 K) := ⟨tU, tU_mem_omega⟩
  have htS2 : tS ^ 2 = 1 := Subtype.ext (by
    show tU ^ 2 = 1
    rw [sq]; exact tU_mul_self)
  have hu2 : π tS ^ 2 = 1 := by rw [← map_pow, htS2, map_one]
  have hu1 : π tS ≠ 1 := by
    intro h
    have h' : tS ∈ (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
        (StatedOmega (StatedQuadPlus 4 K)) :=
      (QuotientGroup.eq_one_iff tS).1 h
    rw [Subgroup.mem_subgroupOf] at h'
    exact tU_not_scalar (K := K) h'
  have hord : orderOf (π tS) = 2 := orderOf_eq_prime hu2 hu1
  have hcomm : ∀ p : Multiplicative (K × K × K × K), Commute (ψ p) (π tS) := by
    intro p
    simp only [ψ, MonoidHom.comp_apply, Commute, SemiconjBy, ← map_mul]
    congr 1
    exact Subtype.ext (Units.ext (gBlk_mul_tBlk _ _ _ _))
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : gU p.toAdd.1 p.toAdd.2.1 p.toAdd.2.2.1 p.toAdd.2.2.2 ∈
        StatedScalars (Fin 4 ⊕ Fin 4) K := by
      have h2 : (gHom p : StatedOmega (StatedQuadPlus 4 K)) ∈
          (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf (StatedOmega (StatedQuadPlus 4 K)) :=
        (QuotientGroup.eq_one_iff _).1 hp
      exact (Subgroup.mem_subgroupOf).1 h2
    obtain ⟨hx, hy, hc, hd⟩ := gU_mem_scalars h1
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact Prod.ext hx (Prod.ext hy (Prod.ext hc hd))
  refine ⟨Subgroup.zpowers (π tS), ψ.range, fun h => hu1 (Subgroup.zpowers_eq_bot.1 h), ?_, ?_,
    ?_, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  · rintro x ⟨p, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [((hcomm p).zpow_right k).eq, mul_inv_cancel_right]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hh : h = (ψ p)⁻¹ * (ψ p * h * (ψ p)⁻¹) * ψ p := by group
      rw [hh, ← hk, mul_assoc, ← ((hcomm p).zpow_right k).eq, inv_mul_cancel_left]
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨p, hp⟩ := a.2
      obtain ⟨q, hq⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, hp⟩ := hz
      rw [← hp, ← map_pow, pow_three_eq_one_mult p, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    show Nat.card (K × K × K × K) = 3 ^ (4 * f)
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, hK]
    ring

theorem isElemAbelian_map_inj {p : ℕ} {A B : Type} [Group A] [Group B] (f : A →* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
      CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hE hx hy]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hE.2 x hx, map_one]

theorem hasTwoLocalWitness_of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    {r : ℕ} (e : S ≃* T) (h : HasTwoLocalWitness T r) : HasTwoLocalWitness S r := by
  obtain ⟨V, E, hV, hV2, hE, hEab, hEc⟩ := h
  refine ⟨V.map e.symm.toMonoidHom, E.map e.symm.toMonoidHom, ?_, hV2.map _, ?_, ?_, ?_⟩
  · exact fun hbot => hV ((Subgroup.map_eq_bot_iff_of_injective V e.symm.injective).1 hbot)
  · calc E.map e.symm.toMonoidHom
        ≤ (Subgroup.normalizer (V : Set T)).map e.symm.toMonoidHom := Subgroup.map_mono hE
      _ = Subgroup.normalizer ((V.map e.symm.toMonoidHom : Subgroup S) : Set S) :=
          Subgroup.map_equiv_normalizer_eq V e.symm
  · exact isElemAbelian_map_inj _ hEab
  · rw [Subgroup.card_map_of_injective e.symm.injective]; exact hEc

theorem exists_D4_of_catalogIs {S : Type} [Group S] {r : ℕ}
    (h : catalogIs S (S8.isD4of r)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.card = r ∧
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, he⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex
    (P := fun | .D 4 q => q.card = r | _ => False) h
  cases d with
  | D r' q =>
    by_cases hne : r' = 4
    · subst hne
      exact ⟨q, hv, hP, he⟩
    · split at hP
      · rename_i h4
        injection h4 with h5 _
        exact absurd h5 hne
      · exact hP.elim
  | _ => exact (hP : False).elim

theorem hasTwoLocalWitness_D4 {S : Type} [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) (f : ℕ) (hf : q.card = 3 ^ f) :
    HasTwoLocalWitness S (4 * f) := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
    (CFSG.Models.lieModel_D 4 q hv e).statedClassicalModel (by decide)
  have hK' : Nat.card K = 3 ^ f := by
    rw [hK, ← TauCeti.PrimePower.card_def, hf]
  exact hasTwoLocalWitness_of_mulEquiv eK (hasTwoLocalWitness_statedProj f hK')

end CFSG.LocalAnalysis.GLTheoremA.H1420.WitD4

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem i1432WitD4Three : ∀ (S : Type) [Group S] [Finite S],
    catalogIs S (S8.isD4of 3) → HasTwoLocalWitness S 4 := by
  intro S _ _ hS
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := WitD4.exists_D4_of_catalogIs hS
  exact WitD4.hasTwoLocalWitness_D4 q hv e 1 (hq.trans (by norm_num))

theorem i1432WitD4_holds : I1432WitD4 := by
  intro S _ _ hS
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := WitD4.exists_D4_of_catalogIs hS
  exact WitD4.hasTwoLocalWitness_D4 q hv e 3 (hq.trans (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
