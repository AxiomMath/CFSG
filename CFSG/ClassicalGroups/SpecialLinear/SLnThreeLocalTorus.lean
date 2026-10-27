module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalBlock
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalReal
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open Polynomial

variable {K : Type} [Field K] {n : ℕ}

private theorem exists_mulVec_single_ne (T : Matrix.SpecialLinearGroup (Fin 2) K) (hT : T ≠ 1) :
    ∃ q : Fin 2, (T : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single q 1 ≠ Pi.single q 1 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hT
  ext i j
  have := congrFun (h j) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

private def scalarGL (K : Type) [Field K] : Kˣ →* GL (Fin 2) K :=
  Units.map (Matrix.scalar (Fin 2)).toMonoidHom

private theorem coe_scalarGL (t : Kˣ) :
    ((scalarGL K t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (t : K) :=
  rfl

private theorem scalarGL_injective : Function.Injective (scalarGL K) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

private theorem det_scalarGL (t : Kˣ) :
    ((scalarGL K t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (t : K) ^ 2 := by
  simp [coe_scalarGL, Matrix.scalar_apply, Matrix.det_diagonal]

private def scalarBlocks (hn : n = 6 ∨ n = 7) : (Fin 3 → Kˣ) →* GL (Fin n) K :=
  (blkGL hn).comp (MonoidHom.compLeft (scalarGL K) (Fin 3))

private theorem scalarBlocks_injective (hn : n = 6 ∨ n = 7) :
    Function.Injective (scalarBlocks (K := K) hn) := by
  intro u u' h
  have h1 := blkGL_injective hn h
  funext i
  exact scalarGL_injective (congrFun h1 i)

private theorem scalarBlocks_mem (hn : n = 6 ∨ n = 7) (u : Fin 3 → Kˣ) (hu : ∏ i, u i = 1) :
    scalarBlocks hn u ∈ StatedSL n K := by
  apply blkGL_mem_statedSL
  show ∏ i, ((scalarGL K (u i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
  simp only [det_scalarGL]
  rw [Finset.prod_pow]
  have : ∏ i, ((u i : Kˣ) : K) = 1 := by
    rw [← Units.coe_prod, hu]
    rfl
  rw [this, one_pow]

private def scalarSL (hn : n = 6 ∨ n = 7) (u : Fin 3 → Kˣ) (hu : ∏ i, u i = 1) :
    StatedSL n K :=
  ⟨scalarBlocks hn u, scalarBlocks_mem hn u hu⟩

private theorem commute_scalarSL_c₀ (hn : n = 6 ∨ n = 7) (u : Fin 3 → Kˣ) (hu : ∏ i, u i = 1)
    (v : Multiplicative (Fin 3 → ZMod 3)) : Commute (scalarSL hn u hu) (c₀ K hn v) := by
  apply Subtype.ext
  show blkGL hn _ * blkGL hn _ = blkGL hn _ * blkGL hn _
  simp only [← map_mul]
  congr 1
  funext i
  apply Units.ext
  simp only [Pi.mul_apply, Units.val_mul, MonoidHom.compLeft_apply, Function.comp_apply,
    coe_scalarGL]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private theorem commute_scalarSL_scalarSL (hn : n = 6 ∨ n = 7) (u u' : Fin 3 → Kˣ)
    (hu : ∏ i, u i = 1) (hu' : ∏ i, u' i = 1) :
    Commute (scalarSL hn u hu) (scalarSL hn u' hu') := by
  apply Subtype.ext
  exact (Commute.all u u').map (scalarBlocks hn)

private theorem scalarSL_mulVec_vecOfBlk_iff (hn : n = 6 ∨ n = 7) (u : Fin 3 → Kˣ)
    (hu : ∏ i, u i = 1) (x : Blk → K) :
    ((scalarSL hn u hu : StatedSL n K) : GL (Fin n) K).val *ᵥ vecOfBlk hn x = vecOfBlk hn x ↔
      ∀ i q, (u i : K) * x (q, i) = x (q, i) := by
  show ((blkGL hn _ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ _ = _ ↔ _
  rw [blkGL_mulVec_vecOfBlk_iff]
  refine forall_congr' fun i => ?_
  simp only [MonoidHom.compLeft_apply, Function.comp_apply, coe_scalarGL, Matrix.scalar_apply]
  constructor
  · intro h q
    simpa [Matrix.mulVec_diagonal] using congrFun h q
  · intro h
    funext q
    simpa [Matrix.mulVec_diagonal] using h q

private theorem orderOf_scalarSL (hn : n = 6 ∨ n = 7) {p : ℕ} [Fact p.Prime] (u : Fin 3 → Kˣ)
    (hu : ∏ i, u i = 1) (hup : ∀ i, u i ^ p = 1) (hu1 : u ≠ 1) :
    orderOf (scalarSL hn u hu) = p := by
  have h1 : orderOf u = p := orderOf_eq_prime (funext hup) hu1
  have h2 := orderOf_injective (scalarBlocks (K := K) hn) (scalarBlocks_injective hn) u
  show orderOf (⟨scalarBlocks hn u, _⟩ : StatedSL n K) = p
  rw [Subgroup.orderOf_mk, h2, h1]

theorem two_le_pRank_centralizer_range_of_dvd_sub_one [Finite K] (hn : n = 6 ∨ n = 7) {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card K - 1) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ K hn).range : Set (StatedSL n K))) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact (Fact.out : p.Prime).one_lt.ne ht
  have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
  have hu₁ : ∏ i, (![t, t⁻¹, 1] : Fin 3 → Kˣ) i = 1 := by simp [Fin.prod_univ_three]
  have hu₂ : ∏ i, (![1, t, t⁻¹] : Fin 3 → Kˣ) i = 1 := by simp [Fin.prod_univ_three]
  have hmem : ∀ u hu, scalarSL hn u hu ∈
      Subgroup.centralizer ((c₀ K hn).range : Set (StatedSL n K)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, rfl⟩
    exact (commute_scalarSL_c₀ hn u hu v).symm.eq
  refine two_le_pRank_of_mulVec (hmem _ hu₁) (hmem _ hu₂) ?_ ?_
    (commute_scalarSL_scalarSL hn _ _ hu₁ hu₂) (w := vecOfBlk hn (Pi.single (0, 2) 1)) ?_ ?_
  · exact orderOf_scalarSL hn _ hu₁ (fun i => by fin_cases i <;> simp [htp])
      (fun h => ht1 (by simpa using congrFun h 0))
  · exact orderOf_scalarSL hn _ hu₂ (fun i => by fin_cases i <;> simp [htp])
      (fun h => ht1 (by simpa using congrFun h 1))
  · rw [scalarSL_mulVec_vecOfBlk_iff]
    intro i q
    fin_cases i <;> simp [Pi.single_apply]
  · rw [Ne, scalarSL_mulVec_vecOfBlk_iff]
    intro h
    have := h 2 0
    simp [Pi.single_apply] at this
    exact ht1 this

private noncomputable def cubeRootPoly (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

private theorem natDegree_cubeRootPoly : (cubeRootPoly K).natDegree = 2 := by
  unfold cubeRootPoly
  compute_degree!

private theorem cubeRootPoly_ne_zero : cubeRootPoly K ≠ 0 := by
  intro h
  have := natDegree_cubeRootPoly (K := K)
  rw [h] at this
  simp at this

private theorem blockS_sq_add : blockS K * blockS K + blockS K + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockS_mul_self, blockS]

private noncomputable def cubeRootRho (K : Type) [Field K] :
    AdjoinRoot (cubeRootPoly K) →+* Matrix (Fin 2) (Fin 2) K :=
  Ideal.Quotient.lift (Ideal.span {cubeRootPoly K}) (Polynomial.aeval (blockS K)).toRingHom (by
    intro g hg
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hg
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, cubeRootPoly, map_add, map_pow,
      aeval_X, map_one]
    rw [pow_two, blockS_sq_add, mul_zero])

private theorem cubeRootRho_root :
    cubeRootRho K (AdjoinRoot.root (cubeRootPoly K)) = blockS K := by
  refine (Ideal.Quotient.lift_mk (Ideal.span {cubeRootPoly K}) _ _).trans ?_
  simp

private theorem natCard_adjoinRoot [Finite K] :
    Nat.card (AdjoinRoot (cubeRootPoly K)) = Nat.card K ^ 2 := by
  let b := (AdjoinRoot.powerBasis (cubeRootPoly_ne_zero (K := K))).basis
  have h1 := Nat.card_congr b.equivFun.toEquiv
  rw [h1, Nat.card_fun]
  simp [natDegree_cubeRootPoly]

private theorem irreducible_cubeRootPoly [Finite K] (hq : Nat.card K % 3 = 2) :
    Irreducible (cubeRootPoly K) := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_natCard_mod_three hq
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [natDegree_cubeRootPoly]
    simp
  · intro x hx
    simp only [cubeRootPoly, IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
    let u : Kˣ := Units.mk0 x hx0
    have hu3 : u ^ 3 = 1 := by
      ext
      simpa [u] using hx3
    have hu1 : u ≠ 1 := by
      intro h
      have hx1 : x = 1 := congrArg Units.val h
      rw [hx1] at hx
      exact h3 (by linear_combination hx)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard u
    rw [Nat.card_units] at hdvd
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega

private theorem dvd_card_ker_aux {q k r p : ℕ} (hq : 2 ≤ q) (h : k * r = q ^ 2 - 1)
    (hr : r ∣ q - 1) (hpos : 0 < r) (hp : p ∣ q + 1) : p ∣ k := by
  obtain ⟨m, hm⟩ := hr
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hk : k = m * (q + 1) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h, hsq, hm]
    ring
  exact hk ▸ Dvd.dvd.mul_left hp m

private theorem exists_orderOf_commute_blockS [Finite K] (hq : Nat.card K % 3 = 2) {p : ℕ}
    [Fact p.Prime] (hp : p ∣ Nat.card K + 1) :
    ∃ T : Matrix.SpecialLinearGroup (Fin 2) K,
      orderOf T = p ∧ Commute (Matrix.SpecialLinearGroup.toGL T) (blockSGL K) := by
  haveI : Fact (Irreducible (cubeRootPoly K)) := ⟨irreducible_cubeRootPoly hq⟩
  have hK : 2 ≤ Nat.card K := by omega
  haveI : Finite (AdjoinRoot (cubeRootPoly K)) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_adjoinRoot]; positivity)
  let ρ := cubeRootRho K
  let u : (AdjoinRoot (cubeRootPoly K))ˣ →* GL (Fin 2) K := Units.map ρ.toMonoidHom
  let δ : (AdjoinRoot (cubeRootPoly K))ˣ →* Kˣ := Matrix.GeneralLinearGroup.det.comp u
  have hcard := Subgroup.card_ker_mul_card_range δ
  rw [Nat.card_units, natCard_adjoinRoot] at hcard
  have hr : Nat.card δ.range ∣ Nat.card K - 1 := by
    have := Subgroup.card_subgroup_dvd_card δ.range
    rwa [Nat.card_units] at this
  have hker : p ∣ Nat.card δ.ker := dvd_card_ker_aux hK hcard hr Nat.card_pos hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hker
  have hx1 : δ (x : (AdjoinRoot (cubeRootPoly K))ˣ) = 1 := x.2
  have hdet : (ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) : AdjoinRoot (cubeRootPoly K))).det = 1 := by
    have := congrArg (fun a : Kˣ => (a : K)) hx1
    simpa [δ, u] using this
  refine ⟨⟨ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) : AdjoinRoot (cubeRootPoly K)), hdet⟩, ?_, ?_⟩
  · have h1 := orderOf_injective (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := K))
      Matrix.SpecialLinearGroup.toGL_injective
      (⟨ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) : AdjoinRoot (cubeRootPoly K)), hdet⟩ :
        Matrix.SpecialLinearGroup (Fin 2) K)
    rw [← h1]
    have h2 := orderOf_injective u (Units.map_injective (RingHom.injective ρ))
      (x : (AdjoinRoot (cubeRootPoly K))ˣ)
    have h3 : Matrix.SpecialLinearGroup.toGL (⟨ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) :
        AdjoinRoot (cubeRootPoly K)), hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) K) =
          u (x : (AdjoinRoot (cubeRootPoly K))ˣ) := Units.ext rfl
    rw [h3, h2, Subgroup.orderOf_coe, hx]
  · apply Units.ext
    show ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) : AdjoinRoot (cubeRootPoly K)) * blockS K =
      blockS K * ρ ((x : (AdjoinRoot (cubeRootPoly K))ˣ) : AdjoinRoot (cubeRootPoly K))
    rw [← cubeRootRho_root, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm _ _

theorem two_le_pRank_centralizer_range_of_dvd_add_one [Finite K] (hq : Nat.card K % 3 = 2)
    (hn : n = 6 ∨ n = 7) {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card K + 1) :
    2 ≤ pRank p (Subgroup.centralizer ((c₀ K hn).range : Set (StatedSL n K))) := by
  obtain ⟨T, hTo, hTc⟩ := exists_orderOf_commute_blockS hq hp
  have hT1 : T ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hTo
    exact (Fact.out : p.Prime).one_lt.ne hTo
  obtain ⟨q', hq'⟩ := exists_mulVec_single_ne T hT1
  have hmem : ∀ j, blockEmb hn j T ∈
      Subgroup.centralizer ((c₀ K hn).range : Set (StatedSL n K)) := by
    intro j
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, rfl⟩
    exact (commute_blockEmb_c₀ hn j T v (hTc.pow_right _)).symm.eq
  exact two_le_pRank_of_mulVec (hmem 0) (hmem 1) (by rw [orderOf_blockEmb, hTo])
    (by rw [orderOf_blockEmb, hTo]) (commute_blockEmb_blockEmb hn (by decide) T T)
    (w := vecOfBlk hn (Pi.single (q', 1) 1)) (blockEmb_mulVec_vecOfBlk_of_ne hn (by decide) T q')
    (blockEmb_mulVec_vecOfBlk_ne_of hn 1 T q' hq')

private theorem le_pRank_of_pi_zpowers {G : Type*} [Group G] [Finite G] {M : Type*}
    [CommGroup M] {p : ℕ} [Fact p.Prime] {t : M} (ht : orderOf t = p) {k : ℕ} {H : Subgroup G}
    (f : (Fin k → Subgroup.zpowers t) →* G) (hf : Function.Injective f) (hH : f.range ≤ H) :
    k ≤ pRank p H := by
  refine CFSG.SectionRank.le_pRank_of_injective (Fact.out : p.Prime).one_lt
    (fun a b => mul_comm a b) (fun a => ?_) ?_ f hf hH
  · funext i
    have h := pow_card_eq_one' (G := Subgroup.zpowers t) (x := a i)
    rwa [Nat.card_zpowers, ht] at h
  · rw [Nat.card_pi]
    simp [Nat.card_zpowers, ht]

private def lastMat (hn : n = 6 ∨ n = 7) (z : K) : Matrix (Fin n) (Fin n) K :=
  Matrix.reindex (blkEquiv hn).symm (blkEquiv hn).symm
    (Matrix.fromBlocks 1 0 0 (Matrix.scalar (Fin (n - 6)) z))

private theorem lastMat_mul (hn : n = 6 ∨ n = 7) (z z' : K) :
    lastMat hn (z * z') = lastMat hn z * lastMat hn z' := by
  simp only [lastMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, map_mul]

private theorem lastMat_one (hn : n = 6 ∨ n = 7) : lastMat hn (1 : K) = 1 := by
  simp [lastMat, Matrix.fromBlocks_one]

private theorem det_lastMat (hn : n = 6 ∨ n = 7) (z : K) :
    (lastMat hn z).det = z ^ (n - 6) := by
  simp [lastMat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

private theorem embMat_mul_lastMat (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) (z : K) :
    embMat hn X * lastMat hn z = lastMat hn z * embMat hn X := by
  simp only [embMat, lastMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]

private theorem embMat_mul_lastMat_apply (hn : n = 6 ∨ n = 7) (X : Matrix Blk Blk K) (z : K)
    (b b' : Blk) :
    (embMat hn X * lastMat hn z) ((blkEquiv hn).symm (Sum.inl b))
      ((blkEquiv hn).symm (Sum.inl b')) = X b b' := by
  simp only [embMat, lastMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Matrix.fromBlocks_apply₁₁]

private def lastGL (hn : n = 6 ∨ n = 7) : Kˣ →* GL (Fin n) K :=
  Units.map ({ toFun := lastMat hn, map_one' := lastMat_one hn, map_mul' := lastMat_mul hn } :
    K →* Matrix (Fin n) (Fin n) K)

private theorem coe_lastGL (hn : n = 6 ∨ n = 7) (z : Kˣ) :
    ((lastGL hn z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = lastMat hn (z : K) :=
  rfl

private theorem commute_lastGL_blkGL (hn : n = 6 ∨ n = 7) (z : Kˣ) (M : Fin 3 → GL (Fin 2) K) :
    Commute (lastGL hn z) (blkGL hn M) := by
  show lastGL hn z * blkGL hn M = blkGL hn M * lastGL hn z
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_lastGL, coe_blkGL]
  exact (embMat_mul_lastMat hn _ _).symm

private theorem commute_scalarBlocks_blkGL (hn : n = 6 ∨ n = 7) (u : Fin 3 → Kˣ)
    (M : Fin 3 → GL (Fin 2) K) : Commute (scalarBlocks hn u) (blkGL hn M) := by
  show blkGL hn _ * blkGL hn _ = blkGL hn _ * blkGL hn _
  simp only [← map_mul]
  congr 1
  funext i
  apply Units.ext
  simp only [Pi.mul_apply, Units.val_mul, MonoidHom.compLeft_apply, Function.comp_apply,
    coe_scalarGL]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private def torusHom (hn : n = 6 ∨ n = 7) : (Fin 3 → Kˣ) →* GL (Fin n) K where
  toFun y := scalarBlocks hn y * lastGL hn ((∏ i, y i)⁻¹ ^ 2)
  map_one' := by simp
  map_mul' y y' := by
    have hc : Commute (lastGL hn ((∏ i, y i)⁻¹ ^ 2)) (scalarBlocks hn y') :=
      commute_lastGL_blkGL hn _ _
    have hz : (∏ i, (y * y') i)⁻¹ ^ 2 = (∏ i, y i)⁻¹ ^ 2 * (∏ i, y' i)⁻¹ ^ 2 := by
      simp only [Pi.mul_apply, Finset.prod_mul_distrib, mul_inv, mul_pow]
    rw [hz, map_mul, map_mul, hc.mul_mul_mul_comm]

private theorem det_torusHom (hn : n = 6 ∨ n = 7) (h7 : n = 7) (y : Fin 3 → Kˣ) :
    ((torusHom hn y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 : (∏ i, ((scalarGL K (y i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) =
      ((∏ i, y i : Kˣ) : K) ^ 2 := by
    simp only [det_scalarGL]
    rw [Finset.prod_pow, Units.coe_prod]
  have h2 : n - 6 = 1 := by omega
  show ((scalarBlocks hn y * lastGL hn ((∏ i, y i)⁻¹ ^ 2) : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K).det = 1
  rw [Units.val_mul, Matrix.det_mul, coe_lastGL, det_lastMat, h2, pow_one]
  change (blkGL hn (fun i => scalarGL K (y i)) : Matrix (Fin n) (Fin n) K).det * _ = 1
  rw [det_blkGL, h1, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  simp

private def torusSL (hn : n = 6 ∨ n = 7) (h7 : n = 7) : (Fin 3 → Kˣ) →* StatedSL n K :=
  (torusHom hn).codRestrict (StatedSL n K) fun y =>
    CFSG.Open.StatedAPI.mem_statedSL_of_det (det_torusHom hn h7 y)

private theorem commute_torusSL_c₀ (hn : n = 6 ∨ n = 7) (h7 : n = 7) (y : Fin 3 → Kˣ)
    (v : Multiplicative (Fin 3 → ZMod 3)) : Commute (torusSL hn h7 y) (c₀ K hn v) := by
  show torusSL hn h7 y * c₀ K hn v = c₀ K hn v * torusSL hn h7 y
  apply Subtype.ext
  exact ((commute_scalarBlocks_blkGL hn y _).mul_left (commute_lastGL_blkGL hn _ _)).eq

private theorem torusHom_apply_blk (hn : n = 6 ∨ n = 7) (y : Fin 3 → Kˣ) (i : Fin 3) :
    ((torusHom hn y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      ((blkEquiv hn).symm (Sum.inl (0, i))) ((blkEquiv hn).symm (Sum.inl (0, i))) = y i := by
  show (embMat hn (Matrix.blockDiagonal fun j =>
    ((scalarGL K (y j) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      lastMat hn (((∏ j, y j)⁻¹ ^ 2 : Kˣ) : K)) _ _ = _
  rw [embMat_mul_lastMat_apply]
  simp [coe_scalarGL]

private theorem torusSL_injective (hn : n = 6 ∨ n = 7) (h7 : n = 7) :
    Function.Injective (torusSL (K := K) hn h7) := by
  intro y y' h
  funext i
  apply Units.ext
  have h1 := congrArg (fun g : StatedSL n K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    ((blkEquiv hn).symm (Sum.inl (0, i))) ((blkEquiv hn).symm (Sum.inl (0, i)))) h
  simpa only [torusSL, MonoidHom.codRestrict_apply, torusHom_apply_blk] using h1

theorem three_le_pRank_centralizer_range_of_dvd_sub_one [Finite K] (hn : n = 6 ∨ n = 7)
    (h7 : n = 7) {p : ℕ} [Fact p.Prime] (hp : p ∣ Nat.card K - 1) :
    3 ≤ pRank p (Subgroup.centralizer ((c₀ K hn).range : Set (StatedSL n K))) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  refine le_pRank_of_pi_zpowers ht
    ((torusSL hn h7).comp (MonoidHom.compLeft (Subgroup.zpowers t).subtype (Fin 3)))
    ((torusSL_injective hn h7).comp fun a b h => funext fun i => Subtype.ext (congrFun h i)) ?_
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, rfl⟩
  exact (commute_torusSL_c₀ hn h7 _ v).symm.eq

end CFSG.ClassicalGroups.SLnThreeLocal
