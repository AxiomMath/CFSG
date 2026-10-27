module

public import CFSG.GH74.GLS.Stage2.Final.ModelBlock
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.ClassicalInvolution.WeakCT.Defs

public section

namespace CFSG.GH74.GLS.LU.Local

open CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock Subgroup
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT Matrix
open scoped MatrixGroups

theorem exists_two_subgroup_of_model {F G : Type} [Field F] [Finite F] [Group G] [Finite G]
    (M : ModelData F) (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hU : Nat.card ↥M.U2 = m * Nat.card ↥M.H2)
    (hZ : Nat.card ↥(Subgroup.center ↥M.K4) ∣ m)
    (ψ : ↥M.K4 →* G) (hker : ψ.ker ≤ Subgroup.center ↥M.K4) (hx : ψ M.xK = 1) :
    ∃ T : Subgroup G, T ≤ ψ.range ∧ (∀ t ∈ T, t * ψ M.yK = ψ M.yK * t) ∧ IsPGroup 2 T ∧
      2 ^ (1 + 2 * (Nat.card ↥M.H2).factorization 2) ≤ Nat.card ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Nsub M with hN
  set R : Subgroup G := N.map ψ with hR
  have hxy : ψ M.xyK = ψ M.yK := by
    rw [← M.xK_mul_yK, map_mul, hx, one_mul]
  have hRc : ∀ r ∈ R, r * ψ M.yK = ψ M.yK * r := by
    rintro _ ⟨g, hg, rfl⟩
    rcases (mem_Nsub_iff M).1 hg with h | h
    · rw [← map_mul, ← map_mul, h]
    · have h' : g * M.yK = M.xyK * g := by
        calc g * M.yK = (g * M.yK * g⁻¹) * g := by group
          _ = M.xyK * g := by rw [h]
      rw [← map_mul, h', map_mul, hxy]
  have hcenD : Subgroup.center ↥M.K4 ≤ Dsub M := fun c hc =>
    mem_Dsub.2 ((Subgroup.mem_center_iff.1 hc M.yK).symm)
  have hNle : ψ.ker ≤ N := hker.trans (hcenD.trans (Dsub_le_Nsub M))
  let ψN : ↥N →* G := ψ.comp N.subtype
  have hψNr : ψN.range = R := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hψNk : ψN.ker = ψ.ker.subgroupOf N := by
    ext x
    simp [ψN, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hcard := Subgroup.card_ker_mul_card_range ψN
  rw [hψNr, hψNk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv, card_Nsub M h2,
    ModelOrd.card_centralizer_yK M h2, hU] at hcard
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := ↥M.U2)
    rw [hU, zero_mul] at this
    exact lt_irrefl _ this
  have hH0 : Nat.card ↥M.H2 ≠ 0 := Nat.card_pos.ne'
  have ha0 : Nat.card ↥ψ.ker ≠ 0 := Nat.card_pos.ne'
  have hb0 : Nat.card ↥R ≠ 0 := Nat.card_pos.ne'
  have hadvd : Nat.card ↥ψ.ker ∣ m := (Subgroup.card_dvd_of_le hker).trans hZ
  have hv1 : (Nat.card ↥ψ.ker).factorization 2 ≤ m.factorization 2 :=
    (Nat.factorization_le_iff_dvd ha0 hm0).2 hadvd 2
  have hv2 : (Nat.card ↥ψ.ker).factorization 2 + (Nat.card ↥R).factorization 2 =
      1 + (m.factorization 2 + 2 * (Nat.card ↥M.H2).factorization 2) := by
    have h := congrArg (fun n => n.factorization 2) hcard
    rw [Nat.factorization_mul ha0 hb0, Nat.factorization_mul (by norm_num) (by positivity),
      Nat.factorization_mul (mul_ne_zero hm0 hH0) hH0, Nat.factorization_mul hm0 hH0] at h
    simp only [Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h
    omega
  have hvR : 1 + 2 * (Nat.card ↥M.H2).factorization 2 ≤ (Nat.card ↥R).factorization 2 := by omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
  refine ⟨(P : Subgroup ↥R).map R.subtype, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans (Subgroup.map_le_range ψ N)
  · intro t ht
    exact hRc t (Subgroup.map_subtype_le _ ht)
  · exact P.isPGroup'.map R.subtype
  · rw [Subgroup.card_map_of_injective R.subtype_injective, Sylow.card_eq_multiplicity]
    exact Nat.pow_le_pow_right (by norm_num) hvR

theorem hU_lin (K : Type) [Field K] [Finite K] :
    Nat.card ↥(ModelData.lin K).U2 = (Nat.card K - 1) * Nat.card ↥(ModelData.lin K).H2 := by
  have hU : Nat.card ↥(ModelData.lin K).U2 = Nat.card (GL (Fin 2) K) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  have hH : Nat.card ↥(ModelData.lin K).H2 = Nat.card ↥(StatedSL 2 K) := rfl
  rw [hU, hH, ModelOrd.card_gl_two, ModelOrd.card_statedSL_two]
  ring

theorem hZ_lin (K : Type) [Field K] [Finite K] :
    Nat.card ↥(Subgroup.center ↥(ModelData.lin K).K4) ∣ Nat.card K - 1 := by
  have h1 : Nat.card ↥(Subgroup.center ↥(ModelData.lin K).K4) =
      Nat.card ↥(Subgroup.center SL(4, K)) :=
    by
      change Nat.card ↥(Subgroup.center ↥(StatedSL 4 K)) = _
      rw [← CFSG.LieType.Universal.Unitary.map_center_mulEquiv (specialLinearGroupEquivStatedSL 4 K)]
      exact (Subgroup.card_map_of_injective (K := Subgroup.center SL(4, K))
        (f := (specialLinearGroupEquivStatedSL 4 K).toMonoidHom)
        (specialLinearGroupEquivStatedSL 4 K).injective)
  have hmax : max (Fintype.card (Fin 4)) 1 = 4 := by simp
  have : NeZero (max (Fintype.card (Fin 4)) 1) := ⟨by omega⟩
  rw [h1, Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 4) (R := K)).toEquiv, hmax,
    ← Nat.card_units K]
  exact Subgroup.card_subgroup_dvd_card _


theorem blk4_apply_aux {K : Type} [Field K] (X Y : Matrix (Fin 2) (Fin 2) K) (a b : Fin 4) :
    blk4 X Y a b =
      (fromBlocks X 0 0 Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (e4.symm a) (e4.symm b) := by
  rw [blk4_eq_reindex]
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem e4_symm_0 : e4.symm (0 : Fin 4) = Sum.inl (0 : Fin 2) := by decide
theorem e4_symm_1 : e4.symm (1 : Fin 4) = Sum.inl (1 : Fin 2) := by decide
theorem e4_symm_2 : e4.symm (2 : Fin 4) = Sum.inr (0 : Fin 2) := by decide
theorem e4_symm_3 : e4.symm (3 : Fin 4) = Sum.inr (1 : Fin 2) := by decide

theorem blockMat_zero_neg (K : Type) [Field K] :
    blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) K) = blk4 (-1) 1 := by
  ext a b
  rw [blockMat_apply, blk4_apply_aux]
  fin_cases a <;> fin_cases b <;> simp [e4_symm_0, e4_symm_1, e4_symm_2, e4_symm_3]

theorem blockMat_two_neg (K : Type) [Field K] :
    blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) K) = blk4 1 (-1) := by
  ext a b
  rw [blockMat_apply, blk4_apply_aux]
  fin_cases a <;> fin_cases b <;> simp [e4_symm_0, e4_symm_1, e4_symm_2, e4_symm_3]

@[expose] def negOneSL2 (K : Type) [Field K] : SL(2, K) := ⟨-1, by simp [Matrix.det_neg]⟩

theorem e_blockSL2_zero (K : Type) [Field K] :
    specialLinearGroupEquivStatedSL 4 K (blockSL2 K 3 0 (negOneSL2 K)) = (ModelData.lin K).yK := by
  apply Subtype.ext
  apply Units.ext
  have h : ((blockSL2 K 3 0 (negOneSL2 K) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) K) := rfl
  show ((blockSL2 K 3 0 (negOneSL2 K) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = _
  rw [h, blockMat_zero_neg]
  simp [ModelData.yK, yGL, coe_diagGL]

theorem e_blockSL2_two (K : Type) [Field K] :
    specialLinearGroupEquivStatedSL 4 K (blockSL2 K 3 2 (negOneSL2 K)) = (ModelData.lin K).xyK := by
  apply Subtype.ext
  apply Units.ext
  have h : ((blockSL2 K 3 2 (negOneSL2 K) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) =
      blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) K) := rfl
  show ((blockSL2 K 3 2 (negOneSL2 K) : SL(4, K)) : Matrix (Fin 4) (Fin 4) K) = _
  rw [h, blockMat_two_neg]
  simp [ModelData.xyK, xyGL, coe_diagGL]


theorem exists_two_subgroup_lin {K G : Type} [Field K] [Finite K] [Group G] [Finite G]
    (h2 : (2 : K) ≠ 0) (ψ : SL(4, K) →* G) (hker : ψ.ker ≤ Subgroup.center SL(4, K))
    (hxy : ψ (blockSL2 K 3 0 (negOneSL2 K)) = ψ (blockSL2 K 3 2 (negOneSL2 K))) :
    ∃ T : Subgroup G, T ≤ ψ.range ∧
      (∀ t ∈ T, t * ψ (blockSL2 K 3 0 (negOneSL2 K)) = ψ (blockSL2 K 3 0 (negOneSL2 K)) * t) ∧
      IsPGroup 2 T ∧ 2 ^ (1 + 2 * (Nat.card ↥(StatedSL 2 K)).factorization 2) ≤ Nat.card ↥T := by
  let ψ' : ↥(ModelData.lin K).K4 →* G :=
    ψ.comp (specialLinearGroupEquivStatedSL 4 K).symm.toMonoidHom
  have hker' : ψ'.ker ≤ Subgroup.center ↥(ModelData.lin K).K4 := by
    intro x hx
    let x' : ↥(StatedSL 4 K) := x
    have h1 : (specialLinearGroupEquivStatedSL 4 K).symm x' ∈ ψ.ker := hx
    have h3 := (MulEquivClass.apply_mem_center_iff (specialLinearGroupEquivStatedSL 4 K)).2
      (hker h1)
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3
  have hy' : ψ' (ModelData.lin K).yK = ψ (blockSL2 K 3 0 (negOneSL2 K)) := by
    show ψ ((specialLinearGroupEquivStatedSL 4 K).symm (ModelData.lin K).yK) = _
    rw [← e_blockSL2_zero K, MulEquiv.symm_apply_apply]
  have hxy' : ψ' (ModelData.lin K).xyK = ψ (blockSL2 K 3 2 (negOneSL2 K)) := by
    show ψ ((specialLinearGroupEquivStatedSL 4 K).symm (ModelData.lin K).xyK) = _
    rw [← e_blockSL2_two K, MulEquiv.symm_apply_apply]
  have hx' : ψ' (ModelData.lin K).xK = 1 := by
    have h1 : ψ' (ModelData.lin K).xyK = ψ' (ModelData.lin K).yK := by rw [hy', hxy', hxy]
    rw [← (ModelData.lin K).xK_mul_yK, map_mul] at h1
    simpa using h1
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_two_subgroup_of_model (ModelData.lin K) h2 (hU_lin K)
    (hZ_lin K) ψ' hker' hx'
  refine ⟨T, fun x hx => ?_, fun t ht => ?_, hT3, hT4⟩
  · obtain ⟨y, hy⟩ := hT1 hx
    exact ⟨(specialLinearGroupEquivStatedSL 4 K).symm y, hy⟩
  · rw [← hy']
    exact hT2 t ht

open CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial in
theorem hU_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card ↥(ModelData.uni hF).U2 = (p ^ f + 1) * Nat.card ↥(ModelData.uni hF).H2 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact hf
  have h : UnitaryFieldData p f F := ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hH : (Nat.card ↥(ModelData.uni hF).H2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    have := ModelOrd.card_statedSU_int h (n := 2) (by norm_num)
    rw [ModelOrd.prod_Icc_two_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  have hU : (Nat.card ↥(ModelData.uni hF).U2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * ((((p ^ f : ℕ) : ℤ) + 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1)) := by
    have := ModelOrd.card_uniGL_int h (n := 2) (by norm_num)
    rw [ModelOrd.prod_Icc_one_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [hU, hH]
  ring

open CFSG.LieType.Universal.Unitary in
theorem hZ_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card ↥(Subgroup.center ↥(ModelData.uni hF).K4) ∣ p ^ f + 1 := by
  have hZ := (isQuasisimple_statedSU_of_card hF (n := 4) (by norm_num) (fun h => by simp at h)).2
  have hk := (CFSG.LinearGroups.unitary_scalar_kernel (Fact.out : p.Prime) hF (n := 4)
    (by norm_num)).2.2
  change Nat.card ↥(Subgroup.center ↥(StatedSU 4 (p ^ f) F)) ∣ _
  rw [hZ, hk]
  exact Nat.gcd_dvd_right _ _

open CFSG.LieType.Universal.Unitary in
@[expose] def negOneSu (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) : Su K p f 2 :=
  ⟨-1, by
    have h := (ModelData.uni hK).neg_one_mem_H2
    change (-1 : GL (Fin 2) K) ∈ StatedSU 2 (p ^ f) K at h
    rwa [← SUid_eq_statedSU hK 2] at h⟩

open CFSG.LieType.Universal.Unitary in
theorem e_blockEmb2_zero {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4) : Su K p f 4 ≃* ↥(StatedSU 4 (p ^ f) K))
      (blockEmb2 K p f 3 0 (negOneSu K p f hK)) = (ModelData.uni hK).yK := by
  apply Subtype.ext
  apply Units.ext
  have h : (((blockEmb2 K p f 3 0 (negOneSu K p f hK) : Su K p f 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = blockMat 4 0 (-1 : Matrix (Fin 2) (Fin 2) K) := rfl
  show (((blockEmb2 K p f 3 0 (negOneSu K p f hK) : Su K p f 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = _
  rw [h, blockMat_zero_neg]
  simp [ModelData.yK, yGL, coe_diagGL]

open CFSG.LieType.Universal.Unitary in
theorem e_blockEmb2_two {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) :
    (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4) : Su K p f 4 ≃* ↥(StatedSU 4 (p ^ f) K))
      (blockEmb2 K p f 3 2 (negOneSu K p f hK)) = (ModelData.uni hK).xyK := by
  apply Subtype.ext
  apply Units.ext
  have h : (((blockEmb2 K p f 3 2 (negOneSu K p f hK) : Su K p f 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = blockMat 4 2 (-1 : Matrix (Fin 2) (Fin 2) K) := rfl
  show (((blockEmb2 K p f 3 2 (negOneSu K p f hK) : Su K p f 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = _
  rw [h, blockMat_two_neg]
  simp [ModelData.xyK, xyGL, coe_diagGL]

open CFSG.LieType.Universal.Unitary in
theorem exists_two_subgroup_uni {K G : Type} [Field K] [Finite K] [Group G] [Finite G] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (ψ : Su K p f 4 →* G) (hker : ψ.ker ≤ Subgroup.center (Su K p f 4))
    (hxy : ψ (blockEmb2 K p f 3 0 (negOneSu K p f hK)) =
      ψ (blockEmb2 K p f 3 2 (negOneSu K p f hK))) :
    ∃ T : Subgroup G, T ≤ ψ.range ∧
      (∀ t ∈ T, t * ψ (blockEmb2 K p f 3 0 (negOneSu K p f hK)) =
        ψ (blockEmb2 K p f 3 0 (negOneSu K p f hK)) * t) ∧
      IsPGroup 2 T ∧
        2 ^ (1 + 2 * (Nat.card ↥(StatedSU 2 (p ^ f) K)).factorization 2) ≤ Nat.card ↥T := by
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card (by rw [hK]; exact hodd.pow)
  let e : Su K p f 4 ≃* ↥(StatedSU 4 (p ^ f) K) := MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)
  let ψ' : ↥(ModelData.uni hK).K4 →* G := ψ.comp e.symm.toMonoidHom
  have hker' : ψ'.ker ≤ Subgroup.center ↥(ModelData.uni hK).K4 := by
    intro x hx
    let x' : ↥(StatedSU 4 (p ^ f) K) := x
    have h1 : e.symm x' ∈ ψ.ker := hx
    have h3 := (MulEquivClass.apply_mem_center_iff e).2 (hker h1)
    rw [MulEquiv.apply_symm_apply] at h3
    exact h3
  have hy' : ψ' (ModelData.uni hK).yK = ψ (blockEmb2 K p f 3 0 (negOneSu K p f hK)) := by
    show ψ (e.symm (ModelData.uni hK).yK) = _
    rw [← e_blockEmb2_zero hK, MulEquiv.symm_apply_apply]
  have hxy' : ψ' (ModelData.uni hK).xyK = ψ (blockEmb2 K p f 3 2 (negOneSu K p f hK)) := by
    show ψ (e.symm (ModelData.uni hK).xyK) = _
    rw [← e_blockEmb2_two hK, MulEquiv.symm_apply_apply]
  have hx' : ψ' (ModelData.uni hK).xK = 1 := by
    have h1 : ψ' (ModelData.uni hK).xyK = ψ' (ModelData.uni hK).yK := by rw [hy', hxy', hxy]
    rw [← (ModelData.uni hK).xK_mul_yK, map_mul] at h1
    simpa using h1
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := exists_two_subgroup_of_model (ModelData.uni hK) h2
    (hU_uni hK) (hZ_uni hK) ψ' hker' hx'
  refine ⟨T, fun x hx => ?_, fun t ht => ?_, hT3, hT4⟩
  · obtain ⟨y, hy⟩ := hT1 hx
    exact ⟨e.symm y, hy⟩
  · rw [← hy']
    exact hT2 t ht

end CFSG.GH74.GLS.LU.Local
