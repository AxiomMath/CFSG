module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenAux
public import CFSG.GH74.Generic.BProg.B2.GenLocDiagU
public import CFSG.GH74.Generic.BProg.B2.GenLocU3
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineSL2

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.GH74.Generic.BProg.B2.GenLocU3Lift Subgroup
  CFSG.GH74.Generic.BProg.B2.GenLocU4Aux CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open scoped MatrixGroups

namespace GenLocU4Gen

variable {K : Type} [Field K] [Finite K]

@[expose] def InBlock (q : ℕ) (P : GL (Fin 4) K) (i : ℕ) (g : ↥(StatedSU 4 q K)) : Prop :=
  ∃ B : Matrix (Fin 2) (Fin 2) K, B.det = 1 ∧ (B.map (· ^ q))ᵀ * B = 1 ∧
    ((P⁻¹ * (g : GL (Fin 4) K) * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 i B

@[expose] def IsTransvU (q : ℕ) (w : Fin 4 → K) (g : ↥(StatedSU 4 q K)) : Prop :=
  ∃ c : K, c + c ^ q = 0 ∧ c ≠ 0 ∧
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + c • Matrix.vecMulVec w (fun i => (w i) ^ q)

omit [Finite K] in
theorem commute_of_frame_commute {n : ℕ} {P x g : GL (Fin n) K}
    (h : (P⁻¹ * g * P) * (P⁻¹ * x * P) = (P⁻¹ * x * P) * (P⁻¹ * g * P)) : g * x = x * g := by
  have hGX : g * x = P * ((P⁻¹ * g * P) * (P⁻¹ * x * P)) * P⁻¹ := by group
  have hXG : x * g = P * ((P⁻¹ * x * P) * (P⁻¹ * g * P)) * P⁻¹ := by group
  rw [hGX, hXG, h]

omit [Finite K] in
theorem inBlock_commute {q : ℕ} (P x : GL (Fin 4) K) (a b : K)
    (hx : ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![a, a, b, b])
    (i : ℕ) (hi : i = 0 ∨ i = 2) (g : ↥(StatedSU 4 q K)) (hg : InBlock q P i g) :
    (g : GL (Fin 4) K) * x = x * (g : GL (Fin 4) K) := by
  obtain ⟨B, -, -, hB⟩ := hg
  have hd : ∀ u v : Fin 4, (i ≤ u.val ∧ u.val < i + 2) → (i ≤ v.val ∧ v.val < i + 2) →
      (![a, a, b, b] : Fin 4 → K) u = (![a, a, b, b] : Fin 4 → K) v := by
    intro u v hu hv
    rcases hi with rfl | rfl <;> fin_cases u <;> fin_cases v <;> simp_all
  have hc := GenLocDiagU.blockMat_commute_diag hd B
  refine commute_of_frame_commute (P := P) ?_
  generalize (P⁻¹ * (g : GL (Fin 4) K) * P) = G at hB ⊢
  generalize (P⁻¹ * x * P) = X at hx ⊢
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hB, hx]
  exact hc.symm

theorem gammaAct_su2_mixed_of_card_le_four
    {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (h5 : 5 ≤ p ^ f) {A : Type} [Group A] [Finite A] (hA : IsRank23 A)
    (β : A →* MulAut (CFSG.ClassicalInvolution.Phan.Su K p f 2))
    (hmix : 11 ≤ p ^ f ∨ (¬ β.range ≤ (MulAut.conj : CFSG.ClassicalInvolution.Phan.Su K p f 2 →* _).range ∧
      Nat.card β.range ≤ 4)) :
    gammaAct β = ⊤ := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card (Fact.out) hK
  by_cases h11 : 11 ≤ p ^ f
  · exact GenLocU3.gammaAct_su2_of_ge11 h hp2 h11 hA β
  obtain ⟨hni, hsmall⟩ := hmix.resolve_left h11
  obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := p)
    (f := f) h.card_eq_sq
  let E : SL(2, fixedSubfield K p f) ≃* CFSG.ClassicalInvolution.Phan.Su K p f 2 :=
    e0.trans (GenLocU3Blk.suEquiv h 2).symm
  let β' : A →* MulAut SL(2, fixedSubfield K p f) := (MulAut.congr E.symm).toMonoidHom.comp β
  have hc : ∀ a x, β a (E x) = E (β' a x) := by
    intro a x
    simp [β', MulAut.congr_apply]
  have hni' : ¬ β'.range ≤ (MulAut.conj : SL(2, fixedSubfield K p f) →* MulAut SL(2, fixedSubfield K p f)).range := by
    intro hle
    apply hni
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := hle ⟨a, rfl⟩
    refine ⟨E s, MulEquiv.ext fun y => ?_⟩
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [hc, ← hs]
    simp [MulAut.conj_apply]
  have hsmall' : Nat.card β'.range ≤ 4 := by
    have : β'.range = β.range.map (MulAut.congr E.symm).toMonoidHom := by
      rw [MonoidHom.range_comp]
    rw [this, Subgroup.card_map_of_injective (MulAut.congr E.symm).injective]
    exact hsmall
  have hK' : Nat.card (fixedSubfield K p f) = p ^ f := card_fixedSubfield h.card_eq_sq
  have h1 : gammaAct β' = ⊤ :=
    GenLocL3Nine.gammaAct_sl2_of_not_inner_small h.prime hp2 hK' h5 β' hA hni' hsmall'
  have := GenLocBasic.gammaAct_map_equiv E β' β hc
  rw [this, h1, Subgroup.map_top_of_surjective _ E.surjective]

theorem gammaAct_su2_mixed_rank2
    {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (h5 : 5 ≤ p ^ f) {A : Type} [Group A] [Finite A] (hA : IsRank23 A) (hk : pRank 2 A = 2)
    (β : A →* MulAut (CFSG.ClassicalInvolution.Phan.Su K p f 2))
    (hmix : 11 ≤ p ^ f ∨ ¬ β.range ≤ (MulAut.conj : CFSG.ClassicalInvolution.Phan.Su K p f 2 →* _).range) :
    gammaAct β = ⊤ := by
  have h4 : Nat.card A = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hk]
    norm_num
  refine gammaAct_su2_mixed_of_card_le_four hp2 hK h5 hA β ?_
  rcases hmix with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    rw [← h4]
    exact Nat.card_le_card_of_surjective _ β.rangeRestrict_surjective

section Diag

variable {K : Type} [Field K]

theorem vecMulVec_commute_diag {n : ℕ} (a b d : Fin n → K) (h : ∀ i j, a i * b j ≠ 0 → d i = d j) :
    Matrix.vecMulVec a b * Matrix.diagonal d = Matrix.diagonal d * Matrix.vecMulVec a b := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.vecMulVec_apply]
  by_cases h0 : a i * b j = 0
  · rw [h0]
    simp
  · rw [h i j h0]
    ring

theorem tvMat_commute_diag {n : ℕ} (σ : K ≃+* K) (a d : Fin n → K) (c : K)
    (h : ∀ i j, a i * σ (a j) ≠ 0 → d i = d j) :
    tvMat σ a c * Matrix.diagonal d = Matrix.diagonal d * tvMat σ a c := by
  have := vecMulVec_commute_diag a (fun i => σ (a i)) d h
  rw [tvMat, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, this]
  simp

end Diag

section Scalars

variable {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] [CharP K p] in
theorem exists_unit_scalar_sq_ne_one (hK : Nat.card K = (p ^ f) ^ 2) (h3 : 3 ≤ p ^ f) :
    ∃ ε : K, ε ^ (p ^ f) * ε = 1 ∧ ε * ε ≠ 1 := by
  have := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hq1 : 1 ≤ p ^ f := by omega
  have hprod : (p ^ f - 1) * (p ^ f + 1) = (p ^ f) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 _ (by omega : 0 < p ^ f)]
    ring
  have hu1 : (g ^ (p ^ f - 1)) ^ (p ^ f + 1) = 1 := by
    rw [← pow_mul, hprod, ← hord, pow_orderOf_eq_one]
  have hu2 : (g ^ (p ^ f - 1)) ^ 2 ≠ 1 := by
    intro h
    rw [← pow_mul] at h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by omega) hd
    have : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := hprod.symm
    rw [this] at hle
    have h4 : 0 < p ^ f - 1 := by omega
    nlinarith
  refine ⟨((g ^ (p ^ f - 1) : Kˣ) : K), ?_, ?_⟩
  · have := congrArg (fun w : Kˣ => (w : K)) hu1
    simpa [Units.val_pow_eq_pow_val, pow_succ] using this
  · intro h
    apply hu2
    apply Units.ext
    simpa [Units.val_pow_eq_pow_val, pow_two] using h

theorem exists_rot_pair (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) (h3 : 3 ≤ p ^ f) :
    ∃ c s : K, unitaryInvolution K p f c = c ∧ unitaryInvolution K p f s = -s ∧ c * c - s * s = 1 ∧ s ≠ 0 := by
  obtain ⟨ε, hε, hε2⟩ := exists_unit_scalar_sq_ne_one hK h3
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hε0 : ε ≠ 0 := by
    rintro rfl
    simp at hε
  have hσ : unitaryInvolution K p f ε = ε⁻¹ := by
    rw [unitaryInvolution_apply K p f]
    exact eq_inv_of_mul_eq_one_left hε
  refine ⟨(ε + ε⁻¹) / 2, (ε - ε⁻¹) / 2, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, map_add, hσ, map_inv₀, hσ, inv_inv, add_comm]
    simp [map_ofNat]
  · rw [map_div₀, map_sub, hσ, map_inv₀, hσ, inv_inv, ← neg_div, neg_sub]
    simp [map_ofNat]
  · field_simp
    ring
  · intro h
    apply hε2
    have : ε - ε⁻¹ = 0 := by
      have := (div_eq_zero_iff.1 h).resolve_right h2
      exact this
    field_simp at this
    linear_combination this

end Scalars

variable {p f : ℕ}

omit [Finite K] in
theorem mem_primeFormUnitary_of_raw (h : UnitaryFieldData p f K) {P : GL (Fin 4) K}
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) : P ∈ primeFormUnitary h (idGram K 4) := by
  rw [mem_primeFormUnitary]
  have hb : ((P : Matrix (Fin 4) (Fin 4) K).map h.bar) = (P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)) := rfl
  rw [hb]
  simpa [idGram] using hP

@[expose] noncomputable def frameConj [Fact p.Prime] [CharP K p] (h : UnitaryFieldData p f K) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) :
    Su K p f 4 →* ↥(StatedSU 4 (p ^ f) K) :=
  ((KFU.conjSU h ⟨P, mem_primeFormUnitary_of_raw h hP⟩).toMonoidHom).comp
    (GenLocU3Blk.suEquiv h 4).toMonoidHom

theorem coe_frameConj [Fact p.Prime] [CharP K p] (h : UnitaryFieldData p f K) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (x : Su K p f 4) :
    ((frameConj h P hP x : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = P * (x : GL (Fin 4) K) * P⁻¹ := rfl

theorem frameConj_surjective [Fact p.Prime] [CharP K p] (h : UnitaryFieldData p f K) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) : Function.Surjective (frameConj h P hP) :=
  (KFU.conjSU h ⟨P, mem_primeFormUnitary_of_raw h hP⟩).surjective.comp (GenLocU3Blk.suEquiv h 4).surjective

theorem su2_prop [Fact p.Prime] [CharP K p] (x : Su K p f 2) :
    (((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1) ∧
      ((((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ *
        ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1) := by
  obtain ⟨h1, h2⟩ := (mem_SUid (σ := unitaryInvolution K p f)).1 x.2
  exact ⟨h1, by rw [conjTr_unitaryInvolution] at h2; exact h2⟩

section Frame

variable [Fact p.Prime] [CharP K p]

omit [CharP K p] in
theorem fieldData (hK : Nat.card K = (p ^ f) ^ 2) : UnitaryFieldData p f K :=
  GenLocDiagU.unitaryFieldData_of_card (Fact.out) hK

omit [CharP K p] in
theorem pow_ne_two' (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) : p ^ f ≠ 2 :=
  GenLocDiagU.pow_ne_two (Fact.out) hp2 hK

variable (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
  (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)

@[expose] noncomputable def frameBlock (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1) (i : Fin 3) : Su K p f 2 →* ↥(StatedSU 4 (p ^ f) K) :=
  (frameConj (fieldData hK) P hP).comp (blockEmb2 K p f 3 i)

theorem coe_frameBlock (i : Fin 3) (x : Su K p f 2) :
    ((frameBlock hK P hP i x : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) =
      P * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * P⁻¹ := rfl

theorem frameBlock_inBlock (i : Fin 3) (x : Su K p f 2) :
    InBlock (p ^ f) P i.val (frameBlock hK P hP i x) := by
  obtain ⟨h1, h2⟩ := su2_prop (p := p) (f := f) x
  refine ⟨((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), h1, h2, ?_⟩
  rw [coe_frameBlock]
  have : P⁻¹ * (P * ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) * P⁻¹) * P =
      ((blockEmb2 K p f 3 i x : Su K p f 4) : GL (Fin 4) K) := by group
  rw [this]
  exact coe_coe_blockEmb2 3 i x

theorem exists_frameBlock_of_inBlock (i : Fin 3) (g : ↥(StatedSU 4 (p ^ f) K))
    (hg : InBlock (p ^ f) P i.val g) : ∃ x : Su K p f 2, frameBlock hK P hP i x = g := by
  obtain ⟨B, hdet, hB, hgB⟩ := hg
  refine ⟨su2Mk (p := p) (f := f) B hdet hB, Subtype.ext ?_⟩
  rw [coe_frameBlock]
  have h4 : ((blockEmb2 K p f 3 i (su2Mk (p := p) (f := f) B hdet hB) : Su K p f 4) : GL (Fin 4) K) =
      P⁻¹ * (g : GL (Fin 4) K) * P := by
    apply Units.ext
    rw [hgB]
    exact coe_coe_blockEmb2 3 i _
  rw [h4]
  group

theorem frameBlock_injective (i : Fin 3) : Function.Injective (frameBlock hK P hP i) := by
  have h1 : Function.Injective (frameConj (fieldData hK) P hP) :=
    (KFU.conjSU (fieldData hK) ⟨P, mem_primeFormUnitary_of_raw (fieldData hK) hP⟩).injective.comp
      (GenLocU3Blk.suEquiv (fieldData hK) 4).injective
  exact h1.comp (blockEmb2_injective 3 i)

theorem iSup_range_frameBlock (hp2 : p ≠ 2) :
    ⨆ i : Fin 3, (frameBlock hK P hP i).range = ⊤ := by
  have hq : p ^ f ≠ 2 := pow_ne_two' hK hp2
  have h3 := sup_range_blockEmb2_three (K := K) (p := p) (f := f) hK hq
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := frameConj_surjective (fieldData hK) P hP g
  have hx : x ∈ (blockEmb2 K p f 3 0).range ⊔ (blockEmb2 K p f 3 1).range ⊔ (blockEmb2 K p f 3 2).range := by
    rw [h3]; trivial
  have key : ∀ i : Fin 3, (blockEmb2 K p f 3 i).range ≤
      (⨆ j : Fin 3, (frameBlock hK P hP j).range).comap (frameConj (fieldData hK) P hP) := by
    rintro i _ ⟨y, rfl⟩
    exact Subgroup.mem_iSup_of_mem i ⟨y, rfl⟩
  have hle : (blockEmb2 K p f 3 0).range ⊔ (blockEmb2 K p f 3 1).range ⊔ (blockEmb2 K p f 3 2).range ≤
      (⨆ j : Fin 3, (frameBlock hK P hP j).range).comap (frameConj (fieldData hK) P hP) :=
    sup_le (sup_le (key 0) (key 1)) (key 2)
  exact hle hx

end Frame

section Link

variable [Fact p.Prime] [CharP K p]

theorem coe_frameConj_tv (hK : Nat.card K = (p ^ f) ^ 2) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (v : Fin 4 → K) (hv : herm (unitaryInvolution K p f) v v = 0) (c : K)
    (hc : c + unitaryInvolution K p f c = 0) :
    (((frameConj (fieldData hK) P hP (tv (isUnitaryInvolution_unitaryInvolution hK).invol hv hc) :
        ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      1 + c • Matrix.vecMulVec ((P : Matrix (Fin 4) (Fin 4) K) *ᵥ v)
        (fun i => (((P : Matrix (Fin 4) (Fin 4) K) *ᵥ v) i) ^ (p ^ f)) := by
  set Pm : Matrix (Fin 4) (Fin 4) K := (P : Matrix (Fin 4) (Fin 4) K) with hPm
  set Pb : Matrix (Fin 4) (Fin 4) K := (Pm.map (· ^ (p ^ f)))ᵀ with hPb
  have hinv : ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Pb := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hP
  have hPP : Pm * Pb = 1 := by
    rw [← hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hsig : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) := fun x => unitaryInvolution_apply K p f x
  have hvec : (fun i => unitaryInvolution K p f (v i)) ᵥ* Pb = fun i => ((Pm *ᵥ v) i) ^ (p ^ f) := by
    funext i
    simp only [Matrix.vecMul, dotProduct, hPb, Matrix.transpose_apply, Matrix.map_apply, Matrix.mulVec, ← hsig,
      map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have e1 : (((frameConj (fieldData hK) P hP (tv (isUnitaryInvolution_unitaryInvolution hK).invol hv hc) :
      ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Pm * (1 + c • Matrix.vecMulVec v (fun i => unitaryInvolution K p f (v i))) * Pb := by
    rw [coe_frameConj, Units.val_mul, Units.val_mul, hinv]
    rfl
  rw [e1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hvec]

end Link

theorem su4_eq_top_of_link_raw {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (h01 : ∀ g, InBlock (p ^ f) P 0 g → g ∈ Γ) (h23 : ∀ g, InBlock (p ^ f) P 2 g → g ∈ Γ)
    (v : Fin 4 → K) (hv : ∑ i, (v i) ^ (p ^ f) * v i = 0)
    (hv01 : (v 0) ^ (p ^ f) * v 0 + (v 1) ^ (p ^ f) * v 1 ≠ 0)
    (hT : ∀ g, IsTransvU (p ^ f) ((P : Matrix (Fin 4) (Fin 4) K) *ᵥ v) g → g ∈ Γ) : Γ = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := (GenLocDiagU.unitaryFieldData_of_card hp hK).charP
  have hq : p ^ f ≠ 2 := GenLocDiagU.pow_ne_two hp hp2 hK
  have hsig : ∀ x : K, unitaryInvolution K p f x = x ^ (p ^ f) := fun x => unitaryInvolution_apply K p f x
  have hv' : herm (unitaryInvolution K p f) v v = 0 := by
    simpa only [herm_def, hsig] using hv
  have hv01' : unitaryInvolution K p f (v 0) * v 0 + unitaryInvolution K p f (v 1) * v 1 ≠ 0 := by
    simpa only [hsig] using hv01
  have h0 : ∀ B : Su K p f 2, blockEmb2 K p f 3 0 B ∈ Γ.comap (frameConj (fieldData hK) P hP) :=
    fun B => h01 _ (frameBlock_inBlock hK P hP 0 B)
  have h2 : ∀ B : Su K p f 2, blockEmb2 K p f 3 2 B ∈ Γ.comap (frameConj (fieldData hK) P hP) :=
    fun B => h23 _ (frameBlock_inBlock hK P hP 2 B)
  have hT' : ∀ (c : K) (hc : c + unitaryInvolution K p f c = 0),
      tv (isUnitaryInvolution_unitaryInvolution hK).invol hv' hc ∈ Γ.comap (frameConj (fieldData hK) P hP) := by
    intro c hc
    by_cases hc0 : c = 0
    · subst hc0
      have h1 : tv (isUnitaryInvolution_unitaryInvolution hK).invol hv' hc = 1 := by
        apply ext_smul
        intro x
        rw [tv_smul, one_smul]
        simp
      rw [h1]
      exact Subgroup.one_mem _
    · exact hT _ ⟨c, by rwa [hsig] at hc, hc0, coe_frameConj_tv hK P hP v hv' c hc⟩
  have hcore := core_link hK hq (Γ.comap (frameConj (fieldData hK) P hP)) h0 h2 v hv' hv01' hT'
  rw [eq_top_iff]
  intro g _
  obtain ⟨x, rfl⟩ := frameConj_surjective (fieldData hK) P hP g
  have hx : x ∈ Γ.comap (frameConj (fieldData hK) P hP) := by
    rw [hcore]
    trivial
  exact hx

end GenLocU4Gen
end CFSG.GH74.Generic.BProg.B2
