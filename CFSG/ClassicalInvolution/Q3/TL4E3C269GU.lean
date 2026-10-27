module

public import CFSG.ClassicalInvolution.Q3.TL4E3C269GL
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3C269G

open CFSG CFSG.ClassicalInvolution Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {p f : ℕ} {K : Type} [Field K]

theorem diagOneNeg_mem_GU2 (h : UnitaryFieldData p f K) : diagOneNeg K ∈ GU2Stated (p ^ f) K := by
  rw [Lemma41aU3.mem_GU2Stated_iff h, coe_diagOneNeg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_GU2_of_unitary (h : UnitaryFieldData p f K) {A : GL (Fin 2) K}
    (U : Matrix (Fin 2) (Fin 2) K) (hU : (U.map h.bar)ᵀ * U = 1)
    (hAU : (A : Matrix (Fin 2) (Fin 2) K) * U = U * !![1, 0; 0, -1]) :
    ∃ U' ∈ GU2Stated (p ^ f) K, A * U' = U' * diagOneNeg K := by
  have hdet : U.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero U hdet, (Lemma41aU3.mem_GU2Stated_iff h).mpr hU,
    Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, coe_diagOneNeg]
  exact hAU

theorem entries_of_involution_GU2 (h : UnitaryFieldData p f K) {A : GL (Fin 2) K}
    (hA : A ∈ GU2Stated (p ^ f) K) (hA2 : A * A = 1) (hA1 : A ≠ 1)
    (hAm : A ≠ -1) :
    (A : Matrix (Fin 2) (Fin 2) K) 1 1 = -(A : Matrix (Fin 2) (Fin 2) K) 0 0 ∧
      h.bar ((A : Matrix (Fin 2) (Fin 2) K) 0 0) = (A : Matrix (Fin 2) (Fin 2) K) 0 0 ∧
      h.bar ((A : Matrix (Fin 2) (Fin 2) K) 0 1) = (A : Matrix (Fin 2) (Fin 2) K) 1 0 ∧
      (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 =
        1 - (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  obtain ⟨htr, e00⟩ := entries_of_involution hA2 hA1 hAm
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hu : (M.map h.bar)ᵀ * M = 1 := (Lemma41aU3.mem_GU2Stated_iff h).mp hA
  have hMM : M * M = 1 := by rw [hMdef, ← Units.val_mul, hA2, Units.val_one]
  have hherm : (M.map h.bar)ᵀ = M :=
    calc (M.map h.bar)ᵀ = (M.map h.bar)ᵀ * (M * M) := by rw [hMM, Matrix.mul_one]
      _ = (M.map h.bar)ᵀ * M * M := by rw [Matrix.mul_assoc]
      _ = M := by rw [hu, Matrix.one_mul]
  refine ⟨htr, ?_, ?_, by linear_combination e00⟩
  · simpa using congrFun (congrFun hherm 0) 0
  · simpa using congrFun (congrFun hherm 1) 0

theorem exists_conj_diagOneNeg_GU2 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {A : GL (Fin 2) K} (hA : A ∈ GU2Stated (p ^ f) K) (hA2 : A * A = 1) (hA1 : A ≠ 1)
    (hAm : A ≠ -1) : ∃ U ∈ GU2Stated (p ^ f) K, A * U = U * diagOneNeg K := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨htr, ha, hb, hcb⟩ := entries_of_involution_GU2 h hA hA2 hA1 hAm
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := Matrix.eta_fin_two M
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  have hσ : ∀ x : K, h.bar x = unitaryInvolution K p f x := fun x => by
    rw [unitaryInvolution_apply, h.bar_apply]
  by_cases hb0 : b = 0
  · have hc0 : c = 0 := by rw [← hb, hb0, map_zero]
    have ha2 : (a - 1) * (a + 1) = 0 := by linear_combination hcb - c * hb0
    rcases mul_eq_zero.mp ha2 with ha1 | ha1
    · have ha' : a = 1 := sub_eq_zero.mp ha1
      refine exists_GU2_of_unitary h 1 (by simp) ?_
      rw [← hMdef, hM, htr, ha', hb0, hc0, Matrix.mul_one, Matrix.one_mul]
    · have ha' : a = -1 := eq_neg_of_add_eq_zero_left ha1
      refine exists_GU2_of_unitary h !![0, 1; 1, 0] ?_ ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · rw [← hMdef, hM, htr, ha', hb0, hc0]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hc0 : c ≠ 0 := by
      rw [← hb]
      exact (map_ne_zero h.bar).mpr hb0
    have h1a : 1 - a * a ≠ 0 := by
      rw [← hcb]
      exact mul_ne_zero hc0 hb0
    have hNp : (2 : K) * (1 - a) ≠ 0 :=
      mul_ne_zero h2 fun h0 => h1a (by linear_combination (1 + a) * h0)
    have hNm : (2 : K) * (1 + a) ≠ 0 :=
      mul_ne_zero h2 fun h0 => h1a (by linear_combination (1 - a) * h0)
    have hfix : ∀ x : K, h.bar x = x → x ≠ 0 →
        ∃ l : K, h.bar l * l * x = 1 := by
      intro x hx hx0
      obtain ⟨l, hl⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed h.card_eq_sq
        (d := x⁻¹) (by rw [← hσ, map_inv₀, hx]) (inv_ne_zero hx0)
      exact ⟨l, by rw [hσ, hl, inv_mul_cancel₀ hx0]⟩
    have hbar2 : h.bar 2 = 2 := by rw [show (2 : K) = 1 + 1 by norm_num, map_add, map_one]
    obtain ⟨l₁, hl₁⟩ := hfix _ (by rw [map_mul, map_sub, map_one, ha, hbar2]) hNp
    obtain ⟨l₂, hl₂⟩ := hfix _ (by rw [map_mul, map_add, map_one, ha, hbar2]) hNm
    refine exists_GU2_of_unitary h !![b * l₁, b * l₂; (1 - a) * l₁, (-1 - a) * l₂] ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
      · linear_combination (h.bar l₁ * l₁) * hcb + hl₁
      · linear_combination (h.bar l₁ * l₂) * hcb
      · linear_combination (h.bar l₂ * l₁) * hcb
      · linear_combination (h.bar l₂ * l₂) * hcb + hl₂
    · rw [← hMdef, hM, htr]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · ring
      · ring
      · linear_combination l₁ * hcb
      · linear_combination l₂ * hcb

theorem embPair_two_comm (A : Matrix (Fin 2) (Fin 2) K) :
    embPair 2 A * negNegOneDiag K = negNegOneDiag K * embPair 2 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair, negNegOneDiag]

theorem embPair_zero_comm (A : Matrix (Fin 2) (Fin 2) K) :
    embPair 0 A * diagonal ![1, -1, -1] = diagonal ![1, -1, -1] * embPair 0 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embPair]

theorem coe_blkU_diagOneNeg (h : UnitaryFieldData p f K) :
    (((Lemma41aU3.blkU h ⟨diagOneNeg K, diagOneNeg_mem_GU2 h⟩ : ↥(StatedSU 3 (p ^ f) K)) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, -1, -1] := by
  show ((Lemma41aL3.blk (diagOneNeg K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [Lemma41aL3.coe_blk, coe_diagOneNeg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, Matrix.det_fin_two_of]

theorem sup_centralizer_blocks_su (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {d : ↥(StatedSU 3 (p ^ f) K)}
    (hd : ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![1, -1, -1]) :
    Subgroup.centralizer ({statedProjMk (StatedSU 3 (p ^ f) K) (unitaryInvT h)} :
        Set (StatedProj (StatedSU 3 (p ^ f) K))) ⊔
      Subgroup.centralizer ({statedProjMk (StatedSU 3 (p ^ f) K) d} :
        Set (StatedProj (StatedSU 3 (p ^ f) K))) = ⊤ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  have hq : p ^ f ≠ 2 := by
    obtain ⟨k, hk⟩ := (h.prime.odd_of_ne_two hp2).pow (n := f)
    omega
  set ρ := statedProjMk (StatedSU 3 (p ^ f) K) with hρ
  set e := MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq 3) with he
  have hφ : Function.Surjective (ρ.comp e.toMonoidHom) :=
    (statedProjMk_surjective _).comp e.surjective
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ hφ, ← Phan.B12_sup_B23 h.card_eq_sq hq,
    Subgroup.map_sup]
  refine sup_le_sup ?_ ?_
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ρ (e (embSUid (unitaryInvolution K p f) 2 A)) * ρ (unitaryInvT h) =
      ρ (unitaryInvT h) * ρ (e (embSUid (unitaryInvolution K p f) 2 A))
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Units.ext (embPair_two_comm _))
  · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show ρ (e (embSUid (unitaryInvolution K p f) 0 A)) * ρ d =
      ρ d * ρ (e (embSUid (unitaryInvolution K p f) 0 A))
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd]
    exact embPair_zero_comm _

theorem sup_centralizer_eq_top_psu3_core (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {s : StatedProj (StatedSU 3 (p ^ f) K)} (hs : orderOf s = 2)
    (hts : statedProjMk (StatedSU 3 (p ^ f) K) (unitaryInvT h) * s =
      s * statedProjMk (StatedSU 3 (p ^ f) K) (unitaryInvT h))
    (hne : statedProjMk (StatedSU 3 (p ^ f) K) (unitaryInvT h) ≠ s) :
    Subgroup.centralizer ({statedProjMk (StatedSU 3 (p ^ f) K) (unitaryInvT h)} :
        Set (StatedProj (StatedSU 3 (p ^ f) K))) ⊔
      Subgroup.centralizer ({s} : Set (StatedProj (StatedSU 3 (p ^ f) K))) = ⊤ := by
  set ρ := statedProjMk (StatedSU 3 (p ^ f) K) with hρ
  have hker : ρ.ker ≤ Subgroup.center _ := ker_statedProjMk_le_center _
  have hZ : ∀ z ∈ ρ.ker, z ^ 3 = 1 := fun z hz => Lemma41aU3.ker_pow_three h z hz
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨b, hb2, hbs⟩ := linConj_lift_involution ρ (statedProjMk_surjective _) hZ hs2
  have ht2 : unitaryInvT h * unitaryInvT h = 1 := by rw [← pow_two, unitaryInvT_sq]
  have hbt : b * unitaryInvT h = unitaryInvT h * b :=
    Lemma41aL3.commute_of_map_commute ρ hker hZ ht2 (by rw [hbs]; exact hts.symm)
  obtain ⟨A, hA⟩ := Lemma41aU3.mem_range_blkU_of_commute h hp2 hbt
  have hA2 : (A : GL (Fin 2) K) * A = 1 := by
    have : A * A = 1 := Lemma41aU3.blkU_injective h (by rw [map_mul, hA, hb2, map_one])
    exact congrArg Subtype.val this
  have hA1 : (A : GL (Fin 2) K) ≠ 1 := by
    intro h1
    have : A = 1 := Subtype.ext h1
    rw [this, map_one] at hA
    rw [← hbs, ← hA, map_one, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hAm : (A : GL (Fin 2) K) ≠ -1 := by
    intro h1
    have : A = ⟨-1, TA3.Q5U3.neg_one_mem_GU2 h⟩ := Subtype.ext h1
    rw [this, TA3.Q5U3.blkU_neg_one] at hA
    exact hne (by rw [← hbs, ← hA])
  obtain ⟨U, hUmem, hU⟩ := exists_conj_diagOneNeg_GU2 h hp2 A.2 hA2 hA1 hAm
  set D : ↥(GU2Stated (p ^ f) K) := ⟨diagOneNeg K, diagOneNeg_mem_GU2 h⟩ with hD
  set Ug : ↥(GU2Stated (p ^ f) K) := ⟨U, hUmem⟩ with hUg
  have hAUD : A = Ug * D * Ug⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact Subtype.ext hU
  set w := ρ (Lemma41aU3.blkU h Ug) with hw
  have h1 : w * ρ (unitaryInvT h) = ρ (unitaryInvT h) * w := by
    rw [hw, ← map_mul, ← map_mul, Lemma41aU3.blkU_commute]
  have hwt : w⁻¹ * ρ (unitaryInvT h) = ρ (unitaryInvT h) * w⁻¹ :=
    calc w⁻¹ * ρ (unitaryInvT h) = w⁻¹ * (ρ (unitaryInvT h) * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * ρ (unitaryInvT h)) * w⁻¹ := by rw [h1]
      _ = ρ (unitaryInvT h) * w⁻¹ := by group
  have hsw : s = w * ρ (Lemma41aU3.blkU h D) * w⁻¹ := by
    rw [← hbs, ← hA, hAUD, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  rw [hsw]
  refine sup_centralizer_eq_top_of_conj hwt ?_
  rw [show w⁻¹ * (w * ρ (Lemma41aU3.blkU h D) * w⁻¹) * w⁻¹⁻¹ = ρ (Lemma41aU3.blkU h D) by
    group]
  exact sup_centralizer_blocks_su h hp2 (coe_blkU_diagOneNeg h)

theorem sup_centralizer_eq_top_psu3 (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {t s : StatedProj (StatedSU 3 (p ^ f) K)} (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hts : t * s = s * t) (hne : t ≠ s) :
    Subgroup.centralizer ({t} : Set (StatedProj (StatedSU 3 (p ^ f) K))) ⊔
      Subgroup.centralizer ({s} : Set (StatedProj (StatedSU 3 (p ^ f) K))) = ⊤ := by
  set ρ := statedProjMk (StatedSU 3 (p ^ f) K) with hρ
  have hZ : ∀ z ∈ ρ.ker, z ^ 3 = 1 := fun z hz => Lemma41aU3.ker_pow_three h z hz
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨a, ha2, hat⟩ := linConj_lift_involution ρ (statedProjMk_surjective _) hZ ht2
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [map_one] at hat
    rw [← hat, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ha_ord : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_unitaryInvT_of_orderOf h hp2 ha_ord)
  set g := ρ c with hg
  have htg : t = g * ρ (unitaryInvT h) * g⁻¹ := by
    rw [← hat, ← hc, map_mul, map_mul, map_inv]
  refine sup_centralizer_eq_top_of_equiv (MulAut.conj g⁻¹) ?_
  have het : MulAut.conj g⁻¹ t = ρ (unitaryInvT h) := by
    rw [MulAut.conj_apply, htg]
    group
  rw [het]
  refine sup_centralizer_eq_top_psu3_core h hp2 ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq]
    exact hs
  · rw [← het, ← map_mul, ← map_mul, hts]
  · rw [← het]
    exact fun h' => hne ((MulAut.conj g⁻¹).injective h')

end CFSG.ClassicalInvolution.Q3.TL4.E3C269G
