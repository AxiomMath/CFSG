module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealComp
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnLift
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Alt
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAut
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBKey

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

section Lift

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem u6r_cube_scalar (hn : 3 ≤ n) (B : primeFormUnitary h (idGram K n))
    (hB : primeFormConjHom h (idGram K n) B ^ 3 = 1) :
    ∃ μ : Kˣ, μ ^ (ℓ ^ f + 1) = 1 ∧
      (B : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) μ := by
  have h3 : primeFormConjHom h (idGram K n) (B ^ 3) = 1 := by rw [map_pow]; exact hB
  obtain ⟨c, hc⟩ := (CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.conj_eq_one_iff h hn (B ^ 3)).1 h3
  have hc' : (B : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [← Subgroup.coe_pow]
    exact hc
  refine ⟨c, ?_, hc'⟩
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
    rw [← hc']
    exact pow_mem B.2 3
  exact CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.pow_succ_eq_one_of_scalar_mem h (by omega) hmem

theorem u6r_comm_scalar (hn : 3 ≤ n) (B C : primeFormUnitary h (idGram K n))
    (hBC : primeFormConjHom h (idGram K n) C * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) C) :
    ∃ ζ : Kˣ, (C : GL (Fin n) K) * B * (C : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) ζ * B := by
  have h1 : primeFormConjHom h (idGram K n) (C * B * C⁻¹ * B⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hBC]
    group
  obtain ⟨ζ, hζ⟩ := (CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.conj_eq_one_iff h hn _).1 h1
  refine ⟨ζ, ?_⟩
  have e : (C : GL (Fin n) K) * B * (C : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) ζ := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hζ
  calc (C : GL (Fin n) K) * B * (C : GL (Fin n) K)⁻¹
      = ((C : GL (Fin n) K) * B * (C : GL (Fin n) K)⁻¹ * (B : GL (Fin n) K)⁻¹) * B := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * B := by rw [e]

theorem u6r_rescale (B : primeFormUnitary h (idGram K n)) {a : Kˣ} (ha : a ^ (ℓ ^ f + 1) = 1) :
    ∃ B' : primeFormUnitary h (idGram K n),
      (B' : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) a⁻¹ * B ∧
        primeFormConjHom h (idGram K n) B' = primeFormConjHom h (idGram K n) B := by
  have ha' : (a⁻¹) ^ (ℓ ^ f + 1) = 1 := by rw [inv_pow, ha, inv_one]
  have hs : Matrix.GeneralLinearGroup.scalar (Fin n) a⁻¹ ∈ primeFormUnitary h (idGram K n) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.scalar_mem_of_pow_succ_eq_one h ha'
  let S : primeFormUnitary h (idGram K n) := ⟨_, hs⟩
  have hS1 : primeFormConjHom h (idGram K n) S = 1 := by
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    change Matrix.GeneralLinearGroup.scalar (Fin n) a⁻¹ * (g : GL (Fin n) K) *
      (Matrix.GeneralLinearGroup.scalar (Fin n) a⁻¹)⁻¹ = g
    rw [← (commute_scalar a⁻¹ (g : GL (Fin n) K)).eq, mul_inv_cancel_right]
  refine ⟨S * B, rfl, ?_⟩
  rw [map_mul, hS1, one_mul]

end Lift

theorem u6r_exists_nontrivial_cubic_scalar_commutator
    {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}
    (g₁ g₂ : primeFormUnitary h (idGram K 6))
    (hcomm : primeFormConjHom h (idGram K 6) g₁ *
        primeFormConjHom h (idGram K 6) g₂ =
      primeFormConjHom h (idGram K 6) g₂ *
        primeFormConjHom h (idGram K 6) g₁)
    (hnc : (g₁ : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) ≠
      (g₂ : GL (Fin 6) K) * (g₁ : GL (Fin 6) K)) :
    ∃ κ : Kˣ, κ ^ 3 = 1 ∧ κ ≠ 1 ∧
      (g₁ : GL (Fin 6) K) * (g₂ : GL (Fin 6) K) * (g₁ : GL (Fin 6) K)⁻¹ *
        (g₂ : GL (Fin 6) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ := by
  haveI : CharP K 2 := h.charP
  obtain ⟨κ, hκ⟩ := u6r_comm_scalar (h := h) (n := 6) (by norm_num) g₂ g₁ hcomm
  have hκc : ⁅(g₁ : GL (Fin 6) K), (g₂ : GL (Fin 6) K)⁆ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ := by
    rw [commutatorElement_def, hκ]
    group
  have hdet : Matrix.GeneralLinearGroup.det
      ⁅(g₁ : GL (Fin 6) K), (g₂ : GL (Fin 6) K)⁆ = 1 := by
    rw [map_commutatorElement (f := Matrix.GeneralLinearGroup.det)]
    exact (Commute.all _ _).commutator_eq
  have h6 : κ ^ 6 = 1 := by
    have h := congrArg Matrix.GeneralLinearGroup.det hκc
    rw [hdet, Matrix.GeneralLinearGroup.det_scalar] at h
    simpa using h.symm
  have h6K : (κ : K) ^ 6 = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) h6
  have h3K : (κ : K) ^ 3 = 1 := by
    apply CharTwo.sq_injective
    have h3sq : ((κ : K) ^ 3) ^ 2 = 1 := by
      rw [← pow_mul]
      norm_num
      exact h6K
    simpa using h3sq
  have hκ1 : κ ≠ 1 := by
    rintro rfl
    apply hnc
    have h1 : ⁅(g₁ : GL (Fin 6) K), (g₂ : GL (Fin 6) K)⁆ = 1 := by
      simpa using hκc
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  exact ⟨κ, Units.ext h3K, hκ1, by simpa [commutatorElement_def] using hκc⟩

theorem S1431Cfg.u6r_not_inner {P : Type} [Group P] [Finite P] {A : Subgroup (MulAut P)}
    {ψ : MulAut P} {J : Subgroup P} {q : ℕ} (c : S1431Cfg P A ψ J q) {η : MulAut P}
    (hηA : η ∈ A) (hηψ : η ∉ Subgroup.zpowers ψ) (hst : η ∈ stabAut J) :
    ¬ IsInnerAut (inducedBarHom J ⟨η, hst⟩) := by
  intro hinn
  have hU := CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
  have hF := CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds
  have hη3 : η ^ 3 = 1 := c.elemAbelian.2 η hηA
  obtain ⟨⟨hs, hfld⟩, hnt⟩ := c.field η hηA hηψ
  have hα1 : inducedBarHom J ⟨η, hs⟩ ≠ 1 := fun h1 => hnt ⟨hs, h1⟩
  have hα3 := inducedBarHom_pow_three J hs hη3
  have hQ : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent c.comp
  have hnot := not_isInnerAut_descend_of_fieldAut hU hF hQ hα3 hα1 hfld c.typeL2 c.not_dvd
    c.ne_eight
  obtain ⟨u, hu⟩ := hinn
  have hu' : MulAut.conj u = inducedBarHom J ⟨η, hs⟩ := hu
  exact hnot ⟨QuotientGroup.mk u, by
    rw [← hu', CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]⟩

section Key

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem u6r_actSU_mem_fix {B D : primeFormUnitary h (idGram K n)}
    (hDB : (D : GL (Fin n) K) * B = B * D) {y : ↥(gramSU h (idGram K n))}
    (hy : y ∈ fixSubgroup (t6psub_actSU h n B)) :
    t6psub_actSU h n D y ∈ fixSubgroup (t6psub_actSU h n B) := by
  have hBD : B * D = D * B := Subtype.ext hDB.symm
  rw [mem_fixSubgroup] at hy ⊢
  calc t6psub_actSU h n B (t6psub_actSU h n D y)
      = (t6psub_actSU h n B * t6psub_actSU h n D) y := rfl
    _ = t6psub_actSU h n (B * D) y := by rw [map_mul]
    _ = t6psub_actSU h n (D * B) y := by rw [hBD]
    _ = t6psub_actSU h n D (t6psub_actSU h n B y) := by rw [map_mul]; rfl
    _ = t6psub_actSU h n D y := by rw [hy]

theorem u6r_conj_mem_map_fix_iff {B C : primeFormUnitary h (idGram K n)}
    (hCB : (C : GL (Fin n) K) * B = B * C) (x : primeFormP h (idGram K n)) :
    primeFormConjHom h (idGram K n) C x ∈ (fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) ↔
      x ∈ (fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) := by
  have hCB' : ((C⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * B =
      B * ((C⁻¹ : primeFormUnitary h (idGram K n)) : GL (Fin n) K) := by
    rw [Subgroup.coe_inv]
    exact (Commute.inv_left hCB)
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨t6psub_actSU h n C⁻¹ y, u6r_actSU_mem_fix hCB' hy, ?_⟩
    rw [t6psub_hact, hyx, map_inv]
    simp
  · rintro ⟨y, hy, rfl⟩
    exact ⟨t6psub_actSU h n C y, u6r_actSU_mem_fix hCB hy, t6psub_hact C y⟩

theorem u6r_inner_of_commute (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hℓ3 : ℓ ≠ 3) (B C : primeFormUnitary h (idGram K n)) {ν ν' : Kˣ}
    (hB3 : (B : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) ν)
    (hC3 : (C : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) ν')
    (hBC : (C : GL (Fin n) K) * B = B * C) {J : Subgroup (primeFormP h (idGram K n))}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub (primeFormConjHom h (idGram K n) B)) J) {q : ℕ}
    (hq : 10 ≤ q) (hT : IsTypeL2 q (barOf 3 J))
    (hst : primeFormConjHom h (idGram K n) C ∈ stabAut J) :
    IsInnerAut (inducedBarHom J ⟨primeFormConjHom h (idGram K n) C, hst⟩) := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B) :=
    t6psuh_primaryData_toLin' h B.2 Nat.prime_three (Ne.symm hℓ3) hB3
  have hJ0 := u6r_comp_sub B hJ
  have hφ : ∀ i : t6psub_Idx h n B,
      barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
        ((t6psub_block B i).map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) =
      barX 3 ((fixSubgroup (t6psub_actSU h n B)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) J →
      ∃ m ∈ (t6psub_block B i).map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)),
        ∀ m' ∈ (t6psub_block B i).map
          (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)),
          primeFormConjHom h (idGram K n) C m' = m * m' * m⁻¹ := by
    intro i hi
    have hT' : IsTypeL2 q ↥((t6psub_block B i).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))) :=
      isTypeL2_of_barX_eq hJ0 (u6r_block_le B i) (u6r_block_normal B i)
        (u6r_block_quasisimple B H i) hi.symm hT
    have hTb : IsTypeL2 q ↥(t6psub_block B i) :=
      (u6r_isTypeL2_map _ u6r_ker_le_center (t6psub_isQuasisimple_block B H i).1).2 hT'
    obtain ⟨s, hs, hsm⟩ := t6psub_block_key hO B H i hq hTb hBC hC3
    refine ⟨QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) s, ⟨s, hs, rfl⟩, ?_⟩
    rintro _ ⟨m0, hm0, rfl⟩
    rw [← t6psub_hact C m0, hsm m0 hm0]
    simp
  obtain ⟨j₀, hj₀, hbj⟩ := exists_inner_of_blocks_aut hJ0
    (fun i => (t6psub_block B i).map
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)))
    (u6r_block_le B) (u6r_block_normal B) (u6r_block_quasisimple B H) (u6r_block_derived B H)
    (u6r_conj_mem_map_fix_iff hBC) hφ
  exact isInnerAut_inducedBarHom_of_barX_aut hJ0 hst hj₀ hbj

end Key

end CFSG.HardMathSupport.Dickson.Sec6.I1431
