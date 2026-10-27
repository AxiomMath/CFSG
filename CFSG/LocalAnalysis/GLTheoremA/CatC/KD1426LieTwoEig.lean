module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSL2
public import CFSG.GroupTheory.PLayer.CentralQuotient
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.Quasithin.Vol2.Ch11SecOE3F
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxN10
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb
public import CFSG.Mathlib.Arithmetic.CubeModSix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426Common
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

theorem exists_piField_true_of_card_mod_six {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 6 = 1) : ∃ p f : ℕ, PiField true p f F := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, _hc, n, hp, hcard⟩ := FiniteField.card' F
  refine ⟨p, (n : ℕ), hp, n.2, ?_⟩
  rw [piCard, Bool.cond_true, ← hcard, Nat.card_eq_fintype_card]

section Block

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] noncomputable def blockSL2 (hK : PiField π p f K) : Subgroup (GL (Fin 3) K) :=
  (slPi π 2 (p ^ f) K).map blockHom

theorem mem_blockSL2 {hK : PiField π p f K} {g : GL (Fin 3) K} :
    g ∈ blockSL2 hK ↔ ∃ B ∈ slPi π 2 (p ^ f) K, blockHom B = g :=
  Subgroup.mem_map

theorem blockSL2_le_slPi (hK : PiField π p f K) : blockSL2 hK ≤ slPi π 3 (p ^ f) K := by
  rintro _ ⟨B, hB, rfl⟩
  exact blockHom_mem_slPi hK (slPi_le_glPi (fun h => by subst h; exact hK.unitary) hB)

theorem blockSL2_le_centralizer (hK : PiField π p f K) (e : Kˣ) :
    blockSL2 hK ≤ Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) K)) := by
  rintro _ ⟨B, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact blockHom_commute e B

theorem blockHom_conj (A B : GL (Fin 2) K) :
    blockHom A * blockHom B * (blockHom A)⁻¹ = blockHom (A * B * A⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]

theorem blockSL2_quasisimple (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) : CFSG.Open.IsQuasisimple ↥(blockSL2 hK) := by
  show CFSG.Open.IsQuasisimple ↥((slPi π 2 (p ^ f) K).map blockHom)
  exact CFSG.LocalAnalysis.GLTheoremA.KD1426Common.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective (slPi π 2 (p ^ f) K) blockHom blockHom_injective)
    (CFSG.Quasithin.Vol2.Ch11.OE3.open_isQuasisimple
      (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.isQuasisimple_slPi_two hK hq hq2))

end Block

section Conj

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem primeFormUnitary_idGram_eq_glPi {p f : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) (n : ℕ) :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) = glPi false n (p ^ f) K := by
  ext A
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary, mem_glPi_false h]
  simp [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Matrix.mul_one]

theorem conj_mem_slPi_two (hK : PiField π p f K) {A B : GL (Fin 2) K}
    (hA : A ∈ glPi π 2 (p ^ f) K) (hB : B ∈ slPi π 2 (p ^ f) K) :
    A * B * A⁻¹ ∈ slPi π 2 (p ^ f) K := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K := fun h => by
    subst h; exact hK.unitary
  rw [mem_slPi_iff hπ]
  refine ⟨?_, ?_⟩
  · cases π with
    | false =>
      have h := hK.unitary
      have hA' : A ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 2) := by
        rw [primeFormUnitary_idGram_eq_glPi h 2]; exact hA
      exact slPi_le_glPi (fun _ => h) (CFSG.RankThree.PartOne.KFU.conj_mem_unitarySU h hA' hB)
    | true => exact mem_glPi_true _ _
  · have hdet : ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
      ((mem_slPi_iff hπ).1 hB).2
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    exact hdet

end Conj

section Normal

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagTwo_pow_three_eq_one {μ : Kˣ} (hμ : (μ : K) ^ 3 = 1) :
    CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo μ ^ 3 = 1 := by
  have hμ0 : (μ : K) ≠ 0 := Units.ne_zero μ
  have hμi : (((μ⁻¹ : Kˣ) : K)) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hμ, inv_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, CFSG.RankThree.PartTwo.Sec11.KS11LieProof.coe_diagTwo,
    Matrix.diagonal_pow, Units.val_one]
  have hcube : (![((μ : K)), (((μ⁻¹ : Kˣ) : K))] : Fin 2 → K) ^ 3 = ![(1 : K), (1 : K)] := by
    funext i
    fin_cases i
    · simpa using hμ
    · simpa using hμi
  rw [hcube]
  have hone : (![(1 : K), (1 : K)] : Fin 2 → K) = 1 := by
    funext i; fin_cases i <;> rfl
  rw [hone]
  exact Matrix.diagonal_one

theorem three_dvd_card_blockSL2 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1) :
    3 ∣ Nat.card ↥(blockSL2 hK) := by
  have hmem : CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e ∈ slPi π 2 (p ^ f) K := by
    refine CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo_mem_slPi hK (fun h => ?_)
    subst h
    exact pow_succ_eq_one_of_modThree hq he3
  have hxmem : blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e) ∈ blockSL2 hK :=
    mem_blockSL2.2 ⟨_, hmem, rfl⟩
  have hx1 : blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e) ≠ 1 := by
    intro hcon
    have h₂ : CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e = 1 :=
      blockHom_injective (by rw [hcon, map_one])
    have h₃ : (((CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      rw [h₂]
      simp
    rw [CFSG.RankThree.PartTwo.Sec11.KS11LieProof.coe_diagTwo] at h₃
    simp at h₃
    exact he1 h₃
  have hx3 : blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e) ^ 3 = 1 := by
    rw [← map_pow, diagTwo_pow_three_eq_one he3, map_one]
  have hord : orderOf (⟨blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e), hxmem⟩ :
      ↥(blockSL2 hK)) = 3 :=
    orderOf_eq_prime (Subtype.ext hx3) (fun hcon => hx1 (congrArg Subtype.val hcon))
  have hdvd := orderOf_dvd_natCard
    (⟨blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e), hxmem⟩ : ↥(blockSL2 hK))
  rwa [hord] at hdvd

theorem blockSL2_normal (hK : PiField π p f K) {e : Kˣ} (he1 : e ≠ 1) :
    ((blockSL2 hK).subgroupOf
      (slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) K)))).Normal := by
  refine ⟨fun l hl g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hl ⊢
  obtain ⟨B, hB, hBl⟩ := mem_blockSL2.1 hl
  obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.1 (show (↑g : GL (Fin 3) K) ∈ _ from g.2)
  have hgm : (↑g : GL (Fin 3) K) ∈ (glPi π 2 (p ^ f) K).map blockHom := by
    rw [← centralizer_diagE_eq hK he1]
    exact Subgroup.mem_inf.2 ⟨hgL, hgC⟩
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.1 hgm
  have hgl : (↑(g * l * g⁻¹) : GL (Fin 3) K) =
      blockHom A * blockHom B * (blockHom A)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAg, hBl]
  rw [hgl, blockHom_conj]
  exact mem_blockSL2.2 ⟨A * B * A⁻¹, conj_mem_slPi_two hK hA hB, rfl⟩

end Normal

section Component

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem blockSL2_ne_bot (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1) : blockSL2 hK ≠ ⊥ := by
  have hmem : CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e ∈ slPi π 2 (p ^ f) K := by
    refine CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo_mem_slPi hK (fun h => ?_)
    subst h
    exact pow_succ_eq_one_of_modThree hq he3
  have hxmem : blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e) ∈ blockSL2 hK :=
    mem_blockSL2.2 ⟨_, hmem, rfl⟩
  intro hbot
  have hx1 : blockHom (CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e) ≠ 1 := by
    intro hcon
    have h₂ : CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e = 1 :=
      blockHom_injective (by rw [hcon, map_one])
    have h₃ : (((CFSG.RankThree.PartTwo.Sec11.KS11LieProof.diagTwo e : GL (Fin 2) K)) :
        Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
      rw [h₂]
      simp
    rw [CFSG.RankThree.PartTwo.Sec11.KS11LieProof.coe_diagTwo] at h₃
    simp at h₃
    exact he1 h₃
  exact hx1 (by rw [hbot] at hxmem; simpa using hxmem)

theorem blockSL2_le_glaPLayer (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1) :
    blockSL2 hK ≤ GLAPLayer 3 (slPi π 3 (p ^ f) K ⊓
      Subgroup.centralizer ({diagE e} : Set (GL (Fin 3) K))) := by
  haveI := hK.finite
  exact le_sSup (CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three
    (blockSL2_quasisimple hK hq hq2) (three_dvd_card_blockSL2 hK hq he3 he1)
    (le_inf (blockSL2_le_slPi hK) (blockSL2_le_centralizer hK e)) (blockSL2_normal hK he1))

end Component

open scoped commutatorElement

theorem map_glaPLayer_fixSubgroup_proj_ne_bot {K : Type} [Group K] [Finite K]
    {Q : Type} [Group Q] (π : K →* Q) (hker : π.ker ≤ Subgroup.center K)
    (α : MulAut K) (hne : GLAPLayer 3 (fixSubgroup α) ≠ ⊥) :
    (GLAPLayer 3 (fixSubgroup α)).map π ≠ ⊥ := by
  intro hbot
  rw [Subgroup.map_eq_bot_iff] at hbot
  have hle : GLAPLayer 3 (fixSubgroup α) ≤ π.ker := hbot
  have hcomm : ⁅GLAPLayer 3 (fixSubgroup α), GLAPLayer 3 (fixSubgroup α)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_center_iff.1 (hker (hle hx)) y
  rw [CFSG.LocalAnalysis.GLTheoremA.layer_perfect (p := 3)] at hcomm
  exact hne hcomm

theorem glaPLayer_fixSubgroup_conjAut_diagE_ne_bot {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 6 = 1) {e : Fˣ} (he3 : (e : F) ^ 3 = 1) (he1 : e ≠ 1) :
    GLAPLayer 3 (fixSubgroup
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F (diagE e))) ≠ ⊥ := by
  obtain ⟨p, f, hK⟩ := exists_piField_true_of_card_mod_six hF
  have hcard : Nat.card F = p ^ f := by
    have h := hK.card
    rw [piCard, Bool.cond_true] at h
    exact h
  have h6 : p ^ f % 6 = 1 := by rw [← hcard]; exact hF
  have hq2 : 2 < p ^ f := by
    have hd : 6 * (p ^ f / 6) + 1 = p ^ f := by
      have h := Nat.div_add_mod (p ^ f) 6
      rw [h6] at h
      omega
    have hp2 : 2 ≤ p ^ f :=
      le_trans hK.prime.two_le
        (Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hK.one_le) p)
    omega
  have hq : ModThree true (p ^ f) := (mod_three_eq_one_of_mod_six_eq_one h6 : ModThree true (p ^ f))
  set A : GL (Fin 3) F := diagE e with hAdef
  set α : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A with hαdef
  set β : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F A with hβdef
  have hβeq : β = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F (diagE e) := by
    rw [hβdef, hAdef]
  have hconv : ∀ s, (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F) (α s) =
      A * (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F) s * A⁻¹ := by
    intro s
    apply Units.ext
    simpa using CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation A s
  have hfixmap : (fixSubgroup α).map ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F)) =
      slPi true 3 (p ^ f) F ⊓ Subgroup.centralizer ({A} : Set (GL (Fin 3) F)) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.map_fixSubgroup_eq_of_conj
      ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F))
      Matrix.SpecialLinearGroup.toGL_injective α A hconv]
    exact congrArg (fun H => H ⊓ Subgroup.centralizer ({A} : Set (GL (Fin 3) F)))
      (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 F).symm
  have h1 : blockSL2 hK ≤
      GLAPLayer 3 ((fixSubgroup α).map
        ((Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F))) := by
    rw [hfixmap]
    exact blockSL2_le_glaPLayer hK hq hq2 he3 he1
  have h2 : GLAPLayer 3 ((fixSubgroup α).map
      ((Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F))) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h1
    exact blockSL2_ne_bot hK hq he3 he1 (le_bot_iff.1 h1)
  have hkbot : ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →*
      GL (Fin 3) F)).ker = ⊥ :=
    MonoidHom.ker_eq_bot _ Matrix.SpecialLinearGroup.toGL_injective
  have h3 : GLAPLayer 3 ((fixSubgroup α).map
        ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F))) =
      (GLAPLayer 3 (fixSubgroup α)).map
        ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F)) :=
    (CFSG.glaPLayer_map_eq_of_ker_le_center Nat.prime_three
      ((Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F))
      (by
        intro y hy x _
        have hy1 : y = 1 := by
          have h2 : y ∈ ((Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin 3) F →* GL (Fin 3) F)).ker := hy.2
          rw [hkbot] at h2
          exact Subgroup.mem_bot.1 h2
        rw [hy1, mul_one, one_mul])).symm
  have h4 : GLAPLayer 3 (fixSubgroup α) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at h3
    exact h2 h3
  have hpker : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.ker_proj,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  have h5 : (GLAPLayer 3 (fixSubgroup α)).map
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) ≠ ⊥ :=
    map_glaPLayer_fixSubgroup_proj_ne_bot
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) hpker α h4
  have hαβ : ∀ s, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F (α s) =
      β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F s) := fun s =>
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj A s).symm
  have h6 := CFSG.HardMathSupport.Solomon.Coordinator.map_glaPLayer_fixSubgroup_eq
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) hpker α β hαβ
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F) Nat.prime_three
  rw [← h6]
  exact h5

section Unitary

open CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K]

theorem diagE_mem_unitaryIsom3 (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (h3 : 3 ∣ p ^ f + 1) {e : Kˣ} (he3 : (e : K) ^ 3 = 1) :
    diagE e ∈ unitaryIsom3 h := by
  rw [mem_unitaryIsom3, coe_diagE]
  have hebar : h.bar (e : K) * (e : K) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree (by
      change p ^ f % 3 = 2
      omega) he3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hebar]

theorem glaPLayer_fixSubgroup_psuConj_diagE_ne_bot
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    (hq6 : p ^ f % 6 = 5) {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1)
    (hA : diagE e ∈ unitaryIsom3 h) :
    GLAPLayer 3 (fixSubgroup (psuConj h ⟨diagE e, hA⟩)) ≠ ⊥ := by
  haveI : Finite K := h.finite
  have hK : PiField false p f K :=
    ⟨h.prime, h.one_le, by rw [h.card, piCard, Bool.cond_false, ← pow_mul, mul_comm]⟩
  have hq : ModThree false (p ^ f) :=
    (mod_three_eq_two_of_mod_six_eq_five hq6 : ModThree false (p ^ f))
  have hq2 : 2 < p ^ f := by have := five_le_of_mod_six_eq_five hq6; omega
  set A : GL (Fin 3) K := diagE e with hAdef
  set α : MulAut ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) :=
    suConj h ⟨A, hA⟩ with hαdef
  set β : MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3) :=
    psuConj h ⟨A, hA⟩ with hβdef
  have hconv : ∀ s, (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype (α s) =
      A * (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype s * A⁻¹ :=
    fun s => coe_suConj ⟨A, hA⟩ s
  have hfixmap : (fixSubgroup α).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype =
      CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3 ⊓
        Subgroup.centralizer ({A} : Set (GL (Fin 3) K)) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.map_fixSubgroup_eq_of_conj _
      Subtype.coe_injective α A hconv, Subgroup.range_subtype]
  have h1 : blockSL2 hK ≤ GLAPLayer 3 ((fixSubgroup α).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype) := by
    rw [hfixmap]
    exact blockSL2_le_glaPLayer hK hq hq2 he3 he1
  have h2 : GLAPLayer 3 ((fixSubgroup α).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h1
    exact blockSL2_ne_bot hK hq he3 he1 (le_bot_iff.1 h1)
  have hkbot : (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype.ker = ⊥ :=
    MonoidHom.ker_eq_bot _ Subtype.coe_injective
  have h3 : GLAPLayer 3 ((fixSubgroup α).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype) =
      (GLAPLayer 3 (fixSubgroup α)).map
        (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype :=
    (CFSG.glaPLayer_map_eq_of_ker_le_center Nat.prime_three
      (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype (by
        intro y hy x _
        have hy1 : y = 1 := by
          have h2 : y ∈ (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3).subtype.ker := hy.2
          rw [hkbot] at h2
          exact Subgroup.mem_bot.1 h2
        rw [hy1, mul_one, one_mul])).symm
  have h4 : GLAPLayer 3 (fixSubgroup α) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at h3
    exact h2 h3
  have hpker : (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3).ker ≤
      Subgroup.center ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) := by
    rw [CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj]
    exact CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_le_center h 3
  have h5 : (GLAPLayer 3 (fixSubgroup α)).map
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3) ≠ ⊥ :=
    map_glaPLayer_fixSubgroup_proj_ne_bot
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3) hpker α h4
  have hαβ : ∀ s, CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3 (α s) =
      β (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3 s) := fun s =>
    (psuConj_mk ⟨A, hA⟩ s).symm
  have h6 := CFSG.HardMathSupport.Solomon.Coordinator.map_glaPLayer_fixSubgroup_eq
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj h 3) hpker α β hαβ
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj_surjective h 3) Nat.prime_three
  rw [← h6]
  exact h5

end Unitary

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
