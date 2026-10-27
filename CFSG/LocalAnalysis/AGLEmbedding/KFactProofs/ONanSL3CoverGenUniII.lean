module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenUniI
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenLinII
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
open CFSG.LieType.Chevalley (fixSubfield)

variable {p f : ℕ} {F : Type} [Field F]

theorem closure_fixSet_eq_top_unitary_of_field [Finite F] (h : UnitaryFieldData p f F)
    (h3 : 3 ∣ p ^ f + 1) (hq : 2 < p ^ f) (T : FrobData F) (hτ : orderOf T.τ = 3)
    (hgen : SubfieldDiagGen h (fixSubfield T.τ))
    (E : Subgroup (MulAut (unitarySU p f F 3))) (hEab : Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9) (hFix : FixCube E) (hτE : suField h T.τ ∈ E) :
    Subgroup.closure (fixSet E) = ⊤ := by
  classical
  have hτ1 : T.τ ≠ 1 := by
    rintro h1
    rw [h1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hf₂1 : suField h T.τ ≠ 1 := suField_ne_one h hq hτ1
  obtain ⟨a, haE, ha⟩ := exists_mem_not_mem_zpowers hEab hEcard hτE
  have hβ3 : a ^ 3 = 1 := hEab.2 a haE
  obtain ⟨m, B, hB⟩ := exists_suConj_mul_pow h hq hτ hβ3
  set e₁ : MulAut (unitarySU p f F 3) := a * suField h T.τ ^ m with he₁
  have he₁E : e₁ ∈ E := E.mul_mem haE (E.pow_mem hτE m)
  have he₁3 : e₁ ^ 3 = 1 := hEab.2 e₁ he₁E
  have he₁not : e₁ ∉ Subgroup.zpowers (suField h T.τ) := by
    intro hmem
    apply ha
    have h1 : a = e₁ * (suField h T.τ ^ m)⁻¹ := by rw [he₁]; group
    rw [h1]
    exact mul_mem hmem (inv_mem (pow_mem (Subgroup.mem_zpowers _) m))
  have he₁1 : e₁ ≠ 1 := fun hh => he₁not (hh ▸ one_mem _)
  have hcomm : e₁ * suField h T.τ = suField h T.τ * e₁ :=
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨_, hτE⟩)
  have hφ₁ : e₁ = suConj h B := hB
  have hφcomm : suConj h B * suField h T.τ = suField h T.τ * suConj h B := by
    rw [← hφ₁]
    exact hcomm
  obtain ⟨c₁, hc₁, hBc⟩ := exists_scalar_of_comm h hφcomm
  obtain ⟨f₀, hf₀⟩ := (CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h
    Nat.prime_three (by norm_num) hτ).1
  obtain ⟨y, hyB, hyfix⟩ := exists_fixed_isometry h T hτ hf₀ hc₁ hBc
  have hφy : e₁ = suConj h y := by rw [hφ₁, hyB]
  have h3F : 3 ∣ Nat.card F - 1 := by
    rw [h.card_eq_sq]
    have hmul : (p ^ f + 1) * (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      simpa [sq] using this.symm
    rw [← hmul]
    exact Dvd.dvd.mul_right h3 _
  obtain ⟨c, hc⟩ := FrobData.exists_fixed_cube T h3F (y : GL (Fin 3) F) hyfix
  have hNc : h.norm (c : F) = 1 := by
    refine norm_eq_one_of_pow_three h h3 c ?_
    rw [Units.val_pow_eq_pow_val, hc]
    exact norm_det_eq_one h y.2
  have hNc' : h.norm (((c⁻¹ : Fˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hNc, inv_one]
  have hsdet : (((GeneralLinearGroup.scalar (Fin 3) c⁻¹ * (y : GL (Fin 3) F) : GL (Fin 3) F)) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Matrix.det_smul, ← hc, Units.val_inv_eq_inv_val]
    have : (c : F) ≠ 0 := c.ne_zero
    simp [inv_pow, this]
  have hsmem : GeneralLinearGroup.scalar (Fin 3) c⁻¹ * (y : GL (Fin 3) F) ∈ unitarySU p f F 3 :=
    (mem_unitarySU_iff h).2 ⟨hsdet, mem_unitaryIsom3.1 (isometry_scalar_mul h hNc' y)⟩
  set s : unitarySU p f F 3 := ⟨_, hsmem⟩ with hs
  have hsiso : (s : GL (Fin 3) F) ∈ unitaryIsom3 h := unitarySU_le_unitaryIsom3 s.2
  have hsy : suConj h y = suConj h ⟨(s : GL (Fin 3) F), hsiso⟩ := by
    have hcs : y = (⟨GeneralLinearGroup.scalar (Fin 3) c, scalar_mem_unitaryIsom3 h hNc⟩ :
        unitaryIsom3 h) * ⟨(s : GL (Fin 3) F), hsiso⟩ := by
      apply Subtype.ext
      change (y : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c *
        (GeneralLinearGroup.scalar (Fin 3) c⁻¹ * (y : GL (Fin 3) F))
      rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [hcs, map_mul, suConj_scalar h hNc, one_mul]
  have hsact : ∀ t, e₁ t = s * t * s⁻¹ := by
    intro t
    rw [hφy, hsy]
    rfl
  have he₁conj : e₁ = MulAut.conj s := MulEquiv.ext fun t => by
    rw [MulAut.conj_apply]
    exact hsact t
  obtain ⟨c', -, hc'⟩ := exists_scalar_pow_three h (B := y) (by rw [← hφy]; exact he₁3)
  have hy3 : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c' : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_pow_eq_pow_val, hc', coe_scalar_eq_smul]
  have hlift : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c : F) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) F) → T.τ (c : F) = c := by
    intro hy3c
    have hM : (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (c ^ 3) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hy3c, coe_scalar_eq_smul, Units.val_pow_eq_pow_val]
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      exact scalar_inv_mul_pow_three hM rfl
    have hfix := hFix (suField h T.τ) hτE s hs3 (he₁conj ▸ he₁E)
    obtain ⟨i, j, hij⟩ : ∃ i j, ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j ≠ 0 := by
      by_contra hcon
      exact GL_ne_zero (y : GL (Fin 3) F) (by ext i j; by_contra hij; exact hcon ⟨i, j, hij⟩)
    have h1 : T.τ (((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
        ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j :=
      congrFun (congrFun (congrArg (fun g : unitarySU p f F 3 =>
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hfix) i) j
    have hsval : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (c : F)⁻¹ • ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      change ((GeneralLinearGroup.scalar (Fin 3) c⁻¹ * (y : GL (Fin 3) F) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = _
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val]
    rw [hsval] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hyfix i j] at h1
    have h2 : T.τ ((c : F)⁻¹) = (c : F)⁻¹ := mul_right_cancel₀ hij h1
    rw [map_inv₀] at h2
    exact inv_injective h2
  obtain ⟨P, u, hP, hPu⟩ := exists_fixed_unitary_frame h T hτ h3 y hyfix hc hy3 hlift
  have hgenS := closure_fixed_eq_top_unitary_semi h T hgen hP hPu
  rw [eq_top_iff, ← hgenS]
  refine Subgroup.closure_mono ?_
  rintro x (hx | hx)
  · exact ⟨_, hτE, hf₂1, hx⟩
  · exact ⟨e₁, he₁E, he₁1, by rw [hφy]; exact hx⟩

theorem closure_fixSet_eq_top_unitary (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1)
    (hq : 2 < p ^ f) (hgen : 3 ∣ f → SubfieldDiagGenAll h)
    (E : Subgroup (MulAut (unitarySU p f F 3))) (hEab : Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9) (hFix : FixCube E) : Subgroup.closure (fixSet E) = ⊤ := by
  classical
  have hfin := h.finite
  by_cases hall : ∀ e ∈ E, ∃ B : unitaryIsom3 h, e = suConj h B
  · exact closure_fixSet_eq_top_unitary_of_conj h h3 hq E hEab hEcard hFix hall
  · push Not at hall
    obtain ⟨e₀, he₀E, he₀⟩ := hall
    have he₀3 : e₀ ^ 3 = 1 := hEab.2 e₀ he₀E
    rcases exists_suConj_or_conj_suField h hq he₀3 with ⟨B, hB⟩ | ⟨σ, H, hσ, hβ⟩
    · exact absurd hB (he₀ B)
    · obtain ⟨T, i, hi, hTσ⟩ := FrobData.exists_of_orderOf_eq_three hσ
      have hτ : orderOf T.τ = 3 := by
        rcases hi with rfl | rfl
        · rw [hTσ, pow_one]
          exact hσ
        · rw [hTσ, orderOf_pow' σ (by norm_num), hσ]
          norm_num
      obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h
        Nat.prime_three (by norm_num) hτ
      set α : MulAut (unitarySU p f F 3) := suConj h H with hα
      have hmem : suField h T.τ ∈ mapAut α.symm E := by
        rw [mem_mapAut, MulEquiv.symm_symm, congr_eq_mul_mul_inv]
        have : α * suField h T.τ * α⁻¹ = e₀ ^ i := by
          rw [hβ, conj_pow, ← map_pow, ← hTσ]
        rw [this]
        exact E.pow_mem he₀E i
      have := closure_fixSet_eq_top_unitary_of_field h h3 hq T hτ (hgen hdvd _ hcard)
        (mapAut α.symm E) (isElemAbelian_mapAut hEab α.symm)
        (by rw [card_mapAut]; exact hEcard) (hFix.mapAut α.symm) hmem
      exact (closure_fixSet_mapAut_eq_top_iff α.symm E).1 this

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
