module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldFrame
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldHilbert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LieType.Chevalley (fixSubfield mem_fixSubfield)

variable {p f : ℕ} {F : Type} [Field F]

theorem suField_ne_one (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) {σ : F ≃+* F}
    (hσ : σ ≠ 1) : suField h σ ≠ 1 := by
  intro h1
  apply hσ
  have h2 := descend_suField h hq σ
  rw [h1, map_one, map_one] at h2
  exact (eq_one_of_psuConj_mul_psuField_eq_one (h := h) 1 σ (by rw [map_one, one_mul]; exact
    h2.symm)).1

theorem closure_fixed_eq_top_unitary_of_field
    {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal] (z : X) [Finite F]
    (h : UnitaryFieldData p f F) (h3 : 3 ∣ p ^ f + 1) (hq : 2 < p ^ f) (T : FrobData F)
    (hτ : orderOf T.τ = 3) (hgen : SubfieldDiagGen h (fixSubfield T.τ))
    (ψ : unitarySU p f F 3 ≃* K) (hzc : z ∈ Subgroup.center X)
    (hCz : ∀ c ∈ Subgroup.centralizer (K : Set X), c ^ 3 = 1 → c ∈ Subgroup.zpowers z)
    {A : Subgroup X} (hAe : Open.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) (hzA : z ∈ A)
    {f₂ : X} (hf₂A : f₂ ∈ A) (hf₂ : actionAut K ψ f₂ = suField h T.τ) :
    Subgroup.closure {x : K | ∃ g ∈ A, g ∉ Subgroup.centralizer (K : Set X) ∧
      g * (x : X) * g⁻¹ = x} = ⊤ := by
  classical
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    isMulCommutative_iff_of_setLike.1 hAe.1 a ha b hb
  obtain ⟨a, haA, ha⟩ := exists_mem_not_mem_sup_zpowers hAe hAcard hzA hf₂A
  have hβ3 : actionAut K ψ a ^ 3 = 1 := by rw [← map_pow, hAe.2 a haA, map_one]
  obtain ⟨m, B, hB⟩ := exists_suConj_mul_pow h hq hτ hβ3
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : X, f₁ = a * f₂ ^ m := ⟨_, rfl⟩
  have hf₁A : f₁ ∈ A := hf₁ ▸ mul_mem haA (pow_mem hf₂A m)
  have hf₁3 : f₁ ^ 3 = 1 := hAe.2 f₁ hf₁A
  have h12 : f₁ * f₂ = f₂ * f₁ := hcomm f₁ hf₁A f₂ hf₂A
  have hφ₁ : actionAut K ψ f₁ = suConj h B := by rw [hf₁, map_mul, map_pow, hf₂, hB]
  have hf₁C : f₁ ∉ Subgroup.centralizer (K : Set X) := by
    intro hmem
    apply ha
    have h1 : a = f₁ * (f₂ ^ m)⁻¹ := by rw [hf₁]; group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left (hCz f₁ hmem hf₁3))
      (inv_mem (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers f₂) m)))
  have hτ1 : T.τ ≠ 1 := by
    rintro h1
    rw [h1, orderOf_one] at hτ
    exact absurd hτ (by norm_num)
  have hf₂C : f₂ ∉ Subgroup.centralizer (K : Set X) := by
    intro hmem
    exact suField_ne_one h hq hτ1 (hf₂ ▸ actionAut_eq_one_of_mem_centralizer K ψ hmem)
  have hφcomm : suConj h B * suField h T.τ = suField h T.τ * suConj h B := by
    rw [← hφ₁, ← hf₂, ← map_mul, ← map_mul, h12]
  obtain ⟨c₁, hc₁, hBc⟩ := exists_scalar_of_comm h hφcomm
  obtain ⟨f₀, hf₀⟩ := (CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h
    Nat.prime_three (by norm_num) hτ).1
  obtain ⟨y, hyB, hyfix⟩ := exists_fixed_isometry h T hτ hf₀ hc₁ hBc
  have hφy : actionAut K ψ f₁ = suConj h y := by rw [hφ₁, hyB]
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
  have hsact : ∀ t, actionAut K ψ f₁ t = s * t * s⁻¹ := by
    intro t
    rw [hφy, hsy]
    rfl
  obtain ⟨c', -, hc'⟩ := exists_scalar_pow_three h (B := y) (by
    rw [← hφy, ← map_pow, hf₁3, map_one])
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
    have hfix := actionAut_fix_of_pow_three K ψ hzc hCz h12 hf₁3 hs3 hsact
    rw [hf₂] at hfix
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
  have hφψ := coe_psi_actionAut K ψ
  have hsub : ∀ x ∈ {x : unitarySU p f F 3 | suField h T.τ x = x ∨ suConj h y x = x},
      (ψ x : K) ∈ {x : K | ∃ g ∈ A, g ∉ Subgroup.centralizer (K : Set X) ∧
        g * (x : X) * g⁻¹ = x} := by
    rintro x (hx | hx)
    · refine ⟨f₂, hf₂A, hf₂C, ?_⟩
      have h1 := hφψ f₂ x
      rw [hf₂, hx] at h1
      exact h1.symm
    · refine ⟨f₁, hf₁A, hf₁C, ?_⟩
      have h1 := hφψ f₁ x
      rw [hφy, hx] at h1
      exact h1.symm
  rw [eq_top_iff]
  have hmap : Subgroup.map (ψ : unitarySU p f F 3 →* K) (Subgroup.closure
      {x : unitarySU p f F 3 | suField h T.τ x = x ∨ suConj h y x = x}) = ⊤ := by
    rw [hgenS, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr ψ.surjective
  rw [MonoidHom.map_closure] at hmap
  rw [← hmap]
  exact Subgroup.closure_mono (Set.image_subset_iff.mpr (fun x hx => hsub x hx))

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
