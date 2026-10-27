module

public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.WeylOdd
public import CFSG.RankThree.PartOne.SEITZ6.G2BigCell

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.SEITZ6

variable {K : Type} [Field K]

theorem exists_sl2_hom_7_10_sign :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, ∃ ε₁ ε₂ : K,
      (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Upper c) = xp 7 (ε₁ * c)) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Lower c) = xp 10 (ε₂ * c)) := by
  obtain ⟨φ, -, hu, hl⟩ := g2_exists_sl2_hom (K := K) e0
  have hu' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Upper c) = xp 0 c := fun c => by
    rw [hu, xp, rt0_eq, xPar_simple]
  have hl' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Lower c) = xp 2 c := fun c => by
    rw [hl, xp, rt2_eq, xPar_neg_simple]
  obtain ⟨a₁, ha₁, he₁⟩ := weylElement_conj_xp_sign (K := K) e1 (p := 0) (q := 3)
    (by norm_num) reflect_0'
  obtain ⟨a₂, ha₂, he₂⟩ := weylElement_conj_xp_sign (K := K) e0 (p := 3) (q := 7)
    (by norm_num) reflect_3'
  obtain ⟨b₁, hb₁, hf₁⟩ := weylElement_conj_xp_sign (K := K) e1 (p := 2) (q := 6)
    (by norm_num) reflect_2
  obtain ⟨b₂, hb₂, hf₂⟩ := weylElement_conj_xp_sign (K := K) e0 (p := 6) (q := 10)
    (by norm_num) reflect_6
  set W : adjointGroup .G2 K := weylElement .G2 K e0 * weylElement .G2 K e1 with hW
  refine ⟨(MulAut.conj W).toMonoidHom.comp φ, a₂ * a₁, b₂ * b₁, sign_mul_sign ha₂ ha₁,
    sign_mul_sign hb₂ hb₁, fun c => ?_, fun c => ?_⟩
  · rw [MonoidHom.comp_apply, hu', MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hW,
      show weylElement .G2 K e0 * weylElement .G2 K e1 * xp 0 c *
        (weylElement .G2 K e0 * weylElement .G2 K e1)⁻¹ =
        weylElement .G2 K e0 * (weylElement .G2 K e1 * xp 0 c * (weylElement .G2 K e1)⁻¹) *
          (weylElement .G2 K e0)⁻¹ by group, he₁, he₂, mul_assoc]
  · rw [MonoidHom.comp_apply, hl', MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hW,
      show weylElement .G2 K e0 * weylElement .G2 K e1 * xp 2 c *
        (weylElement .G2 K e0 * weylElement .G2 K e1)⁻¹ =
        weylElement .G2 K e0 * (weylElement .G2 K e1 * xp 2 c * (weylElement .G2 K e1)⁻¹) *
          (weylElement .G2 K e0)⁻¹ by group, hf₁, hf₂, mul_assoc]

theorem bigCell_gen (g : adjointGroup .G2 K)
    (hne0 : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ≠ 0) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, ∃ μ₁ μ₂ : K,
      μ₁ ≠ 0 ∧ μ₂ ≠ 0 ∧
      (μ₁ * μ₂ = coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ∨
        μ₁ * μ₂ = -coordAt (rt 10) (g • rootVec .G2 K (rt 7))) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Upper (μ₁ * c)) = xp 7 c) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Lower (μ₂ * c)) = g * xp 7 c * g⁻¹) := by
  have hct := g2_isCTGroupDatum K
  have hext := g2_steinbergExtras K
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := CFSG.LieType.Steinberg.exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, a1, bb1, c1⟩ := borel_stab_X7 hb₁
  obtain ⟨χ₂, a2, bb2, c2⟩ := borel_stab_X7 hb₂
  obtain ⟨t, ht, εa, εb, hεa, hεb, hv, hc⟩ := nrep_stab_X7_sign (K := K) w
  have hlam : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * (εa * coordAt (rt 10) (rootVec .G2 K (rt t)))) := by
    rw [hg, mul_smul, mul_smul, a2, smul_smul_comm, hv, bb1, coordAt_smul, coordAt_smul]
  have ht12 : t < 12 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  have ht10 : t = 10 := by
    by_contra hne
    apply hne0
    rw [hlam, coordAt_rootVec_ne (rt_ne_rt_ten t ht12 hne).symm]
    simp
  subst ht10
  obtain ⟨ψ₀, e₁, e₂, he₁, he₂, hu, hl⟩ := exists_sl2_hom_7_10_sign (K := K)
  have hχ₁ : ((χ₁ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hχ₂ : ((χ₂ : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have hee₁ : e₁ * e₁ = 1 := by rcases he₁ with rfl | rfl <;> simp
  have hee₂ : e₂ * e₂ = 1 := by rcases he₂ with rfl | rfl <;> simp
  have hne₁ : e₁ ≠ 0 := by rcases he₁ with rfl | rfl <;> simp
  have hne₂ : e₂ ≠ 0 := by rcases he₂ with rfl | rfl <;> simp
  have hnb : εb ≠ 0 := by rcases hεb with rfl | rfl <;> simp
  refine ⟨(MulAut.conj b₁).toMonoidHom.comp ψ₀, ((χ₁⁻¹ : Kˣ) : K) * e₁, e₂ * εb * (χ₂ : K),
    mul_ne_zero (Units.ne_zero _) hne₁, mul_ne_zero (mul_ne_zero hne₂ hnb) hχ₂, ?_, fun c => ?_,
    fun c => ?_⟩
  · rw [hlam, coordAt_rootVec_self (isRoot_rt (by norm_num))]
    have hεa2 : εa * εa = 1 := by rcases hεa with rfl | rfl <;> simp
    rcases sign_mul_sign (sign_mul_sign (sign_mul_sign he₁ he₂) hεb) hεa with h | h
    · left
      linear_combination (↑χ₁⁻¹ * ↑χ₂ * εa) * h - (↑χ₁⁻¹ * ↑χ₂ * (e₁ * e₂ * εb)) * hεa2
    · right
      linear_combination (↑χ₁⁻¹ * ↑χ₂ * εa) * h - (↑χ₁⁻¹ * ↑χ₂ * (e₁ * e₂ * εb)) * hεa2
  · have hinv : ((χ₁ : Kˣ) : K) * ((χ₁⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [MonoidHom.comp_apply, hu, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, c1]
    have : (χ₁ : K) * (e₁ * (((χ₁⁻¹ : Kˣ) : K) * e₁ * c)) = c := by
      linear_combination (e₁ * e₁ * c) * hinv + c * hee₁
    rw [this]
  · rw [MonoidHom.comp_apply, hl, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg,
      show b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂ * xp 7 c *
        (b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂)⁻¹ =
        b₁ * (CFSG.LieType.Steinberg.nrep hct w * (b₂ * xp 7 c * b₂⁻¹) *
          (CFSG.LieType.Steinberg.nrep hct w)⁻¹) * b₁⁻¹ by group, c2, hc]
    have : e₂ * (e₂ * εb * (χ₂ : K) * c) = εb * ((χ₂ : K) * c) := by
      linear_combination (εb * (χ₂ : K) * c) * hee₂
    rw [this]

theorem mem_of_mul_sign (k : Subfield K) {μ lam : K} (h : μ = lam ∨ μ = -lam) (hμ : μ ∈ k) :
    lam ∈ k := by
  rcases h with rfl | rfl
  · exact hμ
  · simpa using k.neg_mem hμ

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
