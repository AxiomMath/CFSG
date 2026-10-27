module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldSemi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUnitaryAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField CFSG.Semidihedral.FixedFieldData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)

variable {p f : ℕ} {F : Type} [Field F] [Finite F]

theorem card_fixSub (T : FrobData F) (hτ : orderOf T.τ = 3) : Nat.card (fixSub T.τ) = T.r := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  obtain ⟨-, -, -, -, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality p n hpp n.pos F hcard
  obtain ⟨-, hmem, -, hpow⟩ := hA (Subgroup.zpowers T.τ)
  have hfix : fixSub T.τ = FixedPoints.subfield (Subgroup.zpowers T.τ) F := by
    ext x
    rw [mem_fixSub, hmem]
    constructor
    · intro hx a
      have hle : Subgroup.zpowers T.τ ≤ MulAction.stabilizer (F ≃+* F) x :=
        (Subgroup.zpowers_le).2 (by simpa [MulAction.mem_stabilizer_iff] using hx)
      have := hle a.2
      simpa [MulAction.mem_stabilizer_iff] using this
    · intro h
      exact h ⟨T.τ, Subgroup.mem_zpowers _⟩
  rw [hfix]
  rw [Nat.card_zpowers, hτ] at hpow
  have h3 : T.r ^ 3 = Nat.card (FixedPoints.subfield (Subgroup.zpowers T.τ) F) ^ 3 := by
    rw [T.card_eq, hpow]
  exact (Nat.pow_left_injective (by norm_num) h3).symm

theorem FrobData.r_eq_sq (h : UnitaryFieldData p f F) (T : FrobData F) {f₀ : ℕ} (hf : f = 3 * f₀) :
    T.r = (p ^ f₀) ^ 2 := by
  have h1 : T.r ^ 3 = ((p ^ f₀) ^ 2) ^ 3 := by
    rw [T.card_eq, h.card, hf, ← pow_mul, ← pow_mul]
    congr 1
    ring
  exact Nat.pow_left_injective (by norm_num) h1

theorem exists_fixed_unit_norm_eq (h : UnitaryFieldData p f F) (T : FrobData F)
    (hτ : orderOf T.τ = 3) {f₀ : ℕ} (hf : f = 3 * f₀) {a : Fˣ} (ha : T.τ (a : F) = a)
    (haq : a ^ (p ^ f - 1) = 1) : ∃ u : Fˣ, T.τ (u : F) = u ∧ u ^ (p ^ f + 1) = a := by
  have hr := FrobData.r_eq_sq h T hf
  set q₀ := p ^ f₀ with hq₀
  have hq : p ^ f = q₀ ^ 3 := by rw [hf, pow_mul']
  have hq₀1 : 1 < q₀ := by
    have := h.one_le
    exact Nat.one_lt_pow (by omega) h.prime.one_lt
  have ha1 : a ^ (T.r - 1) = 1 := by
    apply Units.ext
    have h1 : (a : F) ^ T.r = a := by rw [← T.apply_eq]; exact ha
    have h0 : (a : F) ≠ 0 := a.ne_zero
    have hpow : (a : F) ^ T.r = (a : F) ^ (T.r - 1) * (a : F) := by
      rw [← pow_succ]
      congr 1
      have := T.two_le
      omega
    rw [hpow] at h1
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ h0 (by rw [h1, one_mul])
  have hgcd : a ^ (q₀ - 1) = 1 := by
    have h1 : a ^ Nat.gcd (q₀ ^ 3 - 1) (q₀ ^ 2 - 1) = 1 := by
      rw [← hq, ← hr]
      exact pow_gcd_eq_one.2 ⟨haq, ha1⟩
    rwa [Nat.pow_sub_one_gcd_pow_sub_one, show Nat.gcd 3 2 = 1 by norm_num, pow_one] at h1
  let K₀ : Subfield F := fixSub T.τ
  have hK₀card : Nat.card K₀ = q₀ ^ 2 := by rw [card_fixSub T hτ, hr]
  let a' : K₀ˣ := Units.mk0 ⟨(a : F), mem_fixSub.2 ha⟩ (by
    intro h0
    exact a.ne_zero (congrArg Subtype.val h0))
  have hGcard : Nat.card K₀ˣ = (q₀ + 1) * (q₀ - 1) := by
    rw [Nat.card_units, hK₀card]
    obtain ⟨s, hs⟩ : ∃ s, q₀ = s + 1 := ⟨q₀ - 1, by omega⟩
    rw [hs]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hdvd : q₀ + 1 ∣ Nat.card K₀ˣ := ⟨q₀ - 1, hGcard⟩
  have hdiv : Nat.card K₀ˣ / (q₀ + 1) = q₀ - 1 := by
    rw [hGcard]
    exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨u₀, hu₀⟩ := exists_pow_eq_of_pow_div_eq_one (G := K₀ˣ) hdvd (x := a')
    (by
      rw [hdiv]
      apply Units.ext
      apply Subtype.ext
      have := congrArg Units.val hgcd
      simpa [a'] using this)
  have hu₀card : u₀ ^ (q₀ ^ 2 - 1) = 1 := by
    have := pow_card_eq_one' (G := K₀ˣ) (x := u₀)
    rwa [Nat.card_units, hK₀card] at this
  refine ⟨Units.map K₀.subtype.toMonoidHom u₀, ?_, ?_⟩
  · exact mem_fixSub.1 (u₀ : K₀).2
  · have hmap : ∀ n : ℕ, Units.map K₀.subtype.toMonoidHom u₀ ^ n =
        Units.map K₀.subtype.toMonoidHom (u₀ ^ n) := fun n => (map_pow _ _ _).symm
    have e1 : Units.map K₀.subtype.toMonoidHom u₀ ^ (q₀ + 1) = a := by
      rw [hmap, hu₀]
      exact Units.ext rfl
    have e2 : Units.map K₀.subtype.toMonoidHom u₀ ^ (q₀ ^ 2 - 1) = 1 := by
      rw [hmap, hu₀card, map_one]
    have hexp : p ^ f + 1 = (q₀ + 1) + (q₀ ^ 2 - 1) * q₀ := by
      rw [hq]
      obtain ⟨t, ht⟩ : ∃ t, q₀ ^ 2 = t + 1 :=
        ⟨q₀ ^ 2 - 1, by have := Nat.one_le_pow 2 q₀ (by omega); omega⟩
      have h3 : q₀ ^ 3 = q₀ ^ 2 * q₀ := by ring
      rw [h3, ht, Nat.add_sub_cancel]
      ring
    rw [hexp, pow_add, e1, pow_mul, e2, one_pow, mul_one]

theorem exists_fixed_isometry (h : UnitaryFieldData p f F) (T : FrobData F)
    (hτ : orderOf T.τ = 3) {f₀ : ℕ} (hf : f = 3 * f₀) {B : unitaryIsom3 h} {c : Fˣ}
    (hc : h.norm (c : F) = 1)
    (hBc : glAut T.τ (B : GL (Fin 3) F) =
      (B : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ y : unitaryIsom3 h, suConj h y = suConj h B ∧
      ∀ i j, T.τ (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
        ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j := by
  set Bm : Matrix (Fin 3) (Fin 3) F := ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hBm
  have hl : Bm.map T.τ = (c : F) • Bm := by
    have := congrArg Units.val hBc
    rw [coe_glAut, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal] at this
    exact this
  obtain ⟨m, hm⟩ := T.exists_unit_smul_fixed Bm (GL_ne_zero (B : GL (Fin 3) F)) c hl
  obtain ⟨i, j, hij⟩ : ∃ i j, Bm i j ≠ 0 := by
    by_contra hcon
    exact GL_ne_zero (B : GL (Fin 3) F) (by ext i j; by_contra hij; exact hcon ⟨i, j, hij⟩)
  have hmc : T.τ (m : F) * c = m := by
    have h1 := congrFun (congrFun hm i) j
    have h2 := congrFun (congrFun hl i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 h2
    rw [h2] at h1
    have : (T.τ (m : F) * c) * Bm i j = m * Bm i j := by linear_combination h1
    exact mul_right_cancel₀ hij this
  have hq1 : (c : F) ^ (p ^ f + 1) = 1 := by rw [← h.norm_eq_pow]; exact hc
  have ha : T.τ ((m ^ (p ^ f + 1) : Fˣ) : F) = (m ^ (p ^ f + 1) : Fˣ) := by
    have h1 : (T.τ (m : F) * c) ^ (p ^ f + 1) = (m : F) ^ (p ^ f + 1) := by rw [hmc]
    rw [mul_pow, hq1, mul_one] at h1
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact h1
  have haq : (m ^ (p ^ f + 1) : Fˣ) ^ (p ^ f - 1) = 1 := by
    have hmul : (p ^ f + 1) * (p ^ f - 1) = (p ^ f) ^ 2 - 1 := by
      have := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
      simpa [sq] using this.symm
    have hc1 : m ^ Nat.card Fˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, h.card_eq_sq] at hc1
    rw [← pow_mul, hmul]
    exact hc1
  obtain ⟨u, huτ, hu⟩ := exists_fixed_unit_norm_eq h T hτ hf ha haq
  have hnorm : h.norm ((m * u⁻¹ : Fˣ) : F) = 1 := by
    rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hu, mul_inv_cancel,
      Units.val_one]
  have hmem : GeneralLinearGroup.scalar (Fin 3) (m * u⁻¹) ∈ unitaryIsom3 h :=
    scalar_mem_unitaryIsom3 h hnorm
  refine ⟨⟨GeneralLinearGroup.scalar (Fin 3) (m * u⁻¹), hmem⟩ * B, ?_, ?_⟩
  · rw [map_mul]
    have := suConj_scalar h hnorm
    rw [this, one_mul]
  · intro i' j'
    have hy : (((⟨GeneralLinearGroup.scalar (Fin 3) (m * u⁻¹), hmem⟩ * B : unitaryIsom3 h) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = ((u⁻¹ : Fˣ) : F) • ((m : F) • Bm) := by
      change ((GeneralLinearGroup.scalar (Fin 3) (m * u⁻¹) * (B : GL (Fin 3) F) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul, Units.val_mul, smul_smul, mul_comm]
    rw [hy]
    have h1 := congrFun (congrFun hm i') j'
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
    rw [h1, Units.val_inv_eq_inv_val, map_inv₀, huτ]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
