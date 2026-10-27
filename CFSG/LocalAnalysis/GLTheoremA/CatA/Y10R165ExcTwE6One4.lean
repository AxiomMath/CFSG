module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAutSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

open Matrix CFSG CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f p : ℕ} {K : Type} [Field K]

variable {F p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def diag3 (a b c : Kˣ) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(a : K), (b : K), (c : K), ((c⁻¹ : Kˣ) : K),
      ((b⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_six]
      simp)

@[simp] theorem coe_diag3 (a b c : Kˣ) :
    ((diag3 a b c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal ![(a : K), (b : K), (c : K), ((c⁻¹ : Kˣ) : K),
        ((b⁻¹ : Kˣ) : K), ((a⁻¹ : Kˣ) : K)] := rfl

theorem diag3_one : diag3 (1 : Kˣ) 1 1 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [coe_diag3]

theorem diag3_mul (a b c a' b' c' : Kˣ) :
    diag3 a b c * diag3 a' b' c' = diag3 (a * a') (b * b') (c * c') := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diag3, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_six]
  all_goals ring

theorem diag3_mem_gramSU (h : UnitaryFieldData 2 F K) (a b c : Kˣ)
    (ha : h.bar (a : K) = a) (hb : h.bar (b : K) = b) (hc : h.bar (c : K) = c) :
    diag3 a b c ∈ gramSU h (CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K) := by
  refine ⟨?_, by
    rw [coe_diag3, Matrix.det_diagonal, Fin.prod_univ_six]; simp⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diag3, CFSG.SeitzReduction.TwistedE6Pilot.coe_antiIdGL,
      CFSG.LieType.Chevalley.E6GraphLevi.antiId, Matrix.mul_apply, Matrix.diagonal,
      Fin.sum_univ_six, Fin.rev, ha, hb, hc]

theorem pow_val_add_of_orderOf [NeZero p] (ζ : Kˣ) (hζ : orderOf ζ = p) (a b : ZMod p) :
    ζ ^ ((a + b).val) = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add]
  refine pow_eq_pow_of_modEq (n := p) ?_ ?_
  · rw [ZMod.val_add]
    exact Nat.mod_modEq (a.val + b.val) p
  · simpa [hζ] using pow_orderOf_eq_one ζ

@[expose] noncomputable def r3Hom (h : UnitaryFieldData 2 F K) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Multiplicative (ZMod p × ZMod p × ZMod p) →*
      ↥(gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K)) where
  toFun x :=
    ⟨diag3 (ζ ^ (x.toAdd.1).val) (ζ ^ (x.toAdd.2.1).val) (ζ ^ (x.toAdd.2.2).val),
      diag3_mem_gramSU h _ _ _
        (by simp only [Units.val_pow_eq_pow_val, map_pow, hζbar])
        (by simp only [Units.val_pow_eq_pow_val, map_pow, hζbar])
        (by simp only [Units.val_pow_eq_pow_val, map_pow, hζbar])⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [diag3_one]
  map_mul' x y := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Subgroup.coe_mul, Units.val_mul, diag3_mul, ← pow_val_add_of_orderOf (p := p) ζ hζ]
    rfl

theorem quotient_r3Hom_injective (h : UnitaryFieldData 2 F K) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) :
    Function.Injective ((QuotientGroup.mk'
      (normOneScalars h (gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6)).comp
      (r3Hom h p ζ hζ hζbar)) := by
  intro x y hxy
  simp only [MonoidHom.comp_apply] at hxy
  have h1 : (QuotientGroup.mk'
      (normOneScalars h (gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6))
      (r3Hom h p ζ hζ hζbar (x / y)) = 1 := by
    rw [map_div (f := r3Hom h p ζ hζ hζbar),
      map_div (f := QuotientGroup.mk' (normOneScalars h (gramSU h
        ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
          Matrix (Fin 6) (Fin 6) K)) 6)), hxy]
    exact div_eq_one.mpr rfl
  have hmem : r3Hom h p ζ hζ hζbar (x / y) ∈
      normOneScalars h (gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K :
        GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) 6 :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨cc, hc, hcn, hg⟩ := (mem_normOneScalars).mp hmem
  have hz := congrArg (fun w : GL (Fin 6) K => ((w : Matrix (Fin 6) (Fin 6) K))) hg
  have e00 : (ζ : K) ^ ((x / y).toAdd.1).val = (cc : K) := by
    have := congrFun (congrFun hz 0) 0
    simpa [r3Hom, coe_diag3] using this
  have e55 : (((ζ : K) ^ ((x / y).toAdd.1).val))⁻¹ = (cc : K) := by
    have := congrFun (congrFun hz 5) 5
    simpa [r3Hom, coe_diag3] using this
  have h05 : ((ζ : K) ^ ((x / y).toAdd.1).val) =
      (((ζ : K) ^ ((x / y).toAdd.1).val))⁻¹ := e00.trans e55.symm
  have e11 : (ζ : K) ^ ((x / y).toAdd.2.1).val = (cc : K) := by
    have := congrFun (congrFun hz 1) 1
    simpa [r3Hom, coe_diag3] using this
  have e44 : (((ζ : K) ^ ((x / y).toAdd.2.1).val))⁻¹ = (cc : K) := by
    have := congrFun (congrFun hz 4) 4
    simpa [r3Hom, coe_diag3] using this
  have h14 : ((ζ : K) ^ ((x / y).toAdd.2.1).val) =
      (((ζ : K) ^ ((x / y).toAdd.2.1).val))⁻¹ := e11.trans e44.symm
  have e22 : (ζ : K) ^ ((x / y).toAdd.2.2).val = (cc : K) := by
    have := congrFun (congrFun hz 2) 2
    simpa [r3Hom, coe_diag3] using this
  have e33 : (((ζ : K) ^ ((x / y).toAdd.2.2).val))⁻¹ = (cc : K) := by
    have := congrFun (congrFun hz 3) 3
    simpa [r3Hom, coe_diag3] using this
  have h23 : ((ζ : K) ^ ((x / y).toAdd.2.2).val) =
      (((ζ : K) ^ ((x / y).toAdd.2.2).val))⁻¹ := e22.trans e33.symm
  have sq0 : (ζ ^ ((x / y).toAdd.1).val) ^ 2 = 1 := by
    have h' : ζ ^ ((x / y).toAdd.1).val = (ζ ^ ((x / y).toAdd.1).val)⁻¹ :=
      Units.ext (by simpa using h05)
    rw [sq]
    conv_lhs => arg 2; rw [h']
    exact mul_inv_cancel _
  have sq1 : (ζ ^ ((x / y).toAdd.2.1).val) ^ 2 = 1 := by
    have h' : ζ ^ ((x / y).toAdd.2.1).val = (ζ ^ ((x / y).toAdd.2.1).val)⁻¹ :=
      Units.ext (by simpa using h14)
    rw [sq]
    conv_lhs => arg 2; rw [h']
    exact mul_inv_cancel _
  have sq2 : (ζ ^ ((x / y).toAdd.2.2).val) ^ 2 = 1 := by
    have h' : ζ ^ ((x / y).toAdd.2.2).val = (ζ ^ ((x / y).toAdd.2.2).val)⁻¹ :=
      Units.ext (by simpa using h23)
    rw [sq]
    conv_lhs => arg 2; rw [h']
    exact mul_inv_cancel _
  have sq0' : ζ ^ (2 * ((x / y).toAdd.1).val) = 1 := by
    rw [mul_comm, pow_mul]; exact sq0
  have sq1' : ζ ^ (2 * ((x / y).toAdd.2.1).val) = 1 := by
    rw [mul_comm, pow_mul]; exact sq1
  have sq2' : ζ ^ (2 * ((x / y).toAdd.2.2).val) = 1 := by
    rw [mul_comm, pow_mul]; exact sq2
  have dvd0 : p ∣ 2 * ((x / y).toAdd.1).val := by
    simpa [hζ] using orderOf_dvd_iff_pow_eq_one.mpr sq0'
  have dvd1 : p ∣ 2 * ((x / y).toAdd.2.1).val := by
    simpa [hζ] using orderOf_dvd_iff_pow_eq_one.mpr sq1'
  have dvd2 : p ∣ 2 * ((x / y).toAdd.2.2).val := by
    simpa [hζ] using orderOf_dvd_iff_pow_eq_one.mpr sq2'
  have odd : ¬ p ∣ 2 := fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hv0 : ((x / y).toAdd.1).val = 0 := by
    have hd : p ∣ ((x / y).toAdd.1).val := by
      rcases hp.dvd_mul.mp dvd0 with h | h
      · exact absurd h odd
      · exact h
    exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt ((x / y).toAdd.1))
  have hv1 : ((x / y).toAdd.2.1).val = 0 := by
    have hd : p ∣ ((x / y).toAdd.2.1).val := by
      rcases hp.dvd_mul.mp dvd1 with h | h
      · exact absurd h odd
      · exact h
    exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt ((x / y).toAdd.2.1))
  have hv2 : ((x / y).toAdd.2.2).val = 0 := by
    have hd : p ∣ ((x / y).toAdd.2.2).val := by
      rcases hp.dvd_mul.mp dvd2 with h | h
      · exact absurd h odd
      · exact h
    exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt ((x / y).toAdd.2.2))
  have hz0 : (x / y).toAdd.1 = 0 := ZMod.val_eq_zero _ |>.mp hv0
  have hz1 : (x / y).toAdd.2.1 = 0 := ZMod.val_eq_zero _ |>.mp hv1
  have hz2 : (x / y).toAdd.2.2 = 0 := ZMod.val_eq_zero _ |>.mp hv2
  have ht : (x / y).toAdd = 0 := by
    ext <;> assumption
  have hzy : x / y = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using ht
  have : x = y := by
    calc x = (x / y) * y := (div_mul_cancel x y).symm
      _ = 1 * y := by rw [hzy]
      _ = y := one_mul y
  exact this

private theorem isElemAbelian_multiplicative_zmod [Fact p.Prime] :
    IsElemAbelian p (⊤ : Subgroup (Multiplicative (ZMod p × ZMod p × ZMod p))) := by
  have hpow : ∀ x : Multiplicative (ZMod p × ZMod p × ZMod p),
      ∀ n : ℕ, (x ^ n).toAdd = n • x.toAdd := by
    intro x n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      change (x ^ n).toAdd + x.toAdd = (n + 1) • x.toAdd
      rw [ih, succ_nsmul]
  refine ⟨⟨⟨fun a b => mul_comm' a b⟩⟩, fun x _ => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hpow x p]
  show p • x.toAdd = (0 : ZMod p × ZMod p × ZMod p)
  ext <;> simp [nsmul_eq_mul, CharP.cast_eq_zero (ZMod p) p]

noncomputable abbrev N6 (h : UnitaryFieldData 2 f K) :
    Subgroup ↥(gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) :=
  normOneScalars h (gramSU h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
    Matrix (Fin 6) (Fin 6) K)) 6

@[expose] noncomputable def r3ToP (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Multiplicative (ZMod p × ZMod p × ZMod p) →*
      primeFormP h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) :=
  (QuotientGroup.mk' (N6 h)).comp (r3Hom h p ζ hζ hζbar)

@[expose] noncomputable def R3bar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Subgroup (primeFormP h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K)) :=
  (r3ToP h p ζ hζ hζbar).range

theorem card_R3bar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    Nat.card (R3bar h p hp hp2 ζ hζ hζbar) = p ^ 3 := by
  rw [R3bar, r3ToP,
    ← Nat.card_congr (MonoidHom.ofInjective
      (quotient_r3Hom_injective h p hp hp2 ζ hζ hζbar)).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p × ZMod p × ZMod p)),
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

theorem isElemAbelian_R3bar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    IsElemAbelian p (R3bar h p hp hp2 ζ hζ hζbar) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [R3bar, r3ToP, MonoidHom.range_eq_map]
  exact CFSG.SectionRank.isElemAbelian_map isElemAbelian_multiplicative_zmod _

@[expose] noncomputable def R3Levi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (R3bar h p hp hp2 ζ hζ hζbar).map
    ((su6Levi σ).subtype.comp (su6LeviEquiv h hσ).toMonoidHom)

theorem R3Levi_le_su6Levi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    R3Levi h p hp hp2 ζ hζ hζbar hσ ≤ su6Levi σ := by
  rw [R3Levi]
  rintro _ ⟨x, -, rfl⟩
  exact Subtype.coe_prop _

theorem R3Levi_le_C0 {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    R3Levi h p hp hp2 ζ hζ hζbar hσ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  (R3Levi_le_su6Levi h p hp hp2 ζ hζ hζbar hσ).trans (su6Levi_le_graphFixedRootGroup σ)

theorem card_R3Levi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Nat.card (R3Levi h p hp hp2 ζ hζ hζbar hσ) = p ^ 3 := by
  rw [R3Levi, Subgroup.card_map_of_injective]
  · exact card_R3bar h p hp hp2 ζ hζ hζbar
  · exact (su6Levi σ).subtype_injective.comp (su6LeviEquiv h hσ).injective

theorem isElemAbelian_R3Levi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    IsElemAbelian p (R3Levi h p hp hp2 ζ hζ hζbar hσ) := by
  rw [R3Levi]
  exact CFSG.SectionRank.isElemAbelian_map (isElemAbelian_R3bar h p hp hp2 ζ hζ hζbar) _

@[expose] noncomputable def zbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (ζ : Kˣ)
    (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    primeFormP h ((CFSG.SeitzReduction.TwistedE6Pilot.antiIdGL K : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) :=
  r3ToP h p ζ hζ hζbar (Multiplicative.ofAdd ((1, 0, 0) : ZMod p × ZMod p × ZMod p))

theorem zbar_mem (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    zbar h p ζ hζ hζbar ∈ R3bar h p hp hp2 ζ hζ hζbar :=
  ⟨_, rfl⟩

theorem orderOf_zbar (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime)
    (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ) :
    orderOf (zbar h p ζ hζ hζbar) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [zbar, r3ToP, orderOf_injective _ (quotient_r3Hom_injective h p hp hp2 ζ hζ hζbar)]
  refine orderOf_eq_prime ?_ ?_
  · exact isElemAbelian_multiplicative_zmod.2 _ (Subgroup.mem_top _)
  · intro h1
    have h2 := congrArg (fun x : Multiplicative (ZMod p × ZMod p × ZMod p) => x.toAdd.1) h1
    simp at h2

@[expose] noncomputable def zLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ModGL TwistTag.E6.tag K :=
  (su6LeviEquiv h hσ (zbar h p ζ hζ hζbar) : ModGL TwistTag.E6.tag K)

theorem zLevi_mem {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    zLevi h p hp hp2 ζ hζ hζbar hσ ∈ R3Levi h p hp hp2 ζ hζ hζbar hσ :=
  ⟨_, zbar_mem h p hp hp2 ζ hζ hζbar, rfl⟩

theorem orderOf_zLevi {σ : K →+* K} (h : UnitaryFieldData 2 f K) [Finite K] (p : ℕ)
    [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    orderOf (zLevi h p hp hp2 ζ hζ hζbar hσ) = p := by
  rw [zLevi]
  have h := (orderOf_injective (su6LeviEquiv h hσ).toMonoidHom
    (su6LeviEquiv h hσ).injective (zbar h p ζ hζ hζbar)).trans
    (orderOf_zbar h p hp hp2 ζ hζ hζbar)
  simpa using h

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
