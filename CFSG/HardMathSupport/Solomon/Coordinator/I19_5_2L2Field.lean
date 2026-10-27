module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Fix
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2L2Mat
public import CFSG.Quasithin.Vol2.GoldschmidtH11AutSL
public import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent

public section

open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.Quasithin.H11

variable {F : Type} [Field F]

@[expose] def l2opFieldAutHom : (F ≃+* F) →* MulAut SL(2, F) where
  toFun σ :=
    { toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
      invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
      left_inv := fun x => by ext i j; simp
      right_inv := fun x => by ext i j; simp
      map_mul' := map_mul _ }
  map_one' := by ext x i j; rfl
  map_mul' σ τ := by ext x i j; rfl

theorem l2opFieldAutHom_apply (σ : F ≃+* F) (x : SL(2, F)) :
    l2opFieldAutHom σ x = Matrix.SpecialLinearGroup.map σ.toRingHom x :=
  rfl

theorem l2opFieldAutHom_apply_apply (σ : F ≃+* F) (x : SL(2, F)) (i j : Fin 2) :
    l2opFieldAutHom σ x i j = σ (x i j) :=
  rfl

theorem mem_l2opFix_fieldAut {σ : F ≃+* F} {x : SL(2, F)} :
    x ∈ l2opFix (l2opFieldAutHom σ) ↔ ∀ i j, σ (x i j) = x i j := by
  rw [mem_l2opFix, Matrix.SpecialLinearGroup.ext_iff]
  rfl

theorem uSL_mem_l2opFix {σ : F ≃+* F} {c : F} (hc : σ c = c) :
    uSL c ∈ l2opFix (l2opFieldAutHom σ) := by
  rw [mem_l2opFix, l2opFieldAutHom_apply, map_uSL, hc]

theorem lSL_mem_l2opFix {σ : F ≃+* F} {c : F} (hc : σ c = c) :
    lSL c ∈ l2opFix (l2opFieldAutHom σ) := by
  rw [mem_l2opFix, l2opFieldAutHom_apply, map_lSL, hc]

variable [CharP F 2]

theorem l2op_exists_orderOf_three (σ : F ≃+* F) (N : Subgroup SL(2, F))
    (hNX : N ≤ l2opFix (l2opFieldAutHom σ))
    (hN : ∀ g ∈ l2opFix (l2opFieldAutHom σ), ∀ x ∈ N, g * x * g⁻¹ ∈ N) (hN1 : N ≠ ⊥) :
    ∃ y ∈ N, orderOf y = 3 := by
  obtain ⟨x, hxN, hx1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN1
  have hcomm : ∀ g ∈ l2opFix (l2opFieldAutHom σ), ∀ z ∈ N, z * g * z⁻¹ * g⁻¹ ∈ N := by
    intro g hg z hz
    have : z * g * z⁻¹ * g⁻¹ = z * (g * z⁻¹ * g⁻¹) := by group
    rw [this]
    exact N.mul_mem hz (hN g hg _ (N.inv_mem hz))
  have hl : ∀ z ∈ N, z 0 1 ≠ 0 → ∃ y ∈ N, orderOf y = 3 := by
    intro z hz hz01
    have hzF := mem_l2opFix_fieldAut.1 (hNX hz)
    refine ⟨z * lSL (z 0 1)⁻¹ * z⁻¹ * (lSL (z 0 1)⁻¹)⁻¹,
      hcomm _ (lSL_mem_l2opFix (by rw [map_inv₀, hzF])) z hz, ?_⟩
    apply l2op_orderOf_eq_three
    rw [l2op_trace_comm_lSL, mul_inv_cancel₀ hz01, one_pow]
  by_cases hc : x 1 0 = 0
  · by_cases hb : x 0 1 = 0
    ·
      have hx'N : uSL 1 * x * (uSL 1)⁻¹ ∈ N := hN _ (uSL_mem_l2opFix (map_one σ)) x hxN
      refine hl _ hx'N ?_
      have hdet := x.2
      rw [Matrix.det_fin_two, hb, hc, zero_mul, sub_zero] at hdet
      have h01 : (uSL 1 * x * (uSL 1)⁻¹ : SL(2, F)) 0 1 = x 1 1 - x 0 0 := by
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          Matrix.adjugate_fin_two, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
          dotProduct, hb, hc]
        ring
      rw [h01, sub_ne_zero]
      intro hda
      apply hx1
      have ha2 : x 0 0 ^ 2 = 1 ^ 2 := by
        rw [one_pow, sq]
        nth_rewrite 2 [← hda]
        exact hdet
      have ha : x 0 0 = 1 := CharTwo.sq_injective ha2
      have hd : x 1 1 = 1 := hda.trans ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hd, hb, hc]
    · exact hl x hxN hb
  · have hxF := mem_l2opFix_fieldAut.1 (hNX hxN)
    refine ⟨x * uSL (x 1 0)⁻¹ * x⁻¹ * (uSL (x 1 0)⁻¹)⁻¹,
      hcomm _ (uSL_mem_l2opFix (by rw [map_inv₀, hxF])) x hxN, ?_⟩
    apply l2op_orderOf_eq_three
    rw [l2op_trace_comm_uSL, mul_inv_cancel₀ hc, one_pow]

theorem l2op_glapPrimeCore_fix_fieldAut (σ : F ≃+* F) :
    GLAPPrimeCore 3 ↥(l2opFix (l2opFieldAutHom σ)) = ⊥ := by
  set X := l2opFix (l2opFieldAutHom σ) with hX
  rw [GLAPPrimeCore, CFSG.pPrimeCore, sSup_eq_bot]
  rintro N ⟨hN, hc⟩
  by_contra hN1
  have hN'1 : N.map X.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  have hN'n : ∀ g ∈ X, ∀ x ∈ N.map X.subtype, g * x * g⁻¹ ∈ N.map X.subtype := by
    intro g hg x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 := hN.conj_mem z hz ⟨g, hg⟩
    refine Subgroup.mem_map.2 ⟨_, h1, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
  obtain ⟨y, hy, hy3⟩ :=
    l2op_exists_orderOf_three σ (N.map X.subtype) (Subgroup.map_subtype_le N) hN'n hN'1
  have h3 := Subgroup.orderOf_dvd_natCard _ hy
  rw [hy3, Subgroup.card_map_of_injective X.subtype_injective] at h3
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc h3

theorem l2op_eq_one_of_conj_uSL_lSL {a : SL(2, F)} (hu : a * uSL 1 * a⁻¹ = uSL 1)
    (hl : a * lSL 1 * a⁻¹ = lSL 1) : a = 1 := by
  have hu' : (a : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (a : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : SL(2, F) => ((x * a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) hu
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_uSL] using this
  have hl' : (a : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (a : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : SL(2, F) => ((x * a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) hl
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_lSL] using this
  have hdet := a.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun hu' 0) 0
  have h01 := congrFun (congrFun hu' 0) 1
  have h11 := congrFun (congrFun hl' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  have hps : (a : Matrix (Fin 2) (Fin 2) F) 0 0 = (a : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    linear_combination h01
  have hp : (a : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_mul_self_eq_one
    rw [h00, h11] at hdet
    nth_rewrite 2 [hps]
    linear_combination hdet
  have hs : (a : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := hps ▸ hp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, hp, hs]

theorem l2op_fix_fieldAut_centralizer [Finite F] {n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hσ : σ ^ 3 = 1) (y : MulAut SL(2, F))
    (hy : ∀ x ∈ l2opFix (l2opFieldAutHom σ), y x = x) (hcop : Nat.Coprime 3 (orderOf y)) :
    y = 1 := by
  obtain ⟨τ, a, ha⟩ := exists_aut_formula y
  have hu : ∀ c, σ c = c → a * uSL (τ c) * a⁻¹ = uSL c := by
    intro c hc
    have := hy (uSL c) (uSL_mem_l2opFix hc)
    rwa [ha, map_uSL] at this
  have hl1 : a * lSL 1 * a⁻¹ = lSL 1 := by
    have := hy (lSL 1) (lSL_mem_l2opFix (map_one σ))
    rwa [ha, map_lSL, map_one] at this
  have hu1 : a * uSL 1 * a⁻¹ = uSL 1 := by
    have := hu 1 (map_one σ)
    rwa [map_one] at this
  have ha1 : a = 1 := l2op_eq_one_of_conj_uSL_lSL hu1 hl1
  have hτ : ∀ c, σ c = c → τ c = c := by
    intro c hc
    have := hu c hc
    rw [ha1, one_mul, inv_one, mul_one] at this
    exact uSL_injective this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.RankThree.LinearTwo.mem_zpowers_of_forall_fixed Nat.prime_two hn hcard σ τ hτ)
  have hτ3 : τ ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hσ,
      _root_.one_zpow]
  have hyτ : y = l2opFieldAutHom τ := by
    ext x : 1
    rw [ha x, ha1, one_mul, inv_one, mul_one]
    rfl
  have hy3 : y ^ 3 = 1 := by rw [hyτ, ← map_pow, hτ3, map_one]
  have hord : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) with h | h
    · exact h
    · rw [h] at hcop
      norm_num at hcop
  exact orderOf_eq_one_iff.1 hord

end CFSG.HardMathSupport.Solomon.Coordinator
