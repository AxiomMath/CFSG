module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Sup

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Odd

theorem odd_orderOf_of_mem_oddCard {G : Type*} [Group G] {N : Subgroup G}
    (hodd : Odd (Nat.card N)) {x : G} (hx : x ∈ N) : Odd (orderOf x) := by
  have h : orderOf (⟨x, hx⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h
  exact hodd.of_dvd_nat h

theorem neg_one_ne_one_SL2_of_two_ne_zero {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact h2 (by linear_combination -this)

variable {F : Type} [Field F]

theorem sl2_odd_normal_eq_bot [Finite F] (h4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    {N : Subgroup (SL(2, F))} (hN : N.Normal) (hodd : ∀ x ∈ N, Odd (orderOf x)) : N = ⊥ := by
  rcases sl2_normal_le_center_or_eq_top h4 hN with hc | htop
  · rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz2 : z * z = 1 := by
      obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hc hz)
      rw [Fintype.card_fin] at hr
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hrz, ← map_mul, ← sq, hr, map_one]
      rfl
    have hd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      have := hodd z hz
      rw [h] at this
      exact absurd this (by decide)
  · exfalso
    have hm : (-1 : SL(2, F)) ∈ N := by rw [htop]; exact Subgroup.mem_top _
    have hsq : (-1 : SL(2, F)) ^ 2 = 1 := by
      rw [sq]
      apply Subtype.ext
      simp
    have h2' : orderOf (-1 : SL(2, F)) = 2 :=
      orderOf_eq_prime hsq (neg_one_ne_one_SL2_of_two_ne_zero h2)
    have := hodd _ hm
    rw [h2'] at this
    exact absurd this (by decide)

end Odd

section Three

theorem sl2_zmod3_pow12 : ∀ g : SL(2, ZMod 3), g ^ 12 = 1 := by decide +kernel

theorem sl2_zmod3_eq_one : ∀ g : SL(2, ZMod 3), g ^ 3 = 1 →
    (∀ h : SL(2, ZMod 3), (g * h * g⁻¹ * h⁻¹) ^ 3 = 1) → g = 1 := by decide +kernel

theorem sl2_three_odd_normal_eq_bot {F : Type} [Field F] (hF : Nat.card F = 3)
    {N : Subgroup (SL(2, F))} (hN : N.Normal) (hodd : ∀ x ∈ N, Odd (orderOf x)) : N = ⊥ := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hFcard : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hFcard
  let ψ : SL(2, ZMod 3) →* SL(2, F) := Matrix.SpecialLinearGroup.map (e : ZMod 3 →+* F)
  have hψinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    ext i j
    have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) i j) h
    simpa [ψ, Matrix.SpecialLinearGroup.map_apply_coe] using this
  have hψsurj : Function.Surjective ψ := by
    intro y
    refine ⟨Matrix.SpecialLinearGroup.map (e.symm : F →+* ZMod 3) y, ?_⟩
    apply Subtype.ext
    ext i j
    simp [ψ, Matrix.SpecialLinearGroup.map_apply_coe]
  have hN' : (N.comap ψ).Normal := hN.comap ψ
  have hcube : ∀ x ∈ N.comap ψ, x ^ 3 = 1 := by
    intro x hx
    have hodd' : Odd (orderOf x) := by
      rw [← orderOf_injective ψ hψinj x]
      exact hodd _ hx
    have hd : orderOf x ∣ 12 := orderOf_dvd_of_pow_eq_one (sl2_zmod3_pow12 x)
    have hc : Nat.Coprime (orderOf x) 4 := by
      have := (Odd.coprime_two_right hodd').pow_right 2
      simpa using this
    have hd3 : orderOf x ∣ 3 := hc.dvd_of_dvd_mul_right (by simpa using hd)
    exact orderOf_dvd_iff_pow_eq_one.mp hd3
  have hbot : ∀ x ∈ N.comap ψ, x = 1 := by
    intro x hx
    refine sl2_zmod3_eq_one x (hcube x hx) fun h => hcube _ ?_
    have h1 : h * x⁻¹ * h⁻¹ ∈ N.comap ψ := hN'.conj_mem x⁻¹ (inv_mem hx) h
    have := mul_mem hx h1
    simpa [mul_assoc] using this
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, rfl⟩ := hψsurj y
  have := hbot x hy
  rw [this, map_one]

end Three

section TD4

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem SProd_conj_slB {n : twistedGroup σ} (hn : n ∈ SProd σ hσ) (C : SL(2, K)) :
    ∃ C' : SL(2, K), n * slB σ hσ C * n⁻¹ = slB σ hσ C' := by
  obtain ⟨t, ht, A, B, rfl⟩ := hn
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
  exact ⟨_, pair_prod_conj2 (slLong_comm_slB hσ) hs A B C⟩

include hσ in
theorem exists_slLong_of_centralizes_slB {z : twistedGroup σ} (hz : z ∈ SProd σ hσ)
    (hc : ∀ C : SL(2, K), z * slB σ hσ C = slB σ hσ C * z) :
    ∃ A' : SL(2, fixedField σ), z = slLong σ hσ A' := by
  obtain ⟨t, ht, A, B, rfl⟩ := hz
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, hsb, hs⟩ := torus_conj_slB hσ hb
  have hzB : ∀ C : SL(2, K), (t * slLong σ hσ A * slB σ hσ B) * slB σ hσ C *
      (t * slLong σ hσ A * slB σ hσ B)⁻¹ =
      slB σ hσ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL B) C) :=
    fun C => pair_prod_conj2 (slLong_comm_slB hσ) hs A B C
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq
    (D := 1) (E := diagGL s * Matrix.SpecialLinearGroup.toGL B) (fun C => by
      apply slB_injective hσ
      rw [← hzB C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  have hscal : ((diagGL s * Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    rw [hcs]; simp
  obtain ⟨v, hBv, hsv⟩ := diag_mul_scalar s B c hscal
  subst hBv
  set t'' : twistedGroup σ := t * slB σ hσ (HSL v) with ht''
  have ht''TK : t'' ∈ TK σ := mul_mem ⟨b, hb⟩ ⟨_, twistedIncl_slB_HSL hσ v⟩
  obtain ⟨b'', hb''⟩ := ht''TK
  obtain ⟨s'', hs''b, hs''⟩ := torus_conj_slB hσ hb''
  have hdiag : ((diagGL s * Matrix.SpecialLinearGroup.toGL (HSL v) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = ((v⁻¹ : Kˣ) : K) • 1 := by
    rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_HSL, hsv]
    have hv0 : (v : K) ≠ 0 := v.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hact : ∀ C : SL(2, K), t'' * slB σ hσ C * t''⁻¹ = slB σ hσ C := by
    intro C
    calc t'' * slB σ hσ C * t''⁻¹
        = t * (slB σ hσ (HSL v) * slB σ hσ C * (slB σ hσ (HSL v))⁻¹) * t⁻¹ := by
          rw [ht'']; group
      _ = t * slB σ hσ (HSL v * C * (HSL v)⁻¹) * t⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = slB σ hσ (glConjSL (diagGL s) (HSL v * C * (HSL v)⁻¹)) := hs _
      _ = slB σ hσ C := by
          congr 1
          rw [← glConjSL_toGL, ← glConjSL_mul]
          exact glConjSL_of_scalar hdiag C
  have hs''1 : s'' = 1 := by
    obtain ⟨c', -, hc'⟩ := exists_scalar_of_glConjSL_eq (D := 1) (E := diagGL s'') (fun C => by
      apply slB_injective hσ
      rw [glConjSL_one]
      exact ((hs'' C).symm.trans (hact C)).symm)
    have e00 := congrFun (congrFun hc' 0) 0
    have e11 := congrFun (congrFun hc' 1) 1
    simp [coe_diagGL_two] at e00 e11
    exact Units.ext (by rw [Units.val_one]; exact e00.trans e11.symm)
  obtain ⟨h1, h3, h0, h2⟩ := torus_compat hb''
  have e : ((b'' (nd 1) : Kˣ) : K) * (b'' (nd 2) : K) * (b'' (nd 3) : K) = 1 := by
    have := hs''b
    rw [hs''1] at this
    simpa using (congrArg Units.val this).symm
  have e' : ((b'' (nd 3) : Kˣ) : K) * (b'' (nd 2) : K) * (b'' (nd 0) : K) = 1 := by
    have := congrArg σ e
    rw [map_mul, map_mul, map_one, ← h3, ← h2, ← h0] at this
    exact this
  have hb10 : ((b'' (nd 1) : Kˣ) : K) = (b'' (nd 0) : K) := by
    have h : ((b'' (nd 1) : Kˣ) - (b'' (nd 0) : K)) *
        ((b'' (nd 2) : K) * (b'' (nd 3) : K)) = 0 := by
      linear_combination e - e'
    rcases mul_eq_zero.mp h with h | h
    · linear_combination h
    · exact absurd h (mul_ne_zero (b'' (nd 2)).ne_zero (b'' (nd 3)).ne_zero)
  have hβσ : σ ((b'' (nd 0) : Kˣ) : K) = ((b'' (nd 0) : Kˣ) : K) := h1.symm.trans hb10
  have hb30 : ((b'' (nd 3) : Kˣ) : K) = (b'' (nd 0) : K) := by rw [h3, hb10, hβσ]
  set β : Kˣ := b'' (nd 0) with hβ
  let βF : fixedField σ := ⟨(β : K), hβσ⟩
  have hβF0 : βF ≠ 0 := fun h => β.ne_zero (congrArg Subtype.val h)
  let u : (fixedField σ)ˣ := (Units.mk0 βF hβF0)⁻¹
  set uK : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom u with huK
  have huKc : ((uK : Kˣ) : K) = ((β : Kˣ) : K)⁻¹ := by
    show (((u : (fixedField σ)ˣ) : fixedField σ) : K) = _
    simp [u, βF]
  have h0' : b'' (nd 0) = (fun j => uK ^ d4.cartan (nd 2) j) (nd 0) := by
    apply Units.ext
    show ((β : Kˣ) : K) = ((uK ^ d4.cartan (nd 2) (nd 0) : Kˣ) : K)
    rw [show d4.cartan (nd 2) (nd 0) = -1 by decide, zpow_neg_one, Units.val_inv_eq_inv_val,
      huKc, inv_inv]
  have h2' : b'' (nd 2) = (fun j => uK ^ d4.cartan (nd 2) j) (nd 2) := by
    apply Units.ext
    show ((b'' (nd 2) : Kˣ) : K) = ((uK ^ d4.cartan (nd 2) (nd 2) : Kˣ) : K)
    rw [show d4.cartan (nd 2) (nd 2) = 2 by decide, zpow_ofNat, Units.val_pow_eq_pow_val, huKc]
    have hβ0 : ((β : Kˣ) : K) ≠ 0 := β.ne_zero
    rw [hb10, hb30] at e
    field_simp
    linear_combination e
  have htup := tuple_eq_of_compat hb'' (twistedIncl_slLong_HSL hσ u) h0' h2'
  have hty : t'' = slLong σ hσ (HSL u) :=
    twistedIncl_injective σ (by rw [hb'', twistedIncl_slLong_HSL hσ, htup])
  have hz : t * slLong σ hσ A * slB σ hσ (HSL v) = slLong σ hσ (HSL u * A) := by
    calc t * slLong σ hσ A * slB σ hσ (HSL v)
        = t * slB σ hσ (HSL v) * slLong σ hσ A := by
          rw [mul_assoc, slLong_comm_slB hσ A (HSL v), ← mul_assoc]
      _ = t'' * slLong σ hσ A := rfl
      _ = slLong σ hσ (HSL u * A) := by rw [hty, map_mul]
  exact ⟨HSL u * A, hz⟩

include hσ in
theorem oddCore_td4 (hK : (-1 : Kˣ) ≠ 1) [Finite K] (h4 : 4 ≤ Nat.card K)
    (hF3 : Nat.card (fixedField σ) = 3)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {N : Subgroup (twistedGroup σ)}
    (hNc : N ≤ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)))
    (hNnorm : ∀ c ∈ Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)),
      ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_neg_one_ne_one hK
  have hBc : ∀ C : SL(2, K), slB σ hσ C ∈
      Subgroup.centralizer ({slLong σ hσ (-1)} : Set (twistedGroup σ)) := fun C => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← slB_neg_one hσ, ← map_mul, ← map_mul,
      ← neg_one_mul_comm_SL2]
  have hNBnormal : (N.comap (slB σ hσ)).Normal := ⟨fun x hx g => by
    show slB σ hσ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNnorm _ (hBc g) _ hx⟩
  have hNBodd : ∀ x ∈ N.comap (slB σ hσ), Odd (orderOf x) := fun x hx => by
    rw [← orderOf_injective (slB σ hσ) (slB_injective hσ) x]
    exact odd_orderOf_of_mem_oddCard hNodd hx
  have hNBbot : N.comap (slB σ hσ) = ⊥ := sl2_odd_normal_eq_bot h4 h2K hNBnormal hNBodd
  have hSP : ∀ n ∈ N, n ∈ SProd σ hσ := fun n hn =>
    mem_SProd_of_centralizes hσ hK hC₀ hgF (Subgroup.mem_centralizer_singleton_iff.mp (hNc hn))
  have hcent : ∀ n ∈ N, ∀ C : SL(2, K), n * slB σ hσ C = slB σ hσ C * n := by
    intro n hn C
    obtain ⟨C', hC'⟩ := SProd_conj_slB hσ (hSP n hn) C
    have hmem : slB σ hσ (C' * C⁻¹) ∈ N := by
      rw [map_mul, map_inv, ← hC']
      have h1 := hNnorm _ (hBc C) _ (inv_mem hn)
      have h2 := mul_mem hn h1
      simpa [mul_assoc] using h2
    have h3 : C' * C⁻¹ ∈ N.comap (slB σ hσ) := hmem
    rw [hNBbot, Subgroup.mem_bot, mul_inv_eq_one] at h3
    rw [h3] at hC'
    exact mul_inv_eq_iff_eq_mul.mp hC'
  have hA : ∀ n ∈ N, ∃ A : SL(2, fixedField σ), n = slLong σ hσ A := fun n hn =>
    exists_slLong_of_centralizes_slB hσ (hSP n hn) (hcent n hn)
  have hNAnormal : (N.comap (slLong σ hσ)).Normal := ⟨fun x hx g => by
    show slLong σ hσ (g * x * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNnorm _ (slLong_mem_centralizer_tauL hσ g) _ hx⟩
  have hNAodd : ∀ x ∈ N.comap (slLong σ hσ), Odd (orderOf x) := fun x hx => by
    rw [← orderOf_injective (slLong σ hσ) (slLong_injective hσ) x]
    exact odd_orderOf_of_mem_oddCard hNodd hx
  have hNAbot : N.comap (slLong σ hσ) = ⊥ := sl2_three_odd_normal_eq_bot hF3 hNAnormal hNAodd
  rw [Subgroup.eq_bot_iff_forall]
  intro n hn
  obtain ⟨A, rfl⟩ := hA n hn
  have h1 : A ∈ N.comap (slLong σ hσ) := hn
  rw [hNAbot, Subgroup.mem_bot] at h1
  rw [h1, map_one]

end TD4


end CFSG.ClassicalInvolution.G2D4Models
