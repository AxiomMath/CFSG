module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.UniA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.ClassicalInvolution.Balance.StrongBalance.Linear
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

theorem eq_of_mul_inv_mem_glaPPrimeCoreOf {S : Type*} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    {J : Subgroup S} (hJq : CFSG.Open.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card ↥J) (α : S →* S)
    (hcent : ∀ j ∈ J, α j * j⁻¹ ∈ GLAPPrimeCoreOf p J) : ∀ j ∈ J, α j = j := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    refine CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hJq
      (GLAPPrimeCore.normal p _) fun htop => ?_
    have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop hpJ
  set C : Subgroup S := (Subgroup.center ↥J).map J.subtype with hC
  have hCJ : ∀ c ∈ C, c ∈ J ∧ ∀ j ∈ J, c * j = j * c := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨c.2, fun j hj => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  have hδ : ∀ j ∈ J, α j * j⁻¹ ∈ C := by
    intro j hj
    have h := hcent j hj
    change α j * j⁻¹ ∈ (GLAPPrimeCore p ↥J).map J.subtype at h
    exact Subgroup.map_mono hcore h
  refine eq_of_perfect_of_mul_inv_mem J C hJq.1
    (fun x hx y hy => (hCJ x hx).2 y (hCJ y hy).1) α hδ fun l hl c hc => ?_
  have hαl : α l ∈ J := by
    have h1 := (hCJ _ (hδ l hl)).1
    have h2 : α l = α l * l⁻¹ * l := by group
    rw [h2]
    exact mul_mem h1 hl
  exact ((hCJ c hc).2 _ hαl).symm

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

private def dOne (z : K) : Fin 4 → K := ![1, z, z, (z ^ 2)⁻¹]

private def dTwo (z : K) : Fin 4 → K := ![1, (z ^ 2)⁻¹, z, z]

private theorem norm_inv_sq {z : K} (hz : h.bar z * z = 1) : h.bar (z ^ 2)⁻¹ * (z ^ 2)⁻¹ = 1 := by
  rw [map_inv₀, map_pow, ← mul_inv, ← mul_pow, hz, one_pow, inv_one]

private theorem norm_dOne {z : K} (hz : h.bar z * z = 1) : ∀ i, h.bar (dOne z i) * dOne z i = 1 := by
  have h1 : h.bar 1 * 1 = 1 := by rw [map_one, one_mul]
  intro i
  fin_cases i
  exacts [h1, hz, hz, norm_inv_sq hz]

private theorem norm_dTwo {z : K} (hz : h.bar z * z = 1) : ∀ i, h.bar (dTwo z i) * dTwo z i = 1 := by
  have h1 : h.bar 1 * 1 = 1 := by rw [map_one, one_mul]
  intro i
  fin_cases i
  exacts [h1, norm_inv_sq hz, hz, hz]

private theorem prod_dOne {z : K} (hz0 : z ≠ 0) : ∏ i, dOne z i = 1 := by
  rw [Fin.prod_univ_four]
  change 1 * z * z * (z ^ 2)⁻¹ = 1
  rw [one_mul, ← pow_two, mul_inv_cancel₀ (pow_ne_zero 2 hz0)]

private theorem prod_dTwo {z : K} (hz0 : z ≠ 0) : ∏ i, dTwo z i = 1 := by
  rw [Fin.prod_univ_four]
  change 1 * (z ^ 2)⁻¹ * z * z = 1
  rw [one_mul, mul_assoc, ← pow_two, inv_mul_cancel₀ (pow_ne_zero 2 hz0)]

private theorem dOne_eq_one_of_not_mem (z : K) : ∀ i, i ∉ blockJ → dOne z i = 1 := by
  intro i hi
  rw [mem_blockJ, not_not] at hi
  subst hi
  rfl

private theorem dTwo_eq_one_of_not_mem (z : K) : ∀ i, i ∉ blockJ → dTwo z i = 1 := by
  intro i hi
  rw [mem_blockJ, not_not] at hi
  subst hi
  rfl

private theorem dOne_dTwo_sep {z : K} (h1 : z ≠ 1) (h1' : 1 ≠ z) (h2 : (z ^ 2)⁻¹ ≠ 1)
    (h2' : 1 ≠ (z ^ 2)⁻¹) (h3 : z ≠ (z ^ 2)⁻¹) (h3' : (z ^ 2)⁻¹ ≠ z) :
    ∀ k l : Fin 4, k ≠ l → dOne z k ≠ dOne z l ∨ dTwo z k ≠ dTwo z l := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [dOne, dTwo]

private theorem entry_eq_zero_of_comm_diagonal {M : Matrix (Fin 4) (Fin 4) K} {d : Fin 4 → K}
    (e : M * diagonal d = diagonal d * M) {k l : Fin 4} (hkl : d k ≠ d l) : M k l = 0 := by
  have h1 := congrFun (congrFun e k) l
  rw [mul_diagonal, diagonal_mul] at h1
  have h2 : M k l * (d l - d k) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0).symm hkl

section Main

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ] {p : ℕ} {μ : K} (hK : Nat.card K = (ℓ ^ f) ^ 2)
  (hq : 5 ≤ ℓ ^ f) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hμ : IsPrimitiveRoot μ p)
  (hpq : p ∣ ℓ ^ f + 1)
include hK hq hℓ2 hp hp2 hμ hpq

theorem aut_eq_conj_yU_zpow (α : MulAut (PS h)) (hα : α ^ p = 1)
    (hcent : ∀ j ∈ JU h, α j * j⁻¹ ∈ GLAPPrimeCoreOf p (JU h)) :
    ∃ k : ℤ, α = MulAut.conj (projU h (yU h hp hp2 hμ hpq) ^ k) := by
  classical
  have hμ0 := ne_zero_of_root hp hp2 hμ
  have hfix : ∀ j ∈ JU h, α j = j :=
    eq_of_mul_inv_mem_glaPPrimeCoreOf hp (isQuasisimple_JU hp hp2 hμ hpq hK hq)
      ((dvd_card_JU hp hp2 hμ hpq hK hq).trans (Subgroup.card_quotient_dvd_card _))
      α.toMonoidHom hcent
  have hC : IsPrimeFormGram (1 : GL (Fin 4) K) := isPrimeFormGram_idGram
  obtain ⟨-, -, hker, -, hform, -⟩ := unitary_prime_form_full_semilinear_realization h hC
    (by norm_num) (fun hh => absurd hh.1 (by norm_num))
  obtain ⟨φ, ⟨A, hαA⟩, -⟩ := hform α
  set Ag : GL (Fin 4) K := (A : GL (Fin 4) K) with hAg
  let β : ↥(SG h) →* ↥(SG h) :=
    (primeFormConjSU h (idGram K 4) A).toMonoidHom.comp (primeFormFieldSU h hC φ).toMonoidHom
  have hβproj : ∀ g, projU h (β g) = α (projU h g) := by
    intro g
    rw [hαA, MulAut.mul_apply]
    have e1 : primeFormFieldHom h hC φ (projU h g) = projU h (primeFormFieldSU h hC φ g) :=
      primeFormFieldAut_mk h hC φ g
    rw [e1]
    exact (primeFormConjAut_mk h _ A _).symm
  have hβfix : ∀ g ∈ blockU h blockJ, β g = g := by
    refine eq_of_perfect_of_mul_inv_mem (blockU h blockJ) (projU h).ker
      (isQuasisimple_blockU hK hq (by decide)).1
      (fun x hx y _ => (Subgroup.mem_center_iff.1 (ker_projU_le_center hx) y).symm) β
      (fun g hg => ?_) (fun g _ c hc => Subgroup.mem_center_iff.1 (ker_projU_le_center hc) _)
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβproj, hfix _ (Subgroup.mem_map_of_mem _ hg),
      mul_inv_cancel]
  have hmat : ∀ g ∈ blockU h blockJ, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (Ag : Matrix (Fin 4) (Fin 4) K) *
        φ.mapMatrix ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((Ag⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro g hg
    have h1 := congrArg (fun x : ↥(SG h) => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      (hβfix g hg)
    change (Ag * glAut φ (g : GL (Fin 4) K) * Ag⁻¹ : GL (Fin 4) K).val = _ at h1
    rw [Units.val_mul, Units.val_mul, coe_glAut] at h1
    rw [RingEquiv.mapMatrix_apply]
    exact h1.symm
  obtain ⟨ζ, hζN, hζord⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq hK
  have hz0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have hzN : h.bar (ζ : K) * ζ = 1 := by
    rw [UnitaryFieldData.bar_apply, ← unitaryInvolution_apply]
    exact hζN
  have hzpow : ∀ m : ℕ, 0 < m → m < ℓ ^ f + 1 → (ζ : K) ^ m ≠ 1 := by
    intro m hm0 hm hzm
    have h1 : ζ ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hzm, Units.val_one])
    have h2 := Nat.le_of_dvd hm0 (orderOf_dvd_of_pow_eq_one h1)
    omega
  have hz1 : (ζ : K) ≠ 1 := fun h1 => hzpow 1 (by norm_num) (by omega) (by rw [pow_one]; exact h1)
  have hz2 : ((ζ : K) ^ 2)⁻¹ ≠ 1 := fun h1 =>
    hzpow 2 (by norm_num) (by omega) (inv_eq_one.1 h1)
  have hz3 : (ζ : K) ≠ ((ζ : K) ^ 2)⁻¹ := by
    intro h1
    apply hzpow 3 (by norm_num) (by omega)
    calc (ζ : K) ^ 3 = (ζ : K) * (ζ : K) ^ 2 := by ring
      _ = ((ζ : K) ^ 2)⁻¹ * (ζ : K) ^ 2 := by rw [← h1]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hz0)
  have hD₁J : diagU h (dOne (ζ : K)) (norm_dOne hzN) (prod_dOne hz0) ∈ blockU h blockJ :=
    diagU_mem_blockU (dOne_eq_one_of_not_mem _)
  have hD₂J : diagU h (dTwo (ζ : K)) (norm_dTwo hzN) (prod_dTwo hz0) ∈ blockU h blockJ :=
    diagU_mem_blockU (dTwo_eq_one_of_not_mem _)
  have hφz : φ (ζ : K) = ζ := by
    have e := comm_of_fixed (g := Ag) (φ := φ) (hmat _ hD₁J)
    rw [coe_diagU] at e
    obtain ⟨k, hk⟩ := exists_entry_ne_zero Ag 1
    have hk' := diag_entry_eq e hk
    have hφ1 : φ (ζ : K) ≠ 1 := by
      intro h1
      apply hz1
      exact φ.injective (h1.trans (map_one φ).symm)
    have hφ3 : φ (ζ : K) ≠ ((ζ : K) ^ 2)⁻¹ := by
      intro h1
      have hodd : Odd (ℓ ^ f) := (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2 |>.pow
      obtain ⟨m, hm⟩ := hodd
      apply hzpow (m + 1) (by omega) (by omega)
      apply φ.injective
      rw [map_pow, h1, map_one, ← inv_pow, ← pow_mul, inv_pow]
      have hz2m : (ζ : K) ^ (2 * (m + 1)) = 1 := by
        have : 2 * (m + 1) = ℓ ^ f + 1 := by omega
        rw [this, ← Units.val_pow_eq_pow_val, ← hζord, pow_orderOf_eq_one, Units.val_one]
      rw [hz2m, inv_one]
    fin_cases k
    · exact absurd hk'.symm hφ1
    · exact hk'.symm
    · exact hk'.symm
    · exact absurd hk'.symm hφ3
  have hφ : φ = 1 := by
    haveI : NeZero (ℓ ^ f + 1) := ⟨by omega⟩
    have hprim : IsPrimitiveRoot (ζ : K) (ℓ ^ f + 1) := by
      rw [← hζord]
      exact IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf ζ)
    refine RingEquiv.ext fun c => ringEquiv_eq_refl_of_fix hK φ (fun a ha => ?_) c
    have ha' : a ^ (ℓ ^ f + 1) = 1 := by
      rw [unitaryInvolution_apply] at ha
      rw [pow_succ]
      exact ha
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one ha'
    rw [← hi, map_pow, hφz]
  subst hφ
  have hαA' : α = primeFormConjHom h _ A := by rw [hαA, map_one, mul_one]
  have hcomm : ∀ g ∈ blockU h blockJ, (Ag : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (Ag : Matrix (Fin 4) (Fin 4) K) := by
    intro g hg
    have e := comm_of_fixed (g := Ag) (φ := 1) (hmat g hg)
    rwa [mapMatrix_eq_self (fun c => rfl)] at e
  have hD₁ := hcomm _ hD₁J
  have hD₂ := hcomm _ hD₂J
  rw [coe_diagU] at hD₁ hD₂
  have hoff : ∀ k l : Fin 4, k ≠ l → (Ag : Matrix (Fin 4) (Fin 4) K) k l = 0 := by
    intro k l hkl
    rcases dOne_dTwo_sep hz1 (Ne.symm hz1) hz2 (Ne.symm hz2) hz3 (Ne.symm hz3) k l hkl with
      hne | hne
    · exact entry_eq_zero_of_comm_diagonal hD₁ hne
    · exact entry_eq_zero_of_comm_diagonal hD₂ hne
  have hsw : ∀ i j : Fin 4, (hij : i ≠ j) → i ≠ 0 → j ≠ 0 →
      (Ag : Matrix (Fin 4) (Fin 4) K) i i = (Ag : Matrix (Fin 4) (Fin 4) K) j j := by
    intro i j hij hi hj
    have e := hcomm _ (swapU_mem_blockU (h := h) hij (mem_blockJ.2 hi) (mem_blockJ.2 hj))
    rw [coe_swapU] at e
    exact diag_eq_of_comm_swap e
  set a := (Ag : Matrix (Fin 4) (Fin 4) K) 0 0 with ha
  set b := (Ag : Matrix (Fin 4) (Fin 4) K) 1 1 with hb
  have hAd : (Ag : Matrix (Fin 4) (Fin 4) K) = diagonal ![a, b, b, b] := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      fin_cases k
      · rfl
      · rfl
      · exact (hsw 1 2 (by decide) (by decide) (by decide)).symm
      · exact ((hsw 1 2 (by decide) (by decide) (by decide)).trans
          (hsw 2 3 (by decide) (by decide) (by decide))).symm
    · rw [diagonal_apply_ne _ hkl]
      exact hoff k l hkl
  have hdet : a * b ^ 3 ≠ 0 := by
    have h1 : (Ag : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := by
      have := Ag.isUnit.map Matrix.detMonoidHom
      exact this.ne_zero
    rw [hAd, det_diagonal, Fin.prod_univ_four] at h1
    simpa [pow_succ, mul_assoc] using h1
  have hb0 : b ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
  have hPsi : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, map_pow, ← hαA', hα]
  obtain ⟨-, c, -, hc⟩ := (hker ⟨A ^ p, 1⟩).1 hPsi
  have hApd : (((A ^ p : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = diagonal ![a ^ p, b ^ p, b ^ p, b ^ p] := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hAg, hAd, diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hab : a ^ p = b ^ p := by
    have hcm := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) hc
    have h0 := congrFun (congrFun hcm 0) 0
    have h1 := congrFun (congrFun hcm 1) 1
    simp only [hApd, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h0 h1
    have h0' : a ^ p = (c : K) := h0
    have h1' : b ^ p = (c : K) := h1
    rw [h0', h1']
  have hν : (a / b) ^ p = 1 := by rw [div_pow, hab, div_self (pow_ne_zero _ hb0)]
  have hprim : IsPrimitiveRoot (μ⁻¹ ^ 4) p := by
    have hcop : Nat.Coprime 4 p := by
      have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      have : Nat.Coprime (2 ^ 2) p := Nat.Coprime.pow_left 2 h2
      simpa using this
    exact hμ.inv.pow_of_coprime 4 hcop
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hν
  have hc' : b * μ⁻¹ ^ i ≠ 0 := mul_ne_zero hb0 (pow_ne_zero _ (inv_ne_zero hμ0))
  have hAy : Ag = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 _ hc') *
      ((yU h hp hp2 hμ hpq ^ i : ↥(SG h)) : GL (Fin 4) K) := by
    apply Units.ext
    rw [Units.val_mul, Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      hAd, coe_diagU]
    simp only [diagonal_pow, Units.val_mk0, scalar_apply, diagonal_mul_diagonal]
    congr 1
    funext k
    have hai : a = b * (μ⁻¹ ^ 4) ^ i := by
      rw [hi]
      field_simp
    fin_cases k
    · show a = b * μ⁻¹ ^ i * ((μ ^ 3)⁻¹) ^ i
      rw [hai, ← pow_mul, ← inv_pow, ← pow_mul, mul_assoc, ← pow_add]
      ring_nf
    all_goals
      show b = b * μ⁻¹ ^ i * μ ^ i
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, mul_one]
  refine ⟨i, ?_⟩
  rw [hαA']
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  set Y : ↥(SG h) := yU h hp hp2 hμ hpq ^ i with hY
  have hconj : (⟨(A : GL (Fin 4) K) * g * (A : GL (Fin 4) K)⁻¹,
      conj_mem_gramSU h _ A.2 g.2⟩ : ↥(SG h)) = Y * g * Y⁻¹ := by
    apply Subtype.ext
    change Ag * g * Ag⁻¹ = (Y : GL (Fin 4) K) * g * (Y : GL (Fin 4) K)⁻¹
    rw [hAy]
    have hs := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ι := Fin 4) (Units.mk0 _ hc')
      ((Y : GL (Fin 4) K) * g * (Y : GL (Fin 4) K)⁻¹)).eq
    generalize GeneralLinearGroup.scalar (Fin 4) (Units.mk0 _ hc') = s at hs ⊢
    calc s * (Y : GL (Fin 4) K) * g * (s * (Y : GL (Fin 4) K))⁻¹
        = s * ((Y : GL (Fin 4) K) * g * (Y : GL (Fin 4) K)⁻¹) * s⁻¹ := by group
      _ = (Y : GL (Fin 4) K) * g * (Y : GL (Fin 4) K)⁻¹ * s * s⁻¹ := by rw [← hs]
      _ = (Y : GL (Fin 4) K) * g * (Y : GL (Fin 4) K)⁻¹ := by group
  rw [primeFormConjHom_mk, hconj, MulAut.conj_apply, zpow_natCast]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rfl

end Main

end CFSG.LocalAnalysis.GLTheoremA.H81.UniA3
