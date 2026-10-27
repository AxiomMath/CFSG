module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSUAlg
public import CFSG.HardMathSupport.Foote.ModuleExclusions.PSLCore

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open Matrix CFSG.Open CFSG.CGT.PushingUpLit.CGT6M
open scoped commutatorElement

section Group

variable {n : ℕ} {K : Type} [Field K] [CharP K 5] (fb : K →+* K) {q : ℕ}

omit [CharP K 5] in
theorem fb_zi (fb : K →+* K) [CharP K 5] (x : ZMod 5) : fb (zi K x) = zi K x := by
  have : fb.comp (zi K) = zi K := RingHom.ext_zmod _ _
  exact congrArg (fun g : ZMod 5 →+* K => g x) this

theorem siegel_c55 [Nonempty (Fin n)] (hfb : ∀ x, fb (fb x) = x) (hfbq : ∀ x : K, fb x = x ^ q)
    {ζ : K} (hζ : fb ζ ≠ ζ) (M : GL (Fin n) K) (hMH : M ∈ StatedSU n q K)
    {a b : Fin n → K} {ε₁ ε₂ : K} (hli : LinearIndependent K ![a, b])
    (ha : (M : Matrix (Fin n) (Fin n) K) *ᵥ a = ε₁ • a)
    (hb : (M : Matrix (Fin n) (Fin n) K) *ᵥ b = ε₂ • b) (h : ε₁ * fb ε₂ = -1)
    (i11 : uHh fb a a = 0) (i12 : uHh fb a b = 0) (i21 : uHh fb b a = 0) (i22 : uHh fb b b = 0) :
    ∃ Φ : C55 →* StatedProj (StatedSU n q K), Function.Injective Φ ∧
      ∀ u : C55, (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K)) *
        Φ u * (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K))⁻¹ =
        (Φ u)⁻¹ := by
  have hU := (unitary_of_mem_statedSU fb hfbq hMH).1
  have hAA : uX fb a b 1 * uX fb a b 1 = 0 := uX_mul fb a b i11 i12 i21 i22 1 1
  have hAB : uX fb a b 1 * uX fb a b ζ = 0 := uX_mul fb a b i11 i12 i21 i22 1 ζ
  have hBA : uX fb a b ζ * uX fb a b 1 = 0 := uX_mul fb a b i11 i12 i21 i22 ζ 1
  have hBB : uX fb a b ζ * uX fb a b ζ = 0 := uX_mul fb a b i11 i12 i21 i22 ζ ζ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hfz : ∀ x : ZMod 5, fb (zi K x) = zi K x := fb_zi fb
  have hcomb : ∀ a' b' : ZMod 5, zi K a' • uX fb a b 1 + zi K b' • uX fb a b ζ =
      uX fb a b (zi K a' * 1 + zi K b' * ζ) := fun a' b' => by
    rw [uX_add, uX_mul_fixed fb a b (hfz a'), uX_mul_fixed fb a b (hfz b')]
  have hH : ∀ a' b' : ZMod 5, Tu hAA hAB hBA hBB (zi K a') (zi K b') ∈ StatedSU n q K :=
    fun a' b' => by
    apply Subgroup.subset_closure
    refine ⟨det_Ehom_eq_one hAA hAB hBA hBB (Multiplicative.ofAdd (a', b')), ?_⟩
    have e : ((Tu hAA hAB hBA hBB (zi K a') (zi K b') : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 + uX fb a b (zi K a' * 1 + zi K b' * ζ) := by
      rw [← hcomb a' b', ← add_assoc]
      rfl
    rw [e]
    have e2 : (fun x : K => x ^ q) = ⇑fb := funext fun x => (hfbq x).symm
    rw [e2]
    exact uX_unitary fb hfb a b i11 i12 i21 i22 _
  have hind : ∀ a' b' : ZMod 5, zi K a' • uX fb a b 1 + zi K b' • uX fb a b ζ = 0 →
      a' = 0 ∧ b' = 0 := by
    intro a' b' hab
    rw [hcomb] at hab
    have h0 := uX_eq_zero fb hli hab
    have hb' : b' = 0 := by
      by_contra hb'
      apply hζ
      have hbz : zi K b' ≠ 0 := fun h => hb' ((zi K).injective (by rw [h, map_zero]))
      have hl : ζ = -(zi K a') / zi K b' := by
        field_simp
        linear_combination h0
      conv_lhs => rw [hl]
      rw [map_div₀, map_neg, hfz, hfz, ← hl]
    subst hb'
    refine ⟨?_, rfl⟩
    rw [map_zero, zero_mul, add_zero, mul_one] at h0
    exact (zi K).injective (by rw [h0, map_zero])
  exact inverted_c55_proj (StatedSU n q K) M hMH hAA hAB hBA hBB
    (uX_anticomm fb hfb hU ha hb h 1) (uX_anticomm fb hfb hU ha hb h ζ) hH hind

end Group

section Heis

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {fb : K →+* K}
  {u w : ι → K}

@[expose] def uEg (huu : uHh fb u u = 0) (huw : uHh fb u w = 0) (hwu : uHh fb w u = 0)
    (h2 : (2 : K) ≠ 0) (α : K) : GL ι K :=
  ⟨uE fb u w α, uE fb u w (-α), uE_mul_neg huu huw hwu h2 α, by
    have := uE_mul_neg huu huw hwu h2 (-α)
    rwa [neg_neg] at this⟩

variable (huu : uHh fb u u = 0) (huw : uHh fb u w = 0) (hwu : uHh fb w u = 0) (h2 : (2 : K) ≠ 0)

theorem uEg_val (α : K) : ((uEg huu huw hwu h2 α : GL ι K) : Matrix ι ι K) = uE fb u w α := rfl

theorem uEg_zero : uEg huu huw hwu h2 0 = 1 := by
  apply Units.ext
  simp [uEg, uE, uX_zero, uCc]

theorem uEg_mul_of_comm {α β : K} (h : α * fb β = β * fb α) :
    uEg huu huw hwu h2 α * uEg huu huw hwu h2 β = uEg huu huw hwu h2 (α + β) :=
  Units.ext (uE_mul_of_comm huu huw hwu h2 h)

theorem uEg_pow (α : K) (k : ℕ) :
    uEg huu huw hwu h2 α ^ k = uEg huu huw hwu h2 ((k : K) * α) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, uEg_zero]
  | succ k ih =>
    rw [pow_succ, ih, uEg_mul_of_comm huu huw hwu h2 (by rw [map_mul, map_natCast]; ring),
      Nat.cast_succ, add_mul, one_mul]

theorem uEg_pow_five [CharP K 5] (α : K) : uEg huu huw hwu h2 α ^ 5 = 1 := by
  rw [uEg_pow]
  have h5 : ((5 : ℕ) : K) = 0 := CharP.cast_eq_zero K 5
  rw [h5, zero_mul, uEg_zero]

theorem uEg_det [CharP K 5] (α : K) : ((uEg huu huw hwu h2 α : GL ι K) : Matrix ι ι K).det = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  have h1 : (((uEg huu huw hwu h2 α : GL ι K) : Matrix ι ι K).det) ^ 5 = 1 ^ 5 := by
    rw [← Matrix.det_pow, ← Units.val_pow_eq_pow_val, uEg_pow_five]
    simp
  exact frobenius_inj K 5 h1

theorem uEg_mem [CharP K 5] {n q : ℕ} {u w : Fin n → K} {fb : K →+* K}
    (huu : uHh fb u u = 0) (huw : uHh fb u w = 0) (hwu : uHh fb w u = 0)
    (h2 : (2 : K) ≠ 0) (hfb : ∀ x, fb (fb x) = x) (hfbq : ∀ x : K, fb x = x ^ q) (α : K) :
    uEg huu huw hwu h2 α ∈ StatedSU n q K := by
  apply Subgroup.subset_closure
  refine ⟨uEg_det huu huw hwu h2 α, ?_⟩
  have e2 : (fun x : K => x ^ q) = ⇑fb := funext fun x => (hfbq x).symm
  rw [e2, uEg_val]
  exact uE_unitary huu huw hwu h2 hfb α

end Heis

section HeisMain

variable {n : ℕ} {K : Type} [Field K] [CharP K 5] (fb : K →+* K) {q : ℕ}

theorem uZ_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] {u : ι → K} (hu0 : u ≠ 0) :
    uZ fb u ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu0 (funext hc)
  have := congrFun (congrFun h0 i) i
  simp only [uZ, uCj, vecMulVec_apply, Matrix.zero_apply] at this
  rcases mul_eq_zero.mp this with h | h
  · exact hi h
  · exact hi ((map_eq_zero_iff fb (RingHom.injective fb)).mp h)

theorem uEg_conj [Nonempty (Fin n)] (h2 : (2 : K) ≠ 0) (hfb : ∀ x, fb (fb x) = x)
    (hfbq : ∀ x : K, fb x = x ^ q) (M : GL (Fin n) K) (hMH : M ∈ StatedSU n q K)
    {u w : Fin n → K} {ε₁ ε₂ : K}
    (hu : (M : Matrix (Fin n) (Fin n) K) *ᵥ u = ε₁ • u)
    (hw : (M : Matrix (Fin n) (Fin n) K) *ᵥ w = ε₂ • w) (h : ε₁ * fb ε₂ = -1)
    (hε₁ : ε₁ * fb ε₁ = 1) (huu : uHh fb u u = 0) (huw : uHh fb u w = 0)
    (hwu : uHh fb w u = 0) (α : K) :
    (⟨M, hMH⟩ : StatedSU n q K) *
        (⟨uEg huu huw hwu h2 α, uEg_mem huu huw hwu h2 hfb hfbq α⟩ : StatedSU n q K) *
        (⟨M, hMH⟩ : StatedSU n q K)⁻¹ =
      (⟨uEg huu huw hwu h2 α, uEg_mem huu huw hwu h2 hfb hfbq α⟩ : StatedSU n q K)⁻¹ := by
  have hU := (unitary_of_mem_statedSU fb hfbq hMH).1
  have hZ : (M : Matrix (Fin n) (Fin n) K) * uZ fb u = uZ fb u * M :=
    uE_anticomm_Z huu huw hwu hU hu hε₁
  have hA := uX_anticomm fb hfb hU hu hw h α
  have hs' : uCc fb w (-α) (-α) = uCc fb w α α := by simp only [uCc, map_neg]; ring
  apply Subtype.ext
  show M * uEg huu huw hwu h2 α * M⁻¹ = (uEg huu huw hwu h2 α)⁻¹
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  show (M : Matrix (Fin n) (Fin n) K) * uE fb u w α = uE fb u w (-α) * M
  simp only [uE, hs', uX_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, hA, hZ, Matrix.neg_mul]

theorem heis_inv [Nonempty (Fin n)] (h2 : (2 : K) ≠ 0) (hfb : ∀ x, fb (fb x) = x)
    (hfbq : ∀ x : K, fb x = x ^ q) {ζ : K} (hζ : fb ζ ≠ ζ) (M : GL (Fin n) K)
    (hMH : M ∈ StatedSU n q K) {u w : Fin n → K} {ε₁ ε₂ : K}
    (hu : (M : Matrix (Fin n) (Fin n) K) *ᵥ u = ε₁ • u)
    (hw : (M : Matrix (Fin n) (Fin n) K) *ᵥ w = ε₂ • w) (h : ε₁ * fb ε₂ = -1)
    (hε₁ : ε₁ * fb ε₁ = 1) (hu0 : u ≠ 0) (huu : uHh fb u u = 0) (huw : uHh fb u w = 0)
    (hww : uHh fb w w ≠ 0) :
    ∃ X Y : StatedProj (StatedSU n q K), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute ⁅Y, X⁆ X ∧
      Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧
      (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K)) * X *
        (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K))⁻¹ = X⁻¹ := by
  have hwu : uHh fb w u = 0 := by rw [uHh_swap fb hfb, huw, map_zero]
  have hU := (unitary_of_mem_statedSU fb hfbq hMH).1
  have h22 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  let E : K → GL (Fin n) K := uEg huu huw hwu h2
  let Eh : K → StatedSU n q K := fun α => ⟨E α, uEg_mem huu huw hwu h2 hfb hfbq α⟩
  let Mh : StatedSU n q K := ⟨M, hMH⟩
  have hinv : ∀ α, Mh * Eh α * Mh⁻¹ = (Eh α)⁻¹ := fun α =>
    uEg_conj fb h2 hfb hfbq M hMH hu hw h hε₁ huu huw hwu α
  have hpow : ∀ α, Eh α ^ 5 = 1 := fun α => Subtype.ext (uEg_pow_five huu huw hwu h2 α)
  set Z : Matrix (Fin n) (Fin n) K := uZ fb u with hZdef
  set d : K := uCc fb w ζ 1 - uCc fb w 1 ζ with hd
  have hd0 : d ≠ 0 := by
    have : d = uHh fb w w * (fb ζ - ζ) := by
      simp only [hd, uCc, map_one]
      ring
    rw [this]
    exact mul_ne_zero hww (sub_ne_zero.mpr hζ)
  have hkey : uE fb u w ζ * uE fb u w 1 = (1 + d • Z) * (uE fb u w 1 * uE fb u w ζ) := by
    rw [uE_mul_sub huu huw hwu h2 ζ 1, uE_mul_sub huu huw hwu h2 1 ζ, add_comm ζ 1]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      hZdef, uZ_mul_uE huu huw hwu, uZ_mul_uZ huu, smul_zero, add_zero, smul_add]
    have e : 2⁻¹ * (uCc fb w ζ 1 - uCc fb w 1 ζ) =
        d + 2⁻¹ * (uCc fb w 1 ζ - uCc fb w ζ 1) := by
      rw [hd]
      linear_combination (uCc fb w ζ 1 - uCc fb w 1 ζ) * h22
    rw [e, add_smul]
    abel
  have hC : (((⁅Eh ζ, Eh 1⁆ : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + d • Z := by
    show uE fb u w ζ * uE fb u w 1 * uE fb u w (-ζ) * uE fb u w (-1) = 1 + d • Z
    calc uE fb u w ζ * uE fb u w 1 * uE fb u w (-ζ) * uE fb u w (-1)
        = (1 + d • Z) * (uE fb u w 1 * (uE fb u w ζ * uE fb u w (-ζ))) * uE fb u w (-1) := by
          rw [hkey]; simp only [Matrix.mul_assoc]
      _ = 1 + d • Z := by
          rw [uE_mul_neg huu huw hwu h2 ζ, Matrix.mul_one, Matrix.mul_assoc,
            uE_mul_neg huu huw hwu h2 1, Matrix.mul_one]
  have hCX : Commute (⁅Eh ζ, Eh 1⁆ : StatedSU n q K) (Eh 1) := by
    apply Subtype.ext
    apply Units.ext
    show (((⁅Eh ζ, Eh 1⁆ : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      uE fb u w 1 = uE fb u w 1 * (((⁅Eh ζ, Eh 1⁆ : StatedSU n q K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)
    rw [hC]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hZdef, uZ_mul_uE huu huw hwu, uE_mul_uZ huu huw hwu]
  have hCY : Commute (⁅Eh ζ, Eh 1⁆ : StatedSU n q K) (Eh ζ) := by
    apply Subtype.ext
    apply Units.ext
    show (((⁅Eh ζ, Eh 1⁆ : StatedSU n q K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      uE fb u w ζ = uE fb u w ζ * (((⁅Eh ζ, Eh 1⁆ : StatedSU n q K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)
    rw [hC]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hZdef, uZ_mul_uE huu huw hwu, uE_mul_uZ huu huw hwu]
  have hne : (⁅Eh ζ, Eh 1⁆ : StatedSU n q K) ∉
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n q K) := by
    intro hmem
    obtain ⟨s, hs⟩ := scalar_of_mk_eq_one (⁅Eh ζ, Eh 1⁆ : StatedSU n q K)
      ((QuotientGroup.eq_one_iff _).mpr hmem)
    rw [hC] at hs
    have hN : (d • Z) * (d • Z) = 0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hZdef, uZ_mul_uZ huu, smul_zero, smul_zero]
    have h0 := nilp_eq_zero_of_add_one_scalar hN (s := s) (by rw [← hs])
    rcases smul_eq_zero.mp h0 with h | h
    · exact hd0 h
    · exact uZ_ne_zero fb hu0 h
  have hmkc : ⁅(QuotientGroup.mk (Eh ζ) : StatedProj (StatedSU n q K)),
      QuotientGroup.mk (Eh 1)⁆ = QuotientGroup.mk ⁅Eh ζ, Eh 1⁆ :=
    (map_commutatorElement (QuotientGroup.mk' _) (Eh ζ) (Eh 1)).symm
  refine ⟨QuotientGroup.mk (Eh 1), QuotientGroup.mk (Eh ζ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]
  · rw [hmkc]
    exact hCX.map (QuotientGroup.mk' _)
  · rw [hmkc]
    exact hCY.map (QuotientGroup.mk' _)
  · rw [hmkc]
    intro h1
    exact hne ((QuotientGroup.eq_one_iff _).mp h1)
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hinv,
      QuotientGroup.mk_inv]

end HeisMain

section Eichler

variable {n : ℕ} {K : Type} [Field K] [CharP K 5] (fb : K →+* K) {q : ℕ}

theorem exists_fixed_not_prime [Finite K] (hq5 : 5 < q) (hK : Nat.card K = q ^ 2)
    (hfbq : ∀ x : K, fb x = x ^ q) : ∃ η : K, fb η = η ∧ ∀ a : ZMod 5, η ≠ zi K a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have e : (p + 1) ^ 2 - 1 = p * (p + 1 + 1) := by
    have : (p + 1) ^ 2 = p * (p + 1 + 1) + 1 := by ring
    omega
  have hord : orderOf g = p * (p + 1 + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK, e]
  have hg1 : g ^ (p * (p + 1 + 1)) = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  refine ⟨((g ^ (p + 1 + 1) : Kˣ) : K), ?_, ?_⟩
  · rw [hfbq, ← Units.val_pow_eq_pow_val, ← pow_mul]
    have e2 : (p + 1 + 1) * (p + 1) = p * (p + 1 + 1) + (p + 1 + 1) := by ring
    have h3 : g ^ ((p + 1 + 1) * (p + 1)) = g ^ (p + 1 + 1) := by
      rw [e2, pow_add, hg1, one_mul]
    rw [h3]
  · intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      rw [map_zero] at ha
      exact (g ^ (p + 1 + 1)).ne_zero ha
    · have h4 : a ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one ha0
      have h5 : (g ^ (p + 1 + 1)) ^ 4 = 1 := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, ha, ← map_pow, h4, map_one]
        rfl
      rw [← pow_mul] at h5
      have h6 := orderOf_dvd_of_pow_eq_one h5
      rw [hord] at h6
      have h7 : p * (p + 1 + 1) ∣ 4 * (p + 1 + 1) := by
        rw [mul_comm 4]; exact h6
      have h8 : p ∣ 4 := Nat.dvd_of_mul_dvd_mul_right (by omega) h7
      have := Nat.le_of_dvd (by omega) h8
      omega

theorem eichler_c55 [Nonempty (Fin n)] (h2 : (2 : K) ≠ 0) (hfb : ∀ x, fb (fb x) = x)
    (hfbq : ∀ x : K, fb x = x ^ q) {η : K} (hη : fb η = η) (hηF : ∀ a : ZMod 5, η ≠ zi K a)
    (M : GL (Fin n) K) (hMH : M ∈ StatedSU n q K) {u w : Fin n → K} {ε₁ ε₂ : K}
    (hu : (M : Matrix (Fin n) (Fin n) K) *ᵥ u = ε₁ • u)
    (hw : (M : Matrix (Fin n) (Fin n) K) *ᵥ w = ε₂ • w) (h : ε₁ * fb ε₂ = -1)
    (hε₁ : ε₁ * fb ε₁ = 1) (hu0 : u ≠ 0) (huu : uHh fb u u = 0) (huw : uHh fb u w = 0)
    (hww : uHh fb w w ≠ 0) :
    ∃ Φ : C55 →* StatedProj (StatedSU n q K), Function.Injective Φ ∧
      ∀ v : C55, (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K)) *
        Φ v * (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) : StatedProj (StatedSU n q K))⁻¹ =
        (Φ v)⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hwu : uHh fb w u = 0 := by rw [uHh_swap fb hfb, huw, map_zero]
  let Eh : K → StatedSU n q K := fun α => ⟨uEg huu huw hwu h2 α, uEg_mem huu huw hwu h2 hfb hfbq α⟩
  have hinv : ∀ α, (⟨M, hMH⟩ : StatedSU n q K) * Eh α * (⟨M, hMH⟩ : StatedSU n q K)⁻¹ =
      (Eh α)⁻¹ := fun α => uEg_conj fb h2 hfb hfbq M hMH hu hw h hε₁ huu huw hwu α
  let α : C55 → K := fun v => zi K (Multiplicative.toAdd v).1 + zi K (Multiplicative.toAdd v).2 * η
  have hαfix : ∀ v, fb (α v) = α v := fun v => by
    simp only [α, map_add, map_mul, fb_zi, hη]
  have hαadd : ∀ v v', α (v * v') = α v + α v' := fun v v' => by
    simp only [α, toAdd_mul, Prod.fst_add, Prod.snd_add, map_add, add_mul]
    ring
  let F : C55 →* StatedSU n q K := MonoidHom.mk' (fun v => Eh (α v)) (fun v v' => by
    apply Subtype.ext
    show uEg huu huw hwu h2 (α (v * v')) = uEg huu huw hwu h2 (α v) * uEg huu huw hwu h2 (α v')
    rw [uEg_mul_of_comm huu huw hwu h2 (by rw [hαfix v', hαfix v]; ring), hαadd])
  refine ⟨(QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n q K))).comp F, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : (QuotientGroup.mk (F v) : StatedProj (StatedSU n q K)) = 1 := hv
    obtain ⟨s, hs⟩ := scalar_of_mk_eq_one (F v) hv'
    have h0 : α v = 0 :=
      eq_zero_of_uE_eq_scalar huu huw hwu hu0 hww (s := s) hs
    obtain ⟨⟨a, b⟩, rfl⟩ : ∃ w, v = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd v, rfl⟩
    simp only [α, toAdd_ofAdd] at h0
    by_cases hb : b = 0
    · subst hb
      simp only [map_zero, zero_mul, add_zero] at h0
      have : a = 0 := (zi K).injective (by rw [h0, map_zero])
      subst this
      rfl
    · exfalso
      have hb' : zi K b ≠ 0 := (map_ne_zero (zi K)).mpr hb
      apply hηF (-a * b⁻¹)
      have h3 : zi K (-a * b⁻¹) = -(zi K a) * (zi K b)⁻¹ := by
        have hneg : zi K (-a) = -zi K a := map_neg (zi K) a
        rw [_root_.map_mul, hneg, _root_.map_inv₀]
      rw [h3]
      field_simp
      linear_combination h0
  · intro v
    have h3 : (⟨M, hMH⟩ : StatedSU n q K) * F v * (⟨M, hMH⟩ : StatedSU n q K)⁻¹ = (F v)⁻¹ :=
      hinv (α v)
    show QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K) * QuotientGroup.mk (F v) *
      (QuotientGroup.mk (⟨M, hMH⟩ : StatedSU n q K))⁻¹ = (QuotientGroup.mk (F v))⁻¹
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h3,
      QuotientGroup.mk_inv]

end Eichler

section Eigen2

variable {K : Type} [Field K]

theorem mulVec_range_eigen {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {c e : K}
    (hMM : M * M = c • 1) (he : e * e = c) (x : ι → K) :
    M *ᵥ ((M + e • (1 : Matrix ι ι K)) *ᵥ x) = e • ((M + e • (1 : Matrix ι ι K)) *ᵥ x) := by
  subst he
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
  module

theorem exists_line_of_no_two {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K}
    {c e : K} (hMM : M * M = c • 1) (he : e * e = c)
    (hno : ¬ ∃ x y : ι → K, LinearIndependent K ![x, y] ∧ M *ᵥ x = e • x ∧ M *ᵥ y = e • y) :
    ∃ a : ι → K, M *ᵥ a = e • a ∧ (∀ x, ∃ r : K, (M + e • (1 : Matrix ι ι K)) *ᵥ x = r • a) ∧
      (M + e • (1 : Matrix ι ι K) ≠ 0 → a ≠ 0) := by
  by_cases hT : M + e • (1 : Matrix ι ι K) = 0
  · exact ⟨0, by simp, fun x => ⟨0, by simp [hT]⟩, fun h => absurd hT h⟩
  · obtain ⟨x₀, hx₀⟩ := exists_mulVec_ne_zero hT
    refine ⟨(M + e • (1 : Matrix ι ι K)) *ᵥ x₀, mulVec_range_eigen hMM he x₀, fun x => ?_,
      fun _ => hx₀⟩
    by_contra hcon
    push Not at hcon
    apply hno
    refine ⟨(M + e • (1 : Matrix ι ι K)) *ᵥ x₀, (M + e • (1 : Matrix ι ι K)) *ᵥ x, ?_,
      mulVec_range_eigen hMM he x₀, mulVec_range_eigen hMM he x⟩
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      have : (M + e • (1 : Matrix ι ι K)) *ᵥ x =
          (-(t⁻¹ * s)) • ((M + e • (1 : Matrix ι ι K)) *ᵥ x₀) := by
        have h1 : t • ((M + e • (1 : Matrix ι ι K)) *ᵥ x) =
            -(s • ((M + e • (1 : Matrix ι ι K)) *ᵥ x₀)) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hst
        calc (M + e • (1 : Matrix ι ι K)) *ᵥ x
            = t⁻¹ • (t • ((M + e • (1 : Matrix ι ι K)) *ᵥ x)) := by
              rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = _ := by rw [h1, smul_neg, smul_smul, neg_smul]
      exact hcon _ this
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx₀, ht⟩

theorem exists_two_eigen {n : ℕ} (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0)
    {M : Matrix (Fin n) (Fin n) K} {c s : K} (hMM : M * M = c • 1) (hs : s * s = c)
    (hs0 : s ≠ 0) :
    ∃ e : K, e * e = c ∧ ∃ x y : Fin n → K, LinearIndependent K ![x, y] ∧ M *ᵥ x = e • x ∧
      M *ᵥ y = e • y := by
  classical
  by_contra hcon
  push Not at hcon
  have hs' : (-s) * (-s) = c := by rw [neg_mul_neg]; exact hs
  obtain ⟨a, -, ha, -⟩ := exists_line_of_no_two hMM hs (by
    rintro ⟨x, y, h1, h2, h3⟩
    exact hcon s hs x y h1 h2 h3)
  obtain ⟨b, -, hb, -⟩ := exists_line_of_no_two hMM hs' (by
    rintro ⟨x, y, h1, h2, h3⟩
    exact hcon (-s) hs' x y h1 h2 h3)
  have hspan : (⊤ : Submodule K (Fin n → K)) ≤ Submodule.span K ((({a, b} : Finset (Fin n → K)) :
      Set (Fin n → K))) := by
    intro x _
    rw [Finset.coe_pair, Submodule.mem_span_pair]
    obtain ⟨r, hr⟩ := ha x
    obtain ⟨r', hr'⟩ := hb x
    refine ⟨(2 * s)⁻¹ * r, -((2 * s)⁻¹ * r'), ?_⟩
    have h2s : (2 * s) ≠ 0 := mul_ne_zero h2 hs0
    have e1 : (M + s • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ x -
        (M + (-s) • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ x = (2 * s) • x := by
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      module
    rw [hr, hr'] at e1
    calc ((2 * s)⁻¹ * r) • a + (-((2 * s)⁻¹ * r')) • b
        = (2 * s)⁻¹ • (r • a - r' • b) := by module
      _ = (2 * s)⁻¹ • ((2 * s) • x) := by rw [e1]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ h2s, one_smul]
  have h1 := Submodule.finrank_mono hspan
  have h3 := finrank_span_finset_le_card (R := K) ({a, b} : Finset (Fin n → K))
  have h4 : ({a, b} : Finset (Fin n → K)).card ≤ 2 := Finset.card_le_two
  rw [finrank_top, Module.finrank_fin_fun] at h1
  have h5 : Module.finrank K (Submodule.span K ((({a, b} : Finset (Fin n → K)) : Set (Fin n → K)))) ≤ 2 :=
    h3.trans h4
  omega

end Eigen2

section Main

variable {K : Type} [Field K]

omit [Field K] in
theorem psu_two_ne_zero [Field K] [CharP K 5] : (2 : K) ≠ 0 := by
  intro h2
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have : (1 : K) = 0 := by linear_combination 3 * h2 - h5
  exact one_ne_zero this

theorem fb_mul_eq_one_of_sq {n : ℕ} [Nonempty (Fin n)] (fb : K →+* K)
    {M : Matrix (Fin n) (Fin n) K} (hU : (M.map fb)ᵀ * M = 1) {c : K} (hMM : M * M = c • 1) :
    fb c * c = 1 := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  set e0 : Fin n → K := Pi.single i 1 with he0
  have h2e : M *ᵥ (M *ᵥ e0) = c • e0 := by
    rw [Matrix.mulVec_mulVec, hMM, Matrix.smul_mulVec, Matrix.one_mulVec]
  have k1 := uHh_unitary fb hU (M *ᵥ e0) (M *ᵥ e0)
  have k2 := uHh_unitary fb hU e0 e0
  rw [h2e, k2, uHh_smul_left, uHh_smul_right] at k1
  have k3 : uHh fb e0 e0 = 1 := by
    simp [uHh, uCj, he0, dotProduct, Pi.single_apply]
  rw [k3] at k1
  linear_combination k1

theorem exists_sqrt [Finite K] {q : ℕ} (hqodd : Odd q) (hK : Nat.card K = q ^ 2) (fb : K →+* K)
    (hfbq : ∀ x : K, fb x = x ^ q) {c : K} (hc0 : c ≠ 0) (hcc : fb c * c = 1)
    (hchar : ringChar K ≠ 2) : ∃ s : K, s * s = c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨k, hk⟩ := hqodd
  have hsq : IsSquare c := by
    rw [FiniteField.isSquare_iff hchar hc0, hcard]
    have e1 : q ^ 2 = 2 * (k * (q + 1)) + 1 := by subst hk; ring
    have e2 : q ^ 2 / 2 = k * (q + 1) := by
      rw [e1, Nat.mul_add_div (by norm_num)]
      simp
    rw [e2, pow_mul', pow_succ, ← hfbq, hcc, one_pow]
  obtain ⟨s, hs⟩ := hsq
  exact ⟨s, hs.symm⟩

end Main

section MainThm

variable {K : Type} [Field K] [CharP K 5] [Finite K]

theorem psu_inverts_aux {n q : ℕ} (hn : 3 ≤ n) (hq1 : 1 < q) (hqodd : Odd q)
    (hK : Nat.card K = q ^ 2) (fb : K →+* K) (hfb : ∀ x, fb (fb x) = x)
    (hfbq : ∀ x : K, fb x = x ^ q) (z : StatedProj (StatedSU n q K)) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedSU n q K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (q ≤ 5 ∧ ∃ X Y : StatedProj (StatedSU n q K), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧ Commute ⁅Y, X⁆ X ∧
      Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h2 : (2 : K) ≠ 0 := psu_two_ne_zero
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; norm_num
  obtain ⟨t, ht⟩ := exists_not_fixed hq1 hK
  have hζ : fb t ≠ t := by rw [hfbq]; exact ht
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨c, hc0, hM⟩ := scalar_sq_of_mk_sq h hz2
  have hnon := not_scalar_of_mk_ne_one h hz1
  have hU := (unitary_of_mem_statedSU fb hfbq h.2).1
  set M : Matrix (Fin n) (Fin n) K := ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hMdef
  have hcc : fb c * c = 1 := fb_mul_eq_one_of_sq fb hU hM
  obtain ⟨s, hs⟩ := exists_sqrt hqodd hK fb hfbq hc0 hcc hchar
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hs]; ring)
  obtain ⟨ε, hε, x, y, hli, hx, hy⟩ := exists_two_eigen hn h2 hM hs hs0
  have hε0 : ε ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hε]; ring)
  have hν : (ε * fb ε) * (ε * fb ε) = 1 := by
    have : fb c = fb ε * fb ε := by rw [← hε, map_mul]
    calc (ε * fb ε) * (ε * fb ε) = (ε * ε) * (fb ε * fb ε) := by ring
      _ = c * fb c := by rw [hε, this]
      _ = 1 := by rw [mul_comm]; exact hcc
  have hm1 : (-1 : K) ≠ 1 := by
    intro h1
    apply h2
    linear_combination -h1
  have hcomb : ∀ (e : K) (x y : Fin n → K) (s₁ s₂ : K), M *ᵥ x = e • x → M *ᵥ y = e • y →
      M *ᵥ (s₁ • x + s₂ • y) = e • (s₁ • x + s₂ • y) := by
    intro e x y s₁ s₂ hx hy
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hy]
    module
  rcases mul_self_eq_one_iff.mp hν with hν1 | hν1
  ·
    have hν1' : fb ε * ε = 1 := by rw [mul_comm]; exact hν1
    by_cases hbig : ∃ x' y' : Fin n → K, LinearIndependent K ![x', y'] ∧
        M *ᵥ x' = (-ε) • x' ∧ M *ᵥ y' = (-ε) • y'
    ·
      obtain ⟨x', y', hli', hx', hy'⟩ := hbig
      obtain ⟨s₁, s₂, hu0, huu⟩ := exists_isotropic_in_plane fb hq1 hK hfb hfbq hli
      obtain ⟨t₁, t₂, hw0, hww⟩ := exists_isotropic_in_plane fb hq1 hK hfb hfbq hli'
      have hu := hcomb ε x y s₁ s₂ hx hy
      have hw := hcomb (-ε) x' y' t₁ t₂ hx' hy'
      have hne1 : fb ε * (-ε) ≠ 1 := by
        rw [mul_neg, hν1']
        exact hm1
      have hne2 : fb (-ε) * ε ≠ 1 := by
        rw [map_neg, neg_mul, hν1']
        exact hm1
      have huw := uHh_eigen_zero fb hU hu hw hne1
      have hwu := uHh_eigen_zero fb hU hw hu hne2
      have hli2 : LinearIndependent K ![s₁ • x + s₂ • y, t₁ • x' + t₂ • y'] :=
        li_of_eigen (ε₁ := ε) (ε₂ := -ε) (by
          intro h1
          apply mul_ne_zero h2 hε0
          linear_combination -h1) hu0 hw0 hu hw
      left
      exact siegel_c55 fb hfb hfbq hζ (h : GL (Fin n) K) h.2 hli2 hu hw
        (by rw [map_neg, mul_neg, hν1]) huu huw hwu hww
    ·
      have hnon' : M + (-ε) • (1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
        intro h0
        apply hnon ε
        rw [neg_smul] at h0
        exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h0))
      obtain ⟨a, ha, hline, ha0⟩ := exists_line_of_no_two hM (by rw [neg_mul_neg]; exact hε) hbig
      have ha0 := ha0 hnon'
      obtain ⟨s₁, s₂, hu0, huu⟩ := exists_isotropic_in_plane fb hq1 hK hfb hfbq hli
      have hu := hcomb ε x y s₁ s₂ hx hy
      have hne1 : fb ε * (-ε) ≠ 1 := by
        rw [mul_neg, hν1']
        exact hm1
      have hne2 : fb (-ε) * ε ≠ 1 := by
        rw [map_neg, neg_mul, hν1']
        exact hm1
      have huw := uHh_eigen_zero fb hU hu ha hne1
      have haa : uHh fb a a ≠ 0 := by
        intro haa
        apply ha0
        apply uHh_eq_zero_of_forall fb
        intro v
        obtain ⟨r, hr⟩ := hline v
        have hp := mulVec_range_eigen hM hε v
        have hpa := uHh_eigen_zero fb hU ha hp hne2
        have e1 : (2 * ε) • v = (M + ε • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ v + (-r) • a := by
          rw [neg_smul, ← hr]
          simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
          module
        have e2 : (2 * ε) * uHh fb a v = 0 := by
          rw [← uHh_smul_right, e1, uHh_add_right, hpa, uHh_smul_right, haa]
          ring
        exact (mul_eq_zero.mp e2).resolve_left (mul_ne_zero h2 hε0)
      by_cases h5q : 5 < q
      · left
        obtain ⟨η, hη, hηF⟩ := exists_fixed_not_prime fb h5q hK hfbq
        exact eichler_c55 fb h2 hfb hfbq hη hηF (h : GL (Fin n) K) h.2 hu ha
          (by rw [map_neg, mul_neg, hν1]) hν1 hu0 huu huw haa
      · right
        exact ⟨not_lt.mp h5q, heis_inv fb h2 hfb hfbq hζ (h : GL (Fin n) K) h.2 hu ha
          (by rw [map_neg, mul_neg, hν1]) hν1 hu0 huu huw haa⟩
  ·
    have hν1' : fb ε * ε = -1 := by rw [mul_comm]; exact hν1
    have hne : fb ε * ε ≠ 1 := by rw [hν1']; exact hm1
    obtain ⟨s₁, s₂⟩ : ∃ s₁ s₂ : K, True := ⟨0, 0, trivial⟩
    left
    exact siegel_c55 fb hfb hfbq hζ (h : GL (Fin n) K) h.2 hli hx hy hν1
      (uHh_eigen_zero fb hU hx hx hne) (uHh_eigen_zero fb hU hx hy hne)
      (uHh_eigen_zero fb hU hy hx hne) (uHh_eigen_zero fb hU hy hy hne)

end MainThm

section Final

theorem psu_inverts {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (5 ^ f) ^ 2) (z : StatedProj (StatedSU n (5 ^ f) K)) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) :
    (∃ Φ : C55 →* StatedProj (StatedSU n (5 ^ f) K), Function.Injective Φ ∧
      ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹) ∨
    (f = 1 ∧ ∃ X Y : StatedProj (StatedSU n (5 ^ f) K), X ^ 5 = 1 ∧ Y ^ 5 = 1 ∧
      Commute ⁅Y, X⁆ X ∧ Commute ⁅Y, X⁆ Y ∧ ⁅Y, X⁆ ≠ 1 ∧ z * X * z⁻¹ = X⁻¹) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Fintype.card K = 5 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  have : CharP K 5 := charP_of_card_eq_prime_pow (p := 5) (f := 2 * f) hcard
  have : ExpChar K 5 := ExpChar.prime Nat.prime_five
  have hq1 : 1 < 5 ^ f := Nat.one_lt_pow (by omega) (by norm_num)
  let fb : K →+* K := iterateFrobenius K 5 f
  have hfbq : ∀ x : K, fb x = x ^ 5 ^ f := fun x => rfl
  have hfb : ∀ x : K, fb (fb x) = x := fun x => by
    have e : 5 ^ f * 5 ^ f = 5 ^ (2 * f) := by rw [two_mul, pow_add]
    rw [hfbq, hfbq, ← pow_mul, e]
    have h := FiniteField.pow_card x
    rwa [hcard] at h
  rcases psu_inverts_aux hn hq1 (Odd.pow (by decide)) hK fb hfb hfbq z hz1 hz2 with h | ⟨h5, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, h⟩
    by_contra hf1
    have : 5 ^ 2 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Final

end CFSG.HardMathSupport.Foote.ModuleExclusions
