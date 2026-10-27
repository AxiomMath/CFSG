module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSL7
public import CFSG.Adapters.CatalogueFieldBridges.Unitary
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

namespace LieClAut

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ} (h : UnitaryFieldData p f K)

theorem primeFormConjHom_mem_inner_of_coprime (hcop : Nat.Coprime m (p ^ f + 1))
    (B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) B ∈
      inner (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  set u := GeneralLinearGroup.det (B : GL (Fin m) K) with hu
  have hN : h.norm (u : K) = 1 := by
    rw [hu, GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h 1 B.2
  have hNpow : ∀ w : Kˣ, h.norm (w : K) = ((w ^ (p ^ f + 1) : Kˣ) : K) := fun w => by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val, pow_succ,
      mul_comm]
  have hu1 : u ^ (p ^ f + 1) = 1 := Units.ext (by rw [← hNpow, hN, Units.val_one])
  have hq1 : 1 < p ^ f + 1 := by
    have := Nat.one_le_pow f p (Nat.pos_of_ne_zero h.prime.ne_zero)
    omega
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq1
  set v := u ^ s
  have hv : h.norm (v : K) = 1 := by
    rw [hNpow, ← pow_mul, mul_comm, pow_mul, hu1, one_pow, Units.val_one]
  have hvm : v ^ m = u := by
    rw [← pow_mul, mul_comm, ← Nat.div_add_mod (m * s) (p ^ f + 1), hs, pow_add, pow_mul, hu1,
      one_pow, one_mul, pow_one]
  have hv' : h.norm ((v⁻¹ : Kˣ) : K) = 1 := by
    rw [hNpow, inv_pow, ← pow_mul, mul_comm, pow_mul, hu1, one_pow, inv_one, Units.val_one]
  set Z : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨GeneralLinearGroup.scalar (Fin m) v⁻¹, scalar_mem_primeFormUnitary_one h hv'⟩ with hZ
  have hS : ((Z * B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
      GL (Fin m) K) ∈ gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨(Z * B).2, ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, map_mul, ← hu, ← hvm]
    change ((GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin m) v⁻¹) * v ^ m : Kˣ) : K) = 1
    rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, inv_mul_cancel, Units.val_one]
  have hcZ : primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) Z = 1 := by
    refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
    rw [primeFormConjHom_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    change GeneralLinearGroup.scalar (Fin m) v⁻¹ * (g : GL (Fin m) K) *
      (GeneralLinearGroup.scalar (Fin m) v⁻¹)⁻¹ = g
    rw [(commute_scalar v⁻¹ (g : GL (Fin m) K)).symm.eq, mul_inv_cancel_right]
  have hB : B = Z⁻¹ * (Z * B) := by group
  rw [hB, map_mul, map_inv, hcZ, inv_one, one_mul, mem_inner_primeFormP h]
  exact ⟨⟨_, hS⟩, rfl⟩

theorem exists_rankFour_psu {X A : Type} [Group X] [Finite X] [CommGroup A] [Finite A]
    (hm : 3 ≤ m) (hq : ¬(m = 3 ∧ p ^ f = 2))
    (hD : ∀ B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
      primeFormConjHom h _ B ∈
        inner (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)))
    (e : X ≃* primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    (g : A →* primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
    (hg : Function.Injective g) (hA3 : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 27)
    (htw : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := m) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := m) (K := K)) τ) (g a) = g a) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  have hC : IsPrimeFormGram (1 : GL (Fin m) K) := isPrimeFormGram_one
  set Ψ : MulAut X ≃* MulAut P := MulAut.congr e with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p : P, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  have hinnΨ : ∀ β, β ∈ (MulAut.conj : X →* MulAut X).range →
      Ψ β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, (hΨconj x).symm⟩
  have hinnΨ' : ∀ γ, γ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P →
      Ψ.symm γ ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨e.symm p, (hΨinv p).symm⟩
  have hcH : ∀ B, Ψ.symm (primeFormConjHom h _ B) ∈ H := fun B => hinn (hinnΨ' _ (hD B))
  have hFinn : ∀ γ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P,
      primeFormFieldFactor h hC hm hq γ = 1 := fun γ hγ => by
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ γ).1 hγ
    have := primeFormFieldFactor_apply h hC hm hq ⟨s, s.2.1⟩ 1
    rwa [map_one, mul_one] at this
  obtain ⟨k, hk⟩ := hα
  obtain ⟨φ, ⟨B, hB⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hm hq (Ψ α)
  have hφk : φ ^ 3 ^ k = 1 := by
    have h1 := primeFormFieldFactor_apply h hC hm hq B φ
    rw [← hB] at h1
    rw [← h1, ← map_pow, ← map_pow, hk, map_one, map_one]
  have hfφ : Ψ.symm (primeFormFieldHom h hC φ) ∈ H := by
    have h1 : primeFormFieldHom h hC φ = (primeFormConjHom h _ B)⁻¹ * Ψ α := by rw [hB]; group
    rw [h1, map_mul, map_inv, Ψ.symm_apply_apply]
    exact H.mul_mem (H.inv_mem (hcH B)) hαH
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    apply hαn
    rw [map_one, mul_one] at hB
    rw [← Ψ.symm_apply_apply α, hB]
    exact hinnΨ' _ (hD B)
  obtain ⟨j, hjk, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by rw [hjo, pow_zero]))
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = φ ^ 3 ^ (j - 1) := ⟨_, rfl⟩
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one (h1 ▸ hτ).symm
    rw [hjo] at h2
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h2
    omega
  obtain ⟨Y, hY3, hYfix⟩ := htw τ hτ3
  have hβH : Ψ.symm (primeFormConjHom h _ Y * primeFormFieldHom h hC τ) ∈ H := by
    rw [map_mul, hτ, map_pow, map_pow]
    exact H.mul_mem (hcH Y) (H.pow_mem hfφ _)
  have hβ3 : (Ψ.symm (primeFormConjHom h _ Y * primeFormFieldHom h hC τ)) ^ 3 = 1 := by
    rw [← map_pow, hY3, map_one]
  have hβn : Ψ.symm (primeFormConjHom h _ Y * primeFormFieldHom h hC τ) ∉
      (MulAut.conj : X →* MulAut X).range := fun h1 => by
    have h2 := hFinn _ (hinnΨ _ h1)
    rw [Ψ.apply_symm_apply, primeFormFieldFactor_apply] at h2
    exact hτ1 h2
  refine exists_rankFour_of_fixed hc hinn hβH hβ3 hβn (e.symm.toMonoidHom.comp g)
    (e.symm.injective.comp hg) hA3 hA fun a => ?_
  simp only [hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
  rw [hYfix]

theorem mul_inv_mem_primeFormUnitary_one {P R : GL (Fin m) K}
    (hPR : ((P : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * P =
      ((R : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * R) :
    P * R⁻¹ ∈ primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  rw [mem_primeFormUnitary, Units.val_one, Units.val_mul, conjTranspose_mul_mul, Matrix.mul_one,
    hPR]
  have h1 := conjTranspose_mul_mul h 1 (R : Matrix (Fin m) (Fin m) K)
    ((R⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h1
  simp only [Matrix.mul_one] at h1
  rw [← h1]
  simp

theorem barT_glAut (φ : K ≃+* K) (P : GL (Fin m) K) :
    (((glAut φ P : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * glAut φ P =
      (((P : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * P).map φ := by
  have := map_gram_eq h (isPrimeFormGram_one (n := m) (K := K)) φ (P : Matrix (Fin m) (Fin m) K)
  simpa [coe_glAut] using this

theorem glAut_pow_three {τ : K ≃+* K} (hτ : τ ^ 3 = 1) (P : GL (Fin m) K) :
    glAut τ (glAut τ (glAut τ P)) = P := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, ← pow_three', hτ, map_one,
    MulAut.one_apply]

theorem exists_twist {A : Type} [Group A] {J : Matrix (Fin m) (Fin m) K}
    (hJ : ∀ σ : K ≃+* K, J.map σ = J) (P : GL (Fin m) K)
    (hP : ((P : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * P = J) (T : A →* GL (Fin m) K)
    (hT : ∀ a, ((T a : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * J * T a = J)
    (hTdet : ∀ a, (T a : Matrix (Fin m) (Fin m) K).det = 1)
    (hTτ : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∀ a, glAut τ (T a) = T a)
    (hTinj : ∀ a (c : Kˣ), T a = GeneralLinearGroup.scalar (Fin m) c → a = 1) :
    ∃ g : A →* primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := m) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := m) (K := K)) τ) (g a) = g a := by
  classical
  have hC : IsPrimeFormGram (1 : GL (Fin m) K) := isPrimeFormGram_one
  have hmem : ∀ a, (MulAut.conj P).toMonoidHom.comp T a ∈
      gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := fun a => by
    refine (mem_gramSU_iff_unitary h).2 ⟨?_, ?_⟩
    · have he : (MulAut.conj P).toMonoidHom.comp T a = P * (P * (T a)⁻¹)⁻¹ := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [he]
      refine mul_inv_mem_primeFormUnitary_one h ?_
      rw [Units.val_mul, ← Matrix.mul_one ((((P : Matrix (Fin m) (Fin m) K) *
        ((T a)⁻¹ : GL (Fin m) K)).map h.bar)ᵀ), conjTranspose_mul_mul, Matrix.mul_one, hP,
        ← map_inv, hT]
    · rw [← GeneralLinearGroup.val_det_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det P),
        mul_inv_cancel_right, GeneralLinearGroup.val_det_apply, hTdet]
  set Q := ((MulAut.conj P).toMonoidHom.comp T).codRestrict _ hmem with hQ
  refine ⟨(QuotientGroup.mk' _).comp Q, ?_, fun τ hτ => ?_⟩
  · refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
    obtain ⟨c, -, -, hc⟩ := ha
    apply hTinj a c
    have h1 : P * T a * P⁻¹ = GeneralLinearGroup.scalar (Fin m) c := hc
    calc T a = P⁻¹ * (P * T a * P⁻¹) * P := by group
      _ = GeneralLinearGroup.scalar (Fin m) c := by
        rw [h1, (commute_scalar c P⁻¹).eq]
        group
  · have hY : P * (glAut τ P)⁻¹ ∈ primeFormUnitary h
        ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
      mul_inv_mem_primeFormUnitary_one h (by rw [barT_glAut, hP, hJ])
    set Y : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := ⟨_, hY⟩
    refine ⟨Y, ?_, fun a => ?_⟩
    · rw [← primeFormPsi_apply h hC Y τ, ← map_pow]
      convert map_one (primeFormPsi h hC)
      refine SemidirectProduct.ext ?_ ?_
      · rw [pow_three, SemidirectProduct.mul_left, SemidirectProduct.mul_left,
          SemidirectProduct.one_left, map_mul]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, coe_primeFormFieldU, OneMemClass.coe_one]
        change P * (glAut τ P)⁻¹ * (glAut τ (P * (glAut τ P)⁻¹) *
          glAut τ (glAut τ (P * (glAut τ P)⁻¹))) = 1
        simp only [map_mul, map_inv, glAut_pow_three hτ]
        group
      · rw [pow_three, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
          SemidirectProduct.one_right]
        change τ * (τ * τ) = 1
        rw [← pow_three, hτ]
    · change primeFormConjHom h _ Y (primeFormFieldAut h hC τ
        (QuotientGroup.mk (Q a))) = QuotientGroup.mk (Q a)
      rw [primeFormFieldAut_mk, primeFormConjHom_mk]
      congr 1
      apply Subtype.ext
      change P * (glAut τ P)⁻¹ * glAut τ (P * T a * P⁻¹) * (P * (glAut τ P)⁻¹)⁻¹ = P * T a * P⁻¹
      rw [map_mul, map_mul, map_inv, hTτ τ hτ]
      group

end LieClAut

namespace HypE27

open TorusE27 SpE27

variable {K : Type} [Field K]

@[expose] def J0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := fromBlocks 0 1 1 0

@[expose] def P0 (l l' : K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks 1 (diagonal fun _ => l) 1 (diagonal fun _ => l')

@[expose] def Q0 (l l' : K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal fun _ => l') (diagonal fun _ => l) 1 1

@[expose] def T0 (ω : K) (v : Fin 3 → ZMod 3) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal fun i => chi ω (v i)) 0 0 (diagonal fun i => chi ω (-v i))

theorem J0_map (σ : K ≃+* K) : (J0 : Matrix _ _ K).map σ = J0 := by
  simp [J0, fromBlocks_map]

theorem diagonal_const_one : (diagonal fun _ : Fin 3 => (1 : K)) = 1 := rfl

variable [CharP K 2]

theorem P0_mul_Q0 {l l' : K} (hl : l + l' = 1) : P0 l l' * Q0 l l' = 1 := by
  have h2 : ∀ x : K, x + x = 0 := CharTwo.add_self_eq_zero
  have hl' : l' + l = 1 := by rw [add_comm]; exact hl
  rw [P0, Q0, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, diagonal_add, h2, diagonal_zero] <;>
    ext i j <;> by_cases hij : i = j <;> simp [diagonal_apply, Matrix.one_apply, hij, hl, hl']

theorem Q0_mul_P0 {l l' : K} (hl : l + l' = 1) : Q0 l l' * P0 l l' = 1 :=
  mul_eq_one_comm.1 (P0_mul_Q0 hl)

theorem P0_gram (b : K →+* K) {l l' : K} (hl : l + l' = 1) (hb : b l = l') (hb' : b l' = l) :
    ((P0 l l').map b)ᵀ * P0 l l' = J0 := by
  have h2 : ∀ x : K, x + x = 0 := CharTwo.add_self_eq_zero
  rw [P0, J0, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply]
  simp only [Matrix.map_one _ (map_zero b) (map_one b), diagonal_map (map_zero b), hb, hb',
    transpose_one, diagonal_transpose, Matrix.one_mul, Matrix.mul_one, diagonal_mul_diagonal,
    diagonal_add, mul_comm l l', h2, diagonal_zero]
  congr 1
  · ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, h2]
  all_goals ext i j
  all_goals by_cases hij : i = j <;>
    simp [diagonal_apply, Matrix.one_apply, hij, hl, add_comm l' l]

theorem chi_mul_neg {ω : K} (hω : ω ^ 3 = 1) (x : ZMod 3) : chi ω x * chi ω (-x) = 1 := by
  rw [← chi_add hω, add_neg_cancel, chi_zero]

theorem T0_gram {ω : K} (hω : ω ^ 3 = 1) (b : K →+* K) (hb : b ω = ω) (v : Fin 3 → ZMod 3) :
    ((T0 ω v).map b)ᵀ * J0 * T0 ω v = J0 := by
  have hc : ∀ x, b (chi ω x) = chi ω x := fun x => by rw [chi, map_pow, hb]
  rw [T0, J0, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_map (map_zero b), hc, Matrix.map_zero _ (map_zero b), transpose_zero,
    diagonal_transpose, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero, diagonal_mul_diagonal, chi_mul_neg hω]
  rw [show (fun i : Fin 3 => chi ω (-v i) * chi ω (v i)) = fun _ => 1 from
    funext fun i => by rw [mul_comm, chi_mul_neg hω], diagonal_const_one]

theorem T0_mul {ω : K} (hω : ω ^ 3 = 1) (v w : Fin 3 → ZMod 3) :
    T0 ω v * T0 ω w = T0 ω (v + w) := by
  rw [T0, T0, T0, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Pi.add_apply, neg_add, chi_add hω]

theorem T0_zero (ω : K) : T0 ω 0 = 1 := by
  rw [T0, ← fromBlocks_one]
  simp [chi_zero]

theorem T0_det {ω : K} (hω : ω ^ 3 = 1) (v : Fin 3 → ZMod 3) : (T0 ω v).det = 1 := by
  rw [T0, det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  simp [chi_mul_neg hω]

theorem T0_map {ω : K} (σ : K ≃+* K) (hσ : σ ω = ω) (v : Fin 3 → ZMod 3) :
    (T0 ω v).map σ = T0 ω v := by
  have hc : ∀ x, σ (chi ω x) = chi ω x := fun x => by rw [chi, map_pow, hσ]
  simp [T0, fromBlocks_map, diagonal_map, hc]

theorem eq_zero_of_eq_neg (x : ZMod 3) (h : x = -x) : x = 0 := by
  revert x h
  decide

theorem T0_eq_scalar {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {v : Fin 3 → ZMod 3} {c : K}
    (h : T0 ω v = scalar _ c) : v = 0 := by
  funext i
  have h1 := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K => M (.inl i) (.inl i)) h
  have h2 := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K => M (.inr i) (.inr i)) h
  simp only [T0, fromBlocks_apply₁₁, fromBlocks_apply₂₂, diagonal_apply_eq, scalar_apply] at h1 h2
  exact eq_zero_of_eq_neg _ (chi_injective hω hω1 (h1.trans h2.symm))

@[expose] def r6 (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  M.submatrix e6.symm e6.symm

theorem r6_mul (M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) : r6 M * r6 N = r6 (M * N) :=
  submatrix_mul_equiv _ _ _ _ _

theorem r6_one : r6 (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1 := submatrix_one_equiv _

theorem r6_map (b : K → K) (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) :
    (r6 M).map b = r6 (M.map b) := rfl

theorem r6_transpose (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) : (r6 M)ᵀ = r6 Mᵀ := rfl

theorem r6_det (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) : (r6 M).det = M.det :=
  det_submatrix_equiv_self _ _

theorem r6_injective : Function.Injective (r6 (K := K)) := fun M N h => by
  ext i j
  have := congrArg (fun A : Matrix (Fin 6) (Fin 6) K => A (e6 i) (e6 j)) h
  simpa [r6] using this

theorem r6_scalar (c : K) : r6 (scalar (Fin 3 ⊕ Fin 3) c) = scalar (Fin 6) c := by
  rw [scalar_apply, scalar_apply, r6, submatrix_diagonal_equiv]
  rfl

@[expose] def P6 {l l' : K} (hl : l + l' = 1) : GL (Fin 6) K :=
  ⟨r6 (P0 l l'), r6 (Q0 l l'), by rw [r6_mul, P0_mul_Q0 hl, r6_one], by
    rw [r6_mul, Q0_mul_P0 hl, r6_one]⟩

@[expose] noncomputable def T6 {ω : K} (hω : ω ^ 3 = 1) :
    Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 6) K where
  toFun v := ⟨r6 (T0 ω v.toAdd), r6 (T0 ω (-v.toAdd)), by
    rw [r6_mul, T0_mul hω, add_neg_cancel, T0_zero, r6_one], by
    rw [r6_mul, T0_mul hω, neg_add_cancel, T0_zero, r6_one]⟩
  map_one' := Units.ext (by
    change r6 (T0 ω 0) = 1
    rw [T0_zero, r6_one])
  map_mul' v w := Units.ext (by
    change r6 (T0 ω (v.toAdd + w.toAdd)) = r6 (T0 ω v.toAdd) * r6 (T0 ω w.toAdd)
    rw [r6_mul, T0_mul hω])

end HypE27

namespace HypE27

open TorusE27

variable {K : Type} [Field K]

theorem w4_zero_eq (i : Fin 4) : w4 (0 : Fin 3 → ZMod 3) i = 0 := by
  fin_cases i <;> simp [w4]

@[expose] noncomputable def T4 {ω : K} (hω : ω ^ 3 = 1) :
    Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 4) K where
  toFun v := ⟨diagonal fun i => chi ω (w4 v.toAdd i), diagonal fun i => chi ω (w4 (-v.toAdd) i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
       rw [← chi_add hω, ← Pi.add_apply (w4 _), ← w4_add, add_neg_cancel, w4_zero_eq, chi_zero],
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
       rw [← chi_add hω, ← Pi.add_apply (w4 _), ← w4_add, neg_add_cancel, w4_zero_eq, chi_zero]⟩
  map_one' := Units.ext (by
    change (diagonal fun i => chi ω (w4 0 i) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    rw [w4_zero_eq, chi_zero])
  map_mul' v w := Units.ext (by
    change (diagonal fun i => chi ω (w4 (v.toAdd + w.toAdd) i) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun i => chi ω (w4 v.toAdd i)) * diagonal fun i => chi ω (w4 w.toAdd i)
    rw [diagonal_mul_diagonal, w4_add]
    simp only [Pi.add_apply, chi_add hω])

theorem coe_T4 {ω : K} (hω : ω ^ 3 = 1) (v : Multiplicative (Fin 3 → ZMod 3)) :
    ((T4 hω v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun i => chi ω (w4 v.toAdd i) := rfl

theorem T4_eq_scalar {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {v : Multiplicative (Fin 3 → ZMod 3)}
    {c : K} (hc : ((T4 hω v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = scalar _ c) :
    v = 1 := by
  have h : ∀ i, chi ω (w4 v.toAdd i) = c := fun i => by
    have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i i) hc
    simpa [coe_T4, scalar_apply] using h1
  have hi : ∀ i, w4 v.toAdd i = w4 v.toAdd 0 := fun i =>
    chi_injective hω hω1 ((h i).trans (h 0).symm)
  have h1 := hi 1
  have h2 := hi 2
  have h3 := hi 3
  rw [w4_one, w4_zero] at h1
  rw [w4_two, w4_zero] at h2
  rw [w4_three, w4_zero] at h3
  have h0 : v.toAdd 0 = 0 := by
    rw [h1, h2] at h3
    have h3' : (3 : ZMod 3) * v.toAdd 0 = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
    linear_combination -h3 - h3'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1.trans h0
  · exact h2.trans h0

end HypE27

namespace SpE27

variable {K : Type} [Field K]

theorem blk_map_ringHom (b : K →+* K) (c : K) (M : Matrix (Fin 6) (Fin 6) K) :
    (blk c M).map b = blk (b c) (M.map b) := by
  rw [blk, blk, ← submatrix_map, fromBlocks_map, diagonal_map (map_zero b)]
  simp

theorem blk_transpose (c : K) (M : Matrix (Fin 6) (Fin 6) K) : (blk c M)ᵀ = blk c Mᵀ := by
  rw [blk, blk, transpose_submatrix, fromBlocks_transpose]
  simp

theorem eq_scalar_of_blk_eq {d c : K} {M : Matrix (Fin 6) (Fin 6) K}
    (h : blk d M = scalar (Fin 7) c) : M = scalar (Fin 6) c := by
  ext i j
  have h1 := congrArg (fun A : Matrix (Fin 7) (Fin 7) K => A (e7 (.inr i)) (e7 (.inr j))) h
  simp only [blk_apply_inr] at h1
  rw [h1]
  simp [scalar_apply, diagonal_apply]

@[expose] def blkGL : GL (Fin 6) K →* GL (Fin 7) K where
  toFun g := ⟨blk 1 g, blk 1 (g⁻¹ : GL (Fin 6) K), by
    rw [blk_mul, one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk_one], by
    rw [blk_mul, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk_one]⟩
  map_one' := Units.ext blk_one
  map_mul' g g' := Units.ext (by
    change blk 1 ((g * g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blk 1 (g : Matrix (Fin 6) (Fin 6) K) * blk 1 g'
    rw [blk_mul, one_mul, Units.val_mul])

theorem coe_blkGL (g : GL (Fin 6) K) :
    ((blkGL g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = blk 1 g := rfl

end SpE27


namespace LieClAut

open TorusE27 SpE27 HypE27

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem exists_twist_blk {A : Type} [Group A] {J : Matrix (Fin 6) (Fin 6) K}
    (hJ : ∀ σ : K ≃+* K, J.map σ = J) (P : GL (Fin 6) K)
    (hP : ((P : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * P = J) (T : A →* GL (Fin 6) K)
    (hT : ∀ a, ((T a : Matrix (Fin 6) (Fin 6) K).map h.bar)ᵀ * J * T a = J)
    (hTdet : ∀ a, (T a : Matrix (Fin 6) (Fin 6) K).det = 1)
    (hTτ : ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∀ a, glAut τ (T a) = T a)
    (hTinj : ∀ a (c : Kˣ), T a = GeneralLinearGroup.scalar (Fin 6) c → a = 1) :
    ∃ g : A →* primeFormP h ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := 7) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 7) (K := K)) τ) (g a) = g a := by
  refine exists_twist h (J := blk 1 J) (fun σ => by rw [blk_map, map_one, hJ]) (blkGL P) ?_
    (blkGL.comp T) (fun a => ?_) (fun a => ?_) (fun τ hτ a => ?_) (fun a c hc => ?_)
  · rw [coe_blkGL, blk_map_ringHom, blk_transpose, blk_mul, map_one, mul_one, hP]
  · rw [MonoidHom.comp_apply, coe_blkGL, blk_map_ringHom, blk_transpose, blk_mul, blk_mul,
      map_one, mul_one, mul_one, hT]
  · rw [MonoidHom.comp_apply, coe_blkGL, det_blk, one_mul, hTdet]
  · apply Units.ext
    rw [coe_glAut, MonoidHom.comp_apply, coe_blkGL, blk_map, map_one, ← coe_glAut, hTτ τ hτ]
  · refine hTinj a c (Units.ext (eq_scalar_of_blk_eq (d := 1) ?_))
    have := congrArg Units.val hc
    simp only [GeneralLinearGroup.coe_scalar] at this
    exact this

theorem exists_twist_u4 {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hbω : h.bar ω * ω = 1) :
    ∃ g : Multiplicative (Fin 3 → ZMod 3) →*
        primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 4) (K := K)) τ) (g a) = g a := by
  refine exists_twist h (J := 1) (fun σ => by simp) 1 (by simp) (T4 hω) (fun a => ?_)
    (fun a => det_torus hω a.toAdd) (fun τ hτ a => ?_) (fun a c hc => ?_)
  · rw [coe_T4, diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_one,
      diagonal_mul_diagonal]
    have hc : ∀ x, h.bar (chi ω x) * chi ω x = 1 := fun x => by
      rw [chi, map_pow, ← mul_pow, hbω, one_pow]
    simp only [hc]
    rfl
  · apply Units.ext
    rw [coe_glAut, coe_T4, diagonal_map (map_zero τ)]
    simp only [chi, map_pow, fix_omega hω hω1 τ hτ]
  · refine T4_eq_scalar hω hω1 (c := (c : K)) ?_
    have h1 := congrArg Units.val hc
    simp only [GeneralLinearGroup.coe_scalar] at h1
    exact h1

theorem exists_add_bar_eq_one [CharP K 2] : ∃ l : K, l + h.bar l = 1 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hs : c + h.bar c ≠ 0 := fun h0 => hc (by
    rw [← sub_eq_zero, CharTwo.sub_eq_add, add_comm]
    exact h0)
  refine ⟨c / (c + h.bar c), ?_⟩
  rw [map_div₀, map_add, h.bar_bar, add_comm (h.bar c) c, ← add_div, div_self hs]

theorem exists_twist_u6 [CharP K 2] {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hbω : h.bar ω = ω) :
    ∃ g : Multiplicative (Fin 3 → ZMod 3) →*
        primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := 6) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 6) (K := K)) τ) (g a) = g a := by
  obtain ⟨l, hl⟩ := exists_add_bar_eq_one h
  refine exists_twist h (J := r6 J0) (fun σ => by rw [r6_map, J0_map]) (P6 hl) ?_ (T6 hω) ?_ ?_
    ?_ ?_
  · change ((r6 (P0 l (h.bar l))).map h.bar)ᵀ * r6 (P0 l (h.bar l)) = r6 J0
    rw [r6_map, r6_transpose, r6_mul, P0_gram h.bar hl rfl (h.bar_bar l)]
  · intro a
    change ((r6 (T0 ω a.toAdd)).map h.bar)ᵀ * r6 J0 * r6 (T0 ω a.toAdd) = r6 J0
    rw [r6_map, r6_transpose, r6_mul, r6_mul, T0_gram hω h.bar hbω]
  · intro a
    change (r6 (T0 ω a.toAdd)).det = 1
    rw [r6_det, T0_det hω]
  · intro τ hτ a
    apply Units.ext
    rw [coe_glAut]
    change (r6 (T0 ω a.toAdd)).map τ = r6 (T0 ω a.toAdd)
    rw [r6_map, T0_map τ (fix_omega hω hω1 τ hτ)]
  · intro a c hc
    have h1 : r6 (T0 ω a.toAdd) = r6 (scalar _ (c : K)) := by
      rw [r6_scalar]
      have := congrArg Units.val hc
      simp only [GeneralLinearGroup.coe_scalar] at this
      exact this
    exact Multiplicative.toAdd.injective (T0_eq_scalar hω hω1 (r6_injective h1))

theorem exists_twist_u7 [CharP K 2] {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hbω : h.bar ω = ω) :
    ∃ g : Multiplicative (Fin 3 → ZMod 3) →*
        primeFormP h ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y * primeFormFieldHom h (isPrimeFormGram_one (n := 7) (K := K)) τ)
        ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 7) (K := K)) τ) (g a) = g a := by
  obtain ⟨l, hl⟩ := exists_add_bar_eq_one h
  refine exists_twist_blk h (J := r6 J0) (fun σ => by rw [r6_map, J0_map]) (P6 hl) ?_ (T6 hω) ?_ ?_
    ?_ ?_
  · change ((r6 (P0 l (h.bar l))).map h.bar)ᵀ * r6 (P0 l (h.bar l)) = r6 J0
    rw [r6_map, r6_transpose, r6_mul, P0_gram h.bar hl rfl (h.bar_bar l)]
  · intro a
    change ((r6 (T0 ω a.toAdd)).map h.bar)ᵀ * r6 J0 * r6 (T0 ω a.toAdd) = r6 J0
    rw [r6_map, r6_transpose, r6_mul, r6_mul, T0_gram hω h.bar hbω]
  · intro a
    change (r6 (T0 ω a.toAdd)).det = 1
    rw [r6_det, T0_det hω]
  · intro τ hτ a
    apply Units.ext
    rw [coe_glAut]
    change (r6 (T0 ω a.toAdd)).map τ = r6 (T0 ω a.toAdd)
    rw [r6_map, T0_map τ (fix_omega hω hω1 τ hτ)]
  · intro a c hc
    have h1 : r6 (T0 ω a.toAdd) = r6 (scalar _ (c : K)) := by
      rw [r6_scalar]
      have := congrArg Units.val hc
      simp only [GeneralLinearGroup.coe_scalar] at this
      exact this
    exact Multiplicative.toAdd.injective (T0_eq_scalar hω hω1 (r6_injective h1))

theorem exists_cube_root (h : UnitaryFieldData 2 f K) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  haveI := h.finite
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Fintype.card Kˣ := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, h.card]
    have : 2 ^ (2 * f) % 3 = 1 := CFSG.two_pow_mod_three_of_even (even_two_mul f)
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 h3
  refine ⟨x, ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
  · rw [show x = 1 from Units.ext h1, orderOf_one] at hx
    norm_num at hx

theorem exists_rankFour_psu6 {X : Type} [Group X] [Finite X] (hp : p = 2) (hf : Even f)
    (e : X ≃* primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  subst hp
  haveI : CharP K 2 := h.charP
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root h
  have h2f := CFSG.two_pow_mod_three_of_even hf
  have hbω : h.bar ω = ω := by
    rw [UnitaryFieldData.bar_apply, ← pow_mod_three hω (2 ^ f), h2f, pow_one]
  obtain ⟨g, hg, htw⟩ := exists_twist_u6 h hω hω1 hbω
  have hcop : Nat.Coprime 6 (2 ^ f + 1) := by
    rw [show 6 = 2 * 3 from rfl, Nat.coprime_mul_iff_left, Nat.coprime_two_left,
      Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    refine ⟨(Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one, by omega⟩
  exact exists_rankFour_psu h (by norm_num) (fun h1 => absurd h1.1 (by norm_num))
    (primeFormConjHom_mem_inner_of_coprime h hcop) e hc hinn hαH hα hαn g hg
    SpE27.pow_three_eq_one SpE27.card_e27 htw

theorem exists_rankFour_psu7 {X : Type} [Group X] [Finite X] (hp : p = 2) (hf : Even f)
    (e : X ≃* primeFormP h ((1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  subst hp
  haveI : CharP K 2 := h.charP
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root h
  have h2f := CFSG.two_pow_mod_three_of_even hf
  have hbω : h.bar ω = ω := by
    rw [UnitaryFieldData.bar_apply, ← pow_mod_three hω (2 ^ f), h2f, pow_one]
  obtain ⟨g, hg, htw⟩ := exists_twist_u7 h hω hω1 hbω
  have hcop : Nat.Coprime 7 (2 ^ f + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)]
    have h7 : 2 ^ f % 7 = 2 ^ (f % 3) % 7 := by
      conv_lhs => rw [← Nat.div_add_mod f 3, pow_add, pow_mul]
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num
    have : f % 3 = 0 ∨ f % 3 = 1 ∨ f % 3 = 2 := by omega
    rcases this with h3 | h3 | h3 <;> rw [h3] at h7 <;> norm_num at h7 <;> omega
  exact exists_rankFour_psu h (by norm_num) (fun h1 => absurd h1.1 (by norm_num))
    (primeFormConjHom_mem_inner_of_coprime h hcop) e hc hinn hαH hα hαn g hg
    SpE27.pow_three_eq_one SpE27.card_e27 htw

theorem exists_rankFour_psu4 {X : Type} [Group X] [Finite X] (hp : p = 2) (hf : Odd f)
    (e : X ≃* primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range) :
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81 := by
  subst hp
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root h
  have h2f := CFSG.two_pow_mod_three_of_odd hf
  have hbω : h.bar ω * ω = 1 := by
    rw [UnitaryFieldData.bar_apply, ← pow_mod_three hω (2 ^ f), h2f, ← pow_succ, hω]
  obtain ⟨g, hg, htw⟩ := exists_twist_u4 h hω hω1 hbω
  have hcop : Nat.Coprime 4 (2 ^ f + 1) :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 (Nat.even_pow.2 ⟨even_two,
      by have := h.one_le; omega⟩).add_one)
  exact exists_rankFour_psu h (by norm_num) (fun h1 => absurd h1.1 (by norm_num))
    (primeFormConjHom_mem_inner_of_coprime h hcop) e hc hinn hαH hα hαn g hg
    SpE27.pow_three_eq_one SpE27.card_e27 htw

end LieClAut

@[expose] def KFactOuterThreeRankFourRestSU : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (d : TauCeti.ValidLieTypeIndex), IsRankTwoPlus d.1 →
    RankThreeList d.1 → (∀ q : TauCeti.PrimePower, d.1 ≠ .B 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 5 q) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .A 6 q) → (∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 3 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 5 q) →
    (∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 6 q) → LieClAut.FieldExponentThree d.1 →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X),
    (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∃ F : Subgroup (MulAut X), F ≤ H ∧ IsElemAbelian 3 F ∧ Nat.card F = 81

theorem unitaryFieldData_galoisField (q : TauCeti.PrimePower) [Fact q.p.Prime] :
    UnitaryFieldData q.p q.exponent (GaloisField q.p (2 * q.exponent)) :=
  ⟨q.prime_p, q.exponent_pos, GaloisField.card _ _ (by have := q.exponent_pos; omega)⟩

theorem kFactOuterThreeRankFourRestSL7_of_su (h : KFactOuterThreeRankFourRestSU) :
    KFactOuterThreeRankFourRestSL7 := by
  classical
  intro X _ _ d hd hl hB hA5 hA3 hA6 h3 he hc H hinn hα
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  by_cases hU3 : ∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 3 q
  · by_cases hU5 : ∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 5 q
    · by_cases hU6 : ∀ q : TauCeti.PrimePower, d.1 ≠ .twistedA 6 q
      · exact h X d hd hl hB hA5 hA3 hA6 hU3 hU5 hU6 h3 he hc H hinn ⟨α, hαH, hαk, hαn⟩
      push Not at hU6
      obtain ⟨q, hq⟩ := hU6
      obtain ⟨d, hv⟩ := d
      simp only at hq
      subst hq
      obtain ⟨e⟩ := he
      haveI : Fact q.p.Prime := ⟨q.prime_p⟩
      have hK := unitaryFieldData_galoisField q
      obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK
        (N := 7) (by norm_num) hv
      exact LieClAut.exists_rankFour_psu7 hK hd.1 hl (e.trans e'.symm) hc hinn hαH hαk hαn
    push Not at hU5
    obtain ⟨q, hq⟩ := hU5
    obtain ⟨d, hv⟩ := d
    simp only at hq
    subst hq
    obtain ⟨e⟩ := he
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK := unitaryFieldData_galoisField q
    obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK
      (N := 6) (by norm_num) hv
    exact LieClAut.exists_rankFour_psu6 hK hd.1 hl (e.trans e'.symm) hc hinn hαH hαk hαn
  push Not at hU3
  obtain ⟨q, hq⟩ := hU3
  obtain ⟨d, hv⟩ := d
  simp only at hq
  subst hq
  obtain ⟨e⟩ := he
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK := unitaryFieldData_galoisField q
  obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK
    (N := 4) (by norm_num) hv
  exact LieClAut.exists_rankFour_psu4 hK hd.1 hl (e.trans e'.symm) hc hinn hαH hαk hαn

theorem kFactTenElevenOneLieAutRes_of_rankFourSU
    (hK : KFactOuterThreeRankFourRestSU) (h2 : KFactTenElevenOneLieAutFieldTwo) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_rankFourSL7 (kFactOuterThreeRankFourRestSL7_of_su hK) h2

end CFSG.LocalAnalysis.RankThreeTheoremC
