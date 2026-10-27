module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClRankFourSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeAbelian

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

namespace LieClAut

theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {N : Subgroup G} {x : G} {m n : ℕ}
    (hmn : m.Coprime n) (hm : x ^ m ∈ N) (hn : x ^ n = 1) : x ∈ N := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmn h1
    have hx : x = (x ^ m) ^ s := by
      rw [← pow_mul, ← Nat.div_add_mod (m * s) n, hs, pow_add, pow_mul, hn, one_pow, one_mul,
        pow_one]
    rw [hx]
    exact N.pow_mem hm s
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · rw [Nat.coprime_zero_right] at hmn
      rwa [hmn, pow_one] at hm
    · rw [pow_one] at hn
      rw [hn]
      exact N.one_mem

theorem three_le_pRank_of_fieldFactor {X C A : Type} [Group X] [Finite X] [Group C]
    [Finite C] [IsCyclic C] [CommGroup A] [Finite A] (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (hab : ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (Φ : MulAut X →* C) (hΦ : ∀ x : X, Φ (MulAut.conj x) = 1)
    (hD : ∀ δ : MulAut X, Φ δ = 1 → (∃ k : ℕ, δ ^ 3 ^ k = 1) →
      δ ∈ (MulAut.conj : X →* MulAut X).range)
    (hA3 : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 9)
    (htw : ∀ τ : C, τ ^ 3 = 1 → τ ≠ 1 → ∃ (β₀ : MulAut X) (f : A →* X),
      Function.Injective f ∧ β₀ ^ 3 = 1 ∧ Φ β₀ = τ ∧ ∀ a, β₀ (f a) = f a)
    {α : MulAut X} (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : C, a * b = b * a := fun a b => (IsCyclic.commGroup (α := C)).mul_comm a b
  obtain ⟨k, hk⟩ := hα
  have hφk : Φ α ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hφ1 : Φ α ≠ 1 := fun h1 => hαn (hD α h1 ⟨k, hk⟩)
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hφk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by rw [hjo, pow_zero]))
  set α₁ := α ^ 3 ^ (j - 1) with hα₁
  have hτ' : Φ α₁ = Φ α ^ 3 ^ (j - 1) := by rw [hα₁, map_pow]
  have hτ3 : Φ α₁ ^ 3 = 1 := by
    rw [hτ', ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hjo,
      pow_orderOf_eq_one]
  have hτ1 : Φ α₁ ≠ 1 := by
    intro h
    rw [hτ'] at h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hjo] at h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h1
    omega
  obtain ⟨β₀, f, hf, hβ₀3, hβ₀Φ, hβ₀f⟩ := htw _ hτ3 hτ1
  have hα₁H : α₁ ∈ H := H.pow_mem hαH _
  have hα₁k : α₁ ^ 3 ^ k = 1 := by rw [hα₁, ← pow_mul, mul_comm, pow_mul, hk, one_pow]
  have hpα : IsPGroup 3 (zpowers α₁) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hα₁k)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hpβ : IsPGroup 3 (zpowers β₀) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (orderOf_dvd_of_pow_eq_one (n := 3 ^ 1) (by rw [pow_one, hβ₀3]))
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨S, hS⟩ := hpβ.exists_le_sylow
  obtain ⟨S', hS'⟩ := hpα.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut X) S S'
  set β := MulAut.conj g β₀ with hβ
  have hβS' : β ∈ (S' : Subgroup (MulAut X)) := by
    have hmem : (MulAut.conj g).toMonoidHom β₀ ∈ ((g • S : Sylow 3 (MulAut X)) :
        Subgroup (MulAut X)) := Subgroup.mem_map_of_mem _ (hS (mem_zpowers β₀))
    rw [hg] at hmem
    exact hmem
  have hβΦ : Φ β = Φ α₁ := by
    rw [hβ, MulAut.conj_apply, map_mul, map_mul, map_inv, hβ₀Φ, hcomm (Φ g), mul_assoc,
      mul_inv_cancel, mul_one]
  have hβH : β ∈ H := by
    have hδ : α₁⁻¹ * β ∈ (S' : Subgroup (MulAut X)) :=
      mul_mem (inv_mem (hS' (mem_zpowers α₁))) hβS'
    obtain ⟨n, hn⟩ := S'.isPGroup' ⟨_, hδ⟩
    have hI := hD (α₁⁻¹ * β) (by rw [map_mul, map_inv, hβΦ, inv_mul_cancel])
      ⟨n, by simpa using congrArg Subtype.val hn⟩
    have : β = α₁ * (α₁⁻¹ * β) := by group
    rw [this]
    exact H.mul_mem hα₁H (hinn hI)
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hβ₀3, map_one]
  have hβn : β ∉ (MulAut.conj : X →* MulAut X).range := by
    rintro ⟨x, hx⟩
    apply hτ1
    rw [← hβΦ, ← hx, hΦ]
  refine three_le_pRank_of_abelian hc hinn hab hβH hβ3 hβn ((g : X ≃* X).toMonoidHom.comp f)
    (g.injective.comp hf) hA3 hA (fun a => ?_) (D := Φ.ker)
    (fun δ hδ h3 => hD δ (MonoidHom.mem_ker.1 hδ) h3) (fun γ _ hγ3 hγn => ?_) hEH hE hEc
  · change (g * β₀ * g⁻¹) (g (f a)) = g (f a)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hβ₀f]
  · have h3 : Φ γ ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
    have h1 : Φ γ ≠ 1 := fun h1 => hγn (hD γ h1 ⟨1, by rw [pow_one, hγ3]⟩)
    rcases eq_or_eq_inv_of_isCyclic hτ3 hτ1 h3 h1 with h | h
    · left
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβΦ, h, mul_inv_cancel]
    · right
      rw [MonoidHom.mem_ker, map_mul, hβΦ, h, inv_mul_cancel]

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem primeFormConjHom_mem_inner_of_det {m : ℕ}
    (B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (v : Kˣ)
    (hv : h.norm (v : K) = 1) (hvm : v ^ m = GeneralLinearGroup.det (B : GL (Fin m) K)) :
    primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) B ∈
      inner (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  have hNpow : ∀ w : Kˣ, h.norm (w : K) = ((w ^ (p ^ f + 1) : Kˣ) : K) := fun w => by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, Units.val_pow_eq_pow_val, pow_succ,
      mul_comm]
  have hv1 : v ^ (p ^ f + 1) = 1 := Units.ext (by rw [← hNpow, hv, Units.val_one])
  have hv' : h.norm ((v⁻¹ : Kˣ) : K) = 1 := by
    rw [hNpow, inv_pow, hv1, inv_one, Units.val_one]
  set Z : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨GeneralLinearGroup.scalar (Fin m) v⁻¹, scalar_mem_primeFormUnitary_one h hv'⟩ with hZ
  have hS : ((Z * B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
      GL (Fin m) K) ∈ gramSU h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨(Z * B).2, ?_⟩
    rw [← GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, map_mul, ← hvm]
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

theorem primeFormConjHom_mem_inner_of_pow {m : ℕ} (hm : m.Coprime 3)
    (B : primeFormUnitary h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) {k : ℕ}
    (hk : primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) B ^ 3 ^ k = 1) :
    primeFormConjHom h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) B ∈
      inner (primeFormP h ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) := by
  refine mem_of_pow_mem_of_coprime (Nat.Coprime.pow_right k hm) ?_ hk
  rw [← map_pow]
  refine primeFormConjHom_mem_inner_of_det h (B ^ m) (GeneralLinearGroup.det (B : GL (Fin m) K))
    ?_ ?_
  · rw [GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h 1 B.2
  · rw [Subgroup.coe_pow, map_pow]

end LieClAut

namespace FieldTwoE9

open TorusE27

variable {K : Type} [Field K]

@[expose] def J2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 1 0

@[expose] def P2 (l l' : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks 1 (diagonal fun _ => l) 1 (diagonal fun _ => l')

@[expose] def Q2 (l l' : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diagonal fun _ => l') (diagonal fun _ => l) 1 1

@[expose] def T2 (ω : K) (v : Fin 2 → ZMod 3) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diagonal fun i => chi ω (v i)) 0 0 (diagonal fun i => chi ω (-v i))

theorem J2_map (σ : K ≃+* K) : (J2 : Matrix _ _ K).map σ = J2 := by
  simp [J2, fromBlocks_map]

theorem diagonal_const_one : (diagonal fun _ : Fin 2 => (1 : K)) = 1 := rfl

theorem chi_mul_neg {ω : K} (hω : ω ^ 3 = 1) (x : ZMod 3) : chi ω x * chi ω (-x) = 1 := by
  rw [← chi_add hω, add_neg_cancel, chi_zero]

theorem T2_mul {ω : K} (hω : ω ^ 3 = 1) (v w : Fin 2 → ZMod 3) :
    T2 ω v * T2 ω w = T2 ω (v + w) := by
  rw [T2, T2, T2, fromBlocks_multiply]
  simp only [diagonal_mul_diagonal, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Pi.add_apply, neg_add, chi_add hω]

theorem T2_zero (ω : K) : T2 ω 0 = 1 := by
  rw [T2, ← fromBlocks_one]
  simp [chi_zero]

theorem T2_det {ω : K} (hω : ω ^ 3 = 1) (v : Fin 2 → ZMod 3) : (T2 ω v).det = 1 := by
  rw [T2, det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  simp [chi_mul_neg hω]

theorem T2_map {ω : K} (σ : K ≃+* K) (hσ : σ ω = ω) (v : Fin 2 → ZMod 3) :
    (T2 ω v).map σ = T2 ω v := by
  have hc : ∀ x, σ (chi ω x) = chi ω x := fun x => by rw [chi, map_pow, hσ]
  simp [T2, fromBlocks_map, diagonal_map, hc]

theorem T2_gram {ω : K} (hω : ω ^ 3 = 1) (b : K →+* K) (hb : b ω = ω) (v : Fin 2 → ZMod 3) :
    ((T2 ω v).map b)ᵀ * J2 * T2 ω v = J2 := by
  have hc : ∀ x, b (chi ω x) = chi ω x := fun x => by rw [chi, map_pow, hb]
  rw [T2, J2, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_map (map_zero b), hc, Matrix.map_zero _ (map_zero b), transpose_zero,
    diagonal_transpose, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
    zero_add, add_zero, diagonal_mul_diagonal, chi_mul_neg hω]
  rw [show (fun i : Fin 2 => chi ω (-v i) * chi ω (v i)) = fun _ => 1 from
    funext fun i => by rw [mul_comm, chi_mul_neg hω], diagonal_const_one]

theorem T2_eq_scalar {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {v : Fin 2 → ZMod 3} {c : K}
    (h : T2 ω v = scalar _ c) : v = 0 := by
  funext i
  have h1 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (.inl i) (.inl i)) h
  have h2 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K => M (.inr i) (.inr i)) h
  simp only [T2, fromBlocks_apply₁₁, fromBlocks_apply₂₂, diagonal_apply_eq, scalar_apply] at h1 h2
  exact HypE27.eq_zero_of_eq_neg _ (chi_injective hω hω1 (h1.trans h2.symm))

section CharTwo

variable [CharP K 2]

theorem P2_mul_Q2 {l l' : K} (hl : l + l' = 1) : P2 l l' * Q2 l l' = 1 := by
  have h2 : ∀ x : K, x + x = 0 := CharTwo.add_self_eq_zero
  have hl' : l' + l = 1 := by rw [add_comm]; exact hl
  rw [P2, Q2, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp only [Matrix.one_mul, Matrix.mul_one, diagonal_add, h2, diagonal_zero] <;>
    ext i j <;> by_cases hij : i = j <;> simp [diagonal_apply, Matrix.one_apply, hij, hl, hl']

theorem Q2_mul_P2 {l l' : K} (hl : l + l' = 1) : Q2 l l' * P2 l l' = 1 :=
  mul_eq_one_comm.1 (P2_mul_Q2 hl)

theorem P2_gram (b : K →+* K) {l l' : K} (hl : l + l' = 1) (hb : b l = l') (hb' : b l' = l) :
    ((P2 l l').map b)ᵀ * P2 l l' = J2 := by
  have h2 : ∀ x : K, x + x = 0 := CharTwo.add_self_eq_zero
  rw [P2, J2, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply]
  simp only [Matrix.map_one _ (map_zero b) (map_one b), diagonal_map (map_zero b), hb, hb',
    transpose_one, diagonal_transpose, Matrix.one_mul, Matrix.mul_one, diagonal_mul_diagonal,
    diagonal_add, mul_comm l l', h2, diagonal_zero]
  congr 1
  · ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, h2]
  all_goals ext i j
  all_goals by_cases hij : i = j <;>
    simp [diagonal_apply, Matrix.one_apply, hij, hl, add_comm l' l]

end CharTwo

@[expose] def ext (s : ℕ) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin (4 + s)) (Fin (4 + s)) K :=
  (fromBlocks M 0 0 1 : Matrix ((Fin 2 ⊕ Fin 2) ⊕ Fin s) ((Fin 2 ⊕ Fin 2) ⊕ Fin s) K).submatrix
    (eL s).symm (eL s).symm

theorem ext_mul (s : ℕ) (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    ext s M * ext s N = ext s (M * N) := by
  simp only [ext, submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.mul_one]

theorem ext_one (s : ℕ) : ext s (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
  simp only [ext, fromBlocks_one, submatrix_one_equiv]

theorem ext_map (s : ℕ) (b : K → K) (hb0 : b 0 = 0) (hb1 : b 1 = 1)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : (ext s M).map b = ext s (M.map b) := by
  rw [ext, ext, ← submatrix_map, fromBlocks_map]
  simp only [Matrix.map_zero _ hb0, Matrix.map_one _ hb0 hb1]

theorem ext_transpose (s : ℕ) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (ext s M)ᵀ = ext s Mᵀ := by
  rw [ext, ext, transpose_submatrix, fromBlocks_transpose]
  simp

theorem ext_det (s : ℕ) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (ext s M).det = M.det := by
  rw [ext, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem eq_of_ext_eq_scalar (s : ℕ) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {c : K}
    (h : ext s M = scalar _ c) : M = scalar _ c := by
  ext i j
  have h1 := congrArg (fun A : Matrix (Fin (4 + s)) (Fin (4 + s)) K =>
    A (eL s (.inl i)) (eL s (.inl j))) h
  simp only [ext, submatrix_apply, Equiv.symm_apply_apply, fromBlocks_apply₁₁] at h1
  rw [h1]
  simp [scalar_apply, diagonal_apply, (eL s).injective.eq_iff]

@[expose] def Pext [CharP K 2] (s : ℕ) {l l' : K} (hl : l + l' = 1) : GL (Fin (4 + s)) K :=
  ⟨ext s (P2 l l'), ext s (Q2 l l'), by rw [ext_mul, P2_mul_Q2 hl, ext_one], by
    rw [ext_mul, Q2_mul_P2 hl, ext_one]⟩

@[expose] noncomputable def Text (s : ℕ) {ω : K} (hω : ω ^ 3 = 1) :
    Multiplicative (Fin 2 → ZMod 3) →* GL (Fin (4 + s)) K where
  toFun v := ⟨ext s (T2 ω v.toAdd), ext s (T2 ω (-v.toAdd)), by
    rw [ext_mul, T2_mul hω, add_neg_cancel, T2_zero, ext_one], by
    rw [ext_mul, T2_mul hω, neg_add_cancel, T2_zero, ext_one]⟩
  map_one' := Units.ext (by
    change ext s (T2 ω 0) = 1
    rw [T2_zero, ext_one])
  map_mul' v w := Units.ext (by
    change ext s (T2 ω (v.toAdd + w.toAdd)) = ext s (T2 ω v.toAdd) * ext s (T2 ω w.toAdd)
    rw [ext_mul, T2_mul hω])

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem exists_twist_ext [CharP K 2] (s : ℕ) {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hbω : h.bar ω = ω) :
    ∃ g : Multiplicative (Fin 2 → ZMod 3) →*
        primeFormP h ((1 : GL (Fin (4 + s)) K) : Matrix (Fin (4 + s)) (Fin (4 + s)) K),
      Function.Injective g ∧ ∀ τ : K ≃+* K, τ ^ 3 = 1 → ∃ Y,
      (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 4 + s) (K := K)) τ) ^ 3 = 1 ∧
      ∀ a, (primeFormConjHom h _ Y *
        primeFormFieldHom h (isPrimeFormGram_one (n := 4 + s) (K := K)) τ) (g a) = g a := by
  obtain ⟨l, hl⟩ := LieClAut.exists_add_bar_eq_one h
  refine LieClAut.exists_twist h (J := ext s J2)
    (fun σ => by rw [ext_map s _ (map_zero σ) (map_one σ), J2_map]) (Pext s hl) ?_ (Text s hω)
    ?_ ?_ ?_ ?_
  · change ((ext s (P2 l (h.bar l))).map h.bar)ᵀ * ext s (P2 l (h.bar l)) = ext s J2
    rw [ext_map s _ (map_zero _) (map_one _), ext_transpose, ext_mul,
      P2_gram h.bar hl rfl (h.bar_bar l)]
  · intro a
    change ((ext s (T2 ω a.toAdd)).map h.bar)ᵀ * ext s J2 * ext s (T2 ω a.toAdd) = ext s J2
    rw [ext_map s _ (map_zero _) (map_one _), ext_transpose, ext_mul, ext_mul,
      T2_gram hω h.bar hbω]
  · intro a
    change (ext s (T2 ω a.toAdd)).det = 1
    rw [ext_det, T2_det hω]
  · intro τ hτ a
    apply Units.ext
    rw [coe_glAut]
    change (ext s (T2 ω a.toAdd)).map τ = ext s (T2 ω a.toAdd)
    rw [ext_map s _ (map_zero τ) (map_one τ), T2_map τ (fix_omega hω hω1 τ hτ)]
  · intro a c hc
    have h1 : ext s (T2 ω a.toAdd) = scalar _ (c : K) := by
      have := congrArg Units.val hc
      simp only [GeneralLinearGroup.coe_scalar] at this
      exact this
    exact Multiplicative.toAdd.injective (T2_eq_scalar hω hω1 (eq_of_ext_eq_scalar s h1))

end FieldTwoE9

namespace LieClAut

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem three_le_pRank_psu {X : Type} [Group X] [Finite X] (hp : p = 2) (hf : Even f)
    {s : ℕ} (hs : s ≤ 1)
    (e : X ≃* primeFormP h ((1 : GL (Fin (4 + s)) K) : Matrix (Fin (4 + s)) (Fin (4 + s)) K))
    (hc : center X = ⊥) (hab : ∀ P : Subgroup X, IsPGroup 3 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H) {α : MulAut X}
    (hαH : α ∈ H) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1)
    (hαn : α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  classical
  subst hp
  haveI : CharP K 2 := h.charP
  haveI := h.finite
  haveI : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic Nat.prime_two K h.card).2
  set P := primeFormP h ((1 : GL (Fin (4 + s)) K) : Matrix (Fin (4 + s)) (Fin (4 + s)) K)
  have hC : IsPrimeFormGram (1 : GL (Fin (4 + s)) K) := isPrimeFormGram_one
  have hm : 3 ≤ 4 + s := by omega
  have hq : ¬(4 + s = 3 ∧ 2 ^ f = 2) := fun h1 => by omega
  set Ψ : MulAut X ≃* MulAut P := MulAut.congr e with hΨ
  have hΨconj : ∀ x : X, Ψ (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext p
    simp [hΨ]
  have hΨinv : ∀ p : P, Ψ.symm (MulAut.conj p) = MulAut.conj (e.symm p) := fun p => by
    rw [MulEquiv.symm_apply_eq, hΨconj, e.apply_symm_apply]
  have hinnΨ' : ∀ γ, γ ∈ inner P → Ψ.symm γ ∈ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨p, rfl⟩
    exact ⟨e.symm p, (hΨinv p).symm⟩
  obtain ⟨ω, hω, hω1⟩ := exists_cube_root h
  have hbω : h.bar ω = ω := by
    rw [UnitaryFieldData.bar_apply, ← TorusE27.pow_mod_three hω (2 ^ f),
      CFSG.two_pow_mod_three_of_even hf, pow_one]
  obtain ⟨g, hg, htw⟩ := FieldTwoE9.exists_twist_ext h s hω hω1 hbω
  have hcop : (4 + s).Coprime 3 := by
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  refine three_le_pRank_of_fieldFactor hc hinn hab
    ((primeFormFieldFactor h hC hm hq).comp Ψ.toMonoidHom) (fun x => ?_) (fun δ hδ hδ3 => ?_)
    FieldTwoE9.pow_three_eq_one FieldTwoE9.card_e9 (fun τ hτ3 _ => ?_) hαH hα hαn hEH hE hEc
  · change primeFormFieldFactor h hC hm hq (Ψ (MulAut.conj x)) = 1
    rw [hΨconj]
    obtain ⟨t, ht⟩ := (mem_inner_primeFormP h _ (MulAut.conj (e x))).1 ⟨e x, rfl⟩
    rw [ht]
    have := primeFormFieldFactor_apply h hC hm hq ⟨t, t.2.1⟩ 1
    rwa [map_one, mul_one] at this
  · obtain ⟨φ, ⟨B, hB⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hm hq (Ψ δ)
    have hφ : φ = 1 := by
      have h1 := primeFormFieldFactor_apply h hC hm hq B φ
      rw [← hB] at h1
      rw [← h1]
      exact hδ
    rw [hφ, map_one, mul_one] at hB
    obtain ⟨k, hk⟩ := hδ3
    have hin := primeFormConjHom_mem_inner_of_pow h hcop B (k := k)
      (by rw [← hB, ← map_pow, hk, map_one])
    rw [← Ψ.symm_apply_apply δ, hB]
    exact hinnΨ' _ hin
  · obtain ⟨Y, hY3, hYfix⟩ := htw τ hτ3
    refine ⟨Ψ.symm (primeFormConjHom h _ Y * primeFormFieldHom h hC τ),
      e.symm.toMonoidHom.comp g, e.symm.injective.comp hg, ?_, ?_, fun a => ?_⟩
    · rw [← map_pow, hY3, map_one]
    · change primeFormFieldFactor h hC hm hq (Ψ (Ψ.symm _)) = τ
      rw [Ψ.apply_symm_apply, primeFormFieldFactor_apply]
    · simp only [hΨ, MulAut.congr_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.apply_symm_apply, MulEquiv.trans_apply]
      rw [hYfix]

theorem three_le_pRank_typeTwistedA {X : Type} [Group X] [Finite X]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsRankTwoPlus d.1) (hl : RankTwoList d.1)
    (hU : ∃ q : TauCeti.PrimePower, d.1 = .twistedA 3 q ∨ d.1 = .twistedA 4 q)
    (he : Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)) (hc : center X = ⊥)
    {H : Subgroup (MulAut X)} (hinn : (MulAut.conj : X →* MulAut X).range ≤ H)
    (hα : ∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range)
    {E : Subgroup (MulAut X)} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) :
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X))) := by
  obtain ⟨α, hαH, hαk, hαn⟩ := hα
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := d
  obtain ⟨q, hq | hq⟩ := hU <;> simp only at hq <;> subst hq
  · have hp : q.p = 2 := hd.1
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK := unitaryFieldData_galoisField q
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := by
      rw [hp]
      exact KFactProofs.Stroth.Bal3.I294Cross.not_three_dvd_pow Nat.prime_two (by norm_num)
    have hq1 : q.p ^ q.exponent % 3 = 1 := by
      rw [hp]
      exact CFSG.two_pow_mod_three_of_even hl
    obtain ⟨_, L, _, _, hL, ⟨e''⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    have hab := comm_of_sylow_comm e''
      (KFactProofs.Stroth.Bal3.I294Cross.sylow_comm_psu hL hq3 hq1 (by norm_num) (by norm_num))
    obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK
      (N := 4) (by norm_num) hv
    exact three_le_pRank_psu hK hp hl (s := 0) (by norm_num) (e.trans e'.symm) hc hab hinn hαH
      hαk hαn hEH hE hEc
  · have hp : q.p = 2 := hd.1
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK := unitaryFieldData_galoisField q
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := by
      rw [hp]
      exact KFactProofs.Stroth.Bal3.I294Cross.not_three_dvd_pow Nat.prime_two (by norm_num)
    have hq1 : q.p ^ q.exponent % 3 = 1 := by
      rw [hp]
      exact CFSG.two_pow_mod_three_of_even hl
    obtain ⟨_, L, _, _, hL, ⟨e''⟩⟩ :=
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e
    have hab := comm_of_sylow_comm e''
      (KFactProofs.Stroth.Bal3.I294Cross.sylow_comm_psu hL hq3 hq1 (by norm_num) (by norm_num))
    obtain ⟨e'⟩ := CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK
      (N := 5) (by norm_num) hv
    exact three_le_pRank_psu hK hp hl (s := 1) le_rfl (e.trans e'.symm) hc hab hinn hαH
      hαk hαn hEH hE hEc

end LieClAut

end CFSG.LocalAnalysis.RankThreeTheoremC
