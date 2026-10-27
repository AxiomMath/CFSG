module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9Defs
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.U45

open Equiv Subgroup

theorem alt9_isConj_inv (σ : alternatingGroup (Fin 9)) (hσ : orderOf σ = 7) : IsConj σ σ⁻¹ := by
  have hord : orderOf (σ : Perm (Fin 9)) = 7 := by rw [Subgroup.orderOf_coe]; exact hσ
  have hne : (σ : Perm (Fin 9)).cycleType ≠ 0 := by
    intro h0
    have h1 : (σ : Perm (Fin 9)) = 1 := Perm.cycleType_eq_zero.1 h0
    rw [h1, orderOf_one] at hord
    omega
  have hall : ∀ n ∈ (σ : Perm (Fin 9)).cycleType, n = 7 := by
    intro n hn
    have h1 := Perm.dvd_of_mem_cycleType hn
    rw [hord] at h1
    have h2 := Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime (by norm_num)).1 h1 with h3 | h3 <;> omega
  have hrep : (σ : Perm (Fin 9)).cycleType =
      Multiset.replicate (Multiset.card (σ : Perm (Fin 9)).cycleType) 7 :=
    Multiset.eq_replicate_card.2 hall
  have hsum := Perm.sum_cycleType (σ : Perm (Fin 9))
  have hle := Perm.sum_cycleType_le (σ : Perm (Fin 9))
  have hpos : 0 < Multiset.card (σ : Perm (Fin 9)).cycleType :=
    Multiset.card_pos.2 hne
  generalize hk : Multiset.card (σ : Perm (Fin 9)).cycleType = k at hrep hpos
  have hsum2 : (σ : Perm (Fin 9)).cycleType.sum = k * 7 := by
    rw [hrep]
    simp [Multiset.sum_replicate]
  simp only [Fintype.card_fin] at hle
  have hk1 : k = 1 := by omega
  have hsupp : (σ : Perm (Fin 9)).support.card = 7 := by omega
  refine alternatingGroup.isConj_of ?_ (by rw [hsupp]; simp)
  rw [Subgroup.coe_inv]
  exact Perm.isConj_iff_cycleType_eq.2 (Perm.cycleType_inv _).symm

private theorem factorization_seven_eq_one {n : ℕ} (hn : n ≠ 0) (h7 : 7 ∣ n) (h49 : ¬ 49 ∣ n) :
    n.factorization 7 = 1 := by
  have h1 : 1 ≤ n.factorization 7 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (p := 7) (k := 1) (by norm_num) hn).1
      (by simpa using h7)
  have h2 : ¬ 2 ≤ n.factorization 7 := fun h =>
    h49 (by simpa using
      (Nat.Prime.pow_dvd_iff_le_factorization (p := 7) (k := 2) (by norm_num) hn).2 h)
  omega

open scoped Pointwise in
theorem exists_inverting_of_section {Γ : Type*} [Group Γ] [Finite Γ]
    (φ : Γ →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (h49 : ¬ 49 ∣ Nat.card Γ) :
    ∃ g x : Γ, orderOf g = 7 ∧ x * g * x⁻¹ = g⁻¹ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card Γ := by
    have h1 : Nat.card (alternatingGroup (Fin 9)) ∣ Nat.card Γ :=
      Subgroup.card_dvd_of_surjective hφ
    rw [SwapP2.card_alt_nine] at h1
    exact (by norm_num : 7 ∣ 181440).trans h1
  have hfac : (Nat.card Γ).factorization 7 = 1 :=
    factorization_seven_eq_one Nat.card_pos.ne' h7 h49
  have hfacA : (Nat.card (alternatingGroup (Fin 9))).factorization 7 = 1 :=
    factorization_seven_eq_one Nat.card_pos.ne' (by rw [SwapP2.card_alt_nine]; norm_num)
      (by rw [SwapP2.card_alt_nine]; norm_num)
  obtain ⟨h₁, hh₁⟩ := exists_prime_orderOf_dvd_card' 7 h7
  obtain ⟨P₁, hP₁eq⟩ : ∃ P₁ : Sylow 7 Γ, (P₁ : Subgroup Γ) = zpowers h₁ :=
    ⟨Sylow.ofCard (zpowers h₁) (by rw [Nat.card_zpowers, hh₁, hfac, pow_one]), rfl⟩
  set σ : alternatingGroup (Fin 9) := φ h₁ with hσdef
  have hσ : orderOf σ = 7 := by
    have h1 := (P₁.mapSurjective hφ).card_eq_multiplicity
    rw [hfacA, pow_one, Sylow.coe_mapSurjective, hP₁eq, MonoidHom.map_zpowers,
      Nat.card_zpowers] at h1
    exact h1
  obtain ⟨τ, hτ⟩ := isConj_iff.1 (alt9_isConj_inv σ hσ)
  obtain ⟨x, hx⟩ := hφ τ
  have hconj : ∀ j : ℤ, τ * σ ^ j * τ⁻¹ = σ ^ (-j) := fun j => by
    rw [← conj_zpow, hτ, inv_zpow']
  set Γ₁ : Subgroup Γ := (zpowers σ).comap φ with hΓ₁
  have hP₁le : (P₁ : Subgroup Γ) ≤ Γ₁ := by
    intro g hg
    rw [hP₁eq, mem_zpowers_iff] at hg
    obtain ⟨m, rfl⟩ := hg
    rw [hΓ₁, mem_comap, map_zpow]
    exact zpow_mem_zpowers σ m
  have hP₂le : ((x • P₁ : Sylow 7 Γ) : Subgroup Γ) ≤ Γ₁ := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hs1 := hP₁le hs
    rw [hΓ₁, mem_comap, mem_zpowers_iff] at hs1
    obtain ⟨j, hj⟩ := hs1
    rw [hΓ₁, mem_comap, mem_zpowers_iff]
    refine ⟨-j, ?_⟩
    have : (MulAut.conj x • s) = x * s * x⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hx, ← hj]
    exact hconj j |>.symm
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥Γ₁) ((x • P₁ : Sylow 7 Γ).subtype hP₂le)
    (P₁.subtype hP₁le)
  rw [Sylow.smul_subtype] at hk
  have hkP : (k : Γ) • (x • P₁ : Sylow 7 Γ) = P₁ := Sylow.subtype_injective hk
  have hz := Sylow.smul_eq_iff_mem_normalizer.1 (show ((k : Γ) * x) • P₁ = P₁ by
    rw [mul_smul]; exact hkP)
  have hu : (k : Γ) * x * h₁ * ((k : Γ) * x)⁻¹ ∈ (P₁ : Subgroup Γ) :=
    (Subgroup.mem_normalizer_iff.1 hz h₁).1 (by rw [hP₁eq]; exact mem_zpowers h₁)
  rw [hP₁eq, mem_zpowers_iff] at hu
  obtain ⟨m, hm⟩ := hu
  have hkφ : φ k ∈ zpowers σ := k.2
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hkφ
  have hφu : φ ((k : Γ) * x * h₁ * ((k : Γ) * x)⁻¹) = σ⁻¹ := by
    have h1 : φ ((k : Γ) * x * h₁ * ((k : Γ) * x)⁻¹) = σ ^ j * (τ * σ * τ⁻¹) * (σ ^ j)⁻¹ := by
      simp only [map_mul, map_inv, hx, ← hj, ← hσdef]
      group
    rw [h1, hτ]
    exact ((Commute.refl σ).inv_right.zpow_left j).mul_inv_cancel
  have hσm : σ ^ m = σ⁻¹ := by
    rw [← hφu, ← hm, map_zpow]
  have h1 : σ ^ (m + 1) = 1 := by rw [zpow_add_one, hσm, inv_mul_cancel]
  have h2 : (orderOf h₁ : ℤ) ∣ m + 1 := by
    rw [hh₁]
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hσ] at this
  have h3 : h₁ ^ (m + 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 h2
  have h4 : h₁ ^ m = h₁⁻¹ := by
    rw [zpow_add_one] at h3
    exact eq_inv_of_mul_eq_one_left h3
  exact ⟨h₁, (k : Γ) * x, hh₁, by rw [← hm, h4]⟩

private theorem charP_five_of_card_25 {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 25) :
    CharP K 5 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have hK' : Fintype.card K = 25 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [hK'] at hn
  have : p ∣ 5 ^ 2 := by
    have : p ∣ p ^ (n : ℕ) := dvd_pow_self p n.ne_zero
    rw [← hn] at this
    simpa using this
  have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 (hpp.dvd_of_dvd_pow this)
  subst h5
  exact hp

section LinearPart

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem finrank_ker_sub_one (hK : Nat.card K = 25) (hV : Module.finrank K V = 4)
    (A : V ≃ₗ[K] V) (hA7 : A ^ 7 = 1) (hA1 : A ≠ 1) :
    Module.finrank K (LinearMap.ker ((A : V →ₗ[K] V) - LinearMap.id)) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite V := Module.finite_of_finite K
  set N : V →ₗ[K] V := (A : V →ₗ[K] V) - LinearMap.id
  have hNv : ∀ v, N v = A v - v := fun v => rfl
  have hord : orderOf A = 7 := orderOf_eq_prime hA7 hA1
  have hG : IsPGroup 7 (zpowers A) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints V
  have hfix : (MulAction.fixedPoints (zpowers A) V) = (LinearMap.ker N : Set V) := by
    ext v
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, LinearMap.mem_ker]
    constructor
    · intro h
      have := h ⟨A, mem_zpowers A⟩
      change A v = v at this
      rw [hNv, this, sub_self]
    · intro h g
      rw [hNv, sub_eq_zero] at h
      have hinv : A⁻¹ v = v := by
        change A.symm v = v
        rw [LinearEquiv.symm_apply_eq]
        exact h.symm
      have hpow : ∀ m : ℤ, (A ^ m) v = v := by
        intro m
        induction m using Int.induction_on with
        | zero => rfl
        | succ i ih =>
          rw [zpow_add_one]
          change (A ^ (i : ℤ)) (A v) = v
          rw [h]; exact ih
        | pred i ih =>
          rw [zpow_sub_one]
          change (A ^ (-(i : ℤ))) (A⁻¹ v) = v
          rw [hinv]; exact ih
      obtain ⟨g, hg⟩ := g
      rw [mem_zpowers_iff] at hg
      obtain ⟨m, rfl⟩ := hg
      exact hpow m
  have hcardF : Nat.card (MulAction.fixedPoints (zpowers A) V) =
      25 ^ Module.finrank K (LinearMap.ker N) := by
    rw [hfix]
    change Nat.card (LinearMap.ker N) = _
    rw [Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker N), hK]
  have hcardV : Nat.card V = 25 ^ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := V), hK, hV]
  rw [hcardF, hcardV] at hmod
  have hle : Module.finrank K (LinearMap.ker N) ≤ 4 := hV ▸ Submodule.finrank_le _
  generalize hd : Module.finrank K (LinearMap.ker N) = d at hmod hle
  interval_cases d
  · exact absurd hmod (by decide)
  · rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exfalso
    have htop : LinearMap.ker N = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hd, hV])
    apply hA1
    ext v
    have : v ∈ LinearMap.ker N := by rw [htop]; trivial
    rw [LinearMap.mem_ker, hNv, sub_eq_zero] at this
    exact this

theorem no_inverting_of_card_25 (hK : Nat.card K = 25) (hV : Module.finrank K V = 4)
    (A Q : V ≃ₗ[K] V) (hA7 : A ^ 7 = 1) (hA1 : A ≠ 1) (hQ : Q * A * Q⁻¹ = A⁻¹) : False := by
  haveI : CharP K 5 := charP_five_of_card_25 hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 5 2).1 (by exact_mod_cast h)
    omega
  have h7 : (7 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 5 7).1 (by exact_mod_cast h)
    omega
  have hd := finrank_ker_sub_one hK hV A hA7 hA1
  set N : V →ₗ[K] V := (A : V →ₗ[K] V) - LinearMap.id
  have hNv : ∀ v, N v = A v - v := fun v => rfl
  have hQA : ∀ v, Q (A v) = A.symm (Q v) := by
    intro v
    have h1 : Q * A = A⁻¹ * Q := by
      rw [mul_inv_eq_iff_eq_mul] at hQ
      exact hQ
    exact congrArg (fun f : V ≃ₗ[K] V => f v) h1
  have hAQA : ∀ v, A (Q (A v)) = Q v := by
    intro v
    rw [hQA, LinearEquiv.apply_symm_apply]
  set W : Submodule K V := LinearMap.range N with hW
  have hW3 : Module.finrank K W = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N
    rw [hd, hV, ← hW] at this
    omega
  have hAW : ∀ w ∈ W, A w ∈ W := by
    rintro _ ⟨v, rfl⟩
    exact ⟨A v, by rw [hNv, hNv, map_sub]⟩
  have hQW : ∀ w ∈ W, Q w ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨-(A.symm (Q v)), ?_⟩
    rw [hNv, hNv, map_sub, hQA, map_neg, LinearEquiv.apply_symm_apply]
    abel
  have hAf7 : (A : V →ₗ[K] V) ^ 7 = 1 := by
    have := congrArg (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := K) (M := V)) hA7
    rw [Module.End.one_eq_id]
    simpa [map_pow] using this
  have hApow : ∀ (i : ℕ) (v : V), A v = v → ((A : V →ₗ[K] V) ^ i) v = v := by
    intro i v hv
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; exact hv
  have hfixW : ∀ w ∈ W, A w = w → w = 0 := by
    rintro _ ⟨v, rfl⟩ hfix
    have h1 : (∑ i ∈ Finset.range 7, (A : V →ₗ[K] V) ^ i) * ((A : V →ₗ[K] V) - 1) = 0 := by
      rw [geom_sum_mul, hAf7, sub_self]
    have h2 := congrArg (fun f : V →ₗ[K] V => f v) h1
    simp only [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sum_apply] at h2
    have h3 : ∑ i ∈ Finset.range 7, ((A : V →ₗ[K] V) ^ i) (N v) = (7 : ℕ) • N v := by
      rw [Finset.sum_congr rfl (fun i _ => hApow i (N v) hfix), Finset.sum_const,
        Finset.card_range]
    have h4 : (7 : ℕ) • N v = 0 := by
      rw [← h3]; exact h2
    rw [← Nat.cast_smul_eq_nsmul K, smul_eq_zero] at h4
    rcases h4 with h4 | h4
    · exact absurd (by exact_mod_cast h4) h7
    · exact h4
  let b : W →ₗ[K] W := (A : V →ₗ[K] V).restrict hAW
  let q : W →ₗ[K] W := (Q : V →ₗ[K] V).restrict hQW
  have hb : ∀ w : W, ((b w : W) : V) = A (w : V) := fun w => rfl
  have hq : ∀ w : W, ((q w : W) : V) = Q (w : V) := fun w => rfl
  let c : W →ₗ[K] W := LinearMap.id - b
  have hc : ∀ w : W, ((c w : W) : V) = (w : V) - A (w : V) := fun w => rfl
  have hckers : LinearMap.ker c = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have h1 : (w : V) - A (w : V) = 0 := by
      rw [← hc, hw]; rfl
    have h2 : A (w : V) = (w : V) := (sub_eq_zero.1 h1).symm
    exact Subtype.ext (hfixW _ w.2 h2)
  have hqker : LinearMap.ker q = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have h1 : Q (w : V) = 0 := by rw [← hq, hw]; rfl
    exact Subtype.ext (by simpa using h1)
  have hrel : b * q * c = (-1 : K) • (c * q) := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hb, hq, hc, map_sub, hAQA,
      neg_smul, one_smul, Submodule.coe_neg]
    abel
  have hdc : LinearMap.det c ≠ 0 :=
    (IsUnit.map LinearMap.det ((LinearMap.isUnit_iff_ker_eq_bot c).2 hckers)).ne_zero
  have hdq : LinearMap.det q ≠ 0 :=
    (IsUnit.map LinearMap.det ((LinearMap.isUnit_iff_ker_eq_bot q).2 hqker)).ne_zero
  have hdet := congrArg LinearMap.det hrel
  rw [map_mul, map_mul, LinearMap.det_smul, hW3, map_mul] at hdet
  have hdb : LinearMap.det b = -1 := by
    have h1 : LinearMap.det b * (LinearMap.det q * LinearMap.det c) =
        -1 * (LinearMap.det q * LinearMap.det c) := by
      linear_combination hdet
    exact mul_right_cancel₀ (mul_ne_zero hdq hdc) h1
  have hbpow : ∀ (n : ℕ) (w : W), (((b ^ n) w : W) : V) = ((A : V →ₗ[K] V) ^ n) (w : V) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hb, ih]
      rfl
  have hb7 : b ^ 7 = 1 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hbpow, hAf7]; rfl
  have h7' : LinearMap.det b ^ 7 = 1 := by rw [← map_pow, hb7, map_one]
  rw [hdb] at h7'
  apply h2
  linear_combination (-1 : K) * h7'

end LinearPart

section Matrices

open CFSG.Open

theorem exists_inverted_pow {Γ : Type*} [Group Γ] (Z : Subgroup Γ) (hZc : Z ≤ Subgroup.center Γ)
    (hZe : ∀ z ∈ Z, z ^ 24 = 1) (a b : Γ) (ha7 : a ^ 7 ∈ Z)
    (hab : (b * a * b⁻¹)⁻¹ * a⁻¹ ∈ Z) (haZ : a ∉ Z) :
    ∃ a' : Γ, a' ^ 7 = 1 ∧ a' ≠ 1 ∧ b * a' * b⁻¹ = a'⁻¹ := by
  refine ⟨a ^ 120, ?_, ?_, ?_⟩
  · have h1 := hZe _ ha7
    calc (a ^ 120) ^ 7 = ((a ^ 7) ^ 24) ^ 5 := by simp only [← pow_mul]
      _ = 1 := by rw [h1, one_pow]
  · intro h
    apply haZ
    have h2 : a = ((a ^ 7) ^ 17)⁻¹ := by
      have h3 : a ^ 120 = a * (a ^ 7) ^ 17 := by rw [← pow_mul, ← pow_succ']
      rw [h3] at h
      exact eq_inv_of_mul_eq_one_left h
    rw [h2]
    exact Z.inv_mem (Z.pow_mem ha7 17)
  · set c := (b * a * b⁻¹)⁻¹ * a⁻¹ with hc
    have hcZ : c ∈ Z := hab
    have h1 : b * a * b⁻¹ = a⁻¹ * c⁻¹ := by
      rw [hc]; group
    have hcc : Commute a⁻¹ c⁻¹ := Subgroup.mem_center_iff.1 (hZc (Z.inv_mem hcZ)) a⁻¹
    have hc120 : (c⁻¹) ^ 120 = 1 := by
      rw [inv_pow, show (120 : ℕ) = 24 * 5 from rfl, pow_mul, hZe c hcZ, one_pow, inv_one]
    calc b * a ^ 120 * b⁻¹ = (b * a * b⁻¹) ^ 120 := (conj_pow).symm
      _ = (a⁻¹ * c⁻¹) ^ 120 := by rw [h1]
      _ = (a⁻¹) ^ 120 * (c⁻¹) ^ 120 := hcc.mul_pow 120
      _ = (a ^ 120)⁻¹ := by rw [hc120, mul_one, inv_pow]

theorem not_real_of_card_25 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 25)
    (H : Subgroup (GL (Fin 4) K)) (g x : StatedProj H) (hg : orderOf g = 7)
    (hx : x * g * x⁻¹ = g⁻¹) : False := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  have hZc : StatedScalars (Fin 4) K ≤ Subgroup.center (GL (Fin 4) K) := by
    rw [StatedScalars, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have hZe : ∀ z ∈ StatedScalars (Fin 4) K, z ^ 24 = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_pow]
    have : c ^ 24 = 1 := by
      have := pow_card_eq_one' (G := Kˣ) (x := c)
      rwa [Nat.card_units, hK] at this
    rw [this, map_one]
  have ha7 : (a : GL (Fin 4) K) ^ 7 ∈ StatedScalars (Fin 4) K := by
    have h1 : (a ^ 7 : ↥H) ∈ (StatedScalars (Fin 4) K).subgroupOf H := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hg]
      exact pow_orderOf_eq_one _
    exact h1
  have hab : ((b : GL (Fin 4) K) * a * (b : GL (Fin 4) K)⁻¹)⁻¹ * (a : GL (Fin 4) K)⁻¹ ∈
      StatedScalars (Fin 4) K := by
    have h1 : (↑(b * a * b⁻¹) : StatedProj H) = ↑(a⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      exact hx
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have haZ : (a : GL (Fin 4) K) ∉ StatedScalars (Fin 4) K := by
    intro h
    have h1 : (↑a : StatedProj H) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact h
    rw [h1, orderOf_one] at hg
    omega
  obtain ⟨a', ha'7, ha'1, hba'⟩ := exists_inverted_pow (StatedScalars (Fin 4) K) hZc hZe
    (a : GL (Fin 4) K) (b : GL (Fin 4) K) ha7 hab haZ
  let Φ : GL (Fin 4) K ≃* ((Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 4 → K))
  refine no_inverting_of_card_25 hK (Module.finrank_fin_fun K) (Φ a') (Φ b) ?_ ?_ ?_
  · rw [← map_pow, ha'7, map_one]
  · intro h
    apply ha'1
    apply Φ.injective
    rw [h, map_one]
  · have := congrArg Φ hba'
    simpa [map_mul, map_inv] using this

end Matrices

end CFSG.ComponentClassification.SolMax.FiveCat.U45

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

theorem u45NoA9Section_holds : FiveCat.U45NoA9Section := by
  intro S _ _ hS ⟨H, φ, hφ⟩
  have hS' : Open.StatedClassicalModel S .PSU 4 5 1 :=
    Blueprint.LieModel.statedClassicalModel hS (by decide)
  have hord : Nat.card S = 14742000000 := by
    rw [Open.StatedAPI.card_of_statedClassicalModel_psu (by norm_num) hS']
    decide
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := hS'
  have hKcard : Nat.card K = 25 := by rw [hcard]; norm_num
  have h49 : ¬ 49 ∣ Nat.card ↥H := by
    intro h
    have := h.trans (Subgroup.card_subgroup_dvd_card H)
    rw [hord] at this
    norm_num at this
  obtain ⟨g, x, hg, hx⟩ := FiveCat.U45.exists_inverting_of_section φ hφ h49
  refine FiveCat.U45.not_real_of_card_25 hKcard _ (e (g : S)) (e (x : S)) ?_ ?_
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hg]
  · have := congrArg (fun y : ↥H => e (y : S)) hx
    simpa [map_mul, map_inv] using this

end CFSG.ComponentClassification.SolMax.SwapP2
