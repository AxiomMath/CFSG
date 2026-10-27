module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_eq_one_iff [Finite K] (hn : 3 ≤ n) (A : GL (Fin n) K) :
    conjAut n K A = 1 ↔ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = A := by
  constructor
  · intro h
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn A 1 (by rw [map_one, mul_one, h])).2
  · rintro ⟨c, rfl⟩
    exact conjAut_scalar c

theorem conjAut_eq_conjAut_iff [Finite K] (hn : 3 ≤ n) (A B : GL (Fin n) K) :
    conjAut n K A = conjAut n K B ↔ ∃ c : Kˣ, A = B * GeneralLinearGroup.scalar (Fin n) c := by
  have key : conjAut n K A = conjAut n K B ↔ conjAut n K (B⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one, eq_comm]
  rw [key, conjAut_eq_one_iff hn]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, mul_inv_cancel_left]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [inv_mul_cancel_left]⟩

theorem eq_one_of_smul_unipotent [NeZero n] {Y : Matrix (Fin n) (Fin n) K} (c : K)
    (hX : (c • Y - 1) * (c • Y - 1) = 0) (hY : (Y - 1) * (Y - 1) = 0) : c = 1 := by
  obtain ⟨N, rfl⟩ : ∃ N, Y = N + 1 := ⟨Y - 1, by rw [sub_add_cancel]⟩
  rw [add_sub_cancel_right] at hY
  have hcY : c • (N + 1) - 1 = c • N + (c - 1) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [smul_add, sub_smul, one_smul]
    abel
  rw [hcY] at hX
  have hexp : (c • N + (c - 1) • (1 : Matrix (Fin n) (Fin n) K)) * (c • N + (c - 1) • 1) =
      (c * c) • (N * N) + (2 * c * (c - 1)) • N + ((c - 1) * (c - 1)) • 1 := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
    module
  rw [hexp, hY, smul_zero, zero_add] at hX
  have h1 : ((c - 1) * (c - 1)) • N = 0 := by
    have := congrArg (N * ·) hX
    simpa only [mul_add, mul_smul_comm, hY, smul_zero, zero_add, mul_one, mul_zero] using this
  have h2 : ((c - 1) * ((c - 1) * (c - 1))) • (1 : Matrix (Fin n) (Fin n) K) = 0 := by
    have := congrArg ((c - 1) • ·) hX
    simp only [smul_add, smul_smul, smul_zero] at this
    rw [← this]
    have h3 : ((c - 1) * (2 * c * (c - 1))) • N = (2 * c) • (((c - 1) * (c - 1)) • N) := by
      rw [smul_smul]
      congr 1
      ring
    rw [h3, h1, smul_zero, zero_add]
  have h4 := congrFun (congrFun h2 0) 0
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h4
  have h5 : (c - 1) ^ 3 = 0 := by
    rw [← h4]
    ring
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp h5)

theorem eq_of_conjAut_eq_of_unipotent [Finite K] (hn : 3 ≤ n) {X Y : GL (Fin n) K}
    (hX : ((X : Matrix (Fin n) (Fin n) K) - 1) * ((X : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hY : ((Y : Matrix (Fin n) (Fin n) K) - 1) * ((Y : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (h : conjAut n K X = conjAut n K Y) : X = Y := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn X Y).mp h
  have hXm : (X : Matrix (Fin n) (Fin n) K) = (c : K) • (Y : Matrix (Fin n) (Fin n) K) := by
    rw [hc, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  rw [hXm] at hX
  have hc1 : (c : K) = 1 := eq_one_of_smul_unipotent (c : K) hX hY
  have hc1' : c = 1 := Units.ext hc1
  rw [hc, hc1', map_one, mul_one]

theorem transvectionUnit_unipotent {i j : Fin n} (hij : i ≠ j) (t : K) :
    (((TauCeti.transvectionUnit hij t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((TauCeti.transvectionUnit hij t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) =
        0 := by
  rw [TauCeti.coe_transvectionUnit, Matrix.transvection, add_sub_cancel_left]
  simp [hij.symm]

theorem unipotent_conj {A X : GL (Fin n) K}
    (hX : ((X : Matrix (Fin n) (Fin n) K) - 1) * ((X : Matrix (Fin n) (Fin n) K) - 1) = 0) :
    (((A * X * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((A * X * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  have hAA : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : ((A * X * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (A : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Units.mul_inv]
  rw [h1]
  calc (A : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K) * ((X : Matrix (Fin n) (Fin n) K) - 1) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      _ = (A : Matrix (Fin n) (Fin n) K) * (((X : Matrix (Fin n) (Fin n) K) - 1) *
          (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)) *
          ((X : Matrix (Fin n) (Fin n) K) - 1)) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hAA, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem unipotent_map (φ : K →+* K) {X : GL (Fin n) K}
    (hX : ((X : Matrix (Fin n) (Fin n) K) - 1) * ((X : Matrix (Fin n) (Fin n) K) - 1) = 0) :
    (((GeneralLinearGroup.map φ X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((GeneralLinearGroup.map φ X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  have h1 : ((GeneralLinearGroup.map φ X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      φ.mapMatrix ((X : Matrix (Fin n) (Fin n) K) - 1) := by
    rw [map_sub, map_one]
    rfl
  rw [h1, ← map_mul, hX, map_zero]

theorem map_transvectionUnit (φ : K →+* K) {i j : Fin n} (hij : i ≠ j) (t : K) :
    GeneralLinearGroup.map φ (TauCeti.transvectionUnit hij t) =
      TauCeti.transvectionUnit hij (φ t) := by
  refine GeneralLinearGroup.ext fun a b => ?_
  rw [GeneralLinearGroup.map_apply, TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem exists_card_eq_prime_pow [Finite K] : ∃ p m : ℕ, p.Prime ∧ 1 ≤ m ∧ Nat.card K = p ^ m := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, m, hp, hcard⟩ := FiniteField.card' K
  exact ⟨p, m, hp, m.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem ringAut_commute [Finite K] (φ ψ : K ≃+* K) : φ * ψ = ψ * φ := by
  obtain ⟨p, m, hp, hm, hcard⟩ := exists_card_eq_prime_pow (K := K)
  obtain ⟨F, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hm hcard
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp (htop ▸ mem_top φ : φ ∈ zpowers F)
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp (htop ▸ mem_top ψ : ψ ∈ zpowers F)
  exact zpow_mul_comm F a b

theorem mem_zpowers_of_fixed [Finite K] {σ φ : K ≃+* K} (h : ∀ x, σ x = x → φ x = x) :
    φ ∈ zpowers σ := by
  obtain ⟨p, m, hp, hm, hcard⟩ := exists_card_eq_prime_pow (K := K)
  obtain ⟨-, -, -, -, hcardAut, hsub⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp hm hcard
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by omega)
  let G₁ : Subgroup (K ≃+* K) :=
    { carrier := {τ | ∀ x, σ x = x → τ x = x}
      mul_mem' := fun {a b} ha hb x hx => by
        change a (b x) = x
        rw [hb x hx, ha x hx]
      one_mem' := fun x _ => rfl
      inv_mem' := fun {a} ha x hx => (a.symm_apply_eq).mpr (ha x hx).symm }
  have hσ₁ : σ ∈ G₁ := fun x hx => hx
  have hle : zpowers σ ≤ G₁ := (zpowers_le).mpr hσ₁
  obtain ⟨hd₀, S₀, hS₀, hc₀⟩ := hsub (zpowers σ)
  obtain ⟨hd₁, S₁, hS₁, hc₁⟩ := hsub G₁
  have hS : S₀ = S₁ := by
    apply SetLike.ext'
    rw [hS₀, hS₁]
    ext x
    constructor
    · intro hx τ hτ
      exact hτ x (hx σ (mem_zpowers σ))
    · intro hx τ hτ
      exact hle hτ x (hx σ hσ₁)
  rw [hS, hc₁] at hc₀
  have hq := Nat.pow_right_injective hp.two_le hc₀
  have hcard₀ : Nat.card (zpowers σ) = Nat.card G₁ := by
    rw [← Nat.div_div_self hd₀ (by omega), ← Nat.div_div_self hd₁ (by omega), hq]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard₀.ge
  rw [heq]
  exact h

theorem conj_conjAut_fieldAut (A g : GL (Fin n) K) (φ : K ≃+* K) :
    conjAut n K A * fieldAut n K φ * conjAut n K g * (conjAut n K A * fieldAut n K φ)⁻¹ =
      conjAut n K (A * GeneralLinearGroup.map (φ : K →+* K) g * A⁻¹) := by
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rw [map_mul, map_mul, map_inv, ← hfc φ g]
  group

theorem conj_conjAut_fieldAut_dualAut (A g : GL (Fin n) K) (φ : K ≃+* K) :
    conjAut n K A * fieldAut n K φ * dualAut n K * conjAut n K g *
        (conjAut n K A * fieldAut n K φ * dualAut n K)⁻¹ =
      conjAut n K (A * GeneralLinearGroup.map (φ : K →+* K)
        (GeneralLinearGroup.inverseTranspose g) * A⁻¹) := by
  obtain ⟨-, -, hfc, hdd, hdc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  have hdinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hdd
  rw [map_mul, map_mul, map_inv, ← hfc φ, ← hdc g]
  simp only [_root_.mul_inv_rev, hdinv]
  group

theorem fieldAut_commute [Finite K] (φ ψ : K ≃+* K) :
    Commute (fieldAut n K φ) (fieldAut n K ψ) := by
  change fieldAut n K φ * fieldAut n K ψ = fieldAut n K ψ * fieldAut n K φ
  rw [← map_mul, ← map_mul, ringAut_commute]

theorem fieldAut_commute_dualAut (φ : K ≃+* K) :
    Commute (fieldAut n K φ) (dualAut n K) :=
  (dualAut_mul_fieldAut φ).symm

theorem centralizer_eq_of_conjAut_commute_iff [Finite K] (hn : 3 ≤ n)
    {θ : MulAut (projectiveSL n K)} (hθf : ∀ φ : K ≃+* K, Commute θ (fieldAut n K φ))
    (hθd : Commute θ (dualAut n K)) (G : Set (GL (Fin n) K))
    (hG : ∀ A : GL (Fin n) K,
      Commute θ (conjAut n K A) ↔ ∃ B ∈ G, conjAut n K A = conjAut n K B) :
    (centralizer {θ} : Set (MulAut (projectiveSL n K))) =
      {α | ∃ B ∈ G, ∃ (φ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
        α = conjAut n K B * fieldAut n K φ * dualAut n K ^ ε} := by
  ext α
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · intro hα
    obtain ⟨A, φ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 α
    have hF : Commute θ (fieldAut n K φ * dualAut n K ^ ε) :=
      (hθf φ).mul_right (hθd.pow_right ε)
    have hαc : Commute θ (conjAut n K A * fieldAut n K φ * dualAut n K ^ ε) := hα.symm
    have hA : Commute θ (conjAut n K A) := by
      have := hαc.mul_right hF.inv_right
      rwa [mul_assoc (conjAut n K A), mul_inv_cancel_right] at this
    obtain ⟨B, hB, hAB⟩ := (hG A).mp hA
    exact ⟨B, hB, φ, ε, hε, by rw [hAB]⟩
  · rintro ⟨B, hB, φ, ε, -, rfl⟩
    have hF : Commute θ (fieldAut n K φ * dualAut n K ^ ε) :=
      (hθf φ).mul_right (hθd.pow_right ε)
    have hBc : Commute θ (conjAut n K B) := (hG B).mpr ⟨B, hB, rfl⟩
    have := hBc.mul_right hF
    rw [← mul_assoc] at this
    exact this.eq.symm

theorem normal_of_conjAut_closed [Finite K] (hn : 3 ≤ n)
    {θ : MulAut (projectiveSL n K)} (hθf : ∀ φ : K ≃+* K, Commute θ (fieldAut n K φ))
    (hθd : Commute θ (dualAut n K)) (G : Set (GL (Fin n) K))
    (hG : ∀ A : GL (Fin n) K,
      Commute θ (conjAut n K A) ↔ ∃ B ∈ G, conjAut n K A = conjAut n K B)
    (S : Subgroup (GL (Fin n) K)) (hSG : ∀ B ∈ G, ∀ g ∈ S, B * g * B⁻¹ ∈ S)
    (hSφ : ∀ φ : K ≃+* K, ∀ g ∈ S, GeneralLinearGroup.map (φ : K →+* K) g ∈ S)
    (hSδ : ∀ g ∈ S, GeneralLinearGroup.inverseTranspose g ∈ S) :
    ((S.map (conjAut n K)).subgroupOf (centralizer {θ})).Normal := by
  have hC := centralizer_eq_of_conjAut_commute_iff hn hθf hθd G hG
  refine ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨g, hg, hgx⟩ := mem_map.mp hx
  have hy : ((y : MulAut (projectiveSL n K))) ∈
      (centralizer {θ} : Set (MulAut (projectiveSL n K))) := y.2
  rw [hC] at hy
  obtain ⟨B, hB, φ, ε, hε, hyB⟩ := hy
  simp only [coe_mul, coe_inv, hyB, ← hgx]
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one, conj_conjAut_fieldAut]
    exact mem_map_of_mem _ (hSG B hB _ (hSφ φ g hg))
  · rw [pow_one, conj_conjAut_fieldAut_dualAut]
    exact mem_map_of_mem _ (hSG B hB _ (hSφ φ _ (hSδ g hg)))

end CFSG.ComponentClassification.UnbalancedCatalog
