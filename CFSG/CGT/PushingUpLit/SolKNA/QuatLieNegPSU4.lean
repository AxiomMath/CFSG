module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegCrit
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSU4Twin
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUGroup
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerSUNormal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ClassicalInvolution.Q3 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

theorem twinAt_of_lift {U Y : Type*} [Group U] [Group Y] (π : U →* Y)
    (hπ : Function.Surjective π) {u : U} (hu : π u * π u = 1)
    (h : ∀ A : U, π A * π u = π u * π A → π A * π A = π u →
      ∃ G : U, π G * π u = π u * π G ∧
        π (G * A * G⁻¹) * π A = π A * π (G * A * G⁻¹) ∧
        π (G * A * G⁻¹) ≠ π A ∧ π (G * A * G⁻¹) ≠ π A * π u) :
    TwinAt (π u) := by
  refine twinAt_of_commuting hu fun a ha ha2 => ?_
  obtain ⟨A, rfl⟩ := hπ a
  rw [Subgroup.mem_centralizer_singleton_iff] at ha
  obtain ⟨G, hG, hc, hne1, hne2⟩ := h A ha (by rwa [← pow_two])
  refine ⟨π G, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hG
  · simpa only [map_mul, map_inv] using hc
  · simpa only [map_mul, map_inv] using hne1
  · simpa only [map_mul, map_inv] using hne2

section Quot

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K))

theorem mk_eq_mk_iff (x y : H) :
    (QuotientGroup.mk x : StatedProj H) = QuotientGroup.mk y ↔
      ∃ c : K, c ≠ 0 ∧ ((y : GL ι K) : Matrix ι ι K) = c • ((x : GL ι K) : Matrix ι ι K) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c.1, c.ne_zero, ?_⟩
    have h1 : (y : GL ι K) = (x : GL ι K) * ((x : GL ι K)⁻¹ * (y : GL ι K)) := by group
    have h2 : (((x⁻¹ * y : H) : GL ι K)) = (x : GL ι K)⁻¹ * (y : GL ι K) := rfl
    rw [← h2, ← hc] at h1
    have h3 := congrArg (fun z : GL ι K => (z : Matrix ι ι K)) h1
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at h3
    simpa using h3
  · rintro ⟨c, hc0, hc⟩
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    have h2 : (((x⁻¹ * y : H) : GL ι K)) = (x : GL ι K)⁻¹ * (y : GL ι K) := rfl
    rw [h2, Units.val_mul]
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Units.val_mk0]
    rw [hc, Matrix.mul_smul, Units.inv_mul]

theorem mk_eq_one_of_smul_one (g : H) (d : K) (hd : d ≠ 0)
    (hg : ((g : GL ι K) : Matrix ι ι K) = d • (1 : Matrix ι ι K)) :
    (QuotientGroup.mk g : StatedProj H) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 d hd, Units.ext ?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Units.val_mk0]
  exact hg.symm

end Quot

section Unitary

variable {K : Type} [Field K]

theorem cT_eq_cube [Finite K] [Fact (Nat.Prime 3)] [CharP K 3] {m n : Type} (A : Matrix m n K) :
    cT (unitaryInvolution K 3 1) A = (A.map (· ^ 3))ᵀ := by
  have h : (⇑(unitaryInvolution K 3 1) : K → K) = fun z => z ^ 3 :=
    funext fun z => by rw [unitaryInvolution_apply, pow_one]
  unfold cT
  rw [h]

@[expose] noncomputable def mkSUG {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K)
    (G : Matrix ι ι K) (h1 : cT σ G * G = 1) (hd : G.det = 1) : SUG σ (1 : Matrix ι ι K) :=
  ⟨Matrix.GeneralLinearGroup.mk'' G (by rw [hd]; exact isUnit_one), hd, by
    show cT σ G * 1 * G = 1
    rw [Matrix.mul_one]
    exact h1⟩

theorem coe_inv_SUG {ι : Type} [Fintype ι] [DecidableEq ι] (σ : K ≃+* K)
    (x : SUG σ (1 : Matrix ι ι K)) :
    (((x⁻¹ : SUG σ (1 : Matrix ι ι K)) : GL ι K) : Matrix ι ι K) =
      cT σ ((x : GL ι K) : Matrix ι ι K) := by
  have h1 : cT σ ((x : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) = 1 := by
    have := x.2.2
    rwa [Matrix.mul_one] at this
  have h2 : (((x⁻¹ : SUG σ (1 : Matrix ι ι K)) : GL ι K) : Matrix ι ι K) =
      (((x : GL ι K) : Matrix ι ι K))⁻¹ := Matrix.GeneralLinearGroup.coe_inv _
  rw [h2]
  exact Matrix.inv_eq_left_inv h1

theorem det_dgn {a b : ℕ} (μ : K) :
    (Matrix.fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) K)) 0 0
      ((-μ) • (1 : Matrix (Fin b) (Fin b) K))).det = μ ^ a * (-μ) ^ b := by
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, Matrix.det_one,
    Matrix.det_one]
  simp [Fintype.card_fin]

theorem det_eq_of_normal_form {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] {g : Matrix ι ι K} {Q : Matrix ι ι' K} {Q' : Matrix ι' ι K}
    {D : Matrix ι' ι' K} (h1 : Q * Q' = 1) (h2 : Q' * Q = 1) (hgQ : g * Q = Q * D) :
    g.det = D.det := by
  have : g = Q * D * Q' := by
    calc g = g * (Q * Q') := by rw [h1, Matrix.mul_one]
      _ = (g * Q) * Q' := by rw [Matrix.mul_assoc]
      _ = Q * D * Q' := by rw [hgQ]
  rw [this]
  exact det_conjMat h1 h2 D

end Unitary

section Helpers

variable {K : Type} [Field K]

theorem ne_zero_of_eq_smul {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X Y : Matrix ι ι K} {c : K} (h : X = c • Y) (hX : X.det ≠ 0) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at h
  rw [h, Matrix.det_zero] at hX
  exact hX rfl

theorem eq_of_smul_eq_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι K} {μ c : K} (hμ : μ ≠ 0) (h : μ • X = (c * μ) • Y) : X = c • Y := by
  have h1 := congrArg (fun Z : Matrix ι ι K => μ⁻¹ • Z) h
  simp only [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h1
  rw [h1]
  congr 1
  field_simp

theorem dgnL_zero_left {b : ℕ} (μ : K) :
    Matrix.fromBlocks (μ • (1 : Matrix (Fin 0) (Fin 0) K)) 0 0
      ((-μ) • (1 : Matrix (Fin b) (Fin b) K))
      = (-μ) • (1 : Matrix (Fin 0 ⊕ Fin b) (Fin 0 ⊕ Fin b) K) := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i
  · exact i.elim0
  · rcases c with j | j
    · exact j.elim0
    · by_cases hij : i = j <;> simp [Matrix.fromBlocks, hij]

theorem dgnL_zero_right {a : ℕ} (μ : K) :
    Matrix.fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) K)) 0 0
      ((-μ) • (1 : Matrix (Fin 0) (Fin 0) K))
      = μ • (1 : Matrix (Fin a ⊕ Fin 0) (Fin a ⊕ Fin 0) K) := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i
  · rcases c with j | j
    · by_cases hij : i = j <;> simp [Matrix.fromBlocks, hij]
    · exact j.elim0
  · exact i.elim0

theorem eq_smul_one_of_mul_eq' {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] {g : Matrix ι ι K} {Q : Matrix ι ι' K} {Q' : Matrix ι' ι K}
    {D : Matrix ι' ι' K} {d : K} (h1 : Q * Q' = 1) (hgQ : g * Q = Q * D)
    (hD : D = d • 1) : g = d • 1 := by
  calc g = g * (Q * Q') := by rw [h1, Matrix.mul_one]
    _ = (g * Q) * Q' := by rw [Matrix.mul_assoc]
    _ = d • 1 := by
        rw [hgQ, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

end Helpers

section Main

variable {K : Type} [Field K] [Finite K]

theorem twinAt_su4_of_involution (hcard : Nat.card K = (3 ^ 1) ^ 2)
    (s : StatedProj (StatedSU 4 (3 ^ 1) K)) (hs : orderOf s = 2) : TwinAt s := by
  have hE : Nat.card K = 9 := by rw [hcard]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hcard
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_three
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hSU : SUid (unitaryInvolution K 3 1) 4 = StatedSU 4 (3 ^ 1) K := SUid_eq_statedSU hcard 4
  have hmemSU : ∀ x : StatedSU 4 (3 ^ 1) K,
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      cT (unitaryInvolution K 3 1) ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := fun x => by
    have : (x : GL (Fin 4) K) ∈ SUid (unitaryInvolution K 3 1) 4 := by rw [hSU]; exact x.2
    exact this
  set gM : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hgM
  have hs1 : (QuotientGroup.mk g : StatedProj (StatedSU 4 (3 ^ 1) K)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hs2 : (QuotientGroup.mk g : StatedProj (StatedSU 4 (3 ^ 1) K)) * QuotientGroup.mk g = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk g : StatedProj (StatedSU 4 (3 ^ 1) K))
    rwa [hs, pow_two] at this
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) u =
      ((g * g : StatedSU 4 (3 ^ 1) K) : GL (Fin 4) K) := by
    have h : (g * g : StatedSU 4 (3 ^ 1) K) ∈
        (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (3 ^ 1) K) :=
      (QuotientGroup.eq_one_iff (g * g)).mp (by rw [QuotientGroup.mk_mul]; exact hs2)
    exact h
  have hgg : gM * gM = (u : K) • (1 : Matrix (Fin 4) (Fin 4) K) := by
    have := congrArg (fun z : GL (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) hu
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Subgroup.coe_mul, Units.val_mul] at this
    exact this.symm
  have hc4 : (u : K) ^ 4 = 1 := by
    obtain ⟨-, hunit⟩ := hmemSU (g * g)
    have h1 : ((g * g : StatedSU 4 (3 ^ 1) K) : GL (Fin 4) K) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) u := hu.symm
    rw [h1] at hunit
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at hunit
    rw [cT_smul, cT_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hunit
    have h3 := congrFun (congrFun hunit 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
    exact pow_four_eq_one_of_norm_eq_one h3
  obtain ⟨μ, hμ⟩ := exists_sq_eq_of_pow_four_eq_one hE hc4
  have hμ4 : μ ^ 4 = 1 ∨ μ ^ 4 = -1 := by
    refine mul_self_eq_one_iff.mp ?_
    calc μ ^ 4 * μ ^ 4 = (μ * μ) ^ 4 := by ring
      _ = 1 := by rw [hμ, hc4]
  have hggμ : gM * gM = (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) K) := by rw [hgg, hμ]
  obtain ⟨hdet, hgU⟩ := hmemSU g
  have hgU' : cT (unitaryInvolution K 3 1) gM * (1 : Matrix (Fin 4) (Fin 4) K) * gM = 1 := by
    rw [Matrix.mul_one]
    exact hgU
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rcases hμ4 with h | h <;> simp at h
  have hdet1 : IsUnit (1 : Matrix (Fin 4) (Fin 4) K).det := by
    rw [Matrix.det_one]
    exact isUnit_one
  rcases hμ4 with h4 | h4
  swap
  · exfalso
    obtain ⟨m, Q, Q', h1, h2', hQJ, hgQ⟩ := exists_normal_form_hyp hE h4
      (cT_one (unitaryInvolution K 3 1)) hdet1 hgU' hggμ
    have hcard' := fintype_card_eq_of_mul_eq_one h1 h2'
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard'
    have hm : m = 2 := by omega
    subst hm
    have hdetg := det_eq_of_normal_form h1 h2' hgQ
    rw [det_dgn, hdet] at hdetg
    have : μ ^ 2 * (-μ) ^ 2 = μ ^ 4 := by ring
    rw [this, h4] at hdetg
    exact hneg hdetg.symm
  · obtain ⟨a, b, Q, Q', h1, h2', hQ1, hgQ⟩ := exists_normal_form_one hE h4
      (cT_one (unitaryInvolution K 3 1)) hdet1 hgU' hggμ
    have hcard' := fintype_card_eq_of_mul_eq_one h1 h2'
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard'
    have hdetg := det_eq_of_normal_form h1 h2' hgQ
    rw [det_dgn, hdet] at hdetg
    have hab : a = 2 ∧ b = 2 := by
      have ha1 : 1 ≤ a := by
        by_contra h0
        obtain rfl : a = 0 := by omega
        apply hs1
        have hgd : gM = (-μ) • (1 : Matrix (Fin 4) (Fin 4) K) :=
          eq_smul_one_of_mul_eq' h1 hgQ (dgnL_zero_left μ)
        exact mk_eq_one_of_smul_one _ g (-μ) (neg_ne_zero.mpr hμ0) hgd
      have hb1 : 1 ≤ b := by
        by_contra h0
        obtain rfl : b = 0 := by omega
        apply hs1
        have hgd : gM = μ • (1 : Matrix (Fin 4) (Fin 4) K) :=
          eq_smul_one_of_mul_eq' h1 hgQ (dgnL_zero_right μ)
        exact mk_eq_one_of_smul_one _ g μ hμ0 hgd
      have hpow : (-1 : K) ^ b = 1 := by
        have h5 : μ ^ a * (-μ) ^ b = (-1) ^ b * μ ^ (a + b) := by
          rw [neg_pow, pow_add]
          ring
        rw [h5, hcard', h4, mul_one] at hdetg
        exact hdetg.symm
      obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even hneg).mp hpow
      omega
    obtain ⟨rfl, rfl⟩ := hab
    set σ := unitaryInvolution K 3 1 with hσ
    let e' : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≃* StatedSU 4 (3 ^ 1) K :=
      (conjSUG σ h1 h2' hQ1).trans (MulEquiv.subgroupCongr ((SUG_one σ 4).trans hSU))
    have hcoe : ∀ x : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
        (((e' x : StatedSU 4 (3 ^ 1) K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Q * ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Q' :=
      fun x => rfl
    have hconj : ∀ Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, Q' * (Q * Y * Q') * Q = Y :=
      fun Y => by
        rw [show Q' * (Q * Y * Q') * Q = (Q' * Q) * Y * (Q' * Q) by
          simp only [Matrix.mul_assoc], h2', Matrix.one_mul, Matrix.mul_one]
    set u₀ := e'.symm g with hu₀def
    have hu₀ : (((u₀ : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        Matrix.fromBlocks (μ • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0
          ((-μ) • (1 : Matrix (Fin 2) (Fin 2) K)) := by
      have h := hcoe u₀
      rw [hu₀def, MulEquiv.apply_symm_apply] at h
      calc _ = Q' * (Q * ((u₀ : GL (Fin 2 ⊕ Fin 2) K) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Q') * Q := (hconj _).symm
        _ = Q' * gM * Q := by rw [← h]
        _ = Q' * (gM * Q) := by rw [Matrix.mul_assoc]
        _ = _ := by rw [hgQ, ← Matrix.mul_assoc, h2', Matrix.one_mul]
    let π : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →*
        StatedProj (StatedSU 4 (3 ^ 1) K) := (QuotientGroup.mk' _).comp e'.toMonoidHom
    have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e'.surjective
    have hπu : π u₀ = QuotientGroup.mk g := by
      show QuotientGroup.mk (e' u₀) = _
      rw [hu₀def, MulEquiv.apply_symm_apply]
    have hπeq : ∀ x y : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), π x = π y ↔
        ∃ c : K, c ≠ 0 ∧ ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          c • ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      intro x y
      show (QuotientGroup.mk (e' x) : StatedProj (StatedSU 4 (3 ^ 1) K)) =
        QuotientGroup.mk (e' y) ↔ _
      rw [mk_eq_mk_iff]
      simp only [hcoe]
      constructor
      · rintro ⟨c, hc0, hc⟩
        refine ⟨c, hc0, ?_⟩
        have := congrArg (fun Z => Q' * Z * Q) hc
        simp only [Matrix.mul_smul, Matrix.smul_mul] at this
        rwa [hconj, hconj] at this
      · rintro ⟨c, hc0, hc⟩
        refine ⟨c, hc0, ?_⟩
        rw [hc, Matrix.mul_smul, Matrix.smul_mul]
    have hu : π u₀ * π u₀ = 1 := by
      rw [hπu]
      exact hs2
    have hδu : ((u₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        μ • psu4Delta K := by
      rw [hu₀]
      unfold psu4Delta
      rw [Matrix.fromBlocks_smul]
      simp [smul_neg]
    have hδdet : (psu4Delta K).det = 1 := by
      unfold psu4Delta
      rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one]
      simp
    have key := twinAt_of_lift π hπ hu ?_
    · rw [hπu] at key
      exact key
    intro A hA1 hA2
    set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
    have hAdet : Am.det = 1 := A.2.1
    have hAu : (Am.map (· ^ 3))ᵀ * Am = 1 := by
      have := A.2.2
      rw [Matrix.mul_one, cT_eq_cube] at this
      exact this
    obtain ⟨c1, hc10, hc1⟩ := (hπeq (A * u₀) (u₀ * A)).mp (by rw [map_mul, map_mul]; exact hA1)
    obtain ⟨c2, hc20, hc2⟩ := (hπeq (A * A) u₀).mp (by rw [map_mul]; exact hA2)
    simp only [Subgroup.coe_mul, Units.val_mul, hδu, ← hAm] at hc1 hc2
    have hr : Am * psu4Delta K = c1⁻¹ • (psu4Delta K * Am) := by
      have h : μ • (psu4Delta K * Am) = (c1 * μ) • (Am * psu4Delta K) := by
        rw [Matrix.smul_mul, Matrix.mul_smul] at hc1
        rw [hc1, smul_smul, mul_comm]
      have h' := eq_of_smul_eq_smul hμ0 h
      rw [h', smul_smul, inv_mul_cancel₀ hc10, one_smul]
    have hs' : Am * Am = (c2⁻¹ * μ) • psu4Delta K := by
      rw [← smul_smul, hc2, smul_smul, inv_mul_cancel₀ hc20, one_smul]
    obtain ⟨Gm, hGu, hGd, ⟨r', hr'⟩, ⟨ε, hε⟩, hne1, hne2⟩ :=
      psu4_block_twin hE Am hAu hAdet _ _ hr hs'
    set G₀ := mkSUG σ Gm (by rw [cT_eq_cube]; exact hGu) hGd with hG₀
    have hG₀val : (((G₀ : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = Gm := rfl
    have hA'val : (((G₀ * A * G₀⁻¹ : SUG σ (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        Gm * Am * (Gm.map (· ^ 3))ᵀ := by
      simp only [Subgroup.coe_mul, Units.val_mul, coe_inv_SUG, hG₀val]
      rw [← hAm]
      exact congrArg (Gm * Am * ·) (cT_eq_cube Gm)
    have hA'det : (Gm * Am * (Gm.map (· ^ 3))ᵀ).det = 1 := by
      rw [← hA'val]
      exact (G₀ * A * G₀⁻¹).2.1
    have hcTG : cT σ Gm = (Gm.map (· ^ 3))ᵀ := cT_eq_cube Gm
    refine ⟨G₀, ?_, ?_, ?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      have hr'0 : r' ≠ 0 := ne_zero_of_eq_smul hr' (by
        rw [Matrix.det_mul, hGd, hδdet, one_mul]
        exact one_ne_zero)
      refine (hπeq (G₀ * u₀) (u₀ * G₀)).mpr ⟨r'⁻¹, inv_ne_zero hr'0, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, hδu, hG₀val]
      rw [Matrix.smul_mul, Matrix.mul_smul, hr', smul_smul, smul_smul]
      congr 1
      field_simp
    · rw [← map_mul, ← map_mul]
      have hε0 : ε ≠ 0 := ne_zero_of_eq_smul hε (by
        rw [Matrix.det_mul, hA'det, hAdet, one_mul]
        exact one_ne_zero)
      refine (hπeq (G₀ * A * G₀⁻¹ * A) (A * (G₀ * A * G₀⁻¹))).mpr ⟨ε⁻¹, inv_ne_zero hε0, ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, coe_inv_SUG, hG₀val, hcTG, ← hAm]
      rw [hε, smul_smul, inv_mul_cancel₀ hε0, one_smul]
    · intro h
      obtain ⟨c, hc0, hc⟩ := (hπeq (G₀ * A * G₀⁻¹) A).mp h
      exact hne1 c⁻¹ (by rw [hA'val] at hc; exact (eq_inv_smul_iff₀ hc0).mpr hc.symm)
    · intro h
      rw [← map_mul] at h
      obtain ⟨c, hc0, hc⟩ := (hπeq (G₀ * A * G₀⁻¹) (A * u₀)).mp h
      rw [hA'val] at hc
      simp only [Subgroup.coe_mul, Units.val_mul, hδu, ← hAm] at hc
      refine hne2 (c⁻¹ * μ) ?_
      rw [(eq_inv_smul_iff₀ hc0).mpr hc.symm, Matrix.mul_smul, smul_smul]

end Main

theorem negModel_PSU4 : NegModel .PSU 4 := by
  intro X _ _ hX K hK R
  obtain ⟨-, K₀, _, _, hcard, ⟨e⟩⟩ := statedClassical_of_lieModel_ne_zero (by norm_num) hX
  exact not_quaternion_of_equiv e
    (fun s hs => Or.inl (twinAt_su4_of_involution hcard s hs)) hK R

end CFSG.CGT.PushingUpLit.SolKNA
