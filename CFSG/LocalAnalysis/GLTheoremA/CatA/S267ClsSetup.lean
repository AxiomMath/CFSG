module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

variable {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {τ : K →+* K}

abbrev innerPart (S B : Subgroup Ω) : Subgroup Ω :=
  B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω))

@[expose] def FieldElt (p : ℕ) (S B : Subgroup Ω) {H : Subgroup (GL ι K)} (φ : ↥H →* Ω)
    (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K) (θ : ↥(innerPart S B) →* ↥H) (b : Ω) (A : GL ι K)
    (σ : K ≃+* K) : Prop :=
  b ∈ B ∧ b ∉ S ⊔ Subgroup.centralizer (S : Set Ω) ∧ B = innerPart S B ⊔ Subgroup.zpowers b ∧
    Subgroup.zpowers b ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) = ⊥ ∧
    ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ ∧
    ∀ x, ModelGen.semiConj A σ ((θ x : ↥H) : GL ι K) = θ x

structure ClsInner (p : ℕ) (S B : Subgroup Ω) (H : Subgroup (GL ι K))
    (β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K) where
  φ : ↥H →* Ω
  range_eq : φ.range = S
  ker_eq : φ.ker = (StatedScalars ι K).subgroupOf H
  not_dvd : ¬ p ∣ Nat.card φ.ker
  θ : ↥(innerPart S B) →* ↥H
  θ_spec : ∀ x, (φ (θ x))⁻¹ * (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)
  elem : IsElemAbelian p θ.range
  range_inf_ker : θ.range ⊓ φ.ker = ⊥
  θ_eq_one : ∀ x, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)
  b : Ω
  A : GL ι K
  σ : K ≃+* K
  split : innerPart S B = B ∨ FieldElt p S B φ β θ b A σ

namespace ClsInner

variable {H : Subgroup (GL ι K)} {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem map_conj [Finite ↥H] (D : ClsInner p S B H β) (x : ↥(innerPart S B)) (h : ↥H) :
    D.φ (D.θ x * h * (D.θ x)⁻¹) = (x : Ω) * D.φ h * (x : Ω)⁻¹ :=
  ModelGen.inner_lift_conj D.φ D.range_eq D.θ D.θ_spec x h

end ClsInner

section FieldAut

variable {H : Subgroup (GL ι K)} [Finite ↥H]

theorem map_semiConj_eq {A : GL ι K} {σ : K ≃+* K}
    (h : ∀ k ∈ H, ModelGen.semiConj A σ k ∈ H) :
    H.map (ModelGen.semiConj A σ : GL ι K →* GL ι K) = H := by
  have hle : H.map (ModelGen.semiConj A σ : GL ι K →* GL ι K) ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  refine (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [Subgroup.card_map_of_injective (ModelGen.semiConj A σ).injective]

@[expose] noncomputable def semiAut (A : GL ι K) (σ : K ≃+* K)
    (h : ∀ k ∈ H, ModelGen.semiConj A σ k ∈ H) : MulAut ↥H :=
  ((ModelGen.semiConj A σ).subgroupMap H).trans (MulEquiv.subgroupCongr (map_semiConj_eq h))

theorem coe_semiAut_apply (A : GL ι K) (σ : K ≃+* K) (h : ∀ k ∈ H, ModelGen.semiConj A σ k ∈ H)
    (k : ↥H) : ((semiAut A σ h k : ↥H) : GL ι K) = ModelGen.semiConj A σ k :=
  rfl

theorem semiConj_mem_of_fieldAct {φ : ↥H →* Ω} {b : Ω} {A : GL ι K} {σ : K ≃+* K}
    (hact : ModelGen.FieldAct p φ b A σ) : ∀ k ∈ H, ModelGen.semiConj A σ k ∈ H := by
  intro k hk
  obtain ⟨k', hk', -⟩ := hact.2.2 ⟨k, hk⟩
  rw [← hk']
  exact k'.2

theorem map_semiAut {φ : ↥H →* Ω} {b : Ω} {A : GL ι K} {σ : K ≃+* K}
    (hact : ModelGen.FieldAct p φ b A σ) (k : ↥H) :
    φ (semiAut A σ (semiConj_mem_of_fieldAct hact) k) = b * φ k * b⁻¹ := by
  obtain ⟨k', hk', hφk'⟩ := hact.2.2 k
  have : semiAut A σ (semiConj_mem_of_fieldAct hact) k = k' := Subtype.ext hk'.symm
  rw [this, hφk']

theorem map_semiAut_pow {φ : ↥H →* Ω} {b : Ω} {A : GL ι K} {σ : K ≃+* K}
    (hact : ModelGen.FieldAct p φ b A σ) (n : ℕ) (k : ↥H) :
    φ ((semiAut A σ (semiConj_mem_of_fieldAct hact) ^ n) k) = b ^ n * φ k * (b ^ n)⁻¹ := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, map_semiAut hact, ih, pow_succ']
    group

theorem coe_semiAut_pow_apply (A : GL ι K) (σ : K ≃+* K)
    (h : ∀ k ∈ H, ModelGen.semiConj A σ k ∈ H) (n : ℕ) (k : ↥H) :
    (((semiAut A σ h ^ n) k : ↥H) : GL ι K) = (ModelGen.semiConj A σ ^ n) k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, coe_semiAut_apply, ih, pow_succ', MulAut.mul_apply]

end FieldAut

section Lift

variable [Finite Ω] {H : Subgroup (GL ι K)} [Finite ↥H]
  {β : (ι → K) →ₗ[K] (ι → K) →ₛₗ[τ] K}

theorem exists_mul_pow_of_mem_sup (hp : p.Prime) (hB : IsElemAbelian p B) {D : Subgroup Ω}
    (hDB : D ≤ B) {b : Ω} (hbB : b ∈ B) {x : Ω} (hx : x ∈ D ⊔ Subgroup.zpowers b) :
    ∃ y ∈ D, ∃ k : ℕ, k < p ∧ x = y * b ^ k := by
  have hcomm : ∀ y ∈ D, ∀ z ∈ Subgroup.zpowers b, y * z = z * y := by
    intro y hy z hz
    exact hB.comm (hDB hy) (Subgroup.zpowers_le.mpr hbB hz)
  have hN : D ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Ω) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hcomm y hy z hz, mul_inv_cancel_right]
      exact hz
    · intro hz
      have h := hcomm y hy _ hz
      have e : z = y * z * y⁻¹ :=
        calc z = y⁻¹ * ((y * z * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * z * y⁻¹)) := by rw [h]
          _ = y * z * y⁻¹ := by group
      rw [e]
      exact hz
  have hx' : x ∈ ((D ⊔ Subgroup.zpowers b : Subgroup Ω) : Set Ω) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hbp : b ^ p = 1 := hB.2 b hbB
  refine ⟨y, hy, (m % p).toNat, ?_, ?_⟩
  · have h1 : m % p < p := Int.emod_lt_of_pos m (by exact_mod_cast hp.pos)
    have h0 : (0 : ℤ) ≤ m % p := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero)
    omega
  · have h0 : (0 : ℤ) ≤ m % p := Int.emod_nonneg m (by exact_mod_cast hp.ne_zero)
    congr 1
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    conv_lhs => rw [← Int.mul_ediv_add_emod m p]
    rw [zpow_add, zpow_mul, zpow_natCast, hbp, one_zpow, one_mul]

theorem exists_inner_mul_pow (hp : p.Prime) (hB : IsElemAbelian p B) {b : Ω} (hbB : b ∈ B)
    (hBb : B = innerPart S B ⊔ Subgroup.zpowers b) (x : Ω) (hx : x ∈ B) :
    ∃ y ∈ innerPart S B, ∃ k : ℕ, k < p ∧ x = y * b ^ k :=
  exists_mul_pow_of_mem_sup hp hB inf_le_left hbB (hBb ▸ hx)

theorem eq_of_mul_pow_eq (hp : p.Prime) (hB : IsElemAbelian p B) {N D : Subgroup Ω}
    (hDN : D ≤ N) {b : Ω} (hbB : b ∈ B) (hbN : b ∉ N)
    (hbout : Subgroup.zpowers b ⊓ N = ⊥) {d d' : Ω} (hd : d ∈ D) (hd' : d' ∈ D) {k k' : ℕ}
    (hk : k < p) (hk' : k' < p) (h : d * b ^ k = d' * b ^ k') : d = d' ∧ k = k' := by
  have hw : d'⁻¹ * d = b ^ k' * (b ^ k)⁻¹ := by
    calc d'⁻¹ * d = d'⁻¹ * (d * b ^ k) * (b ^ k)⁻¹ := by group
      _ = d'⁻¹ * (d' * b ^ k') * (b ^ k)⁻¹ := by rw [h]
      _ = b ^ k' * (b ^ k)⁻¹ := by group
  have hmem : d'⁻¹ * d ∈ Subgroup.zpowers b ⊓ N := by
    refine ⟨?_, hDN (D.mul_mem (D.inv_mem hd') hd)⟩
    rw [hw]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k')
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k))
  rw [hbout, Subgroup.mem_bot] at hmem
  have hdd : d = d' := (inv_inj.mp (mul_eq_one_iff_eq_inv.mp hmem)).symm
  refine ⟨hdd, ?_⟩
  have hbk : b ^ k = b ^ k' := by
    rw [hmem, eq_comm, mul_inv_eq_one] at hw
    exact hw.symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h1 => hbN (h1 ▸ N.one_mem)
  have hord : orderOf b = p := orderOf_eq_prime (hB.2 b hbB) hb1
  have := (pow_eq_pow_iff_modEq.mp hbk)
  rw [hord] at this
  exact Nat.ModEq.eq_of_lt_of_lt this hk hk'

end Lift

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
