module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFD4OI

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open scoped Pointwise commutatorElement

section Sperm

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {ι : Type}

@[expose] noncomputable def sperm (b : Module.Basis ι F V) (π : Equiv.Perm ι) (ε : ι → Fˣ) :
    V ≃ₗ[F] V :=
  b.equiv (b.unitsSMul ε) π

theorem sperm_apply (b : Module.Basis ι F V) (π : Equiv.Perm ι) (ε : ι → Fˣ) (i : ι) :
    sperm b π ε (b i) = (ε (π i) : F) • b (π i) := by
  rw [sperm, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply, Units.smul_def]

theorem sperm_mem_orthogonalGroup [Fintype ι] [DecidableEq ι] {Q : QuadraticForm F V}
    (h2 : (2 : F) ≠ 0)
    (b : Module.Basis ι F V) (horth : ∀ i j, polar Q (b i) (b j) = if i = j then 1 else 0)
    (π : Equiv.Perm ι) (ε : ι → Fˣ) (hε : ∀ i, (ε i : F) * ε i = 1) :
    sperm b π ε ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  have key : (polarBilin Q).compl₁₂ (sperm b π ε : V →ₗ[F] V) (sperm b π ε : V →ₗ[F] V) =
      polarBilin Q := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, sperm_apply, map_smul,
      LinearMap.smul_apply, polarBilin_apply_apply, horth, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      rw [mul_one, mul_comm]
      exact hε _
    · have hπ : π i ≠ π j := π.injective.ne hij
      simp [hij, hπ]
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have h := LinearMap.congr_fun₂ key v v
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, polarBilin_apply_apply,
    polar_self, two_smul] at h
  have h' : (2 : F) * Q (sperm b π ε v) = 2 * Q v := by
    rw [two_mul, two_mul]
    exact h
  exact mul_left_cancel₀ h2 h'

end Sperm

section Rot

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  (b : Module.Basis (Fin 4 ⊕ Fin 4) F V)

@[expose] noncomputable def sgnAt (j : Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 → Fˣ :=
  fun i => if i = j then -1 else 1

theorem sgnAt_mul_self (j i : Fin 4 ⊕ Fin 4) :
    ((sgnAt (F := F) j i : Fˣ) : F) * ((sgnAt (F := F) j i : Fˣ) : F) = 1 := by
  unfold sgnAt
  split_ifs <;> simp

theorem one_mul_self (i : Fin 4 ⊕ Fin 4) :
    ((1 : Fin 4 ⊕ Fin 4 → Fˣ) i : F) * ((1 : Fin 4 ⊕ Fin 4 → Fˣ) i : F) = 1 := by
  simp

@[expose] noncomputable def rot (k : Fin 4) : V ≃ₗ[F] V :=
  sperm b (Equiv.swap (.inl k) (.inr k)) (sgnAt (.inl k))

@[expose] noncomputable def pswap (k l : Fin 4) : V ≃ₗ[F] V :=
  sperm b (Equiv.swap (.inl k) (.inl l) * Equiv.swap (.inr k) (.inr l)) 1

@[expose] noncomputable def refl (l : Fin 4) : V ≃ₗ[F] V :=
  sperm b 1 (sgnAt (.inl l))

theorem pswap_mul_rot (k l : Fin 4) (hkl : (k = 0 ∧ l = 1) ∨ (k = 2 ∧ l = 3)) :
    pswap b k l * rot b k = rot b l * pswap b k l := by
  refine b.ext' fun i => ?_
  rcases hkl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases i with i | i <;> fin_cases i <;>
    simp [pswap, rot, sperm_apply, sgnAt, Equiv.swap_apply_def, Equiv.Perm.mul_apply]

theorem rot_mul_refl_mul_rot (l : Fin 4) : rot b l * refl b l * rot b l = refl b l := by
  refine b.ext' fun i => ?_
  fin_cases l <;> rcases i with i | i <;> fin_cases i <;>
    simp [rot, refl, sperm_apply, sgnAt, Equiv.swap_apply_def]

theorem rot_pow_four (l : Fin 4) : rot b l * rot b l * rot b l * rot b l = 1 := by
  refine b.ext' fun i => ?_
  fin_cases l <;> rcases i with i | i <;> fin_cases i <;>
    simp [rot, sperm_apply, sgnAt, Equiv.swap_apply_def]

theorem rot_mul_rot_mem {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0)
    (horth : ∀ i j, polar Q (b i) (b j) = if i = j then 1 else 0) (k l : Fin 4)
    (hkl : (k = 0 ∧ l = 1) ∨ (k = 2 ∧ l = 3)) :
    rot b k * rot b l ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hρk : rot b k ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sperm_mem_orthogonalGroup h2 b horth _ _ (sgnAt_mul_self _)
  have hρl : rot b l ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sperm_mem_orthogonalGroup h2 b horth _ _ (sgnAt_mul_self _)
  have hs : pswap b k l ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sperm_mem_orthogonalGroup h2 b horth _ _ (one_mul_self)
  have hr : refl b l ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sperm_mem_orthogonalGroup h2 b horth _ _ (sgnAt_mul_self _)
  have h1 := pswap_mul_rot b k l hkl
  have h2' := rot_mul_refl_mul_rot b l
  have h3 := rot_pow_four b l
  have e : rot b k * rot b l = ⁅rot b k, pswap b k l⁆ * ⁅refl b l, rot b l⁆ := by
    have hl : rot b l = pswap b k l * rot b k * (pswap b k l)⁻¹ := by
      rw [h1]
      group
    have hr' : refl b l * rot b l * (refl b l)⁻¹ = (rot b l)⁻¹ := by
      have hi : (refl b l)⁻¹ = (rot b l * refl b l * rot b l)⁻¹ := by rw [h2']
      rw [hi]
      group
    have h4 : (rot b l) ^ 4 = 1 := by
      rw [pow_succ, pow_succ, pow_succ, pow_one]
      exact h3
    calc rot b k * rot b l = rot b k * (rot b l)⁻¹ * ((rot b l)⁻¹ * (rot b l)⁻¹) *
          (rot b l) ^ 4 := by group
      _ = ⁅rot b k, pswap b k l⁆ * ⁅refl b l, rot b l⁆ := by
          rw [h4, mul_one, commutatorElement_def, commutatorElement_def, hr', hl]
          group
  rw [e]
  exact mul_mem (Subgroup.commutator_mem_commutator hρk hs)
    (Subgroup.commutator_mem_commutator hr hρl)

end Rot

section Cplx

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem mem_commutator_of_sq_neg_one (hF : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (h8 : Module.finrank F V = 8) {a : V ≃ₗ[F] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ha2 : ∀ v, a (a v) = -v) :
    a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hF hQ ha ha2
  obtain rfl : m = 4 := by omega
  have haL : ∀ k, a (ab.basis (.inl k)) = ab.basis (.inr k) := fun k => (ab.inr_eq k).symm
  have haR : ∀ k, a (ab.basis (.inr k)) = -ab.basis (.inl k) := fun k => by
    rw [ab.inr_eq, ha2]
  have hrot : a = rot ab.basis 0 * rot ab.basis 1 * (rot ab.basis 2 * rot ab.basis 3) := by
    refine ab.basis.ext' fun i => ?_
    rcases i with i | i <;> fin_cases i <;>
      simp [haL, haR, rot, sperm_apply, sgnAt, Equiv.swap_apply_def, LinearEquiv.mul_apply]
  rw [hrot]
  exact mul_mem (rot_mul_rot_mem ab.basis h2 ab.orth 0 1 (Or.inl ⟨rfl, rfl⟩))
    (rot_mul_rot_mem ab.basis h2 ab.orth 2 3 (Or.inr ⟨rfl, rfl⟩))

end Cplx

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

theorem simFam_one_neg_one : SimFam 1 (-1) := by
  intro a hsim ha2 β hodd hβ
  have hK : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hsim, one_mul]
  have ha2' : ∀ v, a (a v) = -v := fun v => by rw [ha2, neg_one_smul]
  have hmem := mem_commutator_of_sq_neg_one hK (nondegenerate_polarBilin_quadPlus 4 𝔽₃)
    finrank_d4 haO ha2'
  have hΩ := symm_mem_statedOmega hmem
  have hE : a ∈ elementaryGroup Q₄ := by
    rwa [commutator_orthogonalGroup_quadPlus (by norm_num)] at hmem
  obtain ⟨x, hx, hxc⟩ := exists_spin_of_mem_elementary hE hΩ
  refine typeII_smul hK β hodd ⟨_, hΩ⟩ (fun v => ?_) ?_
  · simp only [MulEquiv.apply_symm_apply]
    exact ha2' v
  · rw [← hxc]
    exact hβ x (by rw [hx])

end CFSG.ClassicalInvolution.Q3.TL4
