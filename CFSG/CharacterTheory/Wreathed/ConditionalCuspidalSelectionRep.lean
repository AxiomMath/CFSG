module

public import CFSG.CharacterTheory.OddOrderBasics.TypeIExtensionSupport
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2
  CFSG.TwoRankLowerBound.Helpers

section Restriction

variable {K X V : Type*} [Group K] [Group X] [AddCommGroup V] [Module ℂ V]

theorem isIrreducible_of_comp_hom (ρ : Representation ℂ X V) (f : K →* X)
    (h : Representation.IsIrreducible (ρ.comp f)) : ρ.IsIrreducible := by
  let : IsSimpleOrder (Subrepresentation (ρ.comp f)) := h
  let toK : Subrepresentation ρ → Subrepresentation (ρ.comp f) := fun W =>
    ⟨W.toSubmodule, fun n v hv => W.apply_mem_toSubmodule (f n) hv⟩
  change IsSimpleOrder (Subrepresentation ρ)
  have hnontrivial : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hequal
    have hb : (⊥ : Subrepresentation (ρ.comp f)) ≠ ⊤ := bot_ne_top
    apply hb
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hequal
    exact this
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  rcases eq_bot_or_eq_top (toK W) with hW | hW
  · left
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hW
    exact this
  · right
    apply Subrepresentation.ext
    have := congrArg Subrepresentation.toSubmodule hW
    exact this

end Restriction

section Trace

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem trace_mul_smul_pow (A S : Module.End ℂ V) (ω : ℂ) (j : ℕ) :
    LinearMap.trace ℂ V (A * (ω • S) ^ j) = ω ^ j * LinearMap.trace ℂ V (A * S ^ j) := by
  rw [smul_pow, mul_smul_comm, map_smul, smul_eq_mul]

end Trace

section Extension

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem exists_pow_eq_of_generator [Finite F] {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (σ : Sigma) : ∃ j : ℕ, σ₀ ^ j = σ :=
  (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hgen σ))

theorem exists_semilinear_representation [Finite F] {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : Representation ℂ (CentralExtension F b m hm heven) V) (S : (Module.End ℂ V)ˣ)
    (hS : ∀ k, (S : Module.End ℂ V) * R k * ((S⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      R (fieldAction F b m hm heven Sigma hSigma σ₀ k))
    (hSd : S ^ Nat.card Sigma = 1) :
    ∃ ρ' : Representation ℂ (SemilinearExtension F b m hm heven Sigma hSigma) V,
      ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
        ρ' ⟨k, σ₀ ^ j⟩ = R k * (S : Module.End ℂ V) ^ j := by
  have hord : orderOf σ₀ = Nat.card Sigma := orderOf_eq_card_of_forall_mem_zpowers hgen
  have hdvd : orderOf S ∣ orderOf σ₀ := by
    rw [hord]
    exact orderOf_dvd_of_pow_eq_one hSd
  let Wu : Sigma →* (Module.End ℂ V)ˣ := monoidHomOfForallMemZpowers hgen hdvd
  have hWu : Wu σ₀ = S := monoidHomOfForallMemZpowers_apply_gen hgen hdvd
  let ρu : CentralExtension F b m hm heven →* (Module.End ℂ V)ˣ := R.toHomUnits
  have hSu : ∀ k, S * ρu k * S⁻¹ = ρu (fieldAction F b m hm heven Sigma hSigma σ₀ k) :=
    fun k => Units.ext (hS k)
  have hpow : ∀ (j : ℕ) k, S ^ j * ρu k * (S ^ j)⁻¹ =
      ρu (fieldAction F b m hm heven Sigma hSigma (σ₀ ^ j) k) := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [pow_succ' S, pow_succ' σ₀, map_mul, MulAut.mul_apply, ← hSu, ← ih]
      group
  have hcond : ∀ σ : Sigma, ρu.comp (fieldAction F b m hm heven Sigma hSigma σ).toMonoidHom =
      (MulAut.conj (Wu σ)).toMonoidHom.comp ρu := by
    intro σ
    obtain ⟨j, rfl⟩ := exists_pow_eq_of_generator hgen σ
    refine MonoidHom.ext fun k => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hpow j k, map_pow Wu σ₀ j, hWu]
  refine ⟨(Units.coeHom (Module.End ℂ V)).comp (SemidirectProduct.lift ρu Wu hcond),
    fun k j => ?_⟩
  rw [MonoidHom.comp_apply, SemidirectProduct.mk_eq_inl_mul_inr, map_mul,
    SemidirectProduct.lift_inl, SemidirectProduct.lift_inr, map_pow, hWu, Units.coeHom_apply,
    Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

theorem exists_scaled_semilinear_representation [Finite F] {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : Representation ℂ (CentralExtension F b m hm heven) V) (T : (Module.End ℂ V)ˣ)
    (hT : ∀ k, (T : Module.End ℂ V) * R k * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      R (fieldAction F b m hm heven Sigma hSigma σ₀ k))
    (hTd : T ^ Nat.card Sigma = 1) {ω : ℂ} (hω : ω ^ Nat.card Sigma = 1) :
    ∃ ρ' : Representation ℂ (SemilinearExtension F b m hm heven Sigma hSigma) V,
      ∀ (k : CentralExtension F b m hm heven) (j : ℕ),
        ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    rw [zero_pow Nat.card_pos.ne'] at hω
    exact zero_ne_one hω
  let S : (Module.End ℂ V)ˣ :=
    { val := ω • (T : Module.End ℂ V)
      inv := ω⁻¹ • ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)
      val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hω0, Units.mul_inv, one_smul]
      inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hω0, Units.inv_mul, one_smul] }
  have hS : ∀ k, (S : Module.End ℂ V) * R k * ((S⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
      R (fieldAction F b m hm heven Sigma hSigma σ₀ k) := by
    intro k
    change ω • (T : Module.End ℂ V) * R k * (ω⁻¹ • ((T⁻¹ : (Module.End ℂ V)ˣ) :
      Module.End ℂ V)) = _
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hω0, one_smul,
      hT]
  have hSd : S ^ Nat.card Sigma = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change (ω • (T : Module.End ℂ V)) ^ Nat.card Sigma = 1
    rw [smul_pow, hω, one_smul, ← Units.val_pow_eq_pow_val, hTd, Units.val_one]
  obtain ⟨ρ', hρ'⟩ := exists_semilinear_representation hSigma hgen R S hS hSd
  exact ⟨ρ', hρ'⟩

theorem semilinear_representation_comp_inl {σ₀ : Sigma} {V : Type*} [AddCommGroup V]
    [Module ℂ V] (R : Representation ℂ (CentralExtension F b m hm heven) V)
    (S : Module.End ℂ V)
    (ρ' : Representation ℂ (SemilinearExtension F b m hm heven Sigma hSigma) V)
    (hρ' : ∀ (k : CentralExtension F b m hm heven) (j : ℕ), ρ' ⟨k, σ₀ ^ j⟩ = R k * S ^ j) :
    ρ'.comp SemidirectProduct.inl = R := by
  refine MonoidHom.ext fun k => ?_
  rw [MonoidHom.comp_apply]
  have h := hρ' k 0
  rw [pow_zero, pow_zero, mul_one] at h
  exact h

theorem exists_normalized_intertwiner [Finite F] {σ₀ : Sigma}
    (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (R : Representation ℂ (CentralExtension F b m hm heven) V)
    (hR : R.IsIrreducible)
    (hinv : ∀ k, R.character (fieldAction F b m hm heven Sigma hSigma σ₀ k) = R.character k) :
    ∃ T : (Module.End ℂ V)ˣ,
      (∀ k, (T : Module.End ℂ V) * R k * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
        R (fieldAction F b m hm heven Sigma hSigma σ₀ k)) ∧ T ^ Nat.card Sigma = 1 := by
  have : Finite (CentralExtension F b m hm heven) := by
    have := Fintype.ofFinite F
    infer_instance
  have : Fintype (CentralExtension F b m hm heven) := Fintype.ofFinite _
  have : Nontrivial V := nontrivial_of_isIrreducible R hR
  set d := Nat.card Sigma with hd
  have hd0 : 0 < d := Nat.card_pos
  let σR : Representation ℂ (CentralExtension F b m hm heven) V :=
    R.comp (fieldAction F b m hm heven Sigma hSigma σ₀).toMonoidHom
  have hchar : σR.character = R.character := funext hinv
  obtain ⟨U, hU⟩ := CFSG.OddOrderBasics.exists_unit_intertwining_of_character_eq R σR hR hchar
  have hU' : ∀ k, (U : Module.End ℂ V) * R k =
      R (fieldAction F b m hm heven Sigma hSigma σ₀ k) * U := hU
  have hpow : ∀ (j : ℕ) k, ((U ^ j : (Module.End ℂ V)ˣ) : Module.End ℂ V) * R k =
      R (fieldAction F b m hm heven Sigma hSigma (σ₀ ^ j) k) *
        ((U ^ j : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [pow_succ', Units.val_mul, mul_assoc, ih, ← mul_assoc, hU', mul_assoc, pow_succ',
        map_mul, MulAut.mul_apply]
  have hσd : σ₀ ^ d = 1 := by
    rw [hd, ← orderOf_eq_card_of_forall_mem_zpowers hgen]
    exact pow_orderOf_eq_one σ₀
  obtain ⟨c, hc⟩ := CFSG.OddOrderBasics.exists_eq_smul_of_conj R hR id
    ((U ^ d : (Module.End ℂ V)ˣ) : Module.End ℂ V) 1
    (fun k => by rw [hpow, hσd, map_one, MulAut.one_apply, id]) (fun k => by simp)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact (U ^ d).ne_zero hc
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq c hd0
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hd0.ne'] at hμ
    exact hc0 hμ.symm
  let T : (Module.End ℂ V)ˣ :=
    { val := μ⁻¹ • (U : Module.End ℂ V)
      inv := μ • ((U⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V)
      val_inv := by
        rw [smul_mul_smul_comm, inv_mul_cancel₀ hμ0, Units.mul_inv, one_smul]
      inv_val := by
        rw [smul_mul_smul_comm, mul_inv_cancel₀ hμ0, Units.inv_mul, one_smul] }
  refine ⟨T, fun k => ?_, ?_⟩
  · change μ⁻¹ • (U : Module.End ℂ V) * R k * (μ • ((U⁻¹ : (Module.End ℂ V)ˣ) :
      Module.End ℂ V)) = _
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hμ0,
      one_smul, hU', mul_assoc, Units.mul_inv, mul_one]
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change (μ⁻¹ • (U : Module.End ℂ V)) ^ d = 1
    rw [smul_pow, ← Units.val_pow_eq_pow_val, hc, smul_smul, inv_pow, hμ, inv_mul_cancel₀ hc0,
      one_smul, Units.val_one]

end Extension

end CFSG.Wreathed
