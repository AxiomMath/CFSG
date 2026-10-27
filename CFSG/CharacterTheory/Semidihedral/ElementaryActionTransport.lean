module

public import CFSG.CharacterTheory.Semidihedral.OddCentralDimension
import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.Semidihedral.ElementaryActionTransport

noncomputable section

open scoped IsMulCommutative

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [Group R] [IsElementaryAbelian p R]

@[expose] def endEquivLinear (R : Type u) [Group R] [IsElementaryAbelian p R] :
    Monoid.End R ≃* Module.End (ZMod p) (Additive R) :=
  (MulEquiv.monoidEnd R).trans
    { toEquiv := (AddMonoidHom.toZModLinearMapEquiv p).toEquiv
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }

@[simp] theorem endEquivLinear_apply (a : Monoid.End R) (r : R) :
    endEquivLinear (p := p) R a (Additive.ofMul r) = Additive.ofMul (a r) := rfl

@[expose] def autEquivUnitsEnd (R : Type u) [Group R] :
    MulAut R ≃* (Monoid.End R)ˣ where
  toFun a :=
    { val := a.toMonoidHom
      inv := a.symm.toMonoidHom
      val_inv := MonoidHom.ext a.apply_symm_apply
      inv_val := MonoidHom.ext a.symm_apply_apply }
  invFun a :=
    { a.val with
      invFun := a.inv
      left_inv := fun r => by
        change (a.inv * a.val) r = r
        rw [a.inv_val]
        rfl
      right_inv := fun r => by
        change (a.val * a.inv) r = r
        rw [a.val_inv]
        rfl }
  left_inv _ := MulEquiv.ext fun _ => rfl
  right_inv _ := Units.ext (MonoidHom.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (MonoidHom.ext fun _ => rfl)

@[expose] def autEquivGL :
    MulAut R ≃* LinearMap.GeneralLinearGroup (ZMod p) (Additive R) :=
  (autEquivUnitsEnd R).trans (Units.mapEquiv (endEquivLinear (p := p) R))

@[expose] def autToGL :
    MulAut R →* LinearMap.GeneralLinearGroup (ZMod p) (Additive R) :=
  autEquivGL.toMonoidHom

@[simp] theorem autToGL_apply (a : MulAut R) (r : R) :
    (autToGL (p := p) a : Module.End (ZMod p) (Additive R)) (Additive.ofMul r) =
      Additive.ofMul (a r) := rfl

@[simp] theorem autEquivGL_symm_apply
    (a : LinearMap.GeneralLinearGroup (ZMod p) (Additive R)) (r : R) :
    (autEquivGL (p := p)).symm a r =
      Additive.toMul ((a : Module.End (ZMod p) (Additive R)) (Additive.ofMul r)) := rfl

theorem autToGL_injective : Function.Injective (autToGL (p := p) (R := R)) :=
  autEquivGL.injective

variable {J : Type v} [Group J]

@[expose] def primeFieldAction (ρ : J →* MulAut R) :
    J →* LinearMap.GeneralLinearGroup (ZMod p) (Additive R) :=
  autToGL.comp ρ

@[simp] theorem primeFieldAction_apply (ρ : J →* MulAut R) (j : J) (r : R) :
    (primeFieldAction (p := p) ρ j : Module.End (ZMod p) (Additive R))
      (Additive.ofMul r) = Additive.ofMul (ρ j r) := rfl

theorem primeFieldAction_comp {K : Type w} [Group K]
    (ρ : J →* MulAut R) (φ : K →* J) :
    primeFieldAction (p := p) (ρ.comp φ) = (primeFieldAction (p := p) ρ).comp φ := rfl

theorem primeFieldAction_kernel (ρ : J →* MulAut R) :
    (primeFieldAction (p := p) ρ).ker = ρ.ker :=
  MonoidHom.ker_comp_of_injective ρ autToGL autToGL_injective

theorem primeFieldAction_inversion (ρ : J →* MulAut R) (t : J)
    (hinv : ∀ r : R, ρ t r = r⁻¹) : primeFieldAction (p := p) ρ t = -1 := by
  apply Units.ext
  apply LinearMap.ext
  intro r
  change Additive.ofMul (ρ t (Additive.toMul r)) = -r
  rw [hinv]
  rfl

theorem primeFieldAction_inversion_ne_one [Nontrivial R]
    (hpodd : Odd p) (ρ : J →* MulAut R) (t : J)
    (hinv : ∀ r : R, ρ t r = r⁻¹) : primeFieldAction (p := p) ρ t ≠ 1 := by
  rw [primeFieldAction_inversion ρ t hinv]
  intro heq
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (Fact.out : p.Prime).ne_one
    have hmod := Nat.odd_iff.mp hpodd
    omega
  have hz : ∀ r : Additive R, r = 0 := by
    intro r
    have hneg : -r = r := by
      simpa using congrArg
        (fun a : LinearMap.GeneralLinearGroup (ZMod p) (Additive R) =>
          (a : Module.End (ZMod p) (Additive R)) r) heq
    have hsmul : (2 : ZMod p) • r = 0 := by
      simpa only [two_smul] using (neg_eq_iff_add_eq_zero.mp hneg)
    have hcancel := congrArg (fun x : Additive R => (2 : ZMod p)⁻¹ • x) hsmul
    simpa only [smul_smul, inv_mul_cancel₀ htwo, one_smul, smul_zero] using hcancel
  obtain ⟨r, hr⟩ := exists_ne (0 : Additive R)
  exact hr (hz r)


theorem isElemAbelian_iff_native {G : Type*} [Group G] (n : ℕ) (A : Subgroup G) :
    CFSG.Open.IsElemAbelian n A ↔ IsElementaryAbelian n A :=
  (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian n A).symm

instance subgroupElementary (A : Subgroup R) : IsElementaryAbelian p A where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a =>
    Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p R) (a : R))

@[expose] def subgroupEquivSubmodule :
    Subgroup R ≃o Submodule (ZMod p) (Additive R) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

@[simp] theorem mem_subgroupEquivSubmodule (A : Subgroup R) (r : R) :
    Additive.ofMul r ∈ subgroupEquivSubmodule (p := p) A ↔ r ∈ A := Iff.rfl

@[simp] theorem mem_subgroupEquivSubmodule_symm
    (W : Submodule (ZMod p) (Additive R)) (r : R) :
    r ∈ (subgroupEquivSubmodule (p := p)).symm W ↔ Additive.ofMul r ∈ W := Iff.rfl

theorem subgroupEquivSubmodule_map (A : Subgroup R) (a : MulAut R) :
    subgroupEquivSubmodule (p := p) (A.map a.toMonoidHom) =
      (subgroupEquivSubmodule (p := p) A).map
        (autToGL (p := p) a : Module.End (ZMod p) (Additive R)) := by
  ext x
  change (∃ y : R, y ∈ A ∧ a y = Additive.toMul x) ↔
    ∃ y : Additive R, y ∈ subgroupEquivSubmodule (p := p) A ∧
      (autToGL (p := p) a : Module.End (ZMod p) (Additive R)) y = x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨Additive.ofMul y, hy, congrArg Additive.ofMul hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨Additive.toMul y, hy, congrArg Additive.toMul hxy⟩

@[expose] def primeFieldRepresentation (ρ : J →* MulAut R) :
    Representation (ZMod p) J (Additive R) :=
  (Units.coeHom (Module.End (ZMod p) (Additive R))).comp (primeFieldAction (p := p) ρ)

@[simp] theorem primeFieldRepresentation_apply (ρ : J →* MulAut R) (j : J) (r : R) :
    primeFieldRepresentation (p := p) ρ j (Additive.ofMul r) = Additive.ofMul (ρ j r) := rfl

theorem subgroup_invariant_iff (ρ : J →* MulAut R) (A : Subgroup R) :
    (∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) ↔
      ∀ j : J, subgroupEquivSubmodule (p := p) A ≤
        (subgroupEquivSubmodule (p := p) A).comap (primeFieldRepresentation (p := p) ρ j) := by
  constructor
  · intro h j r hr
    exact h j (Additive.toMul r) hr
  · intro h j r hr
    exact h j hr

@[expose] def subgroupSubrepresentation (ρ : J →* MulAut R) (A : Subgroup R)
    (hA : ∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) :
    Subrepresentation (primeFieldRepresentation (p := p) ρ) where
  toSubmodule := subgroupEquivSubmodule (p := p) A
  apply_mem_toSubmodule j := (subgroup_invariant_iff ρ A).mp hA j

theorem primeFieldRepresentation_irreducible_iff [Nontrivial R] (ρ : J →* MulAut R) :
    Representation.IsIrreducible (primeFieldRepresentation (p := p) ρ) ↔
      ∀ A : Subgroup R, (∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) → A = ⊥ ∨ A = ⊤ := by
  constructor
  · intro hirr A hA
    let := hirr
    have he := IsSimpleOrder.eq_bot_or_eq_top (subgroupSubrepresentation (p := p) ρ A hA)
    rcases he with hb | ht
    · left
      apply (subgroupEquivSubmodule (p := p)).injective
      exact (congrArg Subrepresentation.toSubmodule hb).trans
        (subgroupEquivSubmodule (p := p)).map_bot.symm
    · right
      apply (subgroupEquivSubmodule (p := p)).injective
      exact (congrArg Subrepresentation.toSubmodule ht).trans
        (subgroupEquivSubmodule (p := p)).map_top.symm
  · intro h
    refine (isSimpleOrder_iff _).mpr ⟨?_, ?_⟩
    · refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro heq
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule heq)
    · intro W
      let A := (subgroupEquivSubmodule (p := p)).symm W.toSubmodule
      have hA : ∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A := by
        intro j r hr
        exact W.apply_mem_toSubmodule j hr
      rcases h A hA with hb | ht
      · left
        apply Subrepresentation.toSubmodule_injective
        calc
          W.toSubmodule = subgroupEquivSubmodule (p := p) A :=
            ((subgroupEquivSubmodule (p := p)).apply_symm_apply _).symm
          _ = ⊥ := by rw [hb, (subgroupEquivSubmodule (p := p)).map_bot]
      · right
        apply Subrepresentation.toSubmodule_injective
        calc
          W.toSubmodule = subgroupEquivSubmodule (p := p) A :=
            ((subgroupEquivSubmodule (p := p)).apply_symm_apply _).symm
          _ = ⊤ := by rw [ht, (subgroupEquivSubmodule (p := p)).map_top]


@[expose] def addEquivLinear {A : Type*} {B : Type*}
    [AddCommGroup A] [AddCommGroup B] [Module (ZMod p) A] [Module (ZMod p) B]
    (e : A ≃+ B) : A ≃ₗ[ZMod p] B :=
  { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

@[expose] def mulEquivLinear {S : Type*} [Group S] [IsElementaryAbelian p S]
    (e : R ≃* S) : Additive R ≃ₗ[ZMod p] Additive S :=
  addEquivLinear (MulEquiv.toAdditive e)

@[simp] theorem mulEquivLinear_apply {S : Type*} [Group S] [IsElementaryAbelian p S]
    (e : R ≃* S) (r : R) : mulEquivLinear (p := p) e (Additive.ofMul r) =
      Additive.ofMul (e r) := rfl

@[expose] def subgroupLinearEquiv (A : Subgroup R) :
    Additive A ≃ₗ[ZMod p] subgroupEquivSubmodule (p := p) A :=
  addEquivLinear
    { toFun a := ⟨Additive.ofMul ((Additive.toMul a : A) : R),
        (Additive.toMul a : A).property⟩
      invFun a := Additive.ofMul ⟨Additive.toMul a.val, a.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }

@[simp] theorem subgroupLinearEquiv_apply (A : Subgroup R) (a : A) :
    (subgroupLinearEquiv (p := p) A (Additive.ofMul a) : Additive R) =
      Additive.ofMul (a : R) := rfl

theorem card_eq_prime_pow_finrank [Finite R] :
    Nat.card R = p ^ Module.finrank (ZMod p) (Additive R) := by
  calc
    Nat.card R = Nat.card (Additive R) := (Nat.card_congr Additive.toMul).symm
    _ = p ^ Module.finrank (ZMod p) (Additive R) := by
      simpa [ZMod.card] using
        (Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive R))

theorem subgroup_finrank_eq (A : Subgroup R) :
    Module.finrank (ZMod p) (Additive A) =
      Module.finrank (ZMod p) (subgroupEquivSubmodule (p := p) A) :=
  (subgroupLinearEquiv (p := p) A).finrank_eq

theorem subgroup_card_eq_prime_pow_finrank [Finite R] (A : Subgroup R) :
    Nat.card A = p ^ Module.finrank (ZMod p) (subgroupEquivSubmodule (p := p) A) := by
  rw [card_eq_prime_pow_finrank (p := p) (R := A), subgroup_finrank_eq]

@[expose] def internalProductLinearEquiv (A B : Subgroup R) (e : A × B ≃* R) :
    (Additive A × Additive B) ≃ₗ[ZMod p] Additive R :=
  addEquivLinear (p := p)
    { toFun x := Additive.ofMul (e (Additive.toMul x.1, Additive.toMul x.2))
      invFun x := (Additive.ofMul (e.symm (Additive.toMul x)).1,
        Additive.ofMul (e.symm (Additive.toMul x)).2)
      left_inv x := by simp
      right_inv x := by simp
      map_add' x y := by
        change Additive.ofMul (e ((Additive.toMul x.1, Additive.toMul x.2) *
          (Additive.toMul y.1, Additive.toMul y.2))) =
          Additive.ofMul (e (Additive.toMul x.1, Additive.toMul x.2) *
            e (Additive.toMul y.1, Additive.toMul y.2))
        rw [map_mul] }

@[simp] theorem internalProductLinearEquiv_apply (A B : Subgroup R) (e : A × B ≃* R)
    (a : A) (b : B) :
    internalProductLinearEquiv (p := p) A B e (Additive.ofMul a, Additive.ofMul b) =
      Additive.ofMul (e (a, b)) := rfl

theorem internalProduct_finrank [Finite R] (A B : Subgroup R) (e : A × B ≃* R) :
    Module.finrank (ZMod p) (Additive R) =
      Module.finrank (ZMod p) (Additive A) + Module.finrank (ZMod p) (Additive B) :=
  (internalProductLinearEquiv (p := p) A B e).finrank_eq.symm.trans Module.finrank_prod

theorem internalProduct_card (A B : Subgroup R) (e : A × B ≃* R) :
    Nat.card R = Nat.card A * Nat.card B :=
  (Nat.card_congr e.toEquiv).symm.trans (Nat.card_prod A B)

theorem equal_factor_finranks [Finite R] (A B : Subgroup R)
    (hcard : Nat.card A = Nat.card B) :
    Module.finrank (ZMod p) (Additive A) = Module.finrank (ZMod p) (Additive B) := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  simpa only [card_eq_prime_pow_finrank (p := p)] using hcard

theorem equal_internalProduct_factors_of_finrank [Finite R] (A B : Subgroup R)
    (e : A × B ≃* R) (hcard : Nat.card A = Nat.card B) (f : ℕ)
    (hdim : Module.finrank (ZMod p) (Additive R) = 2 * f) :
    Module.finrank (ZMod p) (Additive A) = f ∧
      Module.finrank (ZMod p) (Additive B) = f ∧
      Nat.card A = p ^ f ∧ Nat.card B = p ^ f ∧ Nat.card R = p ^ (2 * f) := by
  have hsum := internalProduct_finrank (p := p) A B e
  have heq := equal_factor_finranks (p := p) A B hcard
  have hA : Module.finrank (ZMod p) (Additive A) = f := by omega
  have hB : Module.finrank (ZMod p) (Additive B) = f := by omega
  exact ⟨hA, hB, by rw [card_eq_prime_pow_finrank (p := p) (R := A), hA],
    by rw [card_eq_prime_pow_finrank (p := p) (R := B), hB],
    by rw [card_eq_prime_pow_finrank (p := p) (R := R), hdim]⟩

theorem equal_internalProduct_factors_of_card [Finite R] (A B : Subgroup R)
    (e : A × B ≃* R) (hcard : Nat.card A = Nat.card B) (f : ℕ)
    (hR : Nat.card R = p ^ (2 * f)) :
    Module.finrank (ZMod p) (Additive R) = 2 * f ∧
      Module.finrank (ZMod p) (Additive A) = f ∧
      Module.finrank (ZMod p) (Additive B) = f ∧
      Nat.card A = p ^ f ∧ Nat.card B = p ^ f := by
  have hdim : Module.finrank (ZMod p) (Additive R) = 2 * f := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    simpa only [card_eq_prime_pow_finrank (p := p)] using hR
  obtain ⟨hA, hB, hcA, hcB, _⟩ :=
    equal_internalProduct_factors_of_finrank (p := p) A B e hcard f hdim
  exact ⟨hdim, hA, hB, hcA, hcB⟩


theorem primeFieldRepresentation_kernel (ρ : J →* MulAut R) :
    (primeFieldRepresentation (p := p) ρ).ker = ρ.ker :=
  (MonoidHom.ker_comp_of_injective (primeFieldAction (p := p) ρ)
    (Units.coeHom (Module.End (ZMod p) (Additive R))) Units.coeHom_injective).trans
      (primeFieldAction_kernel ρ)

@[expose] def descendedOriginalAction {H : Type w} [Group H] (β : J →* H)
    (hβ : Function.Surjective β) (ρ : J →* MulAut R) (hker : β.ker ≤ ρ.ker) :
    H →* MulAut R :=
  β.liftOfSurjective hβ ⟨ρ, hker⟩

@[simp] theorem descendedOriginalAction_apply {H : Type w} [Group H] (β : J →* H)
    (hβ : Function.Surjective β) (ρ : J →* MulAut R) (hker : β.ker ≤ ρ.ker) (j : J) :
    descendedOriginalAction β hβ ρ hker (β j) = ρ j := by
  simp only [descendedOriginalAction, MonoidHom.liftOfRightInverse_comp_apply]

theorem descendedOriginalAction_apply_element {H : Type w} [Group H] (β : J →* H)
    (hβ : Function.Surjective β) (ρ : J →* MulAut R) (hker : β.ker ≤ ρ.ker)
    (j : J) (r : R) : descendedOriginalAction β hβ ρ hker (β j) r = ρ j r := by
  rw [descendedOriginalAction_apply]

theorem descendedOriginalAction_comp {H : Type w} [Group H] (β : J →* H)
    (hβ : Function.Surjective β) (ρ : J →* MulAut R) (hker : β.ker ≤ ρ.ker) :
    (descendedOriginalAction β hβ ρ hker).comp β = ρ :=
  MonoidHom.ext (descendedOriginalAction_apply β hβ ρ hker)

theorem descendedOriginalAction_injective {H : Type w} [Group H] (β : J →* H)
    (hβ : Function.Surjective β) (ρ : J →* MulAut R) (hker : β.ker ≤ ρ.ker)
    (heq : ρ.ker = β.ker) : Function.Injective (descendedOriginalAction β hβ ρ hker) := by
  apply (MonoidHom.ker_eq_bot_iff (descendedOriginalAction β hβ ρ hker)).mp
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · obtain ⟨j, rfl⟩ := hβ h
    intro hj
    rw [descendedOriginalAction_apply] at hj
    have hjker : j ∈ ρ.ker := hj
    rw [heq] at hjker
    exact MonoidHom.mem_ker.mp hjker
  · intro hh
    rw [hh, map_one]

theorem descendedOriginalAction_primeFieldAction {H : Type w} [Group H]
    (β : J →* H) (hβ : Function.Surjective β) (ρ : J →* MulAut R)
    (hker : β.ker ≤ ρ.ker)
    (hlinear : β.ker ≤ (primeFieldRepresentation (p := p) ρ).ker) :
    primeFieldAction (p := p) (descendedOriginalAction β hβ ρ hker) =
      OddCentralDimension.descendedAction β hβ (primeFieldRepresentation (p := p) ρ) hlinear := by
  apply MonoidHom.ext
  intro h
  obtain ⟨j, rfl⟩ := hβ h
  rw [OddCentralDimension.descendedAction_apply]
  change autToGL (p := p) (descendedOriginalAction β hβ ρ hker (β j)) = _
  rw [descendedOriginalAction_apply]
  exact (OddCentralDimension.asGroupHom_coeHom_comp (primeFieldAction (p := p) ρ))
    |> congrArg (fun f => f j) |> Eq.symm

theorem originalAction_of_checked_full_GL_equality {H : Type w} [Group H]
    (β : J →* H) (hβ : Function.Surjective β) (ρ : J →* MulAut R) (t : J) (n : ℕ)
    (hequality : Module.finrank (ZMod p) (Additive R) = n →
      OddCentralDimension.negativeSpace (primeFieldRepresentation (p := p) ρ) t = ⊤ ∧
        Representation.IsIrreducible (primeFieldRepresentation (p := p) ρ) ∧
        (primeFieldAction (p := p) ρ).ker = β.ker ∧
        ∃ (hlinear : β.ker ≤ (primeFieldRepresentation (p := p) ρ).ker),
          Function.Injective (OddCentralDimension.descendedAction β hβ
            (primeFieldRepresentation (p := p) ρ) hlinear) ∧
          (OddCentralDimension.descendedAction β hβ
            (primeFieldRepresentation (p := p) ρ) hlinear).comp β = primeFieldAction (p := p) ρ)
    (hdim : Module.finrank (ZMod p) (Additive R) = n) :
    OddCentralDimension.negativeSpace (primeFieldRepresentation (p := p) ρ) t = ⊤ ∧
      Representation.IsIrreducible (primeFieldRepresentation (p := p) ρ) ∧
      ρ.ker = β.ker ∧
      ∃ (hker : β.ker ≤ ρ.ker) (hlinear : β.ker ≤ (primeFieldRepresentation (p := p) ρ).ker),
        Function.Injective (descendedOriginalAction β hβ ρ hker) ∧
        (descendedOriginalAction β hβ ρ hker).comp β = ρ ∧
        primeFieldAction (p := p) (descendedOriginalAction β hβ ρ hker) =
          OddCentralDimension.descendedAction β hβ (primeFieldRepresentation (p := p) ρ) hlinear ∧
        ∀ (j : J) (r : R), descendedOriginalAction β hβ ρ hker (β j) r = ρ j r := by
  obtain ⟨hspace, hirr, hGLker, hlinear, hinj, _⟩ := hequality hdim
  have hkernel : ρ.ker = β.ker := (primeFieldAction_kernel ρ).symm.trans hGLker
  have hker : β.ker ≤ ρ.ker := hkernel.ge
  have htransport := descendedOriginalAction_primeFieldAction β hβ ρ hker hlinear
  have hfaithful : Function.Injective (descendedOriginalAction β hβ ρ hker) := by
    intro x y hxy
    apply hinj
    rw [← htransport]
    exact congrArg (autToGL (p := p)) hxy
  exact ⟨hspace, hirr, hkernel, hker, hlinear, hfaithful,
    descendedOriginalAction_comp β hβ ρ hker, htransport,
    descendedOriginalAction_apply_element β hβ ρ hker⟩

theorem original_elementary_odd_cover_full_dimension_and_equality
    [Finite J] [Group.IsPerfect J] [Finite R] [Nontrivial R]
    {F : Type w} [Field F] {f : ℕ} (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (β : J →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : J →* MulAut R) (hinv : ∀ r : R, ρ t r = r⁻¹) :
    2 * f ≤ Module.finrank (ZMod p)
      (OddCentralDimension.negativeSpace (primeFieldRepresentation (p := p) ρ) t) ∧
      2 * f ≤ Module.finrank (ZMod p) (Additive R) ∧
      OddCentralDimension.AllNegativeIrreducibleSubquotientsBound β hβ
        (primeFieldRepresentation (p := p) ρ) t ht (2 * f) ∧
      (Module.finrank (ZMod p) (Additive R) = 2 * f →
        OddCentralDimension.negativeSpace (primeFieldRepresentation (p := p) ρ) t = ⊤ ∧
          Representation.IsIrreducible (primeFieldRepresentation (p := p) ρ) ∧
          ρ.ker = β.ker ∧
          ∃ (hker : β.ker ≤ ρ.ker)
            (hlinear : β.ker ≤ (primeFieldRepresentation (p := p) ρ).ker),
            Function.Injective (descendedOriginalAction β hβ ρ hker) ∧
            (descendedOriginalAction β hβ ρ hker).comp β = ρ ∧
            primeFieldAction (p := p) (descendedOriginalAction β hβ ρ hker) =
              OddCentralDimension.descendedAction β hβ
                (primeFieldRepresentation (p := p) ρ) hlinear ∧
            ∀ (j : J) (r : R), descendedOriginalAction β hβ ρ hker (β j) r = ρ j r) := by
  let : Finite F := Nat.finite_of_card_ne_zero (hF ▸ pow_ne_zero f (Fact.out : p.Prime).ne_zero)
  obtain ⟨hneg, hwhole, hfactors, hequality⟩ :=
    OddCentralDimension.odd_central_SL2_cover_defining_characteristic_minimum_dimension
      (Fact.out : p.Prime) hpodd hf hF hq (by simp [ZMod.card]) β hβ hcentral hodd
      t ht htorder htβ (primeFieldAction (p := p) ρ)
      (primeFieldAction_inversion_ne_one hpodd ρ t hinv)
  exact ⟨hneg, hwhole, hfactors,
    originalAction_of_checked_full_GL_equality β hβ ρ t (2 * f) hequality⟩

end

end CFSG.Semidihedral.ElementaryActionTransport
