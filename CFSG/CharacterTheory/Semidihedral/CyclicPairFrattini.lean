module

public import CFSG.CharacterTheory.Semidihedral.ElementaryActionTransport
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

open scoped IsMulCommutative

namespace CFSG.Semidihedral.CyclicPairFrattini

universe u v w z

abbrev powerSubgroup (ell : ℕ) (R : Type u) [CommGroup R] : Subgroup R :=
  (powMonoidHom ell : R →* R).range

abbrev PowerQuotient (ell : ℕ) (R : Type u) [CommGroup R] := R ⧸ powerSubgroup ell R

instance powerSubgroup_characteristic (ell : ℕ) (R : Type u) [CommGroup R] :
    (powerSubgroup ell R).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr fun e => e.map_range_powMonoidHom ell

@[expose] def powerQuotientMk (ell : ℕ) (R : Type u) [CommGroup R] :
    R →* PowerQuotient ell R :=
  QuotientGroup.mk' (powerSubgroup ell R)

theorem mem_powerSubgroup_iff (ell : ℕ) {R : Type u} [CommGroup R] (r : R) :
    r ∈ powerSubgroup ell R ↔ ∃ x : R, x ^ ell = r :=
  Iff.rfl

theorem powerQuotientMk_surjective (ell : ℕ) (R : Type u) [CommGroup R] :
    Function.Surjective (powerQuotientMk ell R) :=
  QuotientGroup.mk'_surjective (powerSubgroup ell R)

theorem powerQuotientMk_ker (ell : ℕ) (R : Type u) [CommGroup R] :
    (powerQuotientMk ell R).ker = powerSubgroup ell R :=
  QuotientGroup.ker_mk' (powerSubgroup ell R)

theorem power_quotient_exponent (ell : ℕ) {R : Type u} [CommGroup R]
    (x : PowerQuotient ell R) : x ^ ell = 1 := by
  obtain ⟨r, rfl⟩ := powerQuotientMk_surjective ell R x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨r, rfl⟩

instance powerQuotient_elementary (ell : ℕ) (R : Type u) [CommGroup R] :
    CFSG.IsElementaryAbelian ell (PowerQuotient ell R) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (power_quotient_exponent ell)

instance powerQuotient_cyclic (ell : ℕ) (A : Type u) [CommGroup A] [IsCyclic A] :
    IsCyclic (PowerQuotient ell A) :=
  isCyclic_of_surjective (powerQuotientMk ell A) (powerQuotientMk_surjective ell A)

theorem cyclic_power_quotient_card (ell : ℕ) [Fact ell.Prime]
    {A : Type u} [CommGroup A] [Finite A] [Nontrivial A] [IsCyclic A]
    (hA : IsPGroup ell A) : Nat.card (PowerQuotient ell A) = ell := by
  have hdiv : ell ∣ Nat.card A :=
    (hA.card_eq_or_dvd).resolve_left (ne_of_gt Finite.one_lt_card)
  change (powerSubgroup ell A).index = ell
  rw [powerSubgroup, IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdiv]

theorem powerSubgroup_map (ell : ℕ) {R : Type u} {S : Type v}
    [CommGroup R] [CommGroup S] (e : R ≃* S) :
    (powerSubgroup ell R).map e.toMonoidHom = powerSubgroup ell S :=
  e.map_range_powMonoidHom ell

theorem powerSubgroup_prod (ell : ℕ) (A : Type u) (B : Type v)
    [CommGroup A] [CommGroup B] :
    powerSubgroup ell (A × B) = (powerSubgroup ell A).prod (powerSubgroup ell B) := by
  ext x
  change (∃ y : A × B, y ^ ell = x) ↔
    (∃ a : A, a ^ ell = x.1) ∧ (∃ b : B, b ^ ell = x.2)
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

@[expose] noncomputable def powerQuotientCongr (ell : ℕ)
    {R : Type u} {S : Type v} [CommGroup R] [CommGroup S] (e : R ≃* S) :
    PowerQuotient ell R ≃* PowerQuotient ell S :=
  QuotientGroup.congr (powerSubgroup ell R) (powerSubgroup ell S) e
    (powerSubgroup_map ell e)

@[simp] theorem powerQuotientCongr_mk (ell : ℕ)
    {R : Type u} {S : Type v} [CommGroup R] [CommGroup S] (e : R ≃* S) (r : R) :
    powerQuotientCongr ell e (powerQuotientMk ell R r) = powerQuotientMk ell S (e r) :=
  QuotientGroup.congr_mk' _ _ e (powerSubgroup_map ell e) r

@[simp] theorem powerQuotientCongr_symm_mk (ell : ℕ)
    {R : Type u} {S : Type v} [CommGroup R] [CommGroup S] (e : R ≃* S) (s : S) :
    (powerQuotientCongr ell e).symm (powerQuotientMk ell S s) =
      powerQuotientMk ell R (e.symm s) := by
  apply (powerQuotientCongr ell e).injective
  rw [MulEquiv.apply_symm_apply, powerQuotientCongr_mk, e.apply_symm_apply]

@[expose] def productPowerQuotientMk (ell : ℕ)
    (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    A × B →* PowerQuotient ell A × PowerQuotient ell B :=
  (powerQuotientMk ell A).prodMap (powerQuotientMk ell B)

theorem productPowerQuotientMk_surjective (ell : ℕ)
    (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    Function.Surjective (productPowerQuotientMk ell A B) := by
  rintro ⟨x, y⟩
  obtain ⟨a, ha⟩ := powerQuotientMk_surjective ell A x
  obtain ⟨b, hb⟩ := powerQuotientMk_surjective ell B y
  exact ⟨(a, b), Prod.ext ha hb⟩

theorem productPowerQuotientMk_ker (ell : ℕ)
    (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    (productPowerQuotientMk ell A B).ker = powerSubgroup ell (A × B) := by
  rw [productPowerQuotientMk, MonoidHom.ker_prodMap, powerQuotientMk_ker,
    powerQuotientMk_ker, powerSubgroup_prod]

@[expose] noncomputable def productPowerQuotientEquiv (ell : ℕ)
    (A : Type u) (B : Type v) [CommGroup A] [CommGroup B] :
    PowerQuotient ell (A × B) ≃* PowerQuotient ell A × PowerQuotient ell B :=
  QuotientGroup.liftEquiv (powerSubgroup ell (A × B))
    (productPowerQuotientMk_surjective ell A B) (productPowerQuotientMk_ker ell A B).symm

@[simp] theorem productPowerQuotientEquiv_mk (ell : ℕ)
    {A : Type u} {B : Type v} [CommGroup A] [CommGroup B] (a : A) (b : B) :
    productPowerQuotientEquiv ell A B (powerQuotientMk ell (A × B) (a, b)) =
      (powerQuotientMk ell A a, powerQuotientMk ell B b) :=
  QuotientGroup.liftEquiv_mk _ _ _ (a, b)

@[simp] theorem productPowerQuotientEquiv_symm_mk (ell : ℕ)
    {A : Type u} {B : Type v} [CommGroup A] [CommGroup B] (a : A) (b : B) :
    (productPowerQuotientEquiv ell A B).symm
      (powerQuotientMk ell A a, powerQuotientMk ell B b) =
      powerQuotientMk ell (A × B) (a, b) := by
  apply (productPowerQuotientEquiv ell A B).injective
  rw [MulEquiv.apply_symm_apply, productPowerQuotientEquiv_mk]

@[expose] noncomputable def originalProductPowerQuotientEquiv (ell : ℕ)
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) :
    PowerQuotient ell R ≃* PowerQuotient ell A × PowerQuotient ell B :=
  (powerQuotientCongr ell e.symm).trans (productPowerQuotientEquiv ell A B)

@[simp] theorem originalProductPowerQuotientEquiv_mk (ell : ℕ)
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) (r : R) :
    originalProductPowerQuotientEquiv ell e (powerQuotientMk ell R r) =
      (powerQuotientMk ell A (e.symm r).1, powerQuotientMk ell B (e.symm r).2) := by
  rw [originalProductPowerQuotientEquiv, MulEquiv.trans_apply, powerQuotientCongr_mk]
  exact productPowerQuotientEquiv_mk ell (e.symm r).1 (e.symm r).2

theorem originalProductPowerQuotientEquiv_product_mk (ell : ℕ)
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) (a : A) (b : B) :
    originalProductPowerQuotientEquiv ell e (powerQuotientMk ell R (e (a, b))) =
      (powerQuotientMk ell A a, powerQuotientMk ell B b) := by
  rw [originalProductPowerQuotientEquiv_mk, e.symm_apply_apply]

@[simp] theorem originalProductPowerQuotientEquiv_symm_mk (ell : ℕ)
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) (a : A) (b : B) :
    (originalProductPowerQuotientEquiv ell e).symm
      (powerQuotientMk ell A a, powerQuotientMk ell B b) =
      powerQuotientMk ell R (e (a, b)) := by
  apply (originalProductPowerQuotientEquiv ell e).injective
  rw [MulEquiv.apply_symm_apply, originalProductPowerQuotientEquiv_product_mk]

theorem original_power_quotient_card (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) :
    Nat.card (PowerQuotient ell R) = ell ^ 2 := by
  rw [Nat.card_congr (originalProductPowerQuotientEquiv ell e).toEquiv, Nat.card_prod,
    cyclic_power_quotient_card ell hA, cyclic_power_quotient_card ell hB, pow_two]

@[expose] noncomputable def cyclicPowerCoordinate (ell : ℕ) [Fact ell.Prime]
    {A : Type u} [CommGroup A] [Finite A] [Nontrivial A] [IsCyclic A]
    (hA : IsPGroup ell A) : Additive (PowerQuotient ell A) ≃ₗ[ZMod ell] ZMod ell := by
  let : AddCommGroup (ZMod ell) := (inferInstance : Ring (ZMod ell)).toAddCommGroup
  let e : Additive (PowerQuotient ell A) ≃+ ZMod ell := (zmodAddCyclicAddEquiv
    (isAddCyclic_additive_iff.mpr (inferInstance : IsCyclic (PowerQuotient ell A)))).symm.trans
      (ZMod.ringEquivCongr (cyclic_power_quotient_card ell hA)).toAddEquiv
  exact e.toLinearEquiv (R := ZMod ell) (fun c x => ZMod.map_smul e c x)

@[expose] noncomputable def originalProductPowerQuotientLinearEquiv
    (ell : ℕ) [Fact ell.Prime] {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) :
    Additive (PowerQuotient ell R) ≃ₗ[ZMod ell]
      Additive (PowerQuotient ell A) × Additive (PowerQuotient ell B) :=
  let f := (MulEquiv.toAdditive (originalProductPowerQuotientEquiv ell e)).trans
    (AddEquiv.prodAdditive (PowerQuotient ell A) (PowerQuotient ell B))
  f.toLinearEquiv (R := ZMod ell) (fun c x => ZMod.map_smul f c x)

@[simp] theorem originalProductPowerQuotientLinearEquiv_mk
    (ell : ℕ) [Fact ell.Prime] {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R] (e : A × B ≃* R) (r : R) :
    originalProductPowerQuotientLinearEquiv ell e (Additive.ofMul (powerQuotientMk ell R r)) =
      (Additive.ofMul (powerQuotientMk ell A (e.symm r).1),
        Additive.ofMul (powerQuotientMk ell B (e.symm r).2)) := by
  change (Additive.ofMul (originalProductPowerQuotientEquiv ell e
    (powerQuotientMk ell R r)).1, Additive.ofMul (originalProductPowerQuotientEquiv ell e
    (powerQuotientMk ell R r)).2) = _
  rw [originalProductPowerQuotientEquiv_mk]

@[expose] noncomputable def originalProductCoordinates (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) :
    Additive (PowerQuotient ell R) ≃ₗ[ZMod ell] (Fin 2 → ZMod ell) :=
  (originalProductPowerQuotientLinearEquiv ell e).trans
    (((cyclicPowerCoordinate ell hA).prodCongr (cyclicPowerCoordinate ell hB)).trans
      (LinearEquiv.finTwoArrow (ZMod ell) (ZMod ell)).symm)

@[simp] theorem originalProductCoordinates_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) (r : R) :
    originalProductCoordinates ell hA hB e (Additive.ofMul (powerQuotientMk ell R r)) =
      ![cyclicPowerCoordinate ell hA (Additive.ofMul (powerQuotientMk ell A (e.symm r).1)),
        cyclicPowerCoordinate ell hB (Additive.ofMul (powerQuotientMk ell B (e.symm r).2))] := by
  simp only [originalProductCoordinates, LinearEquiv.trans_apply,
    originalProductPowerQuotientLinearEquiv_mk, LinearEquiv.prodCongr_apply,
    LinearEquiv.finTwoArrow_symm_apply]

theorem originalProductCoordinates_product_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) (a : A) (b : B) :
    originalProductCoordinates ell hA hB e
      (Additive.ofMul (powerQuotientMk ell R (e (a, b)))) =
      ![cyclicPowerCoordinate ell hA (Additive.ofMul (powerQuotientMk ell A a)),
        cyclicPowerCoordinate ell hB (Additive.ofMul (powerQuotientMk ell B b))] := by
  rw [originalProductCoordinates_mk, e.symm_apply_apply]

@[simp] theorem originalProductCoordinates_symm_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) (a : A) (b : B) :
    (originalProductCoordinates ell hA hB e).symm
      ![cyclicPowerCoordinate ell hA (Additive.ofMul (powerQuotientMk ell A a)),
        cyclicPowerCoordinate ell hB (Additive.ofMul (powerQuotientMk ell B b))] =
      Additive.ofMul (powerQuotientMk ell R (e (a, b))) := by
  apply (originalProductCoordinates ell hA hB e).injective
  rw [LinearEquiv.apply_symm_apply, originalProductCoordinates_product_mk]

theorem original_power_quotient_finrank (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) :
    Module.finrank (ZMod ell) (Additive (PowerQuotient ell R)) = 2 := by
  rw [(originalProductCoordinates ell hA hB e).finrank_eq]
  simp

instance (priority := 1100) zmodAddCommGroup (ell : ℕ) : AddCommGroup (ZMod ell) :=
  (inferInstance : Ring (ZMod ell)).toAddCommGroup

@[expose] noncomputable def powerQuotientAut (ell : ℕ) {R : Type u} [CommGroup R] :
    MulAut R →* MulAut (PowerQuotient ell R) :=
  CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (powerSubgroup ell R)

@[simp] theorem powerQuotientAut_mk (ell : ℕ) {R : Type u} [CommGroup R]
    (a : MulAut R) (r : R) :
    powerQuotientAut ell a (powerQuotientMk ell R r) = powerQuotientMk ell R (a r) :=
  CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply _ a r

@[expose] noncomputable def powerQuotientAction (ell : ℕ)
    {J : Type v} [Group J] {R : Type u} [CommGroup R] (ρ : J →* MulAut R) :
    J →* MulAut (PowerQuotient ell R) :=
  (powerQuotientAut ell).comp ρ

@[simp] theorem powerQuotientAction_mk (ell : ℕ)
    {J : Type v} [Group J] {R : Type u} [CommGroup R]
    (ρ : J →* MulAut R) (j : J) (r : R) :
    powerQuotientAction ell ρ j (powerQuotientMk ell R r) =
      powerQuotientMk ell R (ρ j r) :=
  powerQuotientAut_mk ell (ρ j) r

theorem powerQuotientAction_comp (ell : ℕ)
    {J : Type v} [Group J] {K : Type w} [Group K] {R : Type u} [CommGroup R]
    (ρ : J →* MulAut R) (φ : K →* J) :
    powerQuotientAction ell (ρ.comp φ) = (powerQuotientAction ell ρ).comp φ := rfl

theorem powerQuotientAction_inversion (ell : ℕ)
    {J : Type v} [Group J] {R : Type u} [CommGroup R]
    (ρ : J →* MulAut R) (t : J) (hinv : ∀ r : R, ρ t r = r⁻¹)
    (x : PowerQuotient ell R) : powerQuotientAction ell ρ t x = x⁻¹ := by
  obtain ⟨r, rfl⟩ := powerQuotientMk_surjective ell R x
  rw [powerQuotientAction_mk, hinv, map_inv]

@[expose] noncomputable def coordinateAut (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w}
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) :
    MulAut R →* LinearMap.GeneralLinearGroup (ZMod ell) (Fin 2 → ZMod ell) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
    (originalProductCoordinates ell hA hB e)).toMonoidHom.comp
      ((ElementaryActionTransport.autToGL (p := ell)).comp (powerQuotientAut ell))

@[expose] noncomputable def coordinateAction (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) (ρ : J →* MulAut R) :
    J →* LinearMap.GeneralLinearGroup (ZMod ell) (Fin 2 → ZMod ell) :=
  (coordinateAut ell hA hB e).comp ρ

theorem coordinateAction_apply (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (j : J) (x : PowerQuotient ell R) :
    (coordinateAction ell hA hB e ρ j : Module.End (ZMod ell) (Fin 2 → ZMod ell))
        (originalProductCoordinates ell hA hB e (Additive.ofMul x)) =
      originalProductCoordinates ell hA hB e
        (Additive.ofMul (powerQuotientAction ell ρ j x)) := by
  change (LinearMap.GeneralLinearGroup.congrLinearEquiv
    (originalProductCoordinates ell hA hB e)
    (ElementaryActionTransport.autToGL (p := ell) (powerQuotientAut ell (ρ j))) :
      Module.End (ZMod ell) (Fin 2 → ZMod ell)) _ = _
  rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  change originalProductCoordinates ell hA hB e
    ((ElementaryActionTransport.autToGL (p := ell) (powerQuotientAut ell (ρ j)) :
      Module.End (ZMod ell) (Additive (PowerQuotient ell R)))
        ((originalProductCoordinates ell hA hB e).symm
          (originalProductCoordinates ell hA hB e (Additive.ofMul x)))) = _
  rw [LinearEquiv.symm_apply_apply, ElementaryActionTransport.autToGL_apply]
  rfl

theorem coordinateAction_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (j : J) (r : R) :
    (coordinateAction ell hA hB e ρ j : Module.End (ZMod ell) (Fin 2 → ZMod ell))
        (originalProductCoordinates ell hA hB e (Additive.ofMul (powerQuotientMk ell R r))) =
      originalProductCoordinates ell hA hB e
        (Additive.ofMul (powerQuotientMk ell R (ρ j r))) := by
  rw [coordinateAction_apply, powerQuotientAction_mk]

theorem coordinateAction_inverse_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (j : J) (r : R) :
    (originalProductCoordinates ell hA hB e).symm
      ((coordinateAction ell hA hB e ρ j : Module.End (ZMod ell) (Fin 2 → ZMod ell))
        (originalProductCoordinates ell hA hB e (Additive.ofMul (powerQuotientMk ell R r)))) =
      Additive.ofMul (powerQuotientMk ell R (ρ j r)) := by
  rw [coordinateAction_mk, LinearEquiv.symm_apply_apply]

theorem coordinateAction_comp (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    {K : Type*} [Group K]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (φ : K →* J) :
    coordinateAction ell hA hB e (ρ.comp φ) = (coordinateAction ell hA hB e ρ).comp φ := rfl

theorem coordinateAction_inversion (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (t : J) (hinv : ∀ r : R, ρ t r = r⁻¹) :
    coordinateAction ell hA hB e ρ t = -1 := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := (originalProductCoordinates ell hA hB e).surjective v
  obtain ⟨r, hr⟩ := powerQuotientMk_surjective ell R (Additive.toMul x)
  have hx : x = Additive.ofMul (powerQuotientMk ell R r) := congrArg Additive.ofMul hr.symm
  rw [hx]
  change _ = -(originalProductCoordinates ell hA hB e (Additive.ofMul (powerQuotientMk ell R r)))
  rw [coordinateAction_mk, hinv, map_inv]
  exact (originalProductCoordinates ell hA hB e).map_neg _

theorem coordinateAction_inversion_ne_one (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (hellodd : Odd ell) (ρ : J →* MulAut R) (t : J)
    (hinv : ∀ r : R, ρ t r = r⁻¹) : coordinateAction ell hA hB e ρ t ≠ 1 := by
  rw [coordinateAction_inversion ell hA hB e ρ t hinv]
  intro heq
  have hneg : (-1 : ZMod ell) = 1 := by
    simpa using congrArg
      (fun g : LinearMap.GeneralLinearGroup (ZMod ell) (Fin 2 → ZMod ell) =>
        (g : Module.End (ZMod ell) (Fin 2 → ZMod ell)) (fun _ => 1) 0) heq
  rcases ZMod.neg_one_eq_one_iff.mp hneg with h | h
  · exact (Fact.out : ell.Prime).ne_one h
  · have := Nat.odd_iff.mp hellodd
    omega


@[expose] noncomputable def matrixCoordinateAction (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R) (ρ : J →* MulAut R) :
    J →* Matrix.GeneralLinearGroup (Fin 2) (ZMod ell) :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp (coordinateAction ell hA hB e ρ)

@[simp] theorem matrixCoordinateAction_toLin (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (j : J) :
    Matrix.GeneralLinearGroup.toLin (matrixCoordinateAction ell hA hB e ρ j) =
      coordinateAction ell hA hB e ρ j :=
  Matrix.GeneralLinearGroup.toLin.apply_symm_apply _

theorem matrixCoordinateAction_mk (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (j : J) (r : R) :
    (matrixCoordinateAction ell hA hB e ρ j : Matrix (Fin 2) (Fin 2) (ZMod ell)).mulVec
        (originalProductCoordinates ell hA hB e (Additive.ofMul (powerQuotientMk ell R r))) =
      originalProductCoordinates ell hA hB e
        (Additive.ofMul (powerQuotientMk ell R (ρ j r))) := by
  rw [← Matrix.toLinAlgEquiv'_apply]
  change (Matrix.GeneralLinearGroup.toLin (matrixCoordinateAction ell hA hB e ρ j) :
    Module.End (ZMod ell) (Fin 2 → ZMod ell)) _ = _
  rw [matrixCoordinateAction_toLin, coordinateAction_mk]

theorem matrixCoordinateAction_inversion (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (ρ : J →* MulAut R) (t : J) (hinv : ∀ r : R, ρ t r = r⁻¹) :
    matrixCoordinateAction ell hA hB e ρ t = -1 := by
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [matrixCoordinateAction_toLin, coordinateAction_inversion ell hA hB e ρ t hinv]
  symm
  exact Units.map_neg_one Matrix.toLinAlgEquiv'

theorem matrixCoordinateAction_inversion_ne_one (ell : ℕ) [Fact ell.Prime]
    {A : Type u} {B : Type v} {R : Type w} {J : Type z} [Group J]
    [CommGroup A] [CommGroup B] [CommGroup R]
    [Finite A] [Nontrivial A] [IsCyclic A] [Finite B] [Nontrivial B] [IsCyclic B]
    (hA : IsPGroup ell A) (hB : IsPGroup ell B) (e : A × B ≃* R)
    (hellodd : Odd ell) (ρ : J →* MulAut R) (t : J)
    (hinv : ∀ r : R, ρ t r = r⁻¹) : matrixCoordinateAction ell hA hB e ρ t ≠ 1 := by
  intro h
  apply coordinateAction_inversion_ne_one ell hA hB e hellodd ρ t hinv
  have hv := congrArg Matrix.GeneralLinearGroup.toLin h
  simpa only [matrixCoordinateAction_toLin, map_one] using hv

end CFSG.Semidihedral.CyclicPairFrattini
