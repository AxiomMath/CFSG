module

public import CFSG.FeitThompson.OddOrder.NormalizerSemilinearFixedVector
public import CFSG.FeitThompson.OddOrder.PrimeDegreeFieldAutomorphisms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

theorem sub_one_mul_pow_sub_one_div_sub_one {p : ℕ} (hp : 1 ≤ p) (q : ℕ) :
    (p - 1) * ((p ^ q - 1) / (p - 1)) = p ^ q - 1 :=
  Nat.mul_div_cancel' ⟨∑ i ∈ Finset.range q, p ^ i, by
    rw [mul_comm, geom_sum_mul_of_one_le hp]⟩

variable {p q : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {A : Subgroup (V ≃ₗ[ZMod p] V)}

theorem zpowers_le_normalizer {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)) := Subgroup.zpowers_le.2 hb

theorem mem_invariants_zpowers_iff {b : V ≃ₗ[ZMod p] V} {s : V} :
    s ∈ Representation.invariants (linearGroupRep (Subgroup.zpowers b)) ↔ b s = s := by
  rw [mem_invariants_linearGroupRep_iff]
  refine ⟨fun h => h b (Subgroup.mem_zpowers b), fun h c hc => ?_⟩
  exact Subgroup.zpowers_le.2 (show b ∈ MulAction.stabilizer (V ≃ₗ[ZMod p] V) s from h) hc

theorem finite_subgroup_linearEquiv [FiniteDimensional (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) : Finite A :=
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (V ≃ₗ[ZMod p] V) := Finite.of_injective (fun f : V ≃ₗ[ZMod p] V => (f : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)
  inferInstance

theorem coe_unitsHom_eq (a : A) :
    ((unitsHom A a : ↥(envelopingSubalgebra A))) =
      ⟨((a : V ≃ₗ[ZMod p] V) : Module.End (ZMod p) V), coe_mem_envelopingSubalgebra a.2⟩ :=
  Subtype.ext (coe_unitsHom a)

variable [FiniteDimensional (ZMod p) V] [IsMulCommutative A] [(linearGroupRep A).IsIrreducible]

instance instFiniteEnvelopingSubalgebra : Finite ↥(envelopingSubalgebra A) :=
  Module.finite_of_finite (ZMod p)

instance instCharPEnvelopingSubalgebra : CharP ↥(envelopingSubalgebra A) p :=
  have : Nontrivial V := nontrivial_of_isIrreducible_linearGroupRep A
  charP_of_injective_algebraMap injective_algebraMap_envelopingSubalgebra p

instance instFiniteAlgEquivEnvelopingSubalgebra :
    Finite (↥(envelopingSubalgebra A) ≃ₐ[ZMod p] ↥(envelopingSubalgebra A)) :=
  have : Finite (↥(envelopingSubalgebra A) ≃+* ↥(envelopingSubalgebra A)) :=
    finite_ringEquiv_of_finite _
  Finite.of_injective (fun σ => σ.toRingEquiv) fun _ _ h => AlgEquiv.ext (RingEquiv.ext_iff.mp h)

theorem natCard_envelopingSubalgebra_eq_pow (hdim : finrank (ZMod p) V = q) :
    Nat.card ↥(envelopingSubalgebra A) = p ^ q := by
  rw [natCard_envelopingSubalgebra_zmod, hdim]

theorem isCyclic_of_isMulCommutative_of_isIrreducible : IsCyclic A :=
  have : IsCyclic (↥(envelopingSubalgebra A))ˣ :=
    isCyclic_units_of_finite_field ↥(envelopingSubalgebra A)
  isCyclic_of_injective (unitsHom A) injective_unitsHom

theorem natCard_dvd_pow_sub_one (hdim : finrank (ZMod p) V = q) :
    Nat.card A ∣ p ^ q - 1 := by
  have h := Subgroup.card_dvd_of_injective (unitsHom A) injective_unitsHom
  rwa [Nat.card_units, natCard_envelopingSubalgebra_eq_pow hdim] at h

theorem ringEquiv_apply_of_mem_bot (σ : ↥(envelopingSubalgebra A) ≃+* ↥(envelopingSubalgebra A))
    {x : ↥(envelopingSubalgebra A)} (hx : x ∈ (⊥ : Subfield ↥(envelopingSubalgebra A))) :
    σ x = x := by
  obtain ⟨n, rfl⟩ := (mem_bot_iff_intCast p _).mp hx
  simp

theorem conjEnveloping_apply_of_mem_bot {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    {x : ↥(envelopingSubalgebra A)} (hx : x ∈ (⊥ : Subfield ↥(envelopingSubalgebra A))) :
    conjEnveloping A hb x = x :=
  ringEquiv_apply_of_mem_bot (conjEnveloping A hb).toRingEquiv hx

theorem eq_one_of_unitsHom_mem_bot {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) {a : A}
    (ha : (unitsHom A a : ↥(envelopingSubalgebra A)) ∈
      (⊥ : Subfield ↥(envelopingSubalgebra A))) : a = 1 := by
  have h := conjEnveloping_apply_of_mem_bot hb ha
  rw [coe_unitsHom_eq, conjEnveloping_coe_group hb a.2] at h
  have h3 : b * (a : V ≃ₗ[ZMod p] V) * b⁻¹ = (a : V ≃ₗ[ZMod p] V) :=
    LinearEquiv.toLinearMap_injective (congrArg Subtype.val h)
  exact Subtype.ext (hCA _ a.2 (mul_inv_eq_iff_eq_mul.mp h3).symm)

theorem eq_one_of_pow_sub_one_eq_one {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) {a : A} (ha : a ^ (p - 1) = 1) : a = 1 := by
  refine eq_one_of_unitsHom_mem_bot hb hCA ?_
  set x : ↥(envelopingSubalgebra A) := (unitsHom A a : ↥(envelopingSubalgebra A)) with hxdef
  have hx : x ^ (p - 1) = 1 := by
    rw [hxdef, ← Units.val_pow_eq_pow_val, ← map_pow, ha, map_one, Units.val_one]
  rw [Subfield.mem_bot_iff_pow_eq_self _ p]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
  calc x ^ p = x ^ (p - 1) * x := by rw [← pow_succ]; congr 1; omega
    _ = x := by rw [hx, one_mul]

theorem coprime_natCard_sub_one {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) : Nat.Coprime (Nat.card A) (p - 1) := by
  have : Finite A := finite_subgroup_linearEquiv A
  have : IsCyclic A := isCyclic_of_isMulCommutative_of_isIrreducible
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have hdvd : Nat.gcd (Nat.card A) (p - 1) ∣ Nat.card A := Nat.gcd_dvd_left _ _
  have ha : orderOf (g ^ (Nat.card A / Nat.gcd (Nat.card A) (p - 1)))
      = Nat.gcd (Nat.card A) (p - 1) := by
    rw [orderOf_pow, hg, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
      Nat.div_div_self hdvd Nat.card_pos.ne']
  have h1 : (g ^ (Nat.card A / Nat.gcd (Nat.card A) (p - 1))) ^ (p - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [ha]; exact Nat.gcd_dvd_right _ _)
  have h2 := eq_one_of_pow_sub_one_eq_one hb hCA h1
  change Nat.gcd (Nat.card A) (p - 1) = 1
  rw [← ha, h2, orderOf_one]

theorem natCard_dvd_normOne (hdim : finrank (ZMod p) V = q) {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) :
    Nat.card A ∣ (p ^ q - 1) / (p - 1) := by
  refine (coprime_natCard_sub_one hb hCA).dvd_of_dvd_mul_left ?_
  rw [sub_one_mul_pow_sub_one_div_sub_one (Fact.out : p.Prime).pos]
  exact natCard_dvd_pow_sub_one hdim

theorem unitsHom_pow_normOne_eq_one (hdim : finrank (ZMod p) V = q) {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) (a : A) :
    (unitsHom A a : ↥(envelopingSubalgebra A)) ^ ((p ^ q - 1) / (p - 1)) = 1 := by
  have : Finite A := finite_subgroup_linearEquiv A
  have haN : a ^ ((p ^ q - 1) / (p - 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard a).trans (natCard_dvd_normOne hdim hb hCA))
  rw [← Units.val_pow_eq_pow_val, ← map_pow, haN, map_one, Units.val_one]

def algEquivEquivRingEquiv (A : Subgroup (V ≃ₗ[ZMod p] V)) :
    (↥(envelopingSubalgebra A) ≃ₐ[ZMod p] ↥(envelopingSubalgebra A)) ≃
      (↥(envelopingSubalgebra A) ≃+* ↥(envelopingSubalgebra A)) where
  toFun σ := σ.toRingEquiv
  invFun σ := AlgEquiv.ofRingEquiv (f := σ) fun x =>
    congrFun (congrArg (fun f : ZMod p →+* ↥(envelopingSubalgebra A) =>
      (f : ZMod p → ↥(envelopingSubalgebra A)))
      (RingHom.ext_zmod ((σ : ↥(envelopingSubalgebra A) →+* ↥(envelopingSubalgebra A)).comp
        (algebraMap (ZMod p) ↥(envelopingSubalgebra A)))
        (algebraMap (ZMod p) ↥(envelopingSubalgebra A)))) x
  left_inv _ := AlgEquiv.ext fun _ => rfl
  right_inv _ := RingEquiv.ext fun _ => rfl

theorem natCard_ringEquiv_envelopingSubalgebra (hq : q.Prime) (hdim : finrank (ZMod p) V = q) :
    Nat.card (↥(envelopingSubalgebra A) ≃+* ↥(envelopingSubalgebra A)) = q := by
  have hF := natCard_envelopingSubalgebra_eq_pow (A := A) hdim
  have h := setOf_ringEquiv_fixing_bot_eq_image p q ↥(envelopingSubalgebra A) hq hF
  have huniv : {σ : ↥(envelopingSubalgebra A) ≃+* ↥(envelopingSubalgebra A) |
      ∀ x ∈ (⊥ : Subfield ↥(envelopingSubalgebra A)), σ x = x} = Set.univ :=
    Set.eq_univ_of_forall fun σ _ hx => ringEquiv_apply_of_mem_bot σ hx
  rw [huniv] at h
  have hinj : Set.InjOn (frobeniusEquiv ↥(envelopingSubalgebra A) p ^ ·) (Set.Iio q) := by
    rw [← orderOf_frobeniusEquiv_eq_of_prime p q ↥(envelopingSubalgebra A) hq hF]
    exact pow_injOn_Iio_orderOf
  rw [← Set.ncard_univ, h, hinj.ncard_image, Set.ncard_Iio_nat]

theorem natCard_algEquiv_envelopingSubalgebra (hq : q.Prime) (hdim : finrank (ZMod p) V = q) :
    Nat.card (↥(envelopingSubalgebra A) ≃ₐ[ZMod p] ↥(envelopingSubalgebra A)) = q := by
  rw [Nat.card_congr (algEquivEquivRingEquiv A), natCard_ringEquiv_envelopingSubalgebra hq hdim]

theorem range_conjEnvelopingHomOfLE_zpowers_eq_top {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))) (hq : q.Prime)
    (hdim : finrank (ZMod p) V = q) (hbq : orderOf b = q) {s : V} (hs0 : s ≠ 0) (hbs : b s = s) :
    (conjEnvelopingHomOfLE (A := A) (zpowers_le_normalizer hb)).range = ⊤ := by
  have hinj := injective_conjEnvelopingHomOfLE (A := A) (zpowers_le_normalizer hb) hs0
    (mem_invariants_zpowers_iff.2 hbs)
  have hcard : Nat.card ↥(Subgroup.zpowers b) =
      Nat.card (↥(envelopingSubalgebra A) ≃ₐ[ZMod p] ↥(envelopingSubalgebra A)) := by
    rw [Nat.card_zpowers, hbq, natCard_algEquiv_envelopingSubalgebra (A := A) hq hdim]
  exact MonoidHom.range_eq_top.2 ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2

omit [FiniteDimensional (ZMod p) V] in
theorem conjEnveloping_ne_one {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))) {s : V} (hs0 : s ≠ 0)
    (hbs : b s = s) (hb1 : b ≠ 1) : conjEnveloping A hb ≠ 1 := by
  intro h
  have hinj := injective_conjEnvelopingHomOfLE (A := A) (zpowers_le_normalizer hb) hs0
    (mem_invariants_zpowers_iff.2 hbs)
  refine hb1 (congrArg Subtype.val (hinj (a₁ := ⟨b, Subgroup.mem_zpowers b⟩) (a₂ := 1) ?_))
  rw [conjEnvelopingHomOfLE_apply, map_one]
  exact h

omit [FiniteDimensional (ZMod p) V] in
theorem mem_invariants_zpowers_iff_conjEnveloping_eq {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))) {s : V} (hs0 : s ≠ 0)
    (hbs : b s = s) {x : ↥(envelopingSubalgebra A)} :
    evalEnvelopingSubalgebraEquiv (A := A) hs0 x ∈
        Representation.invariants (linearGroupRep (Subgroup.zpowers b)) ↔
      conjEnveloping A hb x = x := by
  rw [mem_invariants_zpowers_iff]
  have key := symm_evalEnvelopingSubalgebraEquiv_apply (A := A) hs0 hb hbs
    (evalEnvelopingSubalgebraEquiv hs0 x)
  rw [LinearEquiv.symm_apply_apply] at key
  constructor
  · intro h
    rw [← key, h, LinearEquiv.symm_apply_apply]
  · intro h
    apply (evalEnvelopingSubalgebraEquiv (A := A) hs0).symm.injective
    rw [key, h, LinearEquiv.symm_apply_apply]

theorem symm_evalEnvelopingSubalgebraEquiv_image_invariants {b : V ≃ₗ[ZMod p] V}
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))) (hq : q.Prime)
    (hdim : finrank (ZMod p) V = q) (hb1 : b ≠ 1) {s : V} (hs0 : s ≠ 0) (hbs : b s = s) :
    (evalEnvelopingSubalgebraEquiv (A := A) hs0).symm ''
        (Representation.invariants (linearGroupRep (Subgroup.zpowers b)) : Set V)
      = ((⊥ : Subfield ↥(envelopingSubalgebra A)) : Set ↥(envelopingSubalgebra A)) := by
  have hfix : Function.fixedPoints (conjEnveloping A hb).toRingEquiv =
      ((⊥ : Subfield ↥(envelopingSubalgebra A)) : Set ↥(envelopingSubalgebra A)) :=
    fixedPoints_eq_bot_of_ne_one p q _ hq (natCard_envelopingSubalgebra_eq_pow (A := A) hdim)
      (fun x hx => ringEquiv_apply_of_mem_bot _ hx)
      (fun h => conjEnveloping_ne_one hb hs0 hbs hb1
        (AlgEquiv.ext fun x => RingEquiv.ext_iff.mp h x))
  rw [← hfix]
  ext x
  have hmem : x ∈ Function.fixedPoints (conjEnveloping A hb).toRingEquiv ↔
      conjEnveloping A hb x = x := Iff.rfl
  rw [hmem, Set.mem_image]
  refine ⟨?_, fun hx => ⟨evalEnvelopingSubalgebraEquiv hs0 x,
    (mem_invariants_zpowers_iff_conjEnveloping_eq hb hs0 hbs).2 hx,
    LinearEquiv.symm_apply_apply _ _⟩⟩
  rintro ⟨v, hv, rfl⟩
  refine (mem_invariants_zpowers_iff_conjEnveloping_eq hb hs0 hbs).1 ?_
  rwa [LinearEquiv.apply_symm_apply]

theorem fpf_irreducible_field_image_norm (hq : q.Prime) (hdim : finrank (ZMod p) V = q)
    {b : V ≃ₗ[ZMod p] V} (hbq : orderOf b = q)
    (hb : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V)))
    (hCA : ∀ a ∈ A, a * b = b * a → a = 1) {s : V} (hs0 : s ≠ 0) (hbs : b s = s) :
    IsCyclic A ∧ Nat.Coprime (Nat.card A) (p - 1) ∧
      Nat.card A ∣ (p ^ q - 1) / (p - 1) ∧
      (∀ a : A, (unitsHom A a : ↥(envelopingSubalgebra A)) ^ ((p ^ q - 1) / (p - 1)) = 1) ∧
      (conjEnvelopingHomOfLE (A := A) (zpowers_le_normalizer hb)).range = ⊤ ∧
      (evalEnvelopingSubalgebraEquiv (A := A) hs0).symm ''
          (Representation.invariants (linearGroupRep (Subgroup.zpowers b)) : Set V)
        = ((⊥ : Subfield ↥(envelopingSubalgebra A)) : Set ↥(envelopingSubalgebra A)) := by
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbq
    exact hq.one_lt.ne hbq
  exact ⟨isCyclic_of_isMulCommutative_of_isIrreducible, coprime_natCard_sub_one hb hCA,
    natCard_dvd_normOne hdim hb hCA, unitsHom_pow_normOne_eq_one hdim hb hCA,
    range_conjEnvelopingHomOfLE_zpowers_eq_top hb hq hdim hbq hs0 hbs,
    symm_evalEnvelopingSubalgebraEquiv_image_invariants hb hq hdim hb1 hs0 hbs⟩

end

end CFSG.FeitThompson
