module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReduce
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneExclusion
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement IsMulCommutative

theorem exists_toAdd_mulAut_zmod {p : ℕ} [Fact p.Prime] {C : Type*} [Group C]
    (ε : C ≃* Multiplicative (ZMod p)) (τ : MulAut C) :
    ∃ k : ZMod p, ∀ z : C, Multiplicative.toAdd (ε (τ z)) =
      k * Multiplicative.toAdd (ε z) := by
  let g : C := ε.symm (Multiplicative.ofAdd 1)
  have hgen : ∀ n : ℕ, g ^ n = ε.symm (Multiplicative.ofAdd (n : ZMod p)) := by
    intro n
    rw [show g ^ n = (ε.symm (Multiplicative.ofAdd 1)) ^ n from rfl,
      ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  refine ⟨Multiplicative.toAdd (ε (τ g)), fun z => ?_⟩
  have hz : z = g ^ (Multiplicative.toAdd (ε z)).val := by
    rw [hgen, ZMod.natCast_zmod_val, ← ofAdd_toAdd (ε z)]
    exact (MulEquiv.symm_apply_apply ε z).symm
  calc Multiplicative.toAdd (ε (τ z))
      = Multiplicative.toAdd (ε (τ (g ^ (Multiplicative.toAdd (ε z)).val))) := by
          conv_lhs => rw [hz]
    _ = Multiplicative.toAdd (ε ((τ g) ^ (Multiplicative.toAdd (ε z)).val)) := by rw [map_pow]
    _ = Multiplicative.toAdd ((ε (τ g)) ^ (Multiplicative.toAdd (ε z)).val) := by rw [map_pow]
    _ = (Multiplicative.toAdd (ε z)).val • Multiplicative.toAdd (ε (τ g)) := by rw [toAdd_pow]
    _ = Multiplicative.toAdd (ε (τ g)) * ((Multiplicative.toAdd (ε z)).val : ZMod p) := by
          rw [nsmul_eq_mul, mul_comm]
    _ = Multiplicative.toAdd (ε (τ g)) * Multiplicative.toAdd (ε z) := by
          rw [ZMod.natCast_zmod_val]

theorem exists_frattiniAddEquiv {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hexp : ∀ x : P, x ^ p = 1) :
    ∃ e : Additive (Abelianization P) ≃+ Additive (P ⧸ frattini P),
      ∀ a : P, e (Additive.ofMul (Abelianization.of a)) =
        Additive.ofMul (QuotientGroup.mk' (frattini P) a) := by
  have hΦ : frattini P = commutator P := CFSG.RankThree.PartTwo.frattini_eq_commutator hP hexp
  let f : Abelianization P ≃* (P ⧸ frattini P) := QuotientGroup.quotientMulEquivOfEq hΦ.symm
  let e : Additive (Abelianization P) ≃+ Additive (P ⧸ frattini P) :=
    { toFun := fun u => Additive.ofMul (f (Additive.toMul u))
      invFun := fun v => Additive.ofMul (f.symm (Additive.toMul v))
      left_inv := fun u => by
        exact congrArg Additive.ofMul (MulEquiv.symm_apply_apply f (Additive.toMul u))
      right_inv := fun v => by
        exact congrArg Additive.ofMul (MulEquiv.apply_symm_apply f (Additive.toMul v))
      map_add' := fun u v => by
        exact congrArg Additive.ofMul (map_mul f (Additive.toMul u) (Additive.toMul v)) }
  exact ⟨e, fun a => congrArg (fun y => Additive.ofMul y)
    (QuotientGroup.quotientMulEquivOfEq_mk hΦ.symm a)⟩

theorem exists_commutatorForm_form {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) [CFSG.IsElementaryAbelian p (P ⧸ frattini P)]
    (hexp : ∀ x : P, x ^ p = 1) (hZ : Subgroup.center P = commutator P)
    (hZcard : Nat.card ↥(Subgroup.center P) = p) :
    ∃ (B : LinearMap.BilinForm (ZMod p) (Additive (P ⧸ frattini P)))
      (ε : ↥(commutator P) ≃* Multiplicative (ZMod p)),
      B.IsAlt ∧ B.Nondegenerate ∧
      (∀ a b : P, B (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
        (Additive.ofMul (QuotientGroup.mk' (frattini P) b)) =
        Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b)⟩)) := by
  haveI : Module (ZMod p) (Additive (Abelianization P)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexp)
  obtain ⟨e₀', he_mk⟩ := exists_frattiniAddEquiv hP hexp
  let e : Additive (Abelianization P) ≃ₗ[ZMod p] Additive (P ⧸ frattini P) :=
    e₀'.toLinearEquiv (R := ZMod p) fun c x => ZMod.map_smul e₀' c x
  obtain ⟨ε₀⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hZcard
  obtain ⟨B₀, hAlt, hNondeg, hform⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε₀
  let ε : ↥(commutator P) ≃* Multiplicative (ZMod p) :=
    (MulEquiv.subgroupCongr hZ.symm).trans ε₀
  have hε : ∀ (a b : P) (h : ⁅a, b⁆ ∈ commutator P),
      ε ⟨⁅a, b⁆, h⟩ =
        ε₀ ⟨⁅a, b⁆, CFSG.OddSolvableUnitary.commutatorElement_mem_center hZ a b⟩ := by
    intro a b h
    show ε₀ (MulEquiv.subgroupCongr hZ.symm ⟨⁅a, b⁆, h⟩) = _
    exact congrArg ε₀ (Subtype.ext rfl)
  have hB : ∀ a b : P,
      (LinearMap.BilinForm.congr e B₀) (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
        (Additive.ofMul (QuotientGroup.mk' (frattini P) b)) =
        Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
    intro a b
    have hsimp : ∀ x, e.symm (e₀' x) = x := fun x => by
      rw [show e₀' x = e x from rfl, LinearEquiv.symm_apply_apply]
    rw [hε a b (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)),
      ← he_mk a, ← he_mk b, LinearMap.BilinForm.congr_apply, hsimp, hsimp]
    exact hform a b
  refine ⟨LinearMap.BilinForm.congr e B₀, ε, ?_, ?_, hB⟩
  · intro u
    obtain ⟨w, rfl⟩ := e.surjective u
    rw [LinearMap.BilinForm.congr_apply, e.symm_apply_apply]
    exact hAlt w
  · refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · obtain ⟨w, rfl⟩ := e.surjective u
      have hw : w = 0 := hNondeg.1 w fun y => by
        have h := hu (e y)
        rwa [LinearMap.BilinForm.congr_apply, e.symm_apply_apply, e.symm_apply_apply] at h
      rw [hw, map_zero]
    · obtain ⟨w, rfl⟩ := e.surjective v
      have hw : w = 0 := hNondeg.2 w fun y => by
        have h := hv (e y)
        rwa [LinearMap.BilinForm.congr_apply, e.symm_apply_apply, e.symm_apply_apply] at h
      rw [hw, map_zero]

theorem exists_commutatorForm_similitude {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    [CFSG.IsElementaryAbelian p (P ⧸ frattini P)]
    {B : LinearMap.BilinForm (ZMod p) (Additive (P ⧸ frattini P))}
    {ε : ↥(commutator P) ≃* Multiplicative (ZMod p)}
    (hform : ∀ a b : P, B (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
      (Additive.ofMul (QuotientGroup.mk' (frattini P) b)) =
      Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)⟩)) :
    ∀ σ : MulAut P, ∃ k : ZMod p, ∀ u v : Additive (P ⧸ frattini P),
      B (Additive.ofMul (quotientAutomorphism (frattini P) σ (Additive.toMul u)))
        (Additive.ofMul (quotientAutomorphism (frattini P) σ (Additive.toMul v))) =
          k * B u v := by
  intro σ
  obtain ⟨k, hk⟩ := exists_toAdd_mulAut_zmod ε (MulAut.characteristic (commutator P) σ)
  refine ⟨k, fun u v => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, Additive.ofMul (QuotientGroup.mk' (frattini P) a) = u := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (frattini P) (Additive.toMul u)
    exact ⟨a, congrArg Additive.ofMul ha⟩
  obtain ⟨b, hb⟩ : ∃ b, Additive.ofMul (QuotientGroup.mk' (frattini P) b) = v := by
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (frattini P) (Additive.toMul v)
    exact ⟨b, congrArg Additive.ofMul hb⟩
  subst ha
  subst hb
  have hq : ∀ a : P, Additive.ofMul (quotientAutomorphism (frattini P) σ
      (Additive.toMul (Additive.ofMul (QuotientGroup.mk' (frattini P) a)))) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) (σ a)) := by
    intro a
    show Additive.ofMul (quotientAutomorphism (frattini P) σ
      (QuotientGroup.mk' (frattini P) a)) = _
    rw [quotientAutomorphism_apply]
  rw [hq, hq, hform (σ a) (σ b), hform a b]
  have hz : (⟨⁅σ a, σ b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top (σ a))
        (Subgroup.mem_top (σ b))⟩ : ↥(commutator P)) =
      MulAut.characteristic (commutator P) σ
        ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
          (Subgroup.mem_top b)⟩ := by
    apply Subtype.ext
    change ⁅σ a, σ b⁆ = σ ⁅a, b⁆
    rw [map_commutatorElement]
  rw [hz]
  exact hk _

theorem exists_commutatorForm {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) [CFSG.IsElementaryAbelian p (P ⧸ frattini P)]
    (hexp : ∀ x : P, x ^ p = 1) (hZ : Subgroup.center P = commutator P)
    (hZcard : Nat.card ↥(Subgroup.center P) = p) :
    ∃ (B : LinearMap.BilinForm (ZMod p) (Additive (P ⧸ frattini P)))
      (ε : ↥(commutator P) ≃* Multiplicative (ZMod p)),
      B.IsAlt ∧ B.Nondegenerate ∧
      (∀ a b : P, B (Additive.ofMul (QuotientGroup.mk' (frattini P) a))
        (Additive.ofMul (QuotientGroup.mk' (frattini P) b)) =
        Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b)⟩)) ∧
      (∀ σ : MulAut P, ∃ k : ZMod p, ∀ u v : Additive (P ⧸ frattini P),
        B (Additive.ofMul (quotientAutomorphism (frattini P) σ (Additive.toMul u)))
          (Additive.ofMul (quotientAutomorphism (frattini P) σ (Additive.toMul v))) =
            k * B u v) := by
  obtain ⟨B, ε, hAlt, hNondeg, hform⟩ :=
    exists_commutatorForm_form hP hexp hZ hZcard
  exact ⟨B, ε, hAlt, hNondeg, hform, exists_commutatorForm_similitude hform⟩

@[expose] def frattiniQuotientAct (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    [CFSG.IsElementaryAbelian p (P ⧸ frattini P)] :
    MulAut (P ⧸ frattini P) →* Module.End (ZMod p) (Additive (P ⧸ frattini P)) where
  toFun σ := (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap p
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' σ τ := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, AddMonoidHom.coe_toZModLinearMap,
      AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.coe_toZModLinearMap,
      MonoidHom.coe_toAdditive, MonoidHom.coe_toAdditive, MonoidHom.coe_toAdditive]
    rfl

theorem frattiniQuotientAct_apply {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    [CFSG.IsElementaryAbelian p (P ⧸ frattini P)] (σ : MulAut (P ⧸ frattini P))
    (d : P ⧸ frattini P) :
    frattiniQuotientAct p P σ (Additive.ofMul d) = Additive.ofMul (σ d) := rfl

theorem frattiniQuotientAct_quotient_apply {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    [Finite P] [CFSG.IsElementaryAbelian p (P ⧸ frattini P)] (σ : MulAut P) (d : P) :
    frattiniQuotientAct p P (quotientAutomorphism (frattini P) σ)
        (Additive.ofMul (QuotientGroup.mk' (frattini P) d)) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) (σ d)) := by
  rw [frattiniQuotientAct_apply, quotientAutomorphism_apply]

theorem exists_pow_eq_one_of_ker_quotientAutomorphism {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q]
    [Finite Q] {D : Subgroup Q} [D.Characteristic] (hDq : IsPGroup p D)
    (hDfix : IsPGroup p (fixingSubgroup (MulAut Q) (D : Set Q))) {σ : MulAut Q}
    (hσ : quotientAutomorphism (frattini D) (MulAut.characteristic D σ) = 1) :
    ∃ k : ℕ, σ ^ p ^ k = 1 := by
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel hDq
  obtain ⟨k, hk⟩ := hker ⟨MulAut.characteristic D σ, MonoidHom.mem_ker.mpr hσ⟩
  have h2 : MulAut.characteristic D (σ ^ p ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h3 : σ ^ p ^ k ∈ fixingSubgroup (MulAut Q) (D : Set Q) := by
    rw [mem_fixingSubgroup_iff]
    intro d hd
    exact congrArg (fun τ : MulAut D => ((τ ⟨d, hd⟩ : D) : Q)) h2
  obtain ⟨j, hj⟩ := hDfix ⟨_, h3⟩
  refine ⟨k + j, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hj

theorem exists_frattini_representation {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    (hDq : IsPGroup p D)
    [CFSG.IsElementaryAbelian p (↥D ⧸ frattini ↥D)]
    (hDfix : IsPGroup p (fixingSubgroup (MulAut ↥Q) (D : Set ↥Q))) :
    ∃ φ : X →* (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ,
      (∀ x : X, φ x = 1 → ∃ k : ℕ, x ^ p ^ k ∈ Subgroup.centralizer (Q : Set X)) ∧
      (∀ (x : X) (d : ↥D),
        Additive.ofMul (QuotientGroup.mk' (frattini ↥D)
            (MulAut.characteristic D (MulAut.conjNormal x) d)) =
        ((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
          Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))
          (Additive.ofMul (QuotientGroup.mk' (frattini ↥D) d))) := by
  let ρ : MulAut ↥Q →* (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ :=
    ((frattiniQuotientAct p ↥D).comp
      ((quotientAutomorphism (frattini ↥D)).comp (MulAut.characteristic D))).toHomUnits
  let φ : X →* (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ :=
    ρ.comp (MulAut.conjNormal (H := Q))
  have hρker : ∀ y : MulAut ↥Q, ρ y = 1 → ∃ k : ℕ, y ^ p ^ k = 1 := by
    intro y hy
    have h1 : quotientAutomorphism (frattini D) (MulAut.characteristic D y) = 1 := by
      ext z
      exact congrArg (fun u : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ =>
        (u : Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D))) (Additive.ofMul z)) hy
    exact exists_pow_eq_one_of_ker_quotientAutomorphism hDq hDfix h1
  refine ⟨φ, fun x hx => ?_, fun x d => ?_⟩
  · have hx1 : ρ (MulAut.conjNormal (H := Q) x) = 1 := by
      simpa [φ] using hx
    exact exists_pow_mem_centralizer_of_ker ρ hρker hx1
  · show (frattiniQuotientAct p ↥D)
        (quotientAutomorphism (frattini ↥D) (MulAut.characteristic D (MulAut.conjNormal x)))
        (Additive.ofMul (QuotientGroup.mk' (frattini ↥D) d)) = _
    simp only [φ, ρ, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
      frattiniQuotientAct_quotient_apply]

theorem commutatorModelBar_conj {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (φ : X →* (Module.End (ZMod p) W)ˣ) (π : Additive ↥D →+ W) (bar : X → W)
    (hbar : ∀ (x : X) (hx : x ∈ D.map Q.subtype),
      bar x = π (Additive.ofMul
        ((D.equivMapOfInjective Q.subtype Q.subtype_injective).symm ⟨x, hx⟩)))
    (hbar_sub : ∀ (a : ↥Q) (ha : a ∈ D),
      bar (Q.subtype a) = π (Additive.ofMul (⟨a, ha⟩ : ↥D)))
    (hπconj : ∀ (x : X) (d : ↥D), π (Additive.ofMul (MulAut.characteristic D
      (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (π (Additive.ofMul d))) :
    ∀ x : X, ∀ d ∈ D.map Q.subtype, bar (x * d * x⁻¹) =
      ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (bar d) := by
  classical
  haveI hDn : (D.map Q.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  intro x d hd
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hd
  have hmem : x * (Q.subtype a : X) * x⁻¹ ∈ D.map Q.subtype :=
    hDn.conj_mem (Q.subtype a) (Subgroup.mem_map_of_mem Q.subtype ha) x
  have hval : (D.equivMapOfInjective Q.subtype Q.subtype_injective).symm
        ⟨x * (Q.subtype a : X) * x⁻¹, hmem⟩ =
      MulAut.characteristic D (MulAut.conjNormal (H := Q) x) ⟨a, ha⟩ := by
    apply (D.equivMapOfInjective Q.subtype Q.subtype_injective).injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply, Subgroup.coe_equivMapOfInjective_apply]
    change x * (Q.subtype a : X) * x⁻¹ = ((MulAut.conjNormal (H := Q) x a : ↥Q) : X)
    rw [MulAut.conjNormal_apply]
    rfl
  rw [hbar _ hmem, hval, hbar_sub a ha]
  exact hπconj x ⟨a, ha⟩

theorem exists_bar_of_extraspecial {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (φ : X →* (Module.End (ZMod p) W)ˣ) (π : Additive ↥D →+ W)
    (hπker : ∀ d : ↥D, π (Additive.ofMul d) = 0 ↔ d ∈ Subgroup.center ↥D)
    (hπsurj : Function.Surjective π)
    (hπconj : ∀ (x : X) (d : ↥D), π (Additive.ofMul (MulAut.characteristic D
      (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (π (Additive.ofMul d))) :
    ∃ bar : X → W,
      (∀ (a : ↥Q) (ha : a ∈ D),
        bar (Q.subtype a) = π (Additive.ofMul (⟨a, ha⟩ : ↥D))) ∧
      (∀ a ∈ D.map Q.subtype, ∀ b ∈ D.map Q.subtype, bar (a * b) = bar a + bar b) ∧
      (∀ d ∈ D.map Q.subtype,
        bar d = 0 ↔ d ∈ (Subgroup.center D).map (Q.subtype.comp D.subtype)) ∧
      (∀ w : W, ∃ d ∈ D.map Q.subtype, bar d = w) ∧
      (∀ x : X, ∀ d ∈ D.map Q.subtype, bar (x * d * x⁻¹) =
        ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (bar d)) := by
  classical
  haveI hDn : (D.map Q.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  let κ : ↥D ≃* ↥(D.map Q.subtype) := D.equivMapOfInjective Q.subtype Q.subtype_injective
  let bar : X → W := fun x =>
    if hx : x ∈ D.map Q.subtype then π (Additive.ofMul (κ.symm ⟨x, hx⟩)) else 0
  have hbar_sub : ∀ (a : ↥Q) (ha : a ∈ D),
      bar (Q.subtype a) = π (Additive.ofMul (⟨a, ha⟩ : ↥D)) := by
    intro a ha
    have hmem : (Q.subtype a : X) ∈ D.map Q.subtype := Subgroup.mem_map_of_mem Q.subtype ha
    rw [show bar (Q.subtype a) = π (Additive.ofMul (κ.symm ⟨Q.subtype a, hmem⟩)) from
      dif_pos hmem]
    exact congrArg (fun y => π (Additive.ofMul y)) (κ.symm_apply_eq.mpr (Subtype.ext rfl))
  refine ⟨bar, hbar_sub, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, hbar_sub (a' * b') (D.mul_mem ha' hb'), hbar_sub a' ha', hbar_sub b' hb']
    have hsub : (⟨a' * b', D.mul_mem ha' hb'⟩ : ↥D) = ⟨a', ha'⟩ * ⟨b', hb'⟩ := Subtype.ext rfl
    rw [hsub]
    exact map_add π (Additive.ofMul ⟨a', ha'⟩) (Additive.ofMul ⟨b', hb'⟩)
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hd
    rw [hbar_sub a ha, hπker ⟨a, ha⟩, Subgroup.mem_map]
    constructor
    · intro h; exact ⟨⟨a, ha⟩, h, rfl⟩
    · rintro ⟨c, hc, heq⟩
      have hca : (⟨a, ha⟩ : ↥D) = c := by
        apply Subtype.ext
        exact (Q.subtype_injective heq).symm
      rw [hca]
      exact hc
  · intro w
    obtain ⟨d, hd⟩ := hπsurj w
    obtain ⟨d', rfl⟩ : ∃ d', Additive.ofMul d' = d := ⟨Additive.toMul d, rfl⟩
    refine ⟨Q.subtype (d' : ↥Q), Subgroup.mem_map_of_mem Q.subtype d'.2, ?_⟩
    rw [hbar_sub (d' : ↥Q) d'.2]
    exact hd
  · exact commutatorModelBar_conj φ π bar (fun x hx => dif_pos hx) hbar_sub hπconj

theorem commutatorModel_centralizer {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (φ : X →* (Module.End (ZMod p) W)ˣ) (π : Additive ↥D →+ W)
    (ε : ↥(commutator ↥D) ≃* Multiplicative (ZMod p))
    (B : LinearMap.BilinForm (ZMod p) W)
    (hcz : commutator ↥D = Subgroup.center ↥D)
    (hπconj : ∀ (x : X) (d : ↥D), π (Additive.ofMul (MulAut.characteristic D
      (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (π (Additive.ofMul d)))
    (hform : ∀ a b : ↥D, B (π (Additive.ofMul a)) (π (Additive.ofMul b)) =
      Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)⟩))
    (x : X) (hx : ∀ u v : W,
      B (((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) u)
        (((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) v) = B u v) :
    ∀ c ∈ (Subgroup.center D).map (Q.subtype.comp D.subtype), x * c = c * x := by
  intro c hc
  obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
  have hfix_comm : ∀ a b : ↥D,
      MulAut.characteristic D (MulAut.conjNormal (H := Q) x) ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a b
    have h1 : Multiplicative.toAdd (ε ⟨⁅MulAut.characteristic D (MulAut.conjNormal (H := Q) x) a,
        MulAut.characteristic D (MulAut.conjNormal (H := Q) x) b⁆,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩) =
        Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
          (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
      rw [← hform, ← hform]
      rw [hπconj x a, hπconj x b, hx]
    have h2 : (⟨⁅MulAut.characteristic D (MulAut.conjNormal (H := Q) x) a,
        MulAut.characteristic D (MulAut.conjNormal (H := Q) x) b⁆, _⟩ : ↥(commutator ↥D)) =
        ⟨⁅a, b⁆, _⟩ := ε.injective (Multiplicative.toAdd.injective h1)
    rw [map_commutatorElement]
    exact congrArg Subtype.val h2
  have hfix_all : ∀ z ∈ commutator ↥D,
      MulAut.characteristic D (MulAut.conjNormal (H := Q) x) z = z := by
    intro z hz
    rw [commutator_def, Subgroup.commutator_def] at hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨g₁, -, g₂, -, rfl⟩ := hy
        exact hfix_comm g₁ g₂
    | one => simp
    | mul y z hy hz ihy ihz => rw [map_mul, ihy, ihz]
    | inv y hy ihy => rw [map_inv, ihy]
  have hfix : MulAut.characteristic D (MulAut.conjNormal (H := Q) x) (c' : ↥D) = (c' : ↥D) :=
    hfix_all (c' : ↥D) (hcz.symm ▸ hc')
  have h1 : (MulAut.conjNormal (H := Q) x) (c' : ↥D) = (c' : ↥D) := by
    show ((MulAut.characteristic D (MulAut.conjNormal (H := Q) x)) (c' : ↥D) : ↥Q) = _
    exact congrArg (fun z : ↥D => (z : ↥Q)) hfix
  have hconj : x * ((c' : ↥D) : X) * x⁻¹ = ((c' : ↥D) : X) := by
    calc x * ((c' : ↥D) : X) * x⁻¹
        = (((MulAut.conjNormal (H := Q) x) (c' : ↥D) : ↥Q) : X) :=
          (MulAut.conjNormal_apply (H := Q) x (c' : ↥D)).symm
      _ = (((c' : ↥D) : ↥Q) : X) := congrArg (fun z : ↥Q => (z : X)) h1
  change x * ((c' : ↥D) : X) = ((c' : ↥D) : X) * x
  calc x * ((c' : ↥D) : X)
      = (x * ((c' : ↥D) : X) * x⁻¹) * x := by group
    _ = ((c' : ↥D) : X) * x := by rw [hconj]

theorem isCommutatorModel_of_extraspecial {p : ℕ} [Fact p.Prime] {X : Type} [Group X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    (φ : X →* (Module.End (ZMod p) W)ˣ) (π : Additive ↥D →+ W)
    (ε : ↥(commutator ↥D) ≃* Multiplicative (ZMod p))
    (B : LinearMap.BilinForm (ZMod p) W)
    (hexp : ∀ d : ↥D, d ^ p = 1)
    (hcz : commutator ↥D = Subgroup.center ↥D)
    (hZcard : Nat.card ↥(Subgroup.center ↥D) = p)
    (hπker : ∀ d : ↥D, π (Additive.ofMul d) = 0 ↔ d ∈ Subgroup.center ↥D)
    (hπsurj : Function.Surjective π)
    (hπconj : ∀ (x : X) (d : ↥D), π (Additive.ofMul (MulAut.characteristic D
      (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) (π (Additive.ofMul d)))
    (hform : ∀ a b : ↥D, B (π (Additive.ofMul a)) (π (Additive.ofMul b)) =
      Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)⟩)) :
    IsCommutatorModel p φ B := by
  classical
  haveI hDn : (D.map Q.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hinj : Function.Injective (Q.subtype.comp D.subtype) := fun a b h =>
    D.subtype_injective (Q.subtype_injective h)
  obtain ⟨bar, hbar_sub, hbar_mul, hbar_ker, hbar_surj, hbar_conj⟩ :=
    exists_bar_of_extraspecial φ π hπker hπsurj hπconj
  have hbar_form : ∀ a b : ↥D, B (bar (Q.subtype a)) (bar (Q.subtype b)) =
      Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
    intro a b
    rw [hbar_sub (a : ↥Q) a.2, hbar_sub (b : ↥Q) b.2]
    exact hform a b
  refine ⟨D.map Q.subtype, (Subgroup.center D).map (Q.subtype.comp D.subtype), bar, hDn, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map_of_mem Q.subtype c.2
  · rw [Subgroup.card_map_of_injective hinj]
    exact hZcard
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hd
    rw [← map_pow, show a ^ p = 1 from congrArg Subtype.val (hexp ⟨a, ha⟩), map_one]
  · exact hbar_mul
  · exact hbar_ker
  · exact hbar_surj
  · exact hbar_conj
  · intro a ha b hb hB
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [hbar_form (⟨a', ha'⟩ : ↥D) (⟨b', hb'⟩ : ↥D)] at hB
    have h0 : (⟨⁅(⟨a', ha'⟩ : ↥D), (⟨b', hb'⟩ : ↥D)⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (⟨a', ha'⟩ : ↥D)) (Subgroup.mem_top (⟨b', hb'⟩ : ↥D))⟩ :
        ↥(commutator ↥D)) = 1 := by
      apply ε.injective
      exact Multiplicative.toAdd.injective (hB.trans (by rw [map_one, toAdd_one]))
    have h1 : ⁅(⟨a', ha'⟩ : ↥D), (⟨b', hb'⟩ : ↥D)⁆ = 1 := congrArg Subtype.val h0
    have h2 : a' * b' = b' * a' :=
      congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp h1)
    rw [← map_mul, ← map_mul, h2]
  · exact commutatorModel_centralizer φ π ε B hcz hπconj hform

theorem finrank_frattini_le_three_or {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q]
    (D : Subgroup Q) [D.Characteristic] (hDq : IsPGroup p D)
    [CFSG.IsElementaryAbelian p (D ⧸ frattini D)]
    (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ Subgroup.center D)
    (hrD : CFSG.pRank p D ≤ 3) :
    Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 3 ∨
      (Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) = 4 ∧ Nat.card D = p ^ 5 ∧
        Nat.card (Subgroup.center D) = p ∧ commutator D = Subgroup.center D) := by
  haveI : Finite D := Finite.of_injective D.subtype D.subtype_injective
  have hfr : frattini D = commutator D := CFSG.RankThree.PartTwo.frattini_eq_commutator hDq hexp
  have hfin : Nat.card (Additive (D ⧸ frattini D)) =
      p ^ Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hfin' : Nat.card (D ⧸ commutator D) =
      p ^ Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) := by
    rw [← hfr]
    exact hfin
  have hdim : CFSG.pRank p (D ⧸ commutator D) =
      Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) :=
    (CFSG.RankThree.PartTwo.quotient_commutator_rank Fact.out hexp hfin').2
  obtain ⟨h12, h3, -⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDq hexp hclass
  rcases Nat.lt_or_ge (CFSG.pRank p D) 3 with hlt | hge
  · exact Or.inl (hdim ▸ (h12 (by omega)).trans (by norm_num))
  obtain ⟨i, hi, -⟩ := h3 (le_antisymm hrD hge)
  fin_cases i
  · obtain ⟨-, -, h3'⟩ := hi
    exact Or.inl (hdim ▸ h3'.le)
  · obtain ⟨hD5, hZc, hcz, h4⟩ := hi
    exact Or.inr ⟨hdim ▸ h4, hD5, hZc, hcz⟩
  · obtain ⟨-, -, -, h3'⟩ := hi
    exact Or.inl (hdim ▸ h3'.le)

theorem exists_sympForm_isCommutatorModel {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} [Q.Normal] {D : Subgroup Q} [D.Characteristic]
    (hDq : IsPGroup p D) [CFSG.IsElementaryAbelian p (↥D ⧸ frattini ↥D)]
    (hexp : ∀ d : ↥D, d ^ p = 1) (hcz : commutator ↥D = Subgroup.center ↥D)
    (hZcard : Nat.card ↥(Subgroup.center ↥D) = p)
    (φ : X →* (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ)
    (hφconj : ∀ (x : X) (d : ↥D),
      Additive.ofMul (QuotientGroup.mk' (frattini ↥D)
          (MulAut.characteristic D (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
        Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))
        (Additive.ofMul (QuotientGroup.mk' (frattini ↥D) d))) :
    ∃ B : LinearMap.BilinForm (ZMod p) (Additive (↥D ⧸ frattini ↥D)),
      (∀ u : Additive (↥D ⧸ frattini ↥D), (∀ v, B u v = 0) → u = 0) ∧
      (∀ w, B w w = 0) ∧
      (∀ x : X, ∃ c : ZMod p, ∀ u v : Additive (↥D ⧸ frattini ↥D),
        B (((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
            Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D))) u)
          (((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
            Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D))) v) = c * B u v) ∧
      IsCommutatorModel p φ B := by
  haveI : Finite ↥D := Finite.of_injective D.subtype D.subtype_injective
  have hΦD : frattini ↥D = Subgroup.center ↥D :=
    (CFSG.RankThree.PartTwo.frattini_eq_commutator hDq hexp).trans hcz
  obtain ⟨B, ε, hAlt, hNondeg, hBform, hBsim⟩ :=
    exists_commutatorForm hDq hexp hcz.symm hZcard
  let π : Additive ↥D →+ Additive (↥D ⧸ frattini ↥D) :=
    MonoidHom.toAdditive (QuotientGroup.mk' (frattini ↥D))
  have hπ : ∀ d : ↥D, π (Additive.ofMul d) =
      Additive.ofMul (QuotientGroup.mk' (frattini ↥D) d) := fun d => rfl
  have hπker : ∀ d : ↥D, π (Additive.ofMul d) = 0 ↔ d ∈ Subgroup.center ↥D := by
    intro d
    rw [hπ, ofMul_eq_zero, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hΦD]
  have hπsurj : Function.Surjective π := by
    intro w
    obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective (frattini ↥D) (Additive.toMul w)
    exact ⟨Additive.ofMul d, by rw [hπ, hd]; rfl⟩
  have hπconj : ∀ (x : X) (d : ↥D), π (Additive.ofMul (MulAut.characteristic D
      (MulAut.conjNormal (H := Q) x) d)) =
      ((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
        Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D))) (π (Additive.ofMul d)) := by
    intro x d
    rw [hπ, hπ]
    exact hφconj x d
  have hform : ∀ a b : ↥D, B (π (Additive.ofMul a)) (π (Additive.ofMul b)) =
      Multiplicative.toAdd (ε ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
    intro a b
    rw [hπ, hπ]
    exact hBform a b
  have hφπ : ∀ (x : X) (d : ↥D),
      ((φ x : (Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
        Module.End (ZMod p) (Additive (↥D ⧸ frattini ↥D))) (π (Additive.ofMul d)) =
      Additive.ofMul (quotientAutomorphism (frattini ↥D) (MulAut.characteristic D
        (MulAut.conjNormal (H := Q) x)) (Additive.toMul (π (Additive.ofMul d)))) := by
    intro x d
    rw [hπ]
    rw [show Additive.toMul (Additive.ofMul (QuotientGroup.mk' (frattini ↥D) d)) =
      QuotientGroup.mk' (frattini ↥D) d from rfl, quotientAutomorphism_apply]
    exact (hφconj x d).symm
  refine ⟨B, hNondeg.1, hAlt, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := hBsim (MulAut.characteristic D (MulAut.conjNormal (H := Q) x))
    refine ⟨k, fun u v => ?_⟩
    obtain ⟨a, rfl⟩ : ∃ a, π (Additive.ofMul a) = u := hπsurj u
    obtain ⟨b, rfl⟩ : ∃ b, π (Additive.ofMul b) = v := hπsurj v
    rw [hφπ x a, hφπ x b]
    exact hk _ _
  · exact isCommutatorModel_of_extraspecial φ π ε B hexp hcz hZcard hπker hπsurj hπconj hform

theorem exists_commutatorModel_of_nontrivial {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type}
    [Group X] [Finite X] {Q : Subgroup X} [hQn : Q.Normal] (hQp : IsPGroup p ↥Q)
    (hQ2 : Nontrivial ↥Q) (hC : Subgroup.centralizer (Q : Set X) ≤ CFSG.pCore p X)
    (hQ : CFSG.Open.pRank p Q ≤ 3) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (_ : Module.Finite (ZMod p) W)
      (φ : X →* (Module.End (ZMod p) W)ˣ), φ.ker ≤ CFSG.pCore p X ∧
      (Module.finrank (ZMod p) W ≤ 3 ∨
        (Module.finrank (ZMod p) W = 4 ∧ ∃ B : LinearMap.BilinForm (ZMod p) W,
          (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧ (∀ w : W, B w w = 0) ∧
          (∀ x : X, ∃ c : ZMod p, ∀ u v : W,
            B ((φ x : Module.End (ZMod p) W) u) ((φ x : Module.End (ZMod p) W) v) =
              c * B u v) ∧
          IsCommutatorModel p φ B)) := by
  classical
  obtain ⟨D, hDchar, -, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hp2 hQp
  haveI hDc : D.Characteristic := hDchar
  have hDq : IsPGroup p ↥D := hQp.to_subgroup D
  obtain ⟨-, -, -, hEA, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDq
  haveI hEAi : CFSG.IsElementaryAbelian p (↥D ⧸ frattini ↥D) := hEA
  haveI hEAc : IsMulCommutative (↥D ⧸ frattini ↥D) := hEA.toIsMulCommutative
  obtain ⟨φ, hφker, hφconj⟩ := exists_frattini_representation hDq hDfix
  have hexp : ∀ x : ↥D, x ^ p = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hclass : commutator ↥D ≤ Subgroup.center ↥D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro c
    have hab : ⁅(a : ↥Q), (b : ↥Q)⁆ ∈ D ⊓ Subgroup.centralizer (D : Set ↥Q) :=
      hDcomm (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _))
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp hab.2 c c.2
    simpa only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv] using this
  have hrD : CFSG.pRank p ↥D ≤ 3 := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥Q) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact hQ
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥D) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt le_top).trans h1
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine ⟨Additive (↥D ⧸ frattini ↥D), inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · exact ker_le_pCore_of_exists_pow_mem φ fun x hx => by
      obtain ⟨k, hk⟩ := hφker x (MonoidHom.mem_ker.mp hx)
      exact ⟨k, hC hk⟩
  · rcases finrank_frattini_le_three_or D hDq hexp hclass hrD with h3 | ⟨h4, -, hZcard, hcz⟩
    · exact Or.inl h3
    · obtain ⟨B, hB⟩ := exists_sympForm_isCommutatorModel hDq hexp hcz hZcard φ hφconj
      exact Or.inr ⟨h4, B, hB⟩

theorem exists_commutatorModel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X]
    [Finite X] (hC : Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hQ : CFSG.Open.pRank p (CFSG.pCore p X) ≤ 3) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (_ : Module.Finite (ZMod p) W)
      (φ : X →* (Module.End (ZMod p) W)ˣ), φ.ker ≤ CFSG.pCore p X ∧
      (Module.finrank (ZMod p) W ≤ 3 ∨
        (Module.finrank (ZMod p) W = 4 ∧ ∃ B : LinearMap.BilinForm (ZMod p) W,
          (∀ u : W, (∀ v : W, B u v = 0) → u = 0) ∧ (∀ w : W, B w w = 0) ∧
          (∀ x : X, ∃ c : ZMod p, ∀ u v : W,
            B ((φ x : Module.End (ZMod p) W) u) ((φ x : Module.End (ZMod p) W) v) =
              c * B u v) ∧
          IsCommutatorModel p φ B)) := by
  classical
  let Q : Subgroup X := CFSG.pCore p X
  haveI hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p ↥Q := CFSG.pCore_isPGroup
  rcases subsingleton_or_nontrivial ↥Q with hQ1 | hQ2
  ·
    haveI hQsub : Subsingleton ↥Q := hQ1
    have hQbot : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥Q) = 1 := Subsingleton.elim _ _
      exact congrArg Subtype.val h1
    have hQbot' : CFSG.pCore p X = ⊥ := hQbot
    have htop : (⊤ : Subgroup X) ≤ Q := by
      have h : Subgroup.centralizer (↑(CFSG.pCore p X)) ≤ CFSG.pCore p X := hC
      rw [hQbot'] at h
      rw [show Subgroup.centralizer (↑(⊥ : Subgroup X) : Set X) = ⊤ from by simp] at h
      rw [show Q = ⊤ from hQbot.trans (le_bot_iff.mp h).symm]
    refine ⟨PUnit, inferInstance, inferInstance, inferInstance, 1, ?_, Or.inl ?_⟩
    · rw [MonoidHom.ker_one]
      exact htop
    · exact Module.finrank_zero_of_subsingleton.trans_le (Nat.zero_le 3)
  · exact exists_commutatorModel_of_nontrivial hp2 hQp hQ2 hC hQ

theorem sixThreeOneAt_of_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : LinearListAt p)
    (hS : SympSplitAt p) : SixThreeOneAt p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro X _ _ hC hQ hXrank
  obtain ⟨W, hWac, hWmod, hWfin, φ, hker, hdim⟩ := exists_commutatorModel hp2 hC hQ
  letI : AddCommGroup W := hWac
  letI : Module (ZMod p) W := hWmod
  letI : Module.Finite (ZMod p) W := hWfin
  let H : Subgroup (Module.End (ZMod p) W)ˣ := oPPrimeHull p φ.range
  have hH : oPPrimeHull p H = H := oPPrimeHull_oPPrimeHull p φ.range
  have hHrange : H ≤ φ.range := by
    intro x hx
    exact (Subgroup.closure_le φ.range).mpr (fun y hy => hy.1) hx
  obtain ⟨e⟩ := nonempty_oPPrimeHull_quot_pCore_mulEquiv (p := p) φ hker
  rcases hdim with h3 | ⟨h4, B, hBnd, hBalt, hBsim, hmodel⟩
  · refine SixThreeOneList.of_mulEquiv e.symm (@hL W hWac hWmod hWfin h3 H hH)
  · have hsim : ∀ x ∈ H, ∃ c : ZMod p, ∀ u v : W,
        B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = c * B u v := by
      intro x hx
      obtain ⟨y, hy⟩ := hHrange hx
      obtain ⟨c, hc⟩ := hBsim y
      exact ⟨c, fun u v => by rw [← hy]; exact hc u v⟩
    rcases @hS W hWac hWmod hWfin h4 B hBnd hBalt H hH hsim with hlist | hiso
    · exact SixThreeOneList.of_mulEquiv e.symm hlist
    · obtain ⟨hnegH, E, hEH, hEea, hEcard, π, hπfin, hπB, hEπ⟩ := hiso
      have hneg : -1 ∈ φ.range := hHrange hnegH
      obtain ⟨D, Z, bar, hDn, hZD, hZ, hDp, hbar_mul, hbar_ker, hbar_surj, hbar_conj,
        hcomm, hisoZ⟩ := hmodel
      haveI : D.Normal := hDn
      have hkerp : IsPGroup p φ.ker := by
        refine (CFSG.pCore_isPGroup.to_subgroup (φ.ker.subgroupOf (CFSG.pCore p X))).of_equiv
          (Subgroup.subgroupOfEquivOfLe hker)
      have := four_le_pRank_of_sympModel hp2 B φ hkerp hZD hZ hDp bar hbar_mul hbar_ker
        hbar_surj hbar_conj hcomm hisoZ hneg (hEH.trans hHrange) hEea hEcard hπfin hπB hEπ
      omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
