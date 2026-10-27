module

public import CFSG.FeitThompson.OddOrder.ScalarLinesCoordinateEmbedding
public import CFSG.FeitThompson.OddOrder.ReducibleNormalActionFullLineOrbit
public import CFSG.FeitThompson.OddOrder.IrreducibleFieldImageNormOne
public import CFSG.FeitThompson.OddOrder.FixedFreeScalarLinesDeterminantOne
public import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
public import Mathlib.FieldTheory.PrimeField

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Representation

def zmodEquivFin (q : ℕ) [NeZero q] : ZMod q ≃ Fin q where
  toFun i := ⟨i.val, ZMod.val_lt i⟩
  invFun j := ((j : ℕ) : ZMod q)
  left_inv i := ZMod.natCast_rightInverse i
  right_inv j := Fin.ext (ZMod.val_natCast_of_lt j.isLt)

theorem zmodEquivFin_apply_val {q : ℕ} [NeZero q] (i : ZMod q) :
    ((zmodEquivFin q i : Fin q) : ℕ) = i.val := (rfl)

theorem zmodEquivFin_symm_apply {q : ℕ} [NeZero q] (j : Fin q) :
    (zmodEquivFin q).symm j = ((j : ℕ) : ZMod q) := (rfl)

theorem val_add_one_modEq {q : ℕ} [NeZero q] (i : ZMod q) : (i + 1).val ≡ i.val + 1 [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  simp [ZMod.natCast_val, ZMod.cast_id]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem linearGroupRep_eq_coe (A : Subgroup (V ≃ₗ[k] V)) (a : A) :
    linearGroupRep A a = ((a : V ≃ₗ[k] V) : V →ₗ[k] V) := LinearMap.ext fun v => by simp

def ActsReducibly (A : Subgroup (V ≃ₗ[k] V)) : Prop :=
  ∃ W : Submodule k V, (∀ a ∈ A, ∀ v ∈ W, a v ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤

theorem actsReducibly_iff {A : Subgroup (V ≃ₗ[k] V)} :
    ActsReducibly A ↔
      ∃ W : Submodule k V, (∀ a ∈ A, ∀ v ∈ W, a v ∈ W) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := Iff.rfl

theorem actsReducibly_of_invariant {A : Subgroup (V ≃ₗ[k] V)} {W : Submodule k V}
    (hW : ∀ a ∈ A, ∀ v ∈ W, a v ∈ W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) : ActsReducibly A :=
  ⟨W, hW, hW0, hWt⟩

theorem not_actsReducibly_iff [Nontrivial V] {A : Subgroup (V ≃ₗ[k] V)} :
    ¬ ActsReducibly A ↔ (linearGroupRep A).IsIrreducible := by
  rw [isIrreducible_linearGroupRep_iff]
  simp only [actsReducibly_iff, not_exists, not_and, not_ne_iff]
  refine ⟨fun h => ⟨‹_›, fun W hW => ?_⟩, fun h W hW hW0 => ?_⟩
  · by_cases h0 : W = ⊥
    · exact Or.inl h0
    · exact Or.inr (h W hW h0)
  · rcases h.2 W hW with h1 | h1
    · exact absurd h1 hW0
    · exact h1

variable {q : ℕ}

theorem ScalarLineSystem.isInternal (S : ScalarLineSystem k V q) : DirectSum.IsInternal S.L :=
  have := S.neZero_index
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top S.indep_L S.iSup_L

theorem ScalarLineSystem.L_ne_bot (S : ScalarLineSystem k V q) (i : ZMod q) : S.L i ≠ ⊥ := by
  intro hbot
  have h := S.finrank_L i
  rw [hbot, finrank_bot] at h
  omega

theorem ScalarLineSystem.prod_lineScalar_eq_one [Finite k] [NeZero q]
    (S : ScalarLineSystem k V q) (a : S.A) : ∏ i : ZMod q, (S.lineScalar i a : k) = 1 := by
  choose v hv hv0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (S.L_ne_bot i)
  have hli : LinearIndependent k v := iSupIndep.linearIndependent S.L S.indep_L hv hv0
  have hsp : ⊤ ≤ Submodule.span k (Set.range v) := by
    rw [Submodule.span_range_eq_iSup]
    have hspan : ∀ i, k ∙ v i = S.L i := fun i =>
      (eq_span_singleton_of_mem_of_finrank_eq_one (S.finrank_L i) (hv i) (hv0 i)).symm
    simp only [hspan]
    exact le_of_eq S.iSup_L.symm
  let B : Basis (ZMod q) k V := Basis.mk hli hsp
  have : FiniteDimensional k V := B.finiteDimensional_of_finite
  have hdet : LinearMap.det ((a : V ≃ₗ[k] V) : V →ₗ[k] V) = ∏ i, (S.lineScalar i a : k) :=
    det_eq_prod_of_basis_apply_eq_smul B _ _ fun i => by
      simpa [B] using S.apply_eq_lineScalar_smul i a (hv i)
  have h1 := LinearEquiv.det_eq_one_of_mem_normalizer_of_centralizer S.b_mem_normalizer
    S.inf_centralizer_b a.2
  rw [← hdet, ← _root_.LinearEquiv.coe_det, h1, Units.val_one]

theorem ScalarLineSystem.eq_lineScalar_of_apply_eq_smul (S : ScalarLineSystem k V q) (i : ZMod q)
    (a : S.A) {c : k} (hc : ∀ v ∈ S.L i, (a : V ≃ₗ[k] V) v = c • v) :
    c = (S.lineScalar i a : k) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (S.L_ne_bot i)
  have h : c • v = (S.lineScalar i a : k) • v :=
    (hc v hv).symm.trans (S.apply_eq_lineScalar_smul i a hv)
  have h2 : (c - (S.lineScalar i a : k)) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.1 h2 with h' | h'
  · exact sub_eq_zero.1 h'
  · exact absurd h' hv0

structure PrimeDimLinearSetup (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] where
  ne_char : q ≠ p
  finrank_eq : finrank (ZMod p) V = q
  A : Subgroup (V ≃ₗ[ZMod p] V)
  b : V ≃ₗ[ZMod p] V
  A_ne_bot : A ≠ ⊥
  isMulCommutative_A : IsMulCommutative A
  orderOf_b : orderOf b = q
  b_mem_normalizer : b ∈ Subgroup.normalizer (A : Set (V ≃ₗ[ZMod p] V))
  isIrreducible_sup : (linearGroupRep (A ⊔ Subgroup.zpowers b)).IsIrreducible
  inf_centralizer_b : A ⊓ Subgroup.centralizer {b} = ⊥
  finrank_invariants :
    finrank (ZMod p) ↥(Representation.invariants (linearGroupRep (Subgroup.zpowers b))) = 1

namespace PrimeDimLinearSetup

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V] (D : PrimeDimLinearSetup p q V)

instance instIsMulCommutativeA : IsMulCommutative D.A := D.isMulCommutative_A

include D

theorem finiteDimensional : FiniteDimensional (ZMod p) V :=
  FiniteDimensional.of_finrank_pos (by rw [D.finrank_eq]; exact (Fact.out : q.Prime).pos)

theorem nontrivial : Nontrivial V :=
  have := D.finiteDimensional
  Module.nontrivial_of_finrank_pos (R := ZMod p)
    (by rw [D.finrank_eq]; exact (Fact.out : q.Prime).pos)

theorem eq_one_of_commute {a : V ≃ₗ[ZMod p] V} (ha : a ∈ D.A) (hab : a * D.b = D.b * a) :
    a = 1 := by
  have h : a ∈ D.A ⊓ Subgroup.centralizer {D.b} :=
    ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 hab⟩
  rw [D.inf_centralizer_b] at h
  simpa using h

theorem exists_ne_zero_fixed : ∃ s : V, s ≠ 0 ∧ D.b s = s := by
  have hne : Representation.invariants (linearGroupRep (Subgroup.zpowers D.b)) ≠ ⊥ := by
    intro h
    have h2 := D.finrank_invariants
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨s, hs0, mem_invariants_zpowers_iff.1 hs⟩

theorem xor_actsReducibly_isIrreducible :
    Xor (ActsReducibly D.A) ((linearGroupRep D.A).IsIrreducible) := by
  have := D.nontrivial
  rcases em (ActsReducibly D.A) with h | h
  · exact Or.inl ⟨h, fun h2 => not_actsReducibly_iff.2 h2 h⟩
  · exact Or.inr ⟨not_actsReducibly_iff.1 h, h⟩

theorem exists_scalarLineSystem (hred : ActsReducibly D.A) :
    ∃ S : ScalarLineSystem (ZMod p) V q, S.A = D.A ∧ S.b = D.b := by
  classical
  have hfd := D.finiteDimensional
  have hqp : q.Prime := Fact.out
  have hq0 : NeZero q := ⟨hqp.ne_zero⟩
  set X : Subgroup (V ≃ₗ[ZMod p] V) := D.A ⊔ Subgroup.zpowers D.b with hXdef
  set ρ : Representation (ZMod p) X V := linearGroupRep X with hρ
  have hAX : D.A ≤ X := le_sup_left
  have hbX : D.b ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers D.b)
  set A' : Subgroup X := D.A.subgroupOf X with hA'
  have hA'normal : A'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 D.b_mem_normalizer))
  set b' : X := ⟨D.b, hbX⟩ with hb'
  have hb'ord : orderOf b' = q := by rw [hb', Subgroup.orderOf_mk]; exact D.orderOf_b
  have hb'eq : ((b' : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = ρ b' := by
    rw [hρ, linearGroupRep_eq_coe]
  have hsup : A' ⊔ Subgroup.zpowers b' = ⊤ := by
    have h1 : (Subgroup.zpowers D.b).subgroupOf X ≤ Subgroup.zpowers b' := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ⟨n, Subtype.ext (by simpa [hb'] using hn)⟩
    have h2 : A' ⊔ (Subgroup.zpowers D.b).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hAX le_sup_right, ← hXdef, Subgroup.subgroupOf_self]
    exact top_le_iff.mp (h2.ge.trans (sup_le_sup_left h1 A'))
  have hredρ : ∃ W : Submodule (ZMod p) V,
      W ∈ Representation.invtSubmodule (ρ.comp A'.subtype) ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    obtain ⟨W, hW, hW0, hWt⟩ := hred
    refine ⟨W, ?_, hW0, hWt⟩
    rw [mem_invtSubmodule_comp_subtype_iff]
    intro a ha
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [hρ, linearGroupRep_eq_coe]
    exact hW _ (Subgroup.mem_subgroupOf.1 ha) v hv
  obtain ⟨L, hLinvt, hL1, hLint, _⟩ :=
    exists_line_isInternal_zpow_of_reducible (ρ := ρ) hqp (by rw [D.finrank_eq])
      D.isIrreducible_sup hb'ord hsup hredρ
  set M : ZMod q → Submodule (ZMod p) V := fun i => L.map (ρ (b' ^ i.val)) with hM
  set f : Fin q → Submodule (ZMod p) V := fun j => L.map (ρ (b' ^ (j : ℕ))) with hf
  have hMf : M = f ∘ zmodEquivFin q := rfl
  refine ⟨{ prime_index := hqp
            L := M
            finrank_L := fun i => by rw [hM, finrank_map_rho]; exact hL1
            b := D.b
            A := D.A
            indep_L := by
              rw [hMf]; exact hLint.submodule_iSupIndep.comp (zmodEquivFin q).injective
            iSup_L := by
              rw [hMf]
              exact (Equiv.iSup_comp (g := f) (zmodEquivFin q)).trans hLint.submodule_iSup_eq_top
            orderOf_b := D.orderOf_b
            map_b_L := ?_
            A_ne_bot := D.A_ne_bot
            map_L := ?_
            b_mem_normalizer := D.b_mem_normalizer
            inf_centralizer_b := D.inf_centralizer_b }, rfl, rfl⟩
  · intro i
    change (L.map (ρ (b' ^ i.val))).map ((D.b : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V)
      = L.map (ρ (b' ^ (i + 1).val))
    rw [show ((D.b : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = ρ b' from hb'eq, map_rho_map_rho,
      ← pow_succ']
    congr 2
    exact pow_eq_pow_iff_modEq.mpr (by rw [hb'ord]; exact (val_add_one_modEq i).symm)
  · intro a ha i
    have hMinvt : M i ∈ Representation.invtSubmodule (ρ.comp A'.subtype) := by
      rw [hM]; exact map_mem_invtSubmodule_comp_subtype ρ hLinvt _
    have h2 := map_rho_eq_self_of_mem_invtSubmodule hMinvt (a := ⟨a, hAX ha⟩)
      (Subgroup.mem_subgroupOf.2 ha)
    rwa [hρ, linearGroupRep_eq_coe] at h2

theorem reducible_model (hred : ActsReducibly D.A) :
    ∃ (L : ZMod q → Submodule (ZMod p) V) (m : ℕ),
      (∀ i, finrank (ZMod p) (L i) = 1) ∧
      (∀ a ∈ D.A, ∀ i, (L i).map ((a : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = L i) ∧
      (∀ i, (L i).map ((D.b : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = L (i + 1)) ∧
      DirectSum.IsInternal L ∧
      1 < m ∧ m ∣ p - 1 ∧
      (∃ ψ : D.A →* (Fin (q - 1) → Multiplicative (ZMod m)), Function.Injective ψ) ∧
      (∀ a ∈ D.A, ∀ lam : ZMod q → ZMod p,
        (∀ i, ∀ v ∈ L i, (a : V ≃ₗ[ZMod p] V) v = lam i • v) → ∏ i : ZMod q, lam i = 1) := by
  classical
  obtain ⟨S, hSA, hSb⟩ := D.exists_scalarLineSystem hred
  have := S.neZero_index
  have : Fintype (ZMod q) := ZMod.fintype q
  refine ⟨S.L, S.scalarOrder, S.finrank_L, ?_, ?_, S.isInternal, S.one_lt_scalarOrder, ?_, ?_, ?_⟩
  · intro a ha i
    exact S.map_L a (hSA ▸ ha) i
  · intro i
    rw [← hSb]; exact S.map_b_L i
  · simpa [Nat.card_zmod] using S.scalarOrder_dvd_card_sub_one
  · have hle : D.A ≤ S.A := hSA.ge
    refine ⟨S.ratioZModHom.comp (Subgroup.inclusion hle), ?_⟩
    exact S.injective_ratioZModHom.comp (Subgroup.inclusion_injective hle)
  · intro a ha lam hlam
    have ha' : a ∈ S.A := hSA ▸ ha
    have hcoord : ∀ i, lam i = (S.lineScalar i ⟨a, ha'⟩ : ZMod p) := fun i =>
      S.eq_lineScalar_of_apply_eq_smul i ⟨a, ha'⟩ fun v hv => hlam i v hv
    simp only [hcoord]
    exact S.prod_lineScalar_eq_one ⟨a, ha'⟩

section Irreducible

variable [(linearGroupRep D.A).IsIrreducible]

theorem symm_evalEnvelopingSubalgebraEquiv_self {s : V} (hs0 : s ≠ 0) :
    (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm s = 1 := by
  apply (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).injective
  rw [LinearEquiv.apply_symm_apply, evalEnvelopingSubalgebraEquiv_apply]
  rfl

theorem symm_evalEnvelopingSubalgebraEquiv_smul {s : V} (hs0 : s ≠ 0) (a : D.A) (v : V) :
    (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm ((a : V ≃ₗ[ZMod p] V) v) =
      (unitsHom D.A a : ↥(envelopingSubalgebra D.A)) *
        (evalEnvelopingSubalgebraEquiv hs0).symm v := by
  apply (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).injective
  rw [LinearEquiv.apply_symm_apply, evalEnvelopingSubalgebraEquiv_apply]
  have hcoe : (((unitsHom D.A a : ↥(envelopingSubalgebra D.A)) *
        (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm v : ↥(envelopingSubalgebra D.A)) :
      Module.End (ZMod p) V) =
      ((a : V ≃ₗ[ZMod p] V) : Module.End (ZMod p) V) *
        (((evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm v :
          ↥(envelopingSubalgebra D.A)) : Module.End (ZMod p) V) := by
    rw [Subalgebra.coe_mul, coe_unitsHom]
  have hv : (((evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm v :
      ↥(envelopingSubalgebra D.A)) : Module.End (ZMod p) V) s = v := by
    rw [← evalEnvelopingSubalgebraEquiv_apply hs0, LinearEquiv.apply_symm_apply]
  rw [hcoe, Module.End.mul_apply, hv]
  rfl

theorem irreducible_model {s : V} (hs0 : s ≠ 0) (hbs : D.b s = s) :
    IsField ↥(envelopingSubalgebra D.A) ∧
      Nat.card ↥(envelopingSubalgebra D.A) = p ^ q ∧
      (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm s = 1 ∧
      Function.Injective (unitsHom D.A) ∧
      (∀ (a : D.A) (v : V), (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm
          ((a : V ≃ₗ[ZMod p] V) v) = (unitsHom D.A a : ↥(envelopingSubalgebra D.A)) *
            (evalEnvelopingSubalgebraEquiv hs0).symm v) ∧
      (conjEnvelopingHomOfLE (A := D.A) (zpowers_le_normalizer D.b_mem_normalizer)).range = ⊤ ∧
      (evalEnvelopingSubalgebraEquiv (A := D.A) hs0).symm ''
          (Representation.invariants (linearGroupRep (Subgroup.zpowers D.b)) : Set V)
        = Set.range (algebraMap (ZMod p) ↥(envelopingSubalgebra D.A)) ∧
      IsCyclic D.A ∧ Nat.Coprime (Nat.card D.A) (p - 1) ∧
      Nat.card D.A ∣ (p ^ q - 1) / (p - 1) := by
  have hfd := D.finiteDimensional
  have hqp : q.Prime := Fact.out
  have hCA : ∀ a ∈ D.A, a * D.b = D.b * a → a = 1 := fun a ha h => D.eq_one_of_commute ha h
  obtain ⟨-, hcop, hdvd, -, hrange, himage⟩ :=
    fpf_irreducible_field_image_norm (A := D.A) hqp D.finrank_eq D.orderOf_b D.b_mem_normalizer
      hCA hs0 hbs
  refine ⟨isField_envelopingSubalgebra, ?_, D.symm_evalEnvelopingSubalgebraEquiv_self hs0,
    injective_unitsHom, D.symm_evalEnvelopingSubalgebraEquiv_smul hs0, hrange, ?_,
    isCyclic_of_isMulCommutative_of_isIrreducible, hcop, hdvd⟩
  · exact natCard_envelopingSubalgebra_eq_pow D.finrank_eq
  · rw [himage, Subfield.bot_eq_of_zMod_algebra p (K := ↥(envelopingSubalgebra D.A))]
    exact RingHom.coe_fieldRange _

end Irreducible

end PrimeDimLinearSetup

end CFSG.FeitThompson
