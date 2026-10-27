module

import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.AGLEmbedding.CZeroOrbit

open Subgroup

theorem two_mul_card_lines_add_one {F : Type*} [Group F] [Finite F] (h3 : ∀ x : F, x ^ 3 = 1) :
    2 * Nat.card {ℓ : Subgroup F // Nat.card ℓ = 3} + 1 = Nat.card F := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  have hzp : ∀ x : F, x ≠ 1 → Nat.card (zpowers x) = 3 := fun x hx => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h3 x) hx
  let f : {x : F // x ≠ 1} → {ℓ : Subgroup F // Nat.card ℓ = 3} :=
    fun x => ⟨zpowers x.1, hzp x.1 x.2⟩
  have hfib : ∀ ℓ : {ℓ : Subgroup F // Nat.card ℓ = 3}, Nat.card {x // f x = ℓ} = 2 := by
    intro ℓ
    have e : {x // f x = ℓ} ≃ {y : ↥ℓ.1 // y ≠ 1} :=
      { toFun := fun x => ⟨⟨x.1.1, by
            have h := congrArg Subtype.val x.2
            change zpowers x.1.1 = ℓ.1 at h
            rw [← h]
            exact mem_zpowers _⟩, fun h => x.1.2 (congrArg Subtype.val h)⟩
        invFun := fun y => ⟨⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩, Subtype.ext (by
            change zpowers y.1.1 = ℓ.1
            refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr y.1.2) ?_
            rw [ℓ.2, hzp y.1.1 fun h => y.2 (Subtype.ext h)])⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, ℓ.2]
  have : Finite {ℓ : Subgroup F // Nat.card ℓ = 3} :=
    Finite.of_injective (fun ℓ => ((ℓ.1 : Subgroup F) : Set F))
      fun a b h => Subtype.ext (SetLike.coe_injective h)
  have : Fintype {ℓ : Subgroup F // Nat.card ℓ = 3} := Fintype.ofFinite _
  have hsum : Nat.card {x : F // x ≠ 1} = 2 * Nat.card {ℓ : Subgroup F // Nat.card ℓ = 3} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    simp only [hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card,
      mul_comm]
  have hS : Nat.card {x : F // x ≠ 1} + 1 = Nat.card F := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card]
    have := Nat.card_pos (α := F)
    omega
  omega

@[expose] noncomputable def restrictAut {Y : Type*} [Group Y] (g : MulAut Y) (F : Subgroup Y)
    (h : F.map g.toMonoidHom = F) : MulAut ↥F :=
  (g.subgroupMap F).trans (MulEquiv.subgroupCongr h)

@[simp]
theorem restrictAut_apply {Y : Type*} [Group Y] (g : MulAut Y) (F : Subgroup Y)
    (h : F.map g.toMonoidHom = F) (x : ↥F) : ((restrictAut g F h x : ↥F) : Y) = g x :=
  rfl

@[expose] noncomputable def conjRestrict {Y : Type*} [Group Y] (F : Subgroup Y) :
    ↥(normalizer (F : Set Y)) →* MulAut ↥F where
  toFun n := restrictAut (MulAut.conj (n : Y)) F (mem_normalizer_iff_map_conj_eq.mp n.2)
  map_one' := by
    ext x
    simp
  map_mul' m n := by
    ext x
    change (m * n : Y) * x * (m * n : Y)⁻¹ = m * (n * x * (n : Y)⁻¹) * (m : Y)⁻¹
    group

@[simp]
theorem conjRestrict_apply {Y : Type*} [Group Y] (F : Subgroup Y)
    (n : ↥(normalizer (F : Set Y))) (x : ↥F) :
    ((conjRestrict F n x : ↥F) : Y) = n * x * (n : Y)⁻¹ :=
  rfl

open scoped Pointwise in
@[expose] noncomputable def lines (F : Type*) [Group F] : SubMulAction (MulAut F) (Subgroup F) where
  carrier := {ℓ | Nat.card ℓ = 3}
  smul_mem' g ℓ hℓ := by
    change Nat.card ↥(g • ℓ) = 3
    rw [← SetLike.coe_sort_coe, Subgroup.coe_pointwise_smul, Set.natCard_smul_set,
      SetLike.coe_sort_coe]
    exact hℓ

theorem mem_lines {F : Type*} [Group F] {ℓ : Subgroup F} : ℓ ∈ lines F ↔ Nat.card ℓ = 3 :=
  Iff.rfl

end CFSG.AGLEmbedding.CZeroOrbit
