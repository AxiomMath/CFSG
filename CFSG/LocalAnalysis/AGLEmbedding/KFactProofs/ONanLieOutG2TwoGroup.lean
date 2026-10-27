module

public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem adjointGroup_closure_involutions
    {τ : Tag} {k : Type} [Field k] [CharP k 2] :
    Subgroup.closure {g : ↥(adjointGroup τ k) | g ^ 2 = 1} = ⊤ := by
  set S : Set (ModGL τ k) := {g | ∃ (i : Fin τ.rank) (c : k),
    (g : Module.End k (RootModule τ k)) = xOp τ k i c ∨
      (g : Module.End k (RootModule τ k)) = yOp τ k i c} with hS
  have hs : ∀ g ∈ S, g ^ 2 = 1 := by
    rintro g ⟨i, c, hg | hg⟩
    · have : g = xUnit τ k i c := Units.ext (by rw [coe_xUnit]; exact hg)
      rw [this, sq, ← xUnit_add, CharTwo.add_self_eq_zero, xUnit_zero]
    · have : g = yUnit τ k i c := Units.ext (by rw [coe_yUnit]; exact hg)
      rw [this, sq, ← CFSG.LieType.Chevalley.yUnit_add, CharTwo.add_self_eq_zero,
        CFSG.LieType.Chevalley.yUnit_zero]
  have htop : Subgroup.closure (((↑) : Subgroup.closure S → ModGL τ k) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  refine top_le_iff.1 ((le_of_eq htop.symm).trans (Subgroup.closure_mono (fun g hg => ?_)))
  have h2 : (g : ModGL τ k) ^ 2 = 1 := hs g.1 hg
  exact Subtype.ext h2

theorem g2Two_exists_perfect {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    ∃ V : Subgroup ↥(adjointGroup .G2 k), ⁅V, V⁆ = V ∧ V ≠ ⊥ := by
  have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds k hk
  rcases hL with ⟨-, hC⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  swap
  all_goals first | exact absurd h0 (by norm_num) | skip
  have hC0 := hC
  obtain ⟨⟨hp3, hm, hn3, hne⟩, F, _, _, hF, ⟨e⟩⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnq : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := by decide
  have hperfS : Group.IsPerfect (StatedSU 3 (3 ^ 1) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl hnq
  have hperfP : Group.IsPerfect (StatedProj (StatedSU 3 (3 ^ 1) F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hperfQ : Group.IsPerfect ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hQnt : Nontrivial ↥⁅adjointGroup .G2 k, adjointGroup .G2 k⁆ :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hC0).1
  set D := adjointGroup .G2 k with hD
  set V : Subgroup ↥D := commutator ↥D with hV
  have hmapV : V.map D.subtype = ⁅D, D⁆ := Subgroup.map_subtype_commutator D
  let eV : ↥V ≃* ↥⁅D, D⁆ :=
    (Subgroup.equivMapOfInjective V D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapV)
  have hperfV : Group.IsPerfect ↥V :=
    Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
  refine ⟨V, Subgroup.isPerfect_iff.1 hperfV, fun hbot => ?_⟩
  have hW0 : ⁅D, D⁆ = ⊥ := by rw [← hmapV, hbot, Subgroup.map_bot]
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥⁅D, D⁆)
  apply hq
  have hq0 : (q : ModGL .G2 k) ∈ (⊥ : Subgroup (ModGL .G2 k)) := hW0 ▸ q.2
  exact Subtype.ext (Subgroup.mem_bot.1 hq0)

end CFSG.AGLEmbedding.LieOut
