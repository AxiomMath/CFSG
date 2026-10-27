module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

private theorem isSolvable_sup_of_normal_solvable {X : Type*} [Group X]
    (N₁ N₂ : Subgroup X) [hN₁ : N₁.Normal] [Group.IsSolvable ↥N₁] [Group.IsSolvable ↥N₂] :
    Group.IsSolvable ↥(N₁ ⊔ N₂) := by
  let L : Subgroup X := N₁ ⊔ N₂
  let M : Subgroup ↥L := N₁.subgroupOf L
  haveI hM : M.Normal := Subgroup.normal_subgroupOf
  haveI hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : N₁ ≤ L)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : ↥N₂ →* ↥L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : N₂ ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N₁) (t := N₂)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN₁.conj_mem' a ha b
  haveI : Group.IsSolvable (↥L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient M

theorem lit_solvable_oddCore (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable ↥(CFSG.oddCore X) := by
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (lit_odd_card_oddCore X)

theorem lit_solvable_sup {X : Type*} [Group X] {T P : Subgroup X} [P.Normal]
    (hT : Group.IsSolvable ↥T) (hP : Group.IsSolvable ↥P) : Group.IsSolvable ↥(T ⊔ P) := by
  haveI := hT
  haveI := hP
  rw [sup_comm]
  exact isSolvable_sup_of_normal_solvable P T

theorem lit_solvable_litP {X : Type*} [Group X] [Finite X] {Z : Subgroup X}
    (hZ : ∀ z ∈ Z, ∀ x : X, z * x = x * z) : Group.IsSolvable ↥(litP Z) := by
  have hZsolv : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hZ a a.2 (b : X))
  have hOsolv : Group.IsSolvable ↥(CFSG.oddCore X) := lit_solvable_oddCore X
  change Group.IsSolvable ↥(Z ⊔ CFSG.oddCore X)
  exact lit_solvable_sup (T := Z) (P := CFSG.oddCore X) hZsolv hOsolv

end CFSG.OddStandard.HigherRank.YamadaG23
