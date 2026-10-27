module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

theorem isSolvable_comap_of_isPGroup_ker {L Q : Type} [Group L] [Finite L] [Group Q]
    (pi : L →* Q) (hpi : Function.Surjective pi)
    {BQ : Subgroup Q} (hBQ : Group.IsSolvable ↥BQ)
    (hker : IsPGroup 2 (MonoidHom.ker pi)) :
    Group.IsSolvable ↥(BQ.comap pi) := by
  let f : ↥(BQ.comap pi) →* ↥BQ :=
    { toFun := fun x => ⟨pi x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨l, hl⟩ := hpi (b : Q)
    exact ⟨⟨l, by rw [Subgroup.mem_comap, hl]; exact b.2⟩, Subtype.ext hl⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥(MonoidHom.ker pi) := by
    haveI : Group.IsNilpotent ↥(MonoidHom.ker pi) := IsPGroup.isNilpotent hker
    infer_instance
  have hker_le : MonoidHom.ker pi ≤ BQ.comap pi := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact BQ.one_mem'
  haveI : Group.IsSolvable ↥((MonoidHom.ker pi).subgroupOf (BQ.comap pi)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hker_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hker_le).injective
  have hker_eq : f.ker = (MonoidHom.ker pi).subgroupOf (BQ.comap pi) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hK : Group.IsSolvable ↥(f.ker) := by
    rw [hker_eq]
    infer_instance
  have hq : Group.IsSolvable (↥(BQ.comap pi) ⧸ f.ker) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.surjective
  exact Group.isSolvable_of_subgroup_quotient f.ker

theorem isSolvable_sup_of_isPGroup_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {B T : Subgroup G} (hB : Group.IsSolvable ↥B) (hT : IsPGroup 2 T)
    (hN : T ≤ Subgroup.normalizer (B : Set G)) :
    Group.IsSolvable ↥(B ⊔ T) := by
  have hBY : B ≤ B ⊔ T := le_sup_left
  have hTY : T ≤ B ⊔ T := le_sup_right
  have hBn : (B.subgroupOf (B ⊔ T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := B ⊔ T) (N := B) (sup_le Subgroup.le_normalizer hN)
  have hBs : Group.IsSolvable ↥(B.subgroupOf (B ⊔ T)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hBY).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBY).injective
  have hQ : IsPGroup 2 (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) := by
    refine hT.comap_subtype.of_surjective
      ((QuotientGroup.mk' (B.subgroupOf (B ⊔ T))).comp (T.subgroupOf (B ⊔ T)).subtype) ?_
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : (y : G) ∈ ((B ⊔ T : Subgroup G) : Set G) := y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left B T hN] at hy
    obtain ⟨b, hb, t, ht, hbt⟩ := hy
    refine ⟨⟨⟨t, hTY ht⟩, ht⟩, ?_⟩
    change QuotientGroup.mk (⟨t, hTY ht⟩ : ↥(B ⊔ T)) = QuotientGroup.mk y
    rw [QuotientGroup.eq]
    change t⁻¹ * (y : G) ∈ B
    rw [← hbt, ← mul_assoc]
    exact ((Subgroup.mem_normalizer_iff''.mp (hN ht) b).mp hb)
  have hq : Group.IsSolvable (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) := by
    have := hQ.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (B.subgroupOf (B ⊔ T))

end CFSG.GroupTheory

end
