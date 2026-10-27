module

public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem quasisimple_nontrivial (G : Type u) [Group G] (hquasi : IsQuasisimple G) :
    Nontrivial G := by
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasi.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial

theorem quasisimple_not_isPGroup (G : Type u) [Group G] [Finite G]
    (hquasi : IsQuasisimple G) (prime : ℕ) (hprime : prime.Prime) : ¬IsPGroup prime G := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Nontrivial G := quasisimple_nontrivial G hquasi
  have : Group.IsPerfect G := ⟨hquasi.1⟩
  exact fun hpgroup => Group.IsPerfect.not_isNilpotent G hpgroup.isNilpotent

theorem normal_pSubgroup_le_center_of_quasisimple {G : Type u} [Group G] [Finite G]
    (hquasi : IsQuasisimple G) (prime : ℕ) (hprime : prime.Prime)
    (subgroup : Subgroup G) (hnormal : subgroup.Normal) (hpgroup : IsPGroup prime subgroup) :
    subgroup ≤ Subgroup.center G := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsPerfect G := ⟨hquasi.1⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasi.2
  let quotient := QuotientGroup.mk' (Subgroup.center G)
  have hmappedNormal : (subgroup.map quotient).Normal :=
    hnormal.map quotient (QuotientGroup.mk'_surjective (Subgroup.center G))
  rcases hmappedNormal.eq_bot_or_eq_top with hbot | htop
  · have hker := (Subgroup.map_eq_bot_iff subgroup).mp hbot
    simpa only [quotient, QuotientGroup.ker_mk'] using hker
  · have hpquotient : IsPGroup prime (G ⧸ Subgroup.center G) := by
      have htopGroup : IsPGroup prime (⊤ : Subgroup (G ⧸ Subgroup.center G)) :=
        htop ▸ hpgroup.map quotient
      exact htopGroup.of_equiv Subgroup.topEquiv
    exact False.elim (Group.IsPerfect.not_isNilpotent
      (G ⧸ Subgroup.center G) hpquotient.isNilpotent)

theorem quasisimple_pCore_le_center (G : Type u) [Group G] [Finite G]
    (hquasi : IsQuasisimple G) (prime : ℕ) (hprime : prime.Prime) :
    pCore prime G ≤ Subgroup.center G := by
  exact normal_pSubgroup_le_center_of_quasisimple hquasi prime hprime
    (pCore prime G) (pCore_normal G prime) (pCore_isPGroup G prime)

theorem perfect_centralizes_of_commutator_central {G : Type u} [Group G]
    (perfectSubgroup subgroup : Subgroup G) (hperfect : Group.IsPerfect perfectSubgroup)
    (hcentral : ⁅perfectSubgroup, subgroup⁆ ≤ Subgroup.centralizer (perfectSubgroup : Set G)) :
    perfectSubgroup ≤ Subgroup.centralizer (subgroup : Set G) := by
  have : Group.IsPerfect perfectSubgroup := hperfect
  have hfirst : ⁅⁅perfectSubgroup, subgroup⁆, perfectSubgroup⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hsecond : ⁅⁅subgroup, perfectSubgroup⁆, perfectSubgroup⁆ = ⊥ := by
    rw [Subgroup.commutator_comm subgroup perfectSubgroup]
    exact hfirst
  have hrotate := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := perfectSubgroup) (H₂ := perfectSubgroup) (H₃ := subgroup) hfirst hsecond
  rw [Subgroup.commutator_eq_self] at hrotate
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrotate

theorem normal_quasisimple_centralizes_normal_pSubgroup {G : Type u} [Group G] [Finite G]
    (quasisimpleSubgroup subgroup : Subgroup G) (hquasi : IsQuasisimple quasisimpleSubgroup)
    (hquasiNormal : quasisimpleSubgroup.Normal) (hnormal : subgroup.Normal)
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime subgroup) :
    quasisimpleSubgroup ≤ Subgroup.centralizer (subgroup : Set G) := by
  have : quasisimpleSubgroup.Normal := hquasiNormal
  have : subgroup.Normal := hnormal
  have hperfect : Group.IsPerfect quasisimpleSubgroup := ⟨hquasi.1⟩
  apply perfect_centralizes_of_commutator_central quasisimpleSubgroup subgroup hperfect
  have hrestriction : (subgroup.subgroupOf quasisimpleSubgroup).Normal := inferInstance
  let inclusion : (subgroup.subgroupOf quasisimpleSubgroup) →* subgroup :=
    { toFun := fun element => ⟨((element : quasisimpleSubgroup) : G), element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective inclusion := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun element : subgroup => (element : G)) heq
  have hrestrictedPGroup : IsPGroup prime (subgroup.subgroupOf quasisimpleSubgroup) :=
    hpgroup.of_injective inclusion hinjective
  have hcenter := normal_pSubgroup_le_center_of_quasisimple hquasi prime hprime
    (subgroup.subgroupOf quasisimpleSubgroup) hrestriction hrestrictedPGroup
  intro element hmem
  have hinf := Subgroup.commutator_le_inf quasisimpleSubgroup subgroup hmem
  have hcentral := hcenter (show (⟨element, hinf.1⟩ : quasisimpleSubgroup) ∈
    subgroup.subgroupOf quasisimpleSubgroup from hinf.2)
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcentral ⟨other, hother⟩)

theorem no_normal_quasisimple_of_selfCentralizing_twoCore {G : Type u} [Group G] [Finite G]
    (hcentralizer : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (subgroup : Subgroup G) (hnormal : subgroup.Normal) : ¬IsQuasisimple subgroup := by
  intro hquasi
  have hcentral := normal_quasisimple_centralizes_normal_pSubgroup subgroup (pCore 2 G)
    hquasi hnormal (pCore_normal G 2) 2 Nat.prime_two (pCore_isPGroup G 2)
  have hpgroup := (pCore_isPGroup G 2).to_le (hcentral.trans hcentralizer)
  exact quasisimple_not_isPGroup subgroup hquasi 2 Nat.prime_two hpgroup

end CFSG.RankThreeEvenClassification.Helpers
