module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

theorem pComponent_perfect {G : Type*} [Group G] {p : ℕ} {L : Subgroup G}
    (hL : CFSG.IsPComponent p L) : Group.IsPerfect L := by
  obtain ⟨K, hK, hsubnormal, hmap, hminimal⟩ := hL
  let : Group.IsPerfect K := hK.1.1
  have hderivedNormal : (⁅L, L⁆.subgroupOf L).Normal := by
    have hnormal := (inferInstance : (⁅L, L⁆.subgroupOf (L ⊔ L)).Normal)
    have hsup : L ⊔ L = L := sup_idem L
    rw [hsup] at hnormal
    exact hnormal
  have hderivedSubnormal : ⁅L, L⁆.IsSubnormal :=
    .step _ L (Subgroup.commutator_le_self L) hsubnormal hderivedNormal
  have hderivedMap : ⁅L, L⁆.map (QuotientGroup.mk' (pPrimeCore p G)) = K := by
    rw [Subgroup.map_commutator, hmap]
    exact Subgroup.commutator_eq_self
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self L)
  by_contra hle
  have hlt : ⁅L, L⁆ < L := lt_of_le_of_ne (Subgroup.commutator_le_self L)
    (fun heq => hle (heq.symm.le))
  exact hminimal _ hlt hderivedSubnormal hderivedMap

theorem pComponent_nontrivial {G : Type*} [Group G] {p : ℕ} {L : Subgroup G}
    (hL : CFSG.IsPComponent p L) : Nontrivial L := by
  obtain ⟨K, hK, _, hmap, _⟩ := hL
  let : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.1.2.1
  let : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  apply L.nontrivial_iff_ne_bot.mpr
  intro hbot
  rw [hbot, Subgroup.map_bot] at hmap
  exact K.nontrivial_iff_ne_bot.mp inferInstance hmap.symm

theorem quasisimple_iff_native {G : Type*} [Group G] :
    CFSG.IsQuasisimple G ↔ Open.IsQuasisimple G := by
  constructor
  · rintro ⟨hperfect, hsimple, _⟩
    exact ⟨hperfect.commutator_eq_top, hsimple⟩
  · intro hquasisimple
    let : Group.IsPerfect G := ⟨hquasisimple.1⟩
    let : Group.IsPerfect (G ⧸ Subgroup.center G) := inferInstance
    let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
    refine ⟨inferInstance, inferInstance, ?_⟩
    simpa only [isMulCommutative_iff, not_forall] using
      Group.IsPerfect.not_isMulCommutative (G ⧸ Subgroup.center G)

theorem perfect_le_alternating {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω)) [Group.IsPerfect L] : L ≤ alternatingGroup Ω := by
  calc
    L = ⁅L, L⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ commutator (Equiv.Perm Ω) := Subgroup.commutator_mono le_top le_top
    _ ≤ alternatingGroup Ω := alternatingGroup.commutator_perm_le

theorem five_le_card_of_perfect_nontrivial {Ω : Type*} [Finite Ω]
    (L : Subgroup (Equiv.Perm Ω)) [Group.IsPerfect L] [Nontrivial L] :
    5 ≤ Nat.card Ω := by
  by_contra hsmall
  let : Group.IsSolvable (Equiv.Perm Ω) := Equiv.Perm.isSolvable (by omega)
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem symmetric_perfect_subnormal {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω)) [Group.IsPerfect L] [Nontrivial L]
    (hsubnormal : L.IsSubnormal) : 5 ≤ Nat.card Ω ∧ L = alternatingGroup Ω := by
  have hdegree := five_le_card_of_perfect_nontrivial L
  have hle := perfect_le_alternating L
  have hrestricted := hsubnormal.subgroupOf (K := alternatingGroup Ω)
  rcases hrestricted.eq_bot_or_top_of_isSimpleGroup (alternatingGroup.isSimpleGroup hdegree)
      with hbot | htop
  · have hLbot : L = ⊥ := by
      apply le_bot_iff.mp
      intro member hmember
      have hmem : (⟨member, hle hmember⟩ : alternatingGroup Ω) ∈
          L.subgroupOf (alternatingGroup Ω) := hmember
      rw [hbot] at hmem
      exact congrArg Subtype.val hmem
    exact (L.nontrivial_iff_ne_bot.mp inferInstance hLbot).elim
  · exact ⟨hdegree, le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)⟩

theorem alternating_quasisimple {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hdegree : 5 ≤ Nat.card Ω) : Open.IsQuasisimple (alternatingGroup Ω) := by
  let : IsSimpleGroup (alternatingGroup Ω) := alternatingGroup.isSimpleGroup hdegree
  let : Group.IsPerfect (alternatingGroup Ω) := ⟨commutator_alternatingGroup_eq_top hdegree⟩
  exact Quasisimple.simple_of_perfect _

theorem symmetric_pComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {p : ℕ} (L : Subgroup (Equiv.Perm Ω)) (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card Ω ∧ L = alternatingGroup Ω ∧ CFSG.IsQuasisimple L := by
  let : Group.IsPerfect L := pComponent_perfect hL
  let : Nontrivial L := pComponent_nontrivial hL
  obtain ⟨hdegree, heq⟩ := symmetric_perfect_subnormal L hL.choose_spec.2.1
  refine ⟨hdegree, heq, quasisimple_iff_native.mpr ?_⟩
  exact Components.quasisimple_of_equiv (MulEquiv.subgroupCongr heq)
    (alternating_quasisimple hdegree)

theorem symmetric_twoComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (Equiv.Perm Ω)) (hL : TwoComponents.IsTwoComponent L) :
    5 ≤ Nat.card Ω ∧ L = alternatingGroup Ω ∧ Open.IsQuasisimple L := by
  let : Group.IsPerfect L := ⟨TwoComponents.perfect hL⟩
  let : Nontrivial L := TwoComponents.nontrivial hL
  obtain ⟨hdegree, heq⟩ := symmetric_perfect_subnormal L
    (Components.mathlib_subnormal_of_chain hL.1 .top)
  exact ⟨hdegree, heq, Components.quasisimple_of_equiv (MulEquiv.subgroupCongr heq)
    (alternating_quasisimple hdegree)⟩

theorem symmetric_badSubgroup_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    TwoComponents.badSubgroup (Equiv.Perm Ω) = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  intro L hL
  exact (hL.2 (symmetric_twoComponent L hL.1).2.2).elim

theorem alternating_perfect_subnormal {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (alternatingGroup Ω)) [Group.IsPerfect L] [Nontrivial L]
    (hsubnormal : L.IsSubnormal) : 5 ≤ Nat.card Ω ∧ L = ⊤ := by
  have hdegree : 5 ≤ Nat.card Ω := by
    by_contra hsmall
    let : Group.IsSolvable (alternatingGroup Ω) := alternatingGroup.isSolvable (by omega)
    exact Group.IsPerfect.not_isSolvable L inferInstance
  exact ⟨hdegree, (hsubnormal.eq_bot_or_top_of_isSimpleGroup
    (alternatingGroup.isSimpleGroup hdegree)).resolve_left
      (L.nontrivial_iff_ne_bot.mp inferInstance)⟩

theorem alternating_pComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {p : ℕ} (L : Subgroup (alternatingGroup Ω)) (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card Ω ∧ L = ⊤ ∧ L.map (alternatingGroup Ω).subtype = alternatingGroup Ω ∧
      CFSG.IsQuasisimple L := by
  let : Group.IsPerfect L := pComponent_perfect hL
  let : Nontrivial L := pComponent_nontrivial hL
  obtain ⟨hdegree, heq⟩ := alternating_perfect_subnormal L hL.choose_spec.2.1
  refine ⟨hdegree, heq, ?_, quasisimple_iff_native.mpr ?_⟩
  · rw [heq, Subgroup.map_top, Subgroup.range_subtype]
  · exact Components.quasisimple_of_equiv ((MulEquiv.subgroupCongr heq).trans
      Subgroup.topEquiv) (alternating_quasisimple hdegree)

theorem alternating_twoComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : Subgroup (alternatingGroup Ω)) (hL : TwoComponents.IsTwoComponent L) :
    5 ≤ Nat.card Ω ∧ L = ⊤ ∧ L.map (alternatingGroup Ω).subtype = alternatingGroup Ω ∧
      Open.IsQuasisimple L := by
  let : Group.IsPerfect L := ⟨TwoComponents.perfect hL⟩
  let : Nontrivial L := TwoComponents.nontrivial hL
  obtain ⟨hdegree, heq⟩ := alternating_perfect_subnormal L
    (Components.mathlib_subnormal_of_chain hL.1 .top)
  refine ⟨hdegree, heq, ?_, ?_⟩
  · rw [heq, Subgroup.map_top, Subgroup.range_subtype]
  · exact Components.quasisimple_of_equiv ((MulEquiv.subgroupCongr heq).trans
      Subgroup.topEquiv) (alternating_quasisimple hdegree)

theorem alternating_badSubgroup_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    TwoComponents.badSubgroup (alternatingGroup Ω) = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  intro L hL
  exact (hL.2 (alternating_twoComponent L hL.1).2.2.2).elim

end CFSG.ComponentClassification.CatalogueBAlternating
