module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableActionGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

noncomputable def actionSubgroupFixed {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (subgroup : Subgroup actor) : Subgroup acted :=
  ⨅ member : subgroup, actionFixedSubgroup (member : actor)

@[expose] noncomputable def actionPlaneFixedGenerated {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted] (prime : ℕ) : Subgroup acted :=
  ⨆ (plane : Subgroup actor) (_ : Nat.card plane = prime ^ 2), actionSubgroupFixed plane

theorem mem_actionSubgroupFixed_iff {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (subgroup : Subgroup actor) (element : acted) :
    element ∈ actionSubgroupFixed subgroup ↔ ∀ member : subgroup, (member : actor) • element = element := by
  simp only [actionSubgroupFixed, Subgroup.mem_iInf]
  rfl

theorem actionSubgroupFixed_antitone {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (first second : Subgroup actor) (hle : first ≤ second) :
    actionSubgroupFixed (acted := acted) second ≤ actionSubgroupFixed first := by
  intro element helement
  apply (mem_actionSubgroupFixed_iff first element).mpr
  intro member
  exact (mem_actionSubgroupFixed_iff second element).mp helement ⟨member, hle member.property⟩

theorem actionFixedGenerated_eq_top_of_plane {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [Group acted] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted] (prime : ℕ) (hprime : prime.Prime)
    (plane : Subgroup actor) (hpower : ∀ member : plane, member ^ prime = 1)
    (hcard : Nat.card plane = prime ^ 2) (hcomplement : ¬prime ∣ Nat.card acted) :
    actionFixedGenerated (actor := actor) (acted := acted) = ⊤ := by
  have htop := solvable_action_fixed_generated_eq_top prime hprime hpower hcard hcomplement
    (actor := plane) (acted := acted)
  apply top_le_iff.mp
  rw [← htop]
  apply iSup_le
  intro member
  apply iSup_le
  intro hne
  have hneActor : (member : actor) ≠ 1 := fun heq => hne (Subtype.ext heq)
  exact le_iSup_of_le (member : actor) (le_iSup_of_le hneActor le_rfl)

theorem actionFixedSubgroup_le_plane_fixed_generated {actor : Type u} {acted : Type v}
    [Group actor] [IsMulCommutative actor] [Finite actor]
    [Group acted] [Finite acted] [Group.IsSolvable acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hcomplement : ¬prime ∣ Nat.card acted)
    (member : actor) (hne : member ≠ 1) :
    actionFixedSubgroup (acted := acted) member ≤ actionPlaneFixedGenerated (actor := actor) prime := by
  classical
  have : Fact prime.Prime := ⟨hprime⟩
  let line := Subgroup.zpowers member
  have hlineCard : Nat.card line = prime := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hpower member) hne]
  let fixed := actionFixedSubgroup (acted := acted) member
  have hinvariant : ∀ other : actor, ∀ element ∈ fixed, other • element ∈ fixed := by
    intro other element helement
    change member • (other • element) = other • element
    rw [← mul_smul, isMulCommutative_iff.mp (inferInstance : IsMulCommutative actor) member other,
      mul_smul]
    exact congrArg (fun value : acted => other • value) helement
  let : MulDistribMulAction actor fixed := invariantSubgroupAction fixed hinvariant
  let actionHom := MulDistribMulAction.toMulAut actor fixed
  have hkernel : line ≤ actionHom.ker := by
    intro other hother
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro element
    apply Subtype.ext
    change other • (element : acted) = (element : acted)
    exact MulAction.mem_stabilizer_iff.mp
      ((Subgroup.zpowers_le_of_mem (MulAction.mem_stabilizer_iff.mpr element.property)) hother)
  let quotientHom := QuotientGroup.mk' line
  let quotientActionHom := QuotientGroup.lift line actionHom hkernel
  let : MulDistribMulAction (actor ⧸ line) fixed :=
    MulDistribMulAction.compHom fixed quotientActionHom
  have hquotientAction : ∀ other : actor, ∀ element : fixed,
      quotientHom other • element = other • element := by
    intro other element
    change (QuotientGroup.lift line actionHom hkernel) (quotientHom other) element = _
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    rfl
  have hquotientPower : ∀ other : actor ⧸ line, other ^ prime = 1 := by
    intro other
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective line other
    rw [← map_pow, hpower, map_one]
  have hquotientCard : Nat.card (actor ⧸ line) = prime ^ 2 := by
    have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup line
    rw [hcard, hlineCard, pow_succ] at hcount
    exact Nat.eq_of_mul_eq_mul_right hprime.pos hcount.symm
  have hfixedComplement : ¬prime ∣ Nat.card fixed :=
    fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card fixed))
  have hfixedTop := solvable_action_fixed_generated_eq_top prime hprime hquotientPower
    hquotientCard hfixedComplement (actor := actor ⧸ line) (acted := fixed)
  have hmapLe : (actionFixedGenerated (actor := actor ⧸ line) (acted := fixed)).map fixed.subtype ≤
      actionPlaneFixedGenerated (actor := actor) (acted := acted) prime := by
    rw [actionFixedGenerated]
    simp only [Subgroup.map_iSup]
    apply iSup_le
    intro quotientMember
    apply iSup_le
    intro hquotientNe
    let quotientLine := Subgroup.zpowers quotientMember
    let plane := quotientLine.comap quotientHom
    have hplaneCard : Nat.card plane = prime ^ 2 := by
      have hquotientLineCard : Nat.card quotientLine = prime := by
        rw [Nat.card_zpowers, orderOf_eq_prime (hquotientPower quotientMember) hquotientNe]
      have hcount := card_map_mul_card_kernel_of_kernel_le quotientHom plane
        (MonoidHom.ker_le_comap quotientHom quotientLine)
      rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective line),
        QuotientGroup.ker_mk', hlineCard, hquotientLineCard] at hcount
      simpa only [pow_two] using hcount.symm
    apply le_iSup_of_le plane
    apply le_iSup_of_le hplaneCard
    rintro element ⟨preimage, hpreimage, rfl⟩
    apply (mem_actionSubgroupFixed_iff plane (preimage : acted)).mpr
    intro other
    have hfixed : quotientHom other • preimage = preimage :=
      MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le_of_mem (MulAction.mem_stabilizer_iff.mpr hpreimage)) other.property)
    rw [hquotientAction] at hfixed
    exact congrArg (fun value : fixed => (value : acted)) hfixed
  rw [hfixedTop] at hmapLe
  intro element helement
  exact hmapLe ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩

theorem solvable_action_plane_fixed_generated_eq_top {actor : Type u} {acted : Type v}
    [Group actor] [IsMulCommutative actor] [Finite actor]
    [Group acted] [Finite acted] [Group.IsSolvable acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 3) (hcomplement : ¬prime ∣ Nat.card acted) :
    actionPlaneFixedGenerated (actor := actor) (acted := acted) prime = ⊤ := by
  have hlarge : prime ^ 2 ≤ Nat.card actor := by
    rw [hcard, pow_succ]
    exact Nat.le_mul_of_pos_right _ hprime.pos
  obtain ⟨plane, hplaneCard⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card hprime (IsPGroup.of_card hcard) hlarge
  have hplanePower : ∀ member : plane, member ^ prime = 1 := by
    intro member
    apply Subtype.ext
    exact hpower member
  have htop := actionFixedGenerated_eq_top_of_plane prime hprime plane hplanePower hplaneCard hcomplement
    (acted := acted)
  apply top_le_iff.mp
  rw [← htop]
  apply iSup_le
  intro member
  apply iSup_le
  intro hne
  exact actionFixedSubgroup_le_plane_fixed_generated prime hprime hpower hcard hcomplement member hne

end CFSG.RankThreeEvenClassification.Helpers
