module

public import CFSG.LocalAnalysis.LargeEvenClassification.RankOneAbelian

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem commutative_sup_of_centralizing_normal {Ambient : Type groupUniverse} [Group Ambient]
    (Normal Other : Subgroup Ambient) [Normal.Normal]
    (hnormalCommutative : IsMulCommutative Normal) (hotherCommutative : IsMulCommutative Other)
    (hcentralizes : Other ≤ Subgroup.centralizer (Normal : Set Ambient)) :
    IsMulCommutative (Normal ⊔ Other : Subgroup Ambient) := by
  let : IsMulCommutative Normal := hnormalCommutative
  let : IsMulCommutative Other := hotherCommutative
  apply IsMulCommutative.of_comm
  intro first second
  apply Subtype.ext
  obtain ⟨firstNormal, hfirstNormal, firstOther, hfirstOther, hfirstEq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp first.property
  obtain ⟨secondNormal, hsecondNormal, secondOther, hsecondOther, hsecondEq⟩ :=
    Subgroup.mem_sup_of_normal_left.mp second.property
  change first.val * second.val = second.val * first.val
  rw [← hfirstEq, ← hsecondEq]
  have hcrossFirst : firstOther * secondNormal = secondNormal * firstOther :=
    (Subgroup.mem_centralizer_iff.mp (hcentralizes hfirstOther) secondNormal hsecondNormal).symm
  have hcrossSecond : firstNormal * secondOther = secondOther * firstNormal :=
    Subgroup.mem_centralizer_iff.mp (hcentralizes hsecondOther) firstNormal hfirstNormal
  calc
    firstNormal * firstOther * (secondNormal * secondOther) =
        firstNormal * (firstOther * secondNormal) * secondOther := by simp only [mul_assoc]
    _ = firstNormal * (secondNormal * firstOther) * secondOther := by rw [hcrossFirst]
    _ = secondNormal * firstNormal * (firstOther * secondOther) := by
      rw [← mul_assoc firstNormal secondNormal firstOther,
        setLike_mul_comm hfirstNormal hsecondNormal]
      simp only [mul_assoc]
    _ = secondNormal * (firstNormal * secondOther) * firstOther := by
      rw [setLike_mul_comm hfirstOther hsecondOther]
      simp only [mul_assoc]
    _ = secondNormal * (secondOther * firstNormal) * firstOther := by rw [hcrossSecond]
    _ = secondNormal * secondOther * (firstNormal * firstOther) := by simp only [mul_assoc]

theorem cyclic_pGroup_subgroups_comparable {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] [IsCyclic Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (First Second : Subgroup Ambient) (hcard : Nat.card First ≤ Nat.card Second) : First ≤ Second := by
  let : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨firstRank, hfirstCard⟩ := (hpgroup.to_subgroup First).exists_card_eq
  obtain ⟨secondRank, hsecondCard⟩ := (hpgroup.to_subgroup Second).exists_card_eq
  have hpower : firstRank ≤ secondRank := by
    rw [hfirstCard, hsecondCard] at hcard
    exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcard
  let : CommGroup Ambient := IsCyclic.commGroup
  have hdivides : Nat.card First ∣ Nat.card Second := by
    rw [hfirstCard, hsecondCard]
    exact Nat.pow_dvd_pow prime hpower
  let PowerKernel := (powMonoidHom (Nat.card Second) : Ambient →* Ambient).ker
  have hsecondLe : Second ≤ PowerKernel := by
    intro element helement
    exact congrArg (fun entry : Second => entry.val) (pow_card_eq_one' (x := (⟨element, helement⟩ : Second)))
  have hkernelCard : Nat.card PowerKernel = Nat.card Second := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right Second.card_subgroup_dvd_card]
  have hsecondEq : Second = PowerKernel := Subgroup.eq_of_le_of_card_ge hsecondLe hkernelCard.le
  rw [hsecondEq]
  intro element helement
  obtain ⟨multiplier, hmultiple⟩ := hdivides
  have hpow : element ^ Nat.card First = 1 :=
    congrArg (fun entry : First => entry.val) (pow_card_eq_one' (x := (⟨element, helement⟩ : First)))
  change element ^ Nat.card Second = 1
  rw [hmultiple, pow_mul, hpow, one_pow]

theorem rank_one_centralizing_subgroup_comparable {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (Normal Other : Subgroup Ambient) [Normal.Normal]
    (hnormalCommutative : IsMulCommutative Normal) (hotherCommutative : IsMulCommutative Other)
    (hcentralizes : Other ≤ Subgroup.centralizer (Normal : Set Ambient))
    (hcard : Nat.card Other ≤ Nat.card Normal) : Other ≤ Normal := by
  let Combined := Normal ⊔ Other
  have hcombinedCommutative : IsMulCommutative Combined :=
    commutative_sup_of_centralizing_normal Normal Other hnormalCommutative hotherCommutative hcentralizes
  let : IsCyclic Combined := rank_one_abelian_subgroup_cyclic (⊤ : Subgroup Ambient) Combined le_top
    (hpgroup.to_subgroup ⊤) hrank hcombinedCommutative
  have hotherLe : Other ≤ Combined := le_sup_right
  have hnormalLe : Normal ≤ Combined := le_sup_left
  have hinternalCard : Nat.card (Other.subgroupOf Combined) ≤ Nat.card (Normal.subgroupOf Combined) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hotherLe).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnormalLe).toEquiv]
    exact hcard
  have hinternal := cyclic_pGroup_subgroups_comparable Nat.prime_two (hpgroup.to_subgroup Combined)
    (Other.subgroupOf Combined) (Normal.subgroupOf Combined) hinternalCard
  have hmapped := Subgroup.map_mono (f := Combined.subtype) hinternal
  rw [Subgroup.map_subgroupOf_eq_of_le hotherLe, Subgroup.map_subgroupOf_eq_of_le hnormalLe] at hmapped
  exact hmapped

theorem rank_one_small_order_central {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (element : Ambient) (horder : orderOf element ≤ Nat.card (Subgroup.center Ambient)) :
    element ∈ Subgroup.center Ambient := by
  have hcentralizes : Subgroup.zpowers element ≤ Subgroup.centralizer (Subgroup.center Ambient : Set Ambient) := by
    rw [Subgroup.centralizer_center]
    exact le_top
  have hle := rank_one_centralizing_subgroup_comparable hpgroup hrank (Subgroup.center Ambient)
    (Subgroup.zpowers element) inferInstance inferInstance hcentralizes
      ((Nat.card_zpowers element).le.trans horder)
  exact hle (Subgroup.mem_zpowers element)

theorem cyclic_two_group_involutions_unique {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] [IsCyclic Ambient]
    (first second : Ambient) (hfirst : orderOf first = 2) (hsecond : orderOf second = 2) :
    first = second := by
  let : CommGroup Ambient := IsCyclic.commGroup
  let PowerKernel := (powMonoidHom 2 : Ambient →* Ambient).ker
  have hfirstPow : first ^ 2 = 1 := hfirst ▸ pow_orderOf_eq_one first
  have hsecondPow : second ^ 2 = 1 := hsecond ▸ pow_orderOf_eq_one second
  have hfirstNe : first ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hfirst
    omega
  have hsecondNe : second ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hsecond
    omega
  have hcardLe : Nat.card PowerKernel ≤ 2 := by
    rw [IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right _ (by decide : 0 < 2)
  have hcard : Nat.card PowerKernel = 2 := by
    have hnontrivial : PowerKernel ≠ ⊥ := by
      intro hzero
      exact hfirstNe (Subgroup.mem_bot.mp (hzero ▸ hfirstPow))
    have hcardLarge := (Subgroup.one_lt_card_iff_ne_bot PowerKernel).mpr hnontrivial
    omega
  obtain ⟨other, hotherNe, hunique⟩ := (Nat.card_eq_two_iff' (1 : PowerKernel)).mp hcard
  have hfirstInternal : (⟨first, hfirstPow⟩ : PowerKernel) ≠ 1 := by
    intro hone
    exact hfirstNe (congrArg Subtype.val hone)
  have hsecondInternal : (⟨second, hsecondPow⟩ : PowerKernel) ≠ 1 := by
    intro hone
    exact hsecondNe (congrArg Subtype.val hone)
  exact congrArg (fun entry : PowerKernel => entry.val)
    ((hunique _ hfirstInternal).trans (hunique _ hsecondInternal).symm)

theorem rank_one_involution_central {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient) (hrank : twoRank Ambient ≤ 1)
    (involution : Ambient) (hinvolution : orderOf involution = 2) :
    involution ∈ Subgroup.center Ambient := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnontrivial : Nontrivial Ambient := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsubsingleton
    have hone : involution = 1 := @Subsingleton.elim Ambient hsubsingleton involution 1
    rw [hone, orderOf_one] at hinvolution
    omega
  let := hnontrivial
  have hcenterNe := hpgroup.bot_lt_center
  have hcenterCard := (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center Ambient)).mpr (ne_of_gt hcenterNe)
  exact rank_one_small_order_central hpgroup hrank involution (hinvolution ▸ (by omega))

end CFSG.LargeEvenClassification.Helpers
