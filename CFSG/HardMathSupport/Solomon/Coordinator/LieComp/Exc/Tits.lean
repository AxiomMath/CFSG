module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
public import CFSG.CharacterTheory.Burnside
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Sporadic.Schreier.Tits

section TitsCore

set_option linter.unusedSectionVars false


theorem isSolvable_centralizer_of_orderOf_three_titsD {x : titsD} (hx : orderOf x = 3) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set titsD)) := by
  obtain ⟨a, b, hcard, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_card_centralizer_of_titsD hx
  haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({x} : Set titsD))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := a) (b := b) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [Nat.card_eq_fintype_card] at hcard; exact hcard)

theorem isSolvable_fixSubgroup_titsD (hZ : Subgroup.center titsD = ⊥) {γ : MulAut titsD}
    (hγ : γ ^ 3 = 1) (hγ1 : γ ≠ 1) : Group.IsSolvable ↥(fixSubgroup γ) := by
  have hinner : γ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner titsD := by
    obtain ⟨hO, -⟩ := AT_Tits_derived_group_Schreier
    obtain ⟨k, hk⟩ := hO (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ)
    have h1 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hγ, map_one])
    have h2 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime 3 (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three Nat.prime_two).2 (by norm_num))
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff γ).1 (orderOf_eq_one_iff.1 h3)
  have hmem : γ ∈ (MulAut.conj : titsD →* MulAut titsD).range := hinner
  obtain ⟨x, rfl, hx, hx1⟩ :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ hmem hγ hγ1
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
  exact isSolvable_centralizer_of_orderOf_three_titsD hord

end TitsCore

theorem noThreeComponents_tits
    (hv : TauCeti.LieTypeIndex.tits.Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group))
    {β : MulAut S} (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) : NoThreeComponents β := by
  obtain ⟨e⟩ :=
    titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  have hZ : Subgroup.center titsD = ⊥ := by
    rw [← Subgroup.map_center_eq e, b3Lie_center_eq_bot hnc, Subgroup.map_bot]
  have h := isSolvable_fixSubgroup_titsD hZ (γ := MulAut.congr e β)
    (by rw [← map_pow, hβ, map_one])
    (fun h => hβ1 ((MulAut.congr e).injective (by rw [h, map_one])))
  exact noThreeComponents_of_isSolvable β (isSolvable_fixSubgroup_of_congr e h)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
