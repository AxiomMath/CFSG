module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.ClassesO
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo1
public import Certificates.Certificate214033
public import Certificates.Data.Co1PairSize

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co1Schreier.Native (Rows)
open CFSG.HardMathSupport.Solomon.Coordinator.Co1Pump CFSG.HardMathSupport.Solomon.Coordinator.Co1PairSize
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native (lRows lInvs)
open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census

namespace Co1Pairs

section Numerics

theorem l3Excl_Co1_7_4 : L3Excl 4157776806543360000 7 4 :=
  l3Excl_of_check (B := 300) (by norm_num) (by norm_num) (by decide +kernel)

theorem l3Excl_Co1_5_4 : L3Excl 4157776806543360000 5 4 :=
  l3Excl_of_check (B := 300) (by norm_num) (by norm_num) (by decide +kernel)

theorem noL3Eq_Co1 : NoL3Eq 4157776806543360000 :=
  noL3Eq_of_check (B := 300) (by norm_num) (by decide +kernel)

end Numerics

section Seven

theorem not_seven_sq_dvd {s : ↥GA} (hs : orderOf s = 3) :
    ¬ 7 ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set ↥GA)) := by
  intro h
  haveI : Finite ↥GA := Co1T.finite_GA
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := ↥(Subgroup.centralizer ({s} : Set ↥GA))) 7 h
  let R : Subgroup ↥GA := K.map (Subgroup.centralizer ({s} : Set ↥GA)).subtype
  have hRcard : Nat.card R = 49 := by
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({s} : Set ↥GA)).subtype_injective, hK]
    norm_num
  have hP := Co1S.isPGroup_centralizer_GA Certificates.certificate13696
    Certificates.certificate13697.2.2.2.2.1 R hRcard
  have hs' : s ∈ Subgroup.centralizer (R : Set ↥GA) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro r ⟨c, -, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  obtain ⟨k, hk⟩ := hP ⟨s, hs'⟩
  have h1 : s ^ 7 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : 3 ∣ 7 ^ k := by
    rw [← hs]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

end Seven

section Classes

theorem eE_eq {k : ℕ} {e : List ℕ} (h : (Timmesfeld.Co1Leaf.expVecs 3 6).getD k [] = e) :
    Co1Spor.eE k = Co1T.eltG Co1T.aGA e := by
  rw [Co1Spor.eE, Co1Spor.eExp, h]

theorem pairs_facts :
    (orderOf (Co1Spor.eE 243) = 3 ∧ ∃ a b : ↥GA, a * Co1Spor.eE 243 = Co1Spor.eE 243 * a ∧
      b * Co1Spor.eE 243 = Co1Spor.eE 243 * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      13 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1Spor.eE 81) = 3 ∧ ∃ a b : ↥GA, a * Co1Spor.eE 81 = Co1Spor.eE 81 * a ∧
      b * Co1Spor.eE 81 = Co1Spor.eE 81 * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1Spor.eE 324) = 3 ∧ ∃ a b : ↥GA, a * Co1Spor.eE 324 = Co1Spor.eE 324 * a ∧
      b * Co1Spor.eE 324 = Co1Spor.eE 324 * b ∧ orderOf a = 5 ∧ orderOf b = 5 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) ∧
    (orderOf (Co1T.root 2) = 3 ∧ ∃ a b : ↥GA, a * Co1T.root 2 = Co1T.root 2 * a ∧
      b * Co1T.root 2 = Co1T.root 2 * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set ↥GA))) := by
  rw [eE_eq (k := 243) (e := [1, 0, 0, 0, 0, 0]) (by decide +kernel),
    eE_eq (k := 81) (e := [0, 1, 0, 0, 0, 0]) (by decide +kernel),
    eE_eq (k := 324) (e := [1, 1, 0, 0, 0, 0]) (by decide +kernel)]
  exact Certificates.certificate214033

end Classes

section Main

theorem l3ExclD_Co1_7_13 : L3ExclD 4157776806543360000 7 13 :=
  l3ExclD_of_check (B := 300) (by norm_num) (by norm_num) (by decide +kernel)

theorem noL3Comp_GA (x : ↥GA) (hx : orderOf x = 3) :
    NoL3Comp (Subgroup.centralizer ({x} : Set ↥GA)) := by
  haveI : Finite ↥GA := Co1T.finite_GA
  obtain ⟨k, r, hr, hkr⟩ := Co1Spor.exists_rep hx
  refine noL3Comp_centralizer_of_isConj (x := r) (isConj_iff.2 ⟨k, hkr⟩) ?_
  obtain ⟨⟨o0, a0⟩, ⟨o1, a1⟩, ⟨o2, a2⟩, ⟨o3, a3⟩⟩ := pairs_facts
  have hcard : Nat.card ↥(⊤ : Subgroup ↥GA) = 4157776806543360000 := by
    rw [Subgroup.card_top, card_GA]
  rcases hr with rfl | rfl | rfl | rfl
  · obtain ⟨a, b, ha, hb, hao, hbo, hd⟩ := a0
    refine noL3Comp_of_prime_pair_O (P := ⊤) (q := 7) (d := 13)
      (Co1T.oPrimeCoreTrivialAt_GA _ o0) le_top (by norm_num) (by norm_num) ?_
      (not_seven_sq_dvd o0)
      ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha, b, Subgroup.mem_centralizer_singleton_iff.2 hb,
        hao, hbo, hd⟩
    rw [hcard]
    exact l3ExclD_Co1_7_13
  · obtain ⟨a, b, ha, hb, hao, hbo, hd⟩ := a1
    refine noL3Comp_of_prime_pair (P := ⊤) le_top (q := 7) (k := 4) (by norm_num) (by norm_num) ?_
      (not_seven_sq_dvd o1)
      ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha, b, Subgroup.mem_centralizer_singleton_iff.2 hb,
        hao, hbo, hd⟩
    rw [hcard]
    exact l3Excl_Co1_7_4
  · obtain ⟨a, b, ha, hb, hao, hbo, hd⟩ := a2
    refine noL3Comp_of_prime_pair (P := ⊤) le_top (q := 5) (k := 4) (by norm_num) (by norm_num) ?_
      (Co1Spor.no25_eC Certificates.certificate13670)
      ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha, b, Subgroup.mem_centralizer_singleton_iff.2 hb,
        hao, hbo, hd⟩
    rw [hcard]
    exact l3Excl_Co1_5_4
  · obtain ⟨a, b, ha, hb, hao, hbo, hd⟩ := a3
    refine noL3Comp_of_prime_pair (P := ⊤) le_top (q := 7) (k := 4) (by norm_num) (by norm_num) ?_
      (not_seven_sq_dvd o3)
      ⟨a, Subgroup.mem_centralizer_singleton_iff.2 ha, b, Subgroup.mem_centralizer_singleton_iff.2 hb,
        hao, hbo, hd⟩
    rw [hcard]
    exact l3Excl_Co1_7_4

end Main

end Co1Pairs

private noncomputable def co1Iota (hbr : SporadicBridges) :
    (TauCeti.CFSGIndex.sporadic .Co1).Group ≃* ↥GA :=
  (hbr .Co1).some.symm.trans CFSG.Sporadic.Co1Block.co1MatEquiv

theorem sporL3DownInner_Co1
    (hbr : SporadicBridges) : SporL3DownInner .Co1 := by
  haveI : Finite ↥GA := Co1T.finite_GA
  have hM : Nonempty (↥GA ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) := ⟨(co1Iota hbr).symm⟩
  have h1 := @sporL3DownInner_of_comp .Co1 ↥GA inferInstance inferInstance hM
  have hcard : NoL3Eq (Nat.card ↥GA) := by
    rw [card_GA]
    exact Co1Pairs.noL3Eq_Co1
  exact h1 hcard (fun x hx => Co1Pairs.noL3Comp_GA x hx)

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
