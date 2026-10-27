module

public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
public import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWXa
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB

open CFSG.Sporadic.Schreier.Tits

section TitsCore

set_option linter.unusedSectionVars false


private theorem prime_eq_of_dvd_titsD {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card titsD) : p = 3 ∨ p = 5 ∨ p = 13 := by
  rw [card_titsD] at h
  have h' : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by
    rwa [show (2 : ℕ) ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 = 17971200 by norm_num]
  rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)) hp2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
        (hp.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1))

private theorem isSolvable_centralizer_of_orderOf_three {x : titsD} (hx : orderOf x = 3) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set titsD)) := by
  obtain ⟨a, b, hcard, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_card_centralizer_of_titsD hx
  haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({x} : Set titsD))
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := a) (b := b) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [Nat.card_eq_fintype_card] at hcard; exact hcard)

private theorem tits_isCyclic_of_card_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ≤ 2) : IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (show Nat.card G = 1 ∨ Nat.card G = 2 by omega) with h1 | h1
  · haveI := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h1

private theorem isSolvable_centralizer_of_orderOf_five {x : titsD} (hx : orderOf x = 5) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set titsD)) := by
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set titsD))))
  have hR := (CFSG.RankThree.PartOne.KE.tits_five_centralizer_two_part_and_plane_centralizer_odd).2.1
    x hx R
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW.isSolvable_of_cyclic_sylow_two R
    (tits_isCyclic_of_card_le_two hR)

private theorem not_thirteen_dvd_card_centralizer_involution {t : titsD} (ht : orderOf t = 2) :
    ¬ 13 ∣ Nat.card (Subgroup.centralizer ({t} : Set titsD)) := by
  rcases titsD_involution_conj t ht with h | h
  · rw [← CFSG.RankThree.PartOne.KE.tits_card_centralizer_eq_of_isConj h, card_centralizer_titsZD]
    norm_num
  · rw [← CFSG.RankThree.PartOne.KE.tits_card_centralizer_eq_of_isConj h,
      (titsD_centralizer_t).2.1]
    norm_num

private theorem isSolvable_centralizer_of_orderOf_thirteen {x : titsD} (hx : orderOf x = 13) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set titsD)) := by
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set titsD))) := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set titsD)) := by omega
    obtain ⟨c, hc⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({x} : Set titsD))) 2 h2
    have ht2 : orderOf (c : titsD) = 2 := by rw [Subgroup.orderOf_coe, hc]
    have hct : (c : titsD) ∈ Subgroup.centralizer ({x} : Set titsD) := c.2
    have hxt : x ∈ Subgroup.centralizer ({(c : titsD)} : Set titsD) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hct ⊢
      exact hct.symm
    have h13 : 13 ∣ Nat.card ↥(Subgroup.centralizer ({(c : titsD)} : Set titsD)) := by
      have := orderOf_dvd_natCard (⟨x, hxt⟩ : ↥(Subgroup.centralizer ({(c : titsD)} : Set titsD)))
      rwa [Subgroup.orderOf_mk, hx] at this
    exact not_thirteen_dvd_card_centralizer_involution ht2 h13
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd

private theorem isSolvable_centralizer_of_orderOf_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : titsD} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set titsD)) := by
  haveI := Fact.mk hp
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hdvd : p ∣ Nat.card titsD := by
    rw [← hord]
    exact orderOf_dvd_natCard x
  rcases prime_eq_of_dvd_titsD hp hp2 hdvd with rfl | rfl | rfl
  · exact isSolvable_centralizer_of_orderOf_three hord
  · exact isSolvable_centralizer_of_orderOf_five hord
  · exact isSolvable_centralizer_of_orderOf_thirteen hord

private theorem perfectInLayer_titsD {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center titsD = ⊥) {γ : MulAut titsD} (hγ : γ ^ p = 1) (hγ1 : γ ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer γ := by
  have hinner : γ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner titsD := by
    obtain ⟨hO, -⟩ := AT_Tits_derived_group_Schreier
    obtain ⟨k, hk⟩ := hO (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ)
    have h1 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hγ, map_one])
    have h2 : orderOf (QuotientGroup.mk'
        (CFSG.ComponentClassification.OuterAutomorphisms.inner titsD) γ) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (QuotientGroup.eq_one_iff γ).1 (orderOf_eq_one_iff.1 h3)
  have hmem : γ ∈ (MulAut.conj : titsD →* MulAut titsD).range := hinner
  obtain ⟨x, rfl, hx, hx1⟩ :=
    CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ hmem hγ hγ1
  apply CFSG.HardMathSupport.Dickson.SuzukiReeB.perfectInLayer_of_isSolvable
  rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
  exact isSolvable_centralizer_of_orderOf_prime hp hp2 hx hx1

end TitsCore

theorem perfectInLayer_tits
    (hv : TauCeti.LieTypeIndex.tits.Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer β := by
  obtain ⟨e⟩ :=
    titsModelEquiv S 2 1 (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, he⟩)
  have hZ : Subgroup.center titsD = ⊥ := by
    rw [← Subgroup.map_center_eq e,
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc, Subgroup.map_bot]
  apply CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_congr e β
  apply perfectInLayer_titsD hp hp2 hZ
  · calc MulAut.congr e β ^ p = MulAut.congr e (β ^ p) := (map_pow _ _ _).symm
      _ = 1 := by rw [hβ, map_one]
  · intro h
    apply hβ1
    apply (MulAut.congr e).injective
    rw [h, map_one]

end CFSG.HardMathSupport.Dickson.SuzukiReeB
