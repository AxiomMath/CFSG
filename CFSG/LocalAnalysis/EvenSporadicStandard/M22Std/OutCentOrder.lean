module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRest4

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

theorem OuterSituation.card_complement
    (hS : OuterSituation G L z t T₁ F tb Q x L1) {A : Subgroup G} (hLA : L ≤ A)
    (hidx : (L.subgroupOf A).index = 2) : Nat.card A = 887040 := by
  have hLsub : Nat.card (L.subgroupOf A) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv
  have hAL : Nat.card A = Nat.card L * 2 := by
    have := Subgroup.card_mul_index (L.subgroupOf A)
    rw [hidx, hLsub] at this
    exact this.symm
  have hL : Nat.card L = 443520 := by
    obtain ⟨e⟩ := hS.sporadic
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  rw [hAL, hL]

theorem OuterSituation.card_centralizer_z
    (hS : OuterSituation G L z t T₁ F tb Q x L1) :
    Nat.card (centralizer ({z} : Set G)) = 1774080 := by
  obtain ⟨A, hLA, hAH, hzA, hAz, hidx⟩ := hS.complement
  have hz2 : z * z = 1 := hS.data.cfg.z_sq
  have hz1 : z ≠ 1 := hS.data.cfg.z_ne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : zpowers z ≤ centralizer (A : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hAH ha))
  have hdisj : Disjoint A (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro a haA haz
    rcases mem_zpowers_involution hz2 haz with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ haA) hzA
  have hz2' : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  rw [← hAz, ← Nat.card_congr (mulEquivProdSup hcomm hdisj).toEquiv, Nat.card_prod, hz2',
    hS.card_complement hLA hidx]

end CFSG.EvenSporadicStandard.M22Std
