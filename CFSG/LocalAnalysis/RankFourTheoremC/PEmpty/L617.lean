module

import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Setting
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsTwoInvariantIn IsMaxTwoInvariantIn Prop614Pair)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem isTwoLocal_ne_top (hS : Situation G p P M) {H : Subgroup G} (hH : IsTwoLocal H) :
    H ≠ ⊤ := by
  haveI := hS.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ1, hQ2, rfl⟩ := hH
  intro htop
  have hnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact hQ1 h
  · subst h
    have hG2 : IsPGroup 2 G := hQ2.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent G := hG2.isNilpotent
    have hsolv : Group.IsSolvable G := inferInstance
    obtain ⟨a, b, hab⟩ := hS.nonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)

theorem mem_normalizer_sup {A B' : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B' : Set G)) : g ∈ normalizer ((A ⊔ B' : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ normalizer (A : Set G) → g ∈ normalizer (B' : Set G) →
      ∀ h ∈ A ⊔ B', g * h * g⁻¹ ∈ A ⊔ B' := by
    intro g hgA hgB h hh
    have : A ⊔ B' ≤ (A ⊔ B').comap (MulAut.conj g).toMonoidHom :=
      sup_le (fun h hh => Subgroup.mem_sup_left ((mem_normalizer_iff.mp hgA h).mp hh))
        (fun h hh => Subgroup.mem_sup_right ((mem_normalizer_iff.mp hgB h).mp hh))
    exact this hh
  refine mem_normalizer_iff.mpr fun h => ⟨key g hA hB h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hA) (inv_mem hB) _ hh
  simpa [mul_assoc] using this

theorem not_dvd_card_sup (hp : p.Prime) (hp2 : p ≠ 2) {H O S : Subgroup G} (hOH : O ≤ H)
    (hSH : S ≤ H) (hHO : H ≤ normalizer (O : Set G)) (hO : Nat.Coprime p (Nat.card O))
    (hS2 : IsPGroup 2 S) : ¬ p ∣ Nat.card (O ⊔ S : Subgroup G) := by
  have hOn : (O.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mpr hHO
  have hS' : Nat.Coprime p (Nat.card (S.subgroupOf H)) := by
    obtain ⟨k, hk⟩ := (hS2.comap_subtype : IsPGroup 2 (S.subgroupOf H)).exists_card_eq
    rw [show Nat.card (S.subgroupOf H) = 2 ^ k from hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hO' : Nat.Coprime p (Nat.card (O.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv]
  have hsup := normal_coprime_sup_coprime p (S.subgroupOf H) (O.subgroupOf H) hOn hS' hO'
  have hmap : ((S.subgroupOf H) ⊔ (O.subgroupOf H)).map H.subtype = O ⊔ S := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSH,
      Subgroup.map_subgroupOf_eq_of_le hOH, sup_comm]
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective] at *
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hsup

theorem pCoreOf_le_pCoreOf {H N : Subgroup G} (hNH : N ≤ H) (hQN : pCoreOf 2 H ≤ N) :
    pCoreOf 2 H ≤ pCoreOf 2 N := by
  have hHn := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hQn : ((pCoreOf 2 H).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr (hNH.trans hHn)
  have hQ2 : IsPGroup 2 ((pCoreOf 2 H).subgroupOf N) :=
    (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H).comap_subtype
  have h1 := Subgroup.map_mono (f := N.subtype)
    (CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hQn hQ2)
  rwa [Subgroup.map_subgroupOf_eq_of_le hQN] at h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
