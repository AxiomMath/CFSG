module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

instance standardComponentOddCore_normal : (standardComponentOddCore G).Normal :=
  sSup_normal _ fun _ hN => hN.1

theorem odd_card_standardComponentOddCore [Finite G] :
    Odd (Nat.card (standardComponentOddCore G)) :=
  DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem le_standardComponentOddCore {N : Subgroup G} (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N ≤ standardComponentOddCore G :=
  le_sSup ⟨hN, hodd⟩

theorem standardComponentOddCore_quotient_eq_bot [Finite G] :
    standardComponentOddCore (G ⧸ standardComponentOddCore G) = ⊥ :=
  DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot

theorem le_of_isPerfect_of_odd_relIndex [Finite G] {A M P : Subgroup G}
    [hn : (A.subgroupOf M).Normal] (hodd : Odd (A.relIndex M)) (hPM : P ≤ M)
    [Group.IsPerfect ↥P] : P ≤ A := by
  let φ : ↥P →* ↥M ⧸ A.subgroupOf M :=
    (QuotientGroup.mk' (A.subgroupOf M)).comp (inclusion hPM)
  have hR : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hRodd : Odd (Nat.card φ.range) := by
    have hq : Nat.card (↥M ⧸ A.subgroupOf M) = A.relIndex M := rfl
    exact (hq ▸ hodd).of_dvd_nat (card_subgroup_dvd_card _)
  have hsolv : Group.IsSolvable φ.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hRodd
  have hbot : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable φ.range hsolv
  intro p hp
  have hmem : φ ⟨p, hp⟩ ∈ φ.range := ⟨⟨p, hp⟩, rfl⟩
  rw [hbot, mem_bot] at hmem
  simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

theorem le_centralizer_of_odd_of_normal [Finite G] {A M : Subgroup G} (hA : Open.IsQuasisimple ↥A)
    (hMA : M ≤ A) (hnorm : A ≤ normalizer (M : Set G)) (hodd : Odd (Nat.card M)) :
    M ≤ centralizer (A : Set G) := by
  have hAp : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA.1
  have hsimp : IsSimpleGroup (↥A ⧸ center ↥A) := hA.2
  let M' : Subgroup ↥A := M.subgroupOf A
  have hM' : M'.Normal := (normal_subgroupOf_iff_le_normalizer hMA).mpr hnorm
  let f := QuotientGroup.mk' (center ↥A)
  have hnormal : (M'.map f).Normal := hM'.map f (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M'.map f) with hbot | htop
  · intro m hm
    have hm' : (⟨m, hMA hm⟩ : ↥A) ∈ center ↥A := by
      rw [← QuotientGroup.ker_mk' (center ↥A), MonoidHom.mem_ker]
      have : f ⟨m, hMA hm⟩ ∈ M'.map f := ⟨⟨m, hMA hm⟩, hm, rfl⟩
      rwa [hbot, mem_bot] at this
    rw [mem_centralizer_iff]
    intro a ha
    have := mem_center_iff.mp hm' ⟨a, ha⟩
    exact congrArg Subtype.val this
  · exfalso
    have hcard : Odd (Nat.card (↥A ⧸ center ↥A)) := by
      have h1 : Nat.card (M'.map f) ∣ Nat.card M' := card_map_dvd _ _
      have h2 : Nat.card M' = Nat.card M := Nat.card_congr (subgroupOfEquivOfLe hMA).toEquiv
      rw [htop, card_top, h2] at h1
      exact hodd.of_dvd_nat h1
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
    have hnt : Nontrivial (↥A ⧸ center ↥A) := hsimp.toNontrivial
    exact Group.IsPerfect.not_isSolvable (↥A ⧸ center ↥A) hsolv

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

theorem exists_four_le_of_two_le_pRank [Finite G] {K : Subgroup G}
    (hK : 2 ≤ Open.pRank 2 K) : ∃ U : Subgroup G, U ≤ K ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := {k : ℕ | ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
  have hne : S.Nonempty := by
    by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    have : Open.pRank 2 K = 0 := by
      change sSup S = 0
      rw [hS, csSup_empty]
      rfl
    omega
  obtain ⟨k, ⟨E, hEK, hE, hEc⟩, hk⟩ := exists_lt_of_lt_csSup hne (by omega : 1 < Open.pRank 2 K)
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hEc]
    exact pow_dvd_pow 2 hk
  obtain ⟨U', hU'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) 2 h4
  refine ⟨U'.map E.subtype, (map_subtype_le U').trans hEK,
    isElemAbelian_of_le hE (map_subtype_le U'), ?_⟩
  rw [card_map_of_injective E.subtype_injective, hU']
  norm_num

theorem standardComponentOddCore_le_centralizer [Finite G] {A : Subgroup G}
    (hA : standardComponentIsStandard A) (hrank : 2 ≤ Open.pRank 2 (centralizer (A : Set G))) :
    standardComponentOddCore G ≤ centralizer (A : Set G) := by
  set N := standardComponentOddCore G
  have hNodd : Odd (Nat.card N) := odd_card_standardComponentOddCore
  obtain ⟨U, hUK, hUab, hU4⟩ := exists_four_le_of_two_le_pRank hrank
  have hK := tightlyEmbedded_centralizer_of_standard hA
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two U N (fun u => Subtype.ext (by simpa using hUab.2 u u.2)) (by rw [hU4]; rfl)
    (fun h => (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h))
    (fun u _ => normalizer_eq_top (H := N) ▸ mem_top u)
  have hNN : N ≤ normalizer (A : Set G) := by
    rw [hgen]
    refine iSup₂_le fun u hu => ?_
    rintro c ⟨-, hc⟩
    have hu1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hcu : c * u = u * c := (mem_centralizer_iff.mp hc u rfl).symm
    have := mem_normalizer_of_commute_of_tightlyEmbedded hK (hUK u.2) hu1 (hUab.2 u u.2) hcu
    rwa [hA.2.2.2.1] at this
  have hcomm : ⁅N, A⁆ ≤ N ⊓ A := by
    rw [commutator_le]
    intro n hn a ha
    rw [commutatorElement_def]
    refine ⟨?_, A.mul_mem ((mem_normalizer_iff.mp (hNN hn) a).mp ha) (A.inv_mem ha)⟩
    have h1 : a * n⁻¹ * a⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem _ (N.inv_mem hn) a
    have := N.mul_mem hn h1
    simpa [mul_assoc] using this
  have hcent : N ⊓ A ≤ centralizer (A : Set G) :=
    le_centralizer_of_odd_of_normal hA.1 inf_le_right
      (fun a ha => by
        rw [mem_normalizer_iff]
        intro x
        rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (le_normalizer ha) x]
        constructor
        · rintro ⟨hxN, hxA⟩
          exact ⟨(inferInstance : N.Normal).conj_mem _ hxN a, hxA⟩
        · rintro ⟨hxN, hxA⟩
          refine ⟨?_, hxA⟩
          have := (inferInstance : N.Normal).conj_mem _ hxN a⁻¹
          simpa [mul_assoc] using this)
      (hNodd.of_dvd_nat (card_dvd_of_le inf_le_left))
  have h1 : ⁅⁅A, N⁆, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hcomm.trans hcent
  have h2 : ⁅⁅N, A⁆, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact hcomm.trans hcent
  have h3 : ⁅⁅A, A⁆, N⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have hAA : ⁅A, A⁆ = A := (Subgroup.isPerfect_iff).mp ((Group.isPerfect_def).2 hA.1.1)
  rw [hAA, commutator_eq_bot_iff_le_centralizer] at h3
  intro n hn
  rw [mem_centralizer_iff]
  intro a ha
  exact (mem_centralizer_iff.mp (h3 ha) n hn).symm

theorem normalizer_sup_eq [Finite G] {A N : Subgroup G} [hN : N.Normal]
    (hodd : Odd (Nat.card N)) (hNA : N ≤ centralizer (A : Set G)) (hAp : commutator ↥A = ⊤) :
    normalizer ((A ⊔ N : Subgroup G) : Set G) = normalizer (A : Set G) := by
  have hAperf : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hAp
  apply le_antisymm
  · intro g hg
    have hAAN : A ≤ A ⊔ N := le_sup_left
    have hnormal : (A.subgroupOf (A ⊔ N)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hAAN).mpr
        (sup_le le_normalizer (hNA.trans (centralizer_le_normalizer _)))
    have hodd' : Odd (A.relIndex (A ⊔ N)) := by
      rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N A]
      exact hodd.of_dvd_nat (relIndex_dvd_card _ _)
    let P := A.map (MulAut.conj g).toMonoidHom
    have hPperf : Group.IsPerfect ↥P := Group.IsPerfect.map (f := (MulAut.conj g).toMonoidHom)
    have hPle : P ≤ A ⊔ N := by
      rintro _ ⟨a, ha, rfl⟩
      exact (mem_normalizer_iff.mp hg a).mp (le_sup_left (b := N) ha)
    have hPA := le_of_isPerfect_of_odd_relIndex hodd' hPle
    have heq : P = A := eq_of_le_of_card_ge hPA (by
      rw [card_map_of_injective (MulAut.conj g).injective])
    rw [mem_normalizer_iff_map_conj_eq]
    exact heq
  · intro g hg
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    rw [mem_normalizer_iff_map_conj_eq] at hg
    have hgN : g ∈ normalizer (N : Set G) := normalizer_eq_top (H := N) ▸ mem_top g
    rw [mem_normalizer_iff_map_conj_eq] at hgN
    rw [hg, hgN]

end CFSG.ComponentClassification.RankTwoSporadic
