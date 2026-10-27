module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Action
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Normalizes
import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem exists_injective_action_of_weakBlock {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P M S L H : Subgroup G} {z : G} (hPp : IsPGroup p P) (hL : IsWeakSBlock M S L)
    (hNS : Subgroup.normalizer (S : Set G) = H) (hPM : P ≤ M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hz : orderOf z = p) (hzP : z ∈ P)
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers z)
    (hCH : Subgroup.centralizer ({z} : Set G) ≤ H) (hQS : pCoreOf 2 M ≤ S) :
    ∃ φ : ↥P →* MulAut ↥(barM M L), Function.Injective φ ∧ ∀ x : ↥P, φ x = 1 ↔
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hPM x.2⟩ := by
  obtain ⟨φ, hφ⟩ := exists_action_barM hPM hPL
  have hzp : z ^ p = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have hSH : S ≤ H := hNS ▸ Subgroup.le_normalizer
  have hnot : ¬ ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hPM hzP⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hPM hzP⟩ := fun hc =>
    hL.not_le_normalizer (hNS ▸ le_of_barM_centralizes (Fact.out : p.Prime) hp2 hL.le (hPM hzP)
      hzp (hQS.trans hSH) hCH hc)
  exact ⟨φ, injective_action_barM hPp hPM hzP hz huniq hφ hnot, hφ⟩

theorem inf_preimage_centralizer_eq_bot_of_weakBlock {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P M S L H : Subgroup G} {z : G} (hPp : IsPGroup p P) (hL : IsWeakSBlock M S L)
    (hNS : Subgroup.normalizer (S : Set G) = H) (hPM : P ≤ M)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hz : orderOf z = p) (hzP : z ∈ P)
    (huniq : ∀ y ∈ Subgroup.centralizer (P : Set G), y ∈ P → orderOf y = p →
      y ∈ Subgroup.zpowers z)
    (hCH : Subgroup.centralizer ({z} : Set G) ≤ H) (hQS : pCoreOf 2 M ≤ S) :
    P ⊓ ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype = ⊥ := by
  obtain ⟨φ, hinj, hφ⟩ := exists_injective_action_of_weakBlock hp2 hPp hL hNS hPM hPL hz hzP huniq
    hCH hQS
  rw [eq_bot_iff]
  rintro x ⟨hxP, m, hm, rfl⟩
  have h1 : φ ⟨(m : G), hxP⟩ = 1 := (hφ _).mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hm y hy).symm
  have h2 := hinj (h1.trans (map_one φ).symm)
  exact Subgroup.mem_bot.mpr (congrArg (Subtype.val : ↥P → G) h2)

theorem false_of_sylow_three_action (hrank : evenRank G = 3) (h3 : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M S L H : Subgroup G} {z : G} (hM : IsTwoLocal M)
    (hL : IsWeakSBlock M S L) (hNS : Subgroup.normalizer (S : Set G) = H)
    (hPM : (P : Subgroup G) ≤ M) (hPH : (P : Subgroup G) ≤ H)
    (hP3 : Open.pRank 3 (P : Subgroup G) = 3) (hz : orderOf z = 3) (hzP : z ∈ (P : Subgroup G))
    (huniq : ∀ y ∈ Subgroup.centralizer ((P : Subgroup G) : Set G), y ∈ (P : Subgroup G) →
      orderOf y = 3 → y ∈ Subgroup.zpowers z)
    (hCH : Subgroup.centralizer ({z} : Set G) ≤ H) (hQS : pCoreOf 2 M ≤ S)
    (hK : Group.IsSolvable ↥(Subgroup.normalizer (S : Set G) ⊓ L) →
      ¬ 3 ∣ ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf L).index →
      ¬ 27 ∣ Nat.card (MulAut ↥(barM M L)))
    (hsolv : Group.IsSolvable ↥(Subgroup.normalizer (S : Set G) ⊓ L)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPL : (P : Subgroup G) ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_isPGroup_three3 hrank h3 hM hL.toIsTwoPrimeComponent P.isPGroup' hPM
  obtain ⟨φ, hinj, -⟩ := exists_injective_action_of_weakBlock (by norm_num : 3 ≠ 2) P.isPGroup'
    hL hNS hPM hPL hz hzP huniq hCH hQS
  have h27 : 27 ∣ Nat.card (P : Subgroup G) := by
    obtain ⟨E, hEP, -, hE⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
    rw [hP3] at hE
    exact (show 27 = 3 ^ 3 by norm_num) ▸ hE ▸ Subgroup.card_dvd_of_le hEP
  have hdvd : Nat.card (P : Subgroup G) ∣ Nat.card (MulAut ↥(barM M L)) :=
    Subgroup.card_dvd_of_injective φ hinj
  have hsyl := not_dvd_index_inf_of_sylow_top P hPL
  have hidx : ¬ 3 ∣ ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf L).index := fun h =>
    hsyl (h.trans (Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono L
      (inf_le_inf_right L (hNS ▸ hPH)))))
  exact hK hsolv hidx (h27.trans hdvd)

end CFSG.LocalAnalysis.RankThreeTheoremC
