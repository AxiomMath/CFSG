module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullBasic
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Dihedral.BrauerSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22Full

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22
open scoped commutatorElement

section OddCore

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem oddCore_eq_pPrimeCore : CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext K
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

theorem odd_card_oddCore : Odd (Nat.card (CFSG.oddCore X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

end OddCore

section Normal

variable {X : Type*} [Group X]

theorem le_normalizer_of_normal (Y : Subgroup X) [hY : Y.Normal] (A : Subgroup X) :
    A ≤ normalizer (Y : Set X) := by
  rw [normalizer_eq_top_iff.mpr hY]
  exact le_top

theorem le_or_le_sup_of_isSimpleGroup {M N Y : Subgroup X} [hMN : (M.subgroupOf N).Normal]
    (hsimple : IsSimpleGroup (↥N ⧸ M.subgroupOf N)) (hYN : Y ≤ N) (hY : (Y.subgroupOf N).Normal) :
    Y ≤ M ∨ N ≤ Y ⊔ M := by
  set π := QuotientGroup.mk' (M.subgroupOf N) with hπ
  have hI : ((Y.subgroupOf N).map π).Normal := hY.map π (QuotientGroup.mk'_surjective _)
  rcases hI.eq_bot_or_eq_top with h | h
  · left
    intro y hy
    have hy' : π ⟨y, hYN hy⟩ = 1 := by
      have : π ⟨y, hYN hy⟩ ∈ (Y.subgroupOf N).map π := ⟨⟨y, hYN hy⟩, hy, rfl⟩
      rwa [h, mem_bot] at this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy'
    exact hy'
  · right
    intro n hn
    have : π ⟨n, hn⟩ ∈ (Y.subgroupOf N).map π := h ▸ mem_top _
    obtain ⟨y, hy, hyn⟩ := this
    have hyn' : (y : ↥N ⧸ M.subgroupOf N) = ((⟨n, hn⟩ : ↥N) : ↥N ⧸ M.subgroupOf N) := hyn
    have hm : y⁻¹ * ⟨n, hn⟩ ∈ M.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff (N := M.subgroupOf N), QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, hyn', inv_mul_cancel]
    have hn' : n = (y : X) * ((y⁻¹ * ⟨n, hn⟩ : ↥N) : X) := by simp
    rw [hn']
    exact mul_mem (mem_sup_left hy) (mem_sup_right hm)

end Normal

section Bender

variable {X : Type} [Group X] [Finite X]

theorem bender_of_normal_quasisimple {A R : Subgroup X} (hA : CFSG.Open.IsQuasisimple ↥A)
    (hAn : A.Normal) (hR : IsPGroup 2 R) (hAR : A ⊔ R = ⊤) {H : Subgroup X}
    (hH : fusionStronglyEmbedded H)
    (hnq : ¬ ∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    A = ⊤ ∧ Odd (Nat.card (center X)) ∧ fusionIsBenderGroup (X ⧸ center X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.Open.bender_strongly_embedded_normal_series X H hH with h | ⟨M, N, hM, hN, hMN, hMN',
    hMo, hNi, hB⟩
  · exact absurd h hnq
  have hsimple : IsSimpleGroup (↥N ⧸ M.subgroupOf N) := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hAeven : Even (Nat.card A) := even_card_of_isQuasisimple hA
  have hNodd : Odd (N.relIndex ⊤) := by rwa [relIndex_top_right]
  have hNtopN : (⊤ : Subgroup X) ≤ normalizer (N : Set X) := le_normalizer_of_normal N ⊤
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 A
  have hAN : A ≤ N := by
    rcases le_or_inf_le_centralizer hA (le_normalizer_of_normal N A) with h | h
    · exact h
    · exfalso
      apply not_le_centralizer_of_isSylowOf hA hS
      exact (le_inf hS.le
        (le_of_isPGroup_of_odd_relIndex le_top hNtopN hNodd le_top hS.isPGroup)).trans h
  have hAM : A ⊓ M ≤ centralizer (A : Set X) := by
    rcases le_or_inf_le_centralizer hA (le_normalizer_of_normal M A) with h | h
    · exfalso
      exact (Nat.not_even_iff_odd.mpr (hMo.of_dvd_nat (card_dvd_of_le h))) hAeven
    · exact h
  have hMC : M ≤ centralizer (A : Set X) := fun m hm =>
    mem_centralizer_of_mem hA (le_normalizer_of_normal M A) hAM
      (le_normalizer_of_normal A ⊤ (mem_top m)) hm
  have hAM' : ¬ A ≤ M := fun h =>
    (Nat.not_even_iff_odd.mpr (hMo.of_dvd_nat (card_dvd_of_le h))) hAeven
  have hNAM : N ≤ A ⊔ M := by
    rcases le_or_le_sup_of_isSimpleGroup hsimple hAN (hAn.subgroupOf N) with h | h
    · exact absurd h hAM'
    · exact h
  have hRN : R ≤ N := le_of_isPGroup_of_odd_relIndex le_top hNtopN hNodd le_top hR
  have hAodd : Odd (A.relIndex (A ⊔ M)) := by
    rw [relIndex_sup_left]
    exact hMo.of_dvd_nat (relIndex_dvd_card A M)
  have hRA : R ≤ A :=
    le_of_isPGroup_of_odd_relIndex le_sup_left (le_normalizer_of_normal A _) hAodd
      (hRN.trans hNAM) hR
  have hAtop : A = ⊤ := top_unique (hAR ▸ sup_le le_rfl hRA)
  have hNtop : N = ⊤ := top_unique (hAtop ▸ hAN)
  have hMZ : M ≤ center X := by
    intro m hm
    rw [mem_center_iff]
    intro x
    exact mem_centralizer_iff.mp (hMC hm) x (hAtop ▸ mem_top x)
  have hZM : center X ≤ M := by
    have hZN : center X ≤ N := hNtop ▸ le_top
    rcases le_or_le_sup_of_isSimpleGroup hsimple hZN
        (Subgroup.normal_subgroupOf : ((center X).subgroupOf N).Normal) with h | h
    · exact h
    · exfalso
      have hZodd : Odd ((center X).relIndex ⊤) := by
        have htop : (center X) ⊔ M = ⊤ := top_unique (hNtop ▸ h)
        rw [← htop, relIndex_sup_left]
        exact hMo.of_dvd_nat (relIndex_dvd_card _ M)
      have hSZ : S ≤ center X :=
        le_of_isPGroup_of_odd_relIndex le_top (le_normalizer_of_normal _ ⊤) hZodd le_top
          hS.isPGroup
      apply not_le_centralizer_of_isSylowOf hA hS
      intro s hs
      rw [mem_centralizer_iff]
      intro a _
      exact (mem_center_iff.mp (hSZ hs) a)
  have hMeq : M = center X := le_antisymm hMZ hZM
  refine ⟨hAtop, hMeq ▸ hMo, ?_⟩
  subst hNtop hMeq
  refine CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv (QuotientGroup.congr _ (center X) Subgroup.topEquiv ?_) hB
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, mem_top x⟩, hx, rfl⟩

end Bender

section Quaternion

variable {X : Type} [Group X] [Finite X]

theorem exists_involution_mem_centralizer {A : Subgroup X} (hA : CFSG.Open.IsQuasisimple ↥A)
    (hAn : A.Normal) (S : Sylow 2 X)
    (hS : IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ t ∈ (S : Subgroup X) ⊓ A, orderOf t = 2 ∧ t ∈ centralizer (A : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSX : IsSylowOf 2 (S : Subgroup X) ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, Sylow.card_eq_multiplicity]
  have hSA : IsSylowOf 2 ((S : Subgroup X) ⊓ A) A :=
    hSX.inf_of_le_normalizer le_top (le_normalizer_of_normal A ⊤)
  have hS1 : (S : Subgroup X) ⊓ A ≠ ⊥ := by
    intro hbot
    apply not_le_centralizer_of_isSylowOf hA hSA
    rw [hbot]
    exact bot_le
  rcases hS with hcyc | ⟨r, hr, hquat⟩
  ·
    exfalso
    have : Group.IsPerfect A := ⟨hA.1⟩
    have : Nontrivial A := by
      obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute hA
      refine ⟨⟨⟨a, ha⟩, 1, fun h => hab ?_⟩⟩
      have : a = 1 := congrArg Subtype.val h
      rw [this, one_mul, mul_one]
    obtain ⟨Q, hQ⟩ := hSA.exists_sylow_eq_subgroupOf
    apply not_isCyclic_sylow_of_isPerfect Q
    have hle : (S : Subgroup X) ⊓ A ≤ S := inf_le_left
    have hcyc' : IsCyclic ↥((S : Subgroup X) ⊓ A) :=
      isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [hQ]
    exact isCyclic_of_surjective (subgroupOfEquivOfLe inf_le_right).symm.toMonoidHom
      (subgroupOfEquivOfLe inf_le_right).symm.surjective
  ·
    have heven : ¬ Odd (Nat.card ↥((S : Subgroup X) ⊓ A)) := by
      intro hodd
      apply hS1
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hSA.isPGroup
      rcases n with _ | n
      · exact card_eq_one.mp (by simpa using hn)
      · rw [hn, pow_succ] at hodd
        exact absurd (Nat.even_mul.mpr (Or.inr even_two)) (Nat.not_even_iff_odd.mpr hodd)
    obtain ⟨t, ht, ht2⟩ := exists_orderOf_eq_two heven
    have htc := CFSG.BrauerSuzuki.brauer_suzuki r hr S hquat t (mem_inf.mp ht).1 ht2
    refine ⟨t, ht, ht2, ?_⟩
    have hO : A ⊓ CFSG.oddCore X ≤ centralizer (A : Set X) := by
      rcases le_or_inf_le_centralizer hA (le_normalizer_of_normal (CFSG.oddCore X) A) with h | h
      · exfalso
        exact (Nat.not_even_iff_odd.mpr (odd_card_oddCore.of_dvd_nat (card_dvd_of_le h)))
          (even_card_of_isQuasisimple hA)
      · exact h
    refine mem_centralizer_of_commutator_mem hA hO fun a ha k => ?_
    have htA : t ∈ A := (mem_inf.mp ht).2
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha (zpow_mem htA k)) (inv_mem ha))
        (inv_mem (zpow_mem htA k))
    · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm, map_zpow, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      exact Commute.zpow_right (mem_center_iff.mp htc (a : X ⧸ CFSG.oddCore X)) k
end Quaternion

end Lemma22Full

end CFSG.ComponentClassification.AS76b
