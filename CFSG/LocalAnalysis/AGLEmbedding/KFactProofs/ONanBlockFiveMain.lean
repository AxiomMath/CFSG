module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveA5
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveCenter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Blocks

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_barM_of_isPGroup {M S : Subgroup G} (hS : IsPGroup 2 S) :
    IsPGroup 2 (barM M S) :=
  hS.comap_subtype.map _

theorem le_normalizer_of_barM_le_centralizer {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S)
    (hSM : S ≤ M) (hLM : L ≤ M)
    (h : barM M S ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    L ≤ Subgroup.normalizer (S : Set G) := by
  intro l hl
  apply Subgroup.mem_normalizer_fintype
  intro s hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have h1 : mk ⟨s, hSM hs⟩ ∈ barM M S := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hs)
  have h2 : mk ⟨l, hLM hl⟩ ∈ barM M L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
  have h3 : mk ⟨l, hLM hl⟩ * mk ⟨s, hSM hs⟩ = mk ⟨s, hSM hs⟩ * mk ⟨l, hLM hl⟩ :=
    Subgroup.mem_centralizer_iff.1 (h h1) _ h2
  have h4 : mk (⟨l, hLM hl⟩ * ⟨s, hSM hs⟩ * ⟨l, hLM hl⟩⁻¹) = mk ⟨s, hSM hs⟩ := by
    rw [map_mul, map_mul, map_inv, h3]
    group
  exact coe_mem_of_mk_mem_barM hQS (⟨l, hLM hl⟩ * ⟨s, hSM hs⟩ * ⟨l, hLM hl⟩⁻¹)
    (h4 ▸ h1)

theorem center_eq_bot_of_mulEquiv_alternating_five {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 5)) : Subgroup.center Q = ⊥ := by
  have hc : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  refine eq_bot_iff.mpr fun x hx => ?_
  have hex : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
  rw [hc, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.2 (e.injective (by rw [hex, map_one]))

theorem not_five_dvd_blockPL_of_alt_five (h86 : Asc81bEightSix)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 5)) :
    ¬ 5 ∣ Nat.card (blockPL M S L) := by
  intro h5
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hSM : S ≤ M := hA.twoRadical.1
  have hRQ : barM M S ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M S hK hA (barM M L) hL.component
  have hRc : ¬ barM M S ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun h => hL.not_le_normalizer
      (le_normalizer_of_barM_le_centralizer (twoCore_le_of_hyp hA) hSM hL.le h)
  have hxL : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ barM M L := barM_mono inf_le_right x.2
  have hxR : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨n, hn, hnx⟩ := x.2
    have hnN : (n : G) ∈ Subgroup.normalizer (S : Set G) := (Subgroup.mem_subgroupOf.1 hn).1
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have hnsn : (n : G) * s * (n : G)⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hnN s).1 hsS
    rw [← hnx]
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (n * s * n⁻¹) ∈ barM M S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hnsn)
    simpa using this
  have hx5 : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 5 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have h1 := eq_one_of_five_normalizes_two_group (Q := barM M L) (R := barM M S) e
    (not_five_dvd_card_center_of_alt_five e) hRQ
    (isPGroup_barM_of_isPGroup hA.twoRadical.isPGroup) hRc hxL hxR hx5
  have hx1 : x = 1 := Subtype.ext h1
  rw [hx1, orderOf_one] at hx
  omega

theorem not_five_dvd_blockPL_of_psl_three (hGA : CFSG.Open.GriessAllModelsStatement)
    {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {f : ℕ} (hodd : Odd f)
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) .PSL 3 2 f) :
    ¬ 5 ∣ Nat.card (blockPL M S L) := by
  intro h5
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hPL : Nat.card (blockPL M S L) ∣ Nat.card (barM M L) :=
    Subgroup.card_dvd_of_le (barM_mono inf_le_right)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(barM M L))
  have h5' : 5 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) *
      Nat.card (Subgroup.center ↥(barM M L)) := hcard ▸ h5.trans hPL
  have hf1 : 1 ≤ f := hm.1.2.1
  rcases (Nat.Prime.dvd_mul (by norm_num)).1 h5' with h | h
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projectiveSL hm
    have hdvd : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∣
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.index_dvd_card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K)
    exact not_five_dvd_card_SL_three hK hodd (h.trans hdvd)
  · exact not_five_dvd_card_center_of_psl_three hGA (MulEquiv.refl _) hf1 ⟨hm.1, Or.inl hm⟩ h

theorem hasE9_barM_of_five_dvd (hG2 : LieCyclicG2)
    (h93 : Asc81bNineThree) (h86 : Asc81bEightSix) (hGA : CFSG.Open.GriessAllModelsStatement)
    {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h5 : 5 ∣ Nat.card (blockPL M S L)) : HasE9 ↥(barM M L) := by
  by_contra hno
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5' | h6 | h7 | h8
  · exact hX h1
  · obtain ⟨hcl, T, J, hT, hle, hne, htop, -⟩ := nineThreeTwo_parabolic hA hL hS h2
    rcases lieFiveParabolic_of hG2 _ hcl T J hT hle hne htop with hE | ⟨f, hf, hm⟩ | hA5
    · exact hno (hasE9_of_surjective (QuotientGroup.mk'_surjective _) hE)
    · exact not_five_dvd_blockPL_of_psl_three hGA hL hf hm h5
    · obtain ⟨e⟩ := hA5
      exact not_five_dvd_blockPL_of_alt_five h86 hK hA hL e h5
  · rcases lieFiveOrthogonal _ h3.2.1 with hE | hA5
    · exact hno hE
    · obtain ⟨φ⟩ := hA5
      have hZ : Subgroup.center ↥(barM M L) = ⊥ := center_eq_bot_of_mulEquiv_alternating_five φ
      exact not_five_dvd_blockPL_of_alt_five h86 hK hA hL
        (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans φ) h5
  · exact hno (hasE9_of_nineThree_alt hL (Or.inl h4))
  · exact hno (hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5')))
  · exact hno (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6))))
  · exact hno (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact hno (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inr h8)))))

theorem exists_noncentral_three_of_E9 (hZc : KFactBlockCenterCyclic) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hEL : E ≤ barM M L) (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) :
    ∃ y ∈ barM M L, orderOf y = 3 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  by_contra hno
  push Not at hno
  have hEC : E ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro y hy
    by_cases h1 : y = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · have h3 : y ^ 3 = 1 := hE.2 y hy
      have hord : orderOf y = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h3) with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) h1
        · exact h
      exact hno y (hEL hy) hord
  have hEp : IsPGroup 3 E := fun x => ⟨1, by
    have := hE.2 x x.2
    simpa [Subtype.ext_iff] using this⟩
  exact not_isCyclic_of_isElemAbelian_sq hE hc
    (hZc G M S L hK hA hL hX hS 3 Nat.prime_three (by norm_num) E hEL hEC hEp)

theorem kFactBlockFiveNoncyclic_of_lie (hG2 : LieCyclicG2)
    (h93 : Asc81bNineThree) (h86 : Asc81bEightSix) (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactBlockFiveNoncyclic := by
  intro G _ _ M S L hK hA hL hX hS h5
  obtain ⟨E', hE', hc'⟩ := hasE9_barM_of_five_dvd hG2 h93 h86 hGA hK hA hL hX hS h5
  have hEL : E'.map (barM M L).subtype ≤ barM M L := Subgroup.map_subtype_le E'
  have hE : IsElemAbelian 3 (E'.map (barM M L).subtype) := isElemAbelian_map _ hE'
  have hc : Nat.card (E'.map (barM M L).subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (barM M L).subtype_injective, hc']
  exact ⟨⟨_, hEL, hE, hc⟩, exists_noncentral_three_of_E9
    (kFactBlockCenterCyclic_of_griess h93 hGA) hK hA hL hX hS hEL hE hc⟩

end Blocks

end CFSG.AGLEmbedding.BlockCyc
