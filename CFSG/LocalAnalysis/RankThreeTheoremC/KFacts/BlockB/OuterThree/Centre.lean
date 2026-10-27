module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.ClauseO
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreRankRows

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem centre_le_blockPL_of_nineThreeTwo {M S L : Subgroup G} (h2 : NineThreeTwo M S L) :
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
  obtain ⟨-, ⟨-, T, hT, hN⟩, -⟩ := h2
  rintro z ⟨hzL, hzC⟩
  exact hN ⟨hzL, Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (fun t ht => hT.1 ht) hzC)⟩

theorem exists_noncentral_three_of_centrePLRank (hCP : KFactBlockCentrePLRank)
    {M S L : Subgroup G} (hL : IsWeakSBlock M S L) (hconc : NineThreeConclusion M S L)
    (hX : ¬ NineThreeOne L)
    (hSyl : NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L)
    (hZP : barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L))
    (hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨h9, hr⟩ := hCP G M S L hL hconc hX hSyl hsolv hZP hZ
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
    Nat.prime_three (barM M (Subgroup.normalizer (S : Set G) ⊓ L))
  by_contra hcon
  push Not at hcon
  have hEC : E ≤ barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun e he =>
    ⟨barM_mono inf_le_right (hEP he), hcon e (hEP he) (hE.2 e he)⟩
  apply h9
  have hdvd := Subgroup.card_dvd_of_le hEC
  rw [hEcard] at hdvd
  have h32 : (3 : ℕ) ^ 2 ∣
      3 ^ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :=
    pow_dvd_pow 3 hr
  simpa using h32.trans hdvd

theorem exists_noncentral_three_of_tripleA6 {M S L : Subgroup G}
    (h4 : NineThreeFour M S L) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨-, hZ, ⟨e⟩, -, ⟨φ⟩⟩ := h4
  set c : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 with hc
  have hc3 : orderOf c = 3 := orderOf_eq_prime (by decide) (by decide)
  set x := φ.symm c with hx
  obtain ⟨p, hpP, hpx⟩ := Subgroup.mem_map.mp x.2
  have hw3 : orderOf (QuotientGroup.mk' (Subgroup.center ↥(barM M L)) p) = 3 := by
    rw [hpx, Subgroup.orderOf_coe, hx, MulEquiv.orderOf_eq, hc3]
  have hpZ : p ∉ Subgroup.center ↥(barM M L) := fun h => by
    have h1 : QuotientGroup.mk' (Subgroup.center ↥(barM M L)) p = 1 :=
      (QuotientGroup.eq_one_iff p).mpr h
    rw [h1, orderOf_one] at hw3
    omega
  have hp3Z : p ^ 3 ∈ Subgroup.center ↥(barM M L) := by
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥(barM M L)) p) ^ 3 = 1 := by
      rw [← hw3]
      exact pow_orderOf_eq_one _
    rw [← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hp9 : p ^ 9 = 1 := by
    have h1 := pow_card_eq_one' (G := Subgroup.center ↥(barM M L)) (x := ⟨p ^ 3, hp3Z⟩)
    rw [hZ] at h1
    have h2 := congrArg Subtype.val h1
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul] at h2
    exact h2
  have hp1 : p ≠ 1 := fun h => hpZ (h ▸ Subgroup.one_mem _)
  have hord : orderOf p = 3 := by
    have hdvd : orderOf p ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hp9)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have h9 := orderOf_ne_nine_tripleA6 hZ e p
    have h1 : orderOf p ≠ 1 := fun h => hp1 (orderOf_eq_one_iff.mp h)
    interval_cases k
    · rw [pow_zero] at hk'
      exact absurd hk' h1
    · rw [pow_one] at hk'
      exact hk'
    · norm_num at hk'
      exact absurd hk' h9
  refine ⟨(p : ↥M ⧸ CFSG.pCore 2 ↥M), Subgroup.mem_subgroupOf.mp hpP, ?_, fun hC => hpZ ?_⟩
  · have h1 : p ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one p
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  · refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.mp hC (g : ↥M ⧸ CFSG.pCore 2 ↥M) g.2

theorem exists_noncentral_three_of_nineThreeSix {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h6 : NineThreeSix M S L) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨-, n, ⟨e⟩, ⟨φ⟩⟩ := h6
  have h5 : 5 ≤ 2 * n := five_le_of_quasisimple_cover_alt hL.le hL.perfect hL.component.2.2 e
  have h3P : 3 ∣ Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
    have h1 : 3 ∣ Nat.card (Equiv.Perm (Fin n)) := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact Nat.dvd_factorial (by norm_num) (by omega)
    rw [← Nat.card_congr φ.toEquiv] at h1
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3P
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : (y : ↥M ⧸ CFSG.pCore 2 ↥M) ≠ 1 := fun h => by
    have h1 : y = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hy
    omega
  have hy3' : (y : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  refine ⟨y, y.2, hy3', fun hyC => ?_⟩
  exact false_of_central_three_perm _ (y : ↥M ⧸ CFSG.pCore 2 ↥M) hy3' hy1 y.2
    (fun q hq => Subgroup.mem_centralizer_iff.mp hyC q (barM_mono inf_le_right hq)) φ

theorem five_le_of_block_alt {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {N : ℕ}
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) : 5 ≤ N := by
  have hperf : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    (hL.component.2.2).2.toNontrivial
  have : Nontrivial ↥(barM M L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
  exact five_le_of_perfect_alt (Group.isPerfect_def.mp hperf) e

theorem not_three_dvd_centre_of_block_alt {M S L : Subgroup G} (hL : IsWeakSBlock M S L) {N : ℕ}
    (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) :
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) := by
  rw [card_inf_centralizer_eq_card_center, center_eq_bot_of_alt (five_le_of_block_alt hL e) e,
    Subgroup.card_bot]
  norm_num

theorem exists_noncentral_three_of_nineThreeConclusion (hCP : KFactBlockCentrePLRank)
    (hT : CitedBlockTransvectionPLType) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M)
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L)
    (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (hconc : NineThreeConclusion M S L)
    (hsolv : BlockPLThreeSolv M S L)
    (hZ : 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    ∃ y ∈ barM M (Subgroup.normalizer (S : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hSyl := CFSG.HardMathSupport.Curtis.Coordinator.not_isSylowTwoOf_barM hA hL hS
  rcases id hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact exists_noncentral_three_of_centrePLRank hCP hL hconc hX (fun _ => hSyl) hsolv
      (centre_le_blockPL_of_nineThreeTwo h2) hZ
  · obtain ⟨n, -, ⟨e⟩⟩ := exists_alt_of_nineThreeThree hT hK hA hL hX hS h3 hsolv
    exact absurd hZ (not_three_dvd_centre_of_block_alt hL e)
  · exact exists_noncentral_three_of_tripleA6 h4
  · obtain ⟨-, ⟨e⟩, -⟩ := h5
    exact absurd hZ (not_three_dvd_centre_of_block_alt hL e)
  · exact exists_noncentral_three_of_nineThreeSix hL h6
  · obtain ⟨-, n, ⟨e⟩, -⟩ := h7
    exact absurd hZ (not_three_dvd_centre_of_block_alt hL e)
  · exact (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.not_nineThreeEight h8 hsolv).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree
