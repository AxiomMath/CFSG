module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Mult
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Rank
public import CFSG.RankThree.PartOne.K159F.CenterRankFive
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

open scoped commutatorElement in
theorem kd291_aux_CA_nonab {Q : Type} [Group Q] (hperf : commutator Q = ⊤)
    [IsSimpleGroup (Q ⧸ Subgroup.center Q)] : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a := by
  by_contra hc
  have hc' : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b => by
    by_contra h
    exact hc ⟨a, b, h⟩
  have hcen : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, commutator_le]
    intro g₁ _ g₂ _
    have hmap : ((⁅g₁, g₂⁆ : Q) : Q ⧸ Subgroup.center Q)
        = ⁅(g₁ : Q ⧸ Subgroup.center Q), (g₂ : Q ⧸ Subgroup.center Q)⁆ :=
      map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q)) g₁ g₂
    have h1 : ((⁅g₁, g₂⁆ : Q) : Q ⧸ Subgroup.center Q) = 1 := by
      rw [hmap, commutatorElement_eq_one_iff_mul_comm]
      exact hc' _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  have htop : Subgroup.center Q = ⊤ := by
    have h2 : (⊤ : Subgroup Q) ≤ Subgroup.center Q := by
      rw [← hperf]
      exact hcen
    exact top_le_iff.1 h2
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (Q ⧸ Subgroup.center Q) hsub

theorem kd291_center_bot {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSp : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {Y : Type} [Group Y] [Finite Y] (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (L : Subgroup Y) (hL : IsComponentOf L ⊤) (hZp : IsPGroup p (center ↥L))
    (hY3 : Open.pRank p (⊤ : Subgroup Y) ≤ 3) : center ↥L = ⊥ := by
  by_contra hZ
  obtain ⟨hperf, hsimp⟩ := hL.2.2
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hsimp
  haveI : Fact p.Prime := ⟨hp⟩
  have hnonab : ∃ a b : ↥L ⧸ center ↥L, a * b ≠ b * a := kd291_aux_CA_nonab hperf
  have hcatL : IsCatalogGroup (↥L ⧸ center ↥L) :=
    CFSG.AGLEmbedding.CatalogSimpleSections.surjective_image hcat L
      (QuotientGroup.mk' (center ↥L)) (QuotientGroup.mk'_surjective (N := center ↥L)) hnonab
  have hlu : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.kdMultP5_of_tables hGA hSp p hp hp5 ↥L hL.2.2
      hcatL hZ hZp
  have hquasi : CFSG.IsQuasisimple ↥L := ⟨⟨hperf⟩, hsimp, hnonab⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hZp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hZ
    rw [pow_zero] at hm
    exact Subgroup.card_eq_one.1 hm
  have hpZ : p ∣ Nat.card (center ↥L) := by
    rw [hm]
    exact dvd_pow_self p hm0
  have hodd : Odd (Nat.card (center ↥L)) := by
    rw [hm]
    exact Odd.pow (hp.odd_of_ne_two (by omega))
  have hp3 : 3 < p := by omega
  have hE : CFSG.RankThree.PartOne.K159F.ElemAbFive p ↥L := by
    rcases hlu with ⟨n, K, hK, hfin, hpn, -, ⟨e⟩⟩ | ⟨n, q, K, hK, hfin, hKq, hpn, hpq, ⟨e⟩⟩
    · obtain ⟨r, f, hr, -, hf, hKr⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
      have hn0 : n ≠ 0 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291.ne_zero_of_not_comm n
        (StatedSL n K) e hnonab
      have hpn' : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
      have hn5 : 5 ≤ n := le_trans hp5 hpn'
      have hmod : StatedClassicalModel (↥L ⧸ center ↥L) .PSL n r f := by
        unfold StatedClassicalModel StatedLieAdmissible
        refine ⟨⟨hr, hf, by omega, ?_, ?_⟩, K, hK, hfin, hKr, ⟨e⟩⟩
        · intro h
          have := (Prod.mk.inj h).1
          omega
        · intro h
          have := (Prod.mk.inj h).1
          omega
      exact CFSG.RankThree.PartOne.K159F.exists_elemAbelian_five_of_model hGA hquasi hmod
        hp hp3 hpZ hodd
    · obtain ⟨r, f, hr, -, hf, hKr⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
      obtain ⟨g, -, hqg⟩ : ∃ g ≤ f, q = r ^ g := by
        refine (Nat.dvd_prime_pow hr).1 ?_
        rw [← hKr, hKq]
        exact dvd_pow_self q two_ne_zero
      subst hqg
      have hg : 1 ≤ g := by
        by_contra h0
        have h00 : g = 0 := by omega
        subst h00
        have h2 : p ∣ 2 := by simpa using hpq
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      have hn0 : n ≠ 0 := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291.ne_zero_of_not_comm n
        (StatedSU n (r ^ g) K) e hnonab
      have hpn' : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn
      have hn5 : 5 ≤ n := le_trans hp5 hpn'
      have hmod : StatedClassicalModel (↥L ⧸ center ↥L) .PSU n r g := by
        unfold StatedClassicalModel StatedLieAdmissible
        refine ⟨⟨hr, hg, by omega, ?_⟩, K, hK, hfin, hKq, ⟨e⟩⟩
        intro h
        have := (Prod.mk.inj h).1
        omega
      exact CFSG.RankThree.PartOne.K159F.exists_elemAbelian_five_of_model hGA hquasi hmod
        hp hp3 hpZ hodd
  obtain ⟨B, hBp, hBc, hB⟩ : ∃ B : Subgroup ↥L, (∀ b ∈ B, b ^ p = 1) ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ p ^ 4 ≤ Nat.card B := by
    rcases hE with ⟨B, hBp, hBc, hB⟩ | ⟨-, B, hBp, hBc, hB⟩
    · exact ⟨B, hBp, hBc, le_trans (Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 5)) hB⟩
    · exact ⟨B, hBp, hBc, hB⟩
  have hBpp : IsPGroup p ↥B := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hgpow : g ^ p = 1 := Subtype.ext (hBp g.1 g.2)
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hgpow) with h | h
    · exact ⟨0, by rw [pow_zero, h]⟩
    · exact ⟨1, by rw [pow_one, h]⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hBpp
  have hk4 : 4 ≤ k := by
    rw [hk] at hB
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < p)).1 hB
  have hcomm : ∀ a b : ↥B, a * b = b * a := fun a b => Subtype.ext (hBc a.1 a.2 b.1 b.2)
  have hpow : ∀ a : ↥B, a ^ p = 1 := fun a => Subtype.ext (hBp a.1 a.2)
  have hinj : Function.Injective (L.subtype.comp B.subtype : ↥B →* Y) :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hrank : k ≤ Open.pRank p (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank_of_injective (by omega : 1 < p) hcomm hpow hk _ hinj le_top
  omega

theorem kd291_centralizer_bot {p : ℕ} {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y)
    [L.Normal] (hL : L ≠ ⊥) (hZ : center ↥L = ⊥) {w : Y} (hwo : orderOf w = p) (hp : p.Prime)
    (hw : ∀ N : Subgroup Y, N.Normal → N ≠ ⊥ → w ∈ N) : centralizer (L : Set Y) = ⊥ := by
  by_contra hC
  have hCn : (centralizer (L : Set Y)).Normal := Subgroup.normal_centralizer
  have hwC : w ∈ centralizer (L : Set Y) := hw _ hCn hC
  have hwL : w ∈ L := hw L inferInstance hL
  have hcen : (⟨w, hwL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.mp hwC (g : Y) g.2
    simpa using h
  rw [hZ, Subgroup.mem_bot] at hcen
  have hw1 : w = 1 := congrArg Subtype.val hcen
  rw [hw1, orderOf_one] at hwo
  exact hp.ne_one hwo.symm

theorem kd291_simple_of_center_bot {Y : Type} [Group Y] (L : Subgroup Y)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZ : center ↥L = ⊥) : IsSimpleGroup ↥L := by
  haveI := hq.2
  exact (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).isSimpleGroup

theorem kd291_nonabelian_of_quasisimple {Y : Type} [Group Y] (L : Subgroup Y)
    (hq : CFSG.Open.IsQuasisimple ↥L) : ∃ a b : ↥L, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  have hcomm : commutator ↥L = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro k _
    exact h k g
  rw [hq.1] at hcomm
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥L)).1 inferInstance hcomm

theorem kd291_ne_bot_of_quasisimple {Y : Type} [Group Y] (L : Subgroup Y)
    (hq : CFSG.Open.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro h
  haveI := CFSG.ComponentClassification.Quasisimple.nontrivial hq
  haveI : Subsingleton ↥L := by
    rw [h]
    infer_instance
  exact not_subsingleton ↥L ‹_›

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
