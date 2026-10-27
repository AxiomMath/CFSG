module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
import CFSG.Adapters.TauCetiLieModels
import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev
import CFSG.LieType.SeitzGeneration.ExcCatModels
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ClassicalRankOne
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

@[expose] def List93NonSolvable : Prop :=
  ∀ (Q₀ : Type) [Group Q₀], catalogIs Q₀ (S9.isList93 3) → ¬ Group.IsSolvable Q₀

theorem core3Group_of_benderBorel_of_nonsolvable (hns : List93NonSolvable) {S : Type} [Group S]
    [Finite S] {q k : ℕ} (hB : fusionBenderBorel S q k) : Core3Group S := by
  intro T A hT2 hT hA Q₀ _ ⟨f, hf⟩ hQ
  exfalso
  refine CFSG.QuasithinUnique.Lin2.false_of_benderBorel hB hT hT2 hA fun hsolv => ?_
  haveI := hsolv
  exact hns Q₀ hQ (Group.isSolvable_of_surjective hf)

private theorem primePower_p_eq_two {q : PrimePower} {m : ℕ} (h : q.card = 2 ^ (m + 1)) :
    q.p = 2 := by
  have h1 : q.p ∣ 2 ^ (m + 1) := by
    rw [← h, PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)

theorem fusionIsBenderGroup_of_catalog_A1 {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) : fusionIsBenderGroup S := by
  have hm : StatedClassicalModel S .PSL 2 q.p q.exponent :=
    (CFSG.Models.lieModel_A 1 q hv e).2.resolve_right fun h => absurd h.1 (by norm_num)
  rw [hq] at hm
  exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSL_two hm

theorem fusionIsBenderGroup_of_catalog_twistedA2 {S : Type} [Group S] {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p = 2)
    (e : S ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : fusionIsBenderGroup S := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hq] at hm
  exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSU_three hm

theorem finite_fusionIsBenderGroup_of_SU3cover {Q : Type} [Group Q] {n : ℕ} (hn : 1 < n)
    (h : FullLinearCover true 3 (2 ^ n) Q) :
    Finite (Q ⧸ Subgroup.center Q) ∧ fusionIsBenderGroup (Q ⧸ Subgroup.center Q) := by
  obtain ⟨K, _, hKfin, hcard, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdq : ((3 : ℕ), 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hcen := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := n)
    hcard (le_refl 3) hdq).2
  let eQ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSU 3 (2 ^ n) K) :=
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
      (QuotientGroup.quotientMulEquivOfEq hcen)
  refine ⟨Finite.of_equiv _ eQ.symm.toEquiv, ?_⟩
  exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSU_three
    (f := n) ⟨⟨Nat.prime_two, by omega, le_refl 3, hdq⟩, K, inferInstance, hKfin, hcard, ⟨eQ⟩⟩

theorem core3At_L2two_of_nonsolvable (hns : List93NonSolvable) :
    Core3At fun d => ∃ q : PrimePower, d = .A 1 q ∧ q.p = 2 := by
  rintro ⟨d, hv⟩ ⟨q, rfl, hq⟩ S _ _ ⟨e⟩
  obtain ⟨_, _, hB⟩ := CFSG.QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup
    (fusionIsBenderGroup_of_catalog_A1 hv hq e)
  exact core3Group_of_benderBorel_of_nonsolvable hns hB

theorem core3At_U3two_of_nonsolvable (hns : List93NonSolvable) :
    Core3At fun d => ∃ q : PrimePower, d = .twistedA 2 q ∧ q.p = 2 := by
  rintro ⟨d, hv⟩ ⟨q, rfl, hq⟩ S _ _ ⟨e⟩
  obtain ⟨_, _, hB⟩ := CFSG.QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup
    (fusionIsBenderGroup_of_catalog_twistedA2 hv hq e)
  exact core3Group_of_benderBorel_of_nonsolvable hns hB

theorem core3Group_of_SU3cover_of_nonsolvable (hns : List93NonSolvable) {Q : Type} [Group Q]
    {n : ℕ} (hn : 1 < n) (h : FullLinearCover true 3 (2 ^ n) Q) :
    Core3Group (Q ⧸ Subgroup.center Q) := by
  obtain ⟨hfin, hB⟩ := finite_fusionIsBenderGroup_of_SU3cover hn h
  obtain ⟨_, _, hB'⟩ :=
    CFSG.QuasithinUnique.Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup hB
  exact core3Group_of_benderBorel_of_nonsolvable hns hB'

private theorem finite_isSimpleGroup_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Models.LieModel G t n p f) : Finite G ∧ IsSimpleGroup G := by
  have hm : StatedClassicalModel G t n p f := h.2.resolve_right fun h' => hn h'.1
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Simplicity.fam_classical_converse G ⟨t, n, p, f, hm⟩
  exact ⟨hfin, hs⟩

section Certs

theorem list93NonSolvable_holds : List93NonSolvable := by
  intro Q₀ _ h
  obtain ⟨⟨d, hv⟩, ⟨e⟩, hshape⟩ := list93three_cases h
  obtain ⟨hfin, hsimp, hchar⟩ : Finite Q₀ ∧ IsSimpleGroup Q₀ ∧ d.characteristic = 2 := by
    rcases hshape with ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ | ⟨q, hd, hq⟩ |
      ⟨q, hd, hq⟩ | hd | ⟨q, hd, hq, -⟩ | ⟨q, hd, hq, -⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 0) (hq.trans (by norm_num))
      have hfs := finite_isSimpleGroup_of_lieModel (by norm_num)
        (CFSG.Models.lieModel_D 4 q hv e)
      exact ⟨hfs.1, hfs.2, by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 2) (hq.trans (by norm_num))
      have hfs : Finite Q₀ ∧ IsSimpleGroup Q₀ := by
        rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm <;>
          exact finite_isSimpleGroup_of_lieModel (by norm_num) hm
      exact ⟨hfs.1, hfs.2, by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 2) (hq.trans (by norm_num))
      obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_G2 hv
      exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs,
        by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 2) (hq.trans (by norm_num))
      have hfs := finite_isSimpleGroup_of_lieModel (by norm_num)
        (CFSG.Models.lieModel_twistedA 3 q hv e)
      exact ⟨hfs.1, hfs.2, by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 0) (hq.trans (by norm_num))
      have hfs := finite_isSimpleGroup_of_lieModel (by norm_num)
        (CFSG.Models.lieModel_twistedA 5 q hv e)
      exact ⟨hfs.1, hfs.2, by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      have hp := primePower_p_eq_two (m := 0) (hq.trans (by norm_num))
      obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv
      exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs,
        by simp [hp]⟩
    ·
      dsimp only at hd
      subst hd
      obtain ⟨hf, hs⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_reeF4 hv
      exact ⟨Finite.of_equiv _ e.symm.toEquiv, (MulEquiv.isSimpleGroup_congr e).2 hs,
        by simp⟩
    ·
      dsimp only at hd
      subst hd
      have hfs := finite_isSimpleGroup_of_lieModel (by norm_num)
        (CFSG.Models.lieModel_A 2 q hv e)
      exact ⟨hfs.1, hfs.2, by simp [hq]⟩
    ·
      dsimp only at hd
      subst hd
      have hfs := finite_isSimpleGroup_of_lieModel (by norm_num)
        (CFSG.Models.lieModel_twistedA 2 q hv e)
      exact ⟨hfs.1, hfs.2, by simp [hq]⟩
  haveI := hfin
  haveI := hsimp
  have hchev : IsChevSimple 2 Q₀ := Or.inl ⟨.lie ⟨d, hv⟩, hchar, ⟨e⟩⟩
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.GLTheoremA.chevTwoNonabelian_holds Q₀ hsimp hchev
  exact fun hsolv => hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)

theorem core3At_L2two : Core3At fun d => ∃ q : PrimePower, d = .A 1 q ∧ q.p = 2 :=
  core3At_L2two_of_nonsolvable list93NonSolvable_holds

theorem core3At_U3two : Core3At fun d => ∃ q : PrimePower, d = .twistedA 2 q ∧ q.p = 2 :=
  core3At_U3two_of_nonsolvable list93NonSolvable_holds

theorem core3Group_of_SU3cover {Q : Type} [Group Q] {n : ℕ} (hn : 1 < n)
    (h : FullLinearCover true 3 (2 ^ n) Q) : Core3Group (Q ⧸ Subgroup.center Q) :=
  core3Group_of_SU3cover_of_nonsolvable list93NonSolvable_holds hn h

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
