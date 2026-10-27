module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank
public import CFSG.RankThree.PartOne.KF.ClsSpWit
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015Lift
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti

namespace I1015

section Lift

variable {G : Type} [Group G] [Finite G]

theorem four_of_rank_noThree {K : Subgroup G} (hk3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hr : 3 ≤ CFSG.Open.twoLocalPrimeRank 3 (↥K ⧸ Subgroup.center ↥K)) :
    ∃ F T : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ T ≤ K ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      F ≤ Subgroup.normalizer (T : Set G) ∧
      3 ^ 3 * Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card F := by
  obtain ⟨Eb, Wb, hE, hEc, hW2, hW1, hEW⟩ := D4XF.exists_E27_of_three_le_twoLocalPrimeRank hr
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  have hker : π.ker = Subgroup.center ↥K := QuotientGroup.ker_mk' _
  obtain ⟨F, T, W, hFW, hFK, hFe, hFc, hWmap, hWinj, hTK, hT2, hFN, t, htT, hπt⟩ :=
    exists_two_local_lift_subgroup π (QuotientGroup.mk'_surjective _) (by rw [hker]; exact hk3) hE hW2 hW1 hEW
  refine ⟨F, T, hFK, hFe, hTK, hT2, ?_, hFN, ?_⟩
  · intro hT
    apply hπt
    rw [hT, Subgroup.mem_bot] at htT
    have : t = 1 := Subtype.ext htT
    rw [this, map_one]
  · have hbot : F ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxF, hxC⟩
      rw [hFW] at hxF
      obtain ⟨w, hw, rfl⟩ := hxF
      have hwz : w ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.1 hxC (k : G) k.2)
      have h1 : π w = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hwz
      have h2 : (⟨w, hw⟩ : W) = 1 := hWinj (by simpa using h1)
      have : w = 1 := congrArg Subtype.val h2
      rw [this, map_one]
      exact Subgroup.one_mem _
    rw [hbot, Subgroup.card_bot, mul_one, hFc, hEc]

end Lift

section Types

open CFSG.RankThree.PartTwo.Census (localRank_eq_of_mulEquiv le_localRank_of_le_normalizer)

theorem charP_two_of_card_two {K₀ : Type} [Field K₀] [Finite K₀] (h : Nat.card K₀ = 2) :
    CharP K₀ 2 := by
  have := Fintype.ofFinite K₀
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, h, pow_one])

theorem lieIndex_isSp8two {S : Type} [Group S] (h : catalogIs S S9.isSp8two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem stated_sp8_of_catalog {S : Type} [Group S] (h : catalogIs S S9.isSp8two) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = 2 ∧
      Nonempty (S ≃* StatedProj (StatedSp 4 K₀)) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isSp8two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
  · rw [h1, h2] at hm
    obtain ⟨-, K₀, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
    exact ⟨K₀, inferInstance, inferInstance, by rw [hK]; norm_num, ⟨e'⟩⟩
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem three_le_rank_sp8two {M : Type} [Group M] [Finite M] (h : catalogIs M S9.isSp8two) :
    3 ≤ CFSG.Open.twoLocalPrimeRank 3 M := by
  obtain ⟨K₀, _, _, hK, ⟨e⟩⟩ := stated_sp8_of_catalog h
  haveI := charP_two_of_card_two hK
  haveI : Finite (StatedProj (StatedSp 4 K₀)) := Finite.of_equiv M e.toEquiv
  have hr := CFSG.RankThree.PartOne.KFU.le_localRank_three_statedSp_blocks (K := K₀) (m := 3)
    (by norm_num)
  have hloc := localRank_eq_of_mulEquiv e Nat.prime_three
  change 3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 M
  rw [hloc]
  exact hr

theorem equiv_projSU_five {M : Type} [Group M] (h : catalogIs M S9.isU5two) :
    Nonempty (M ≃* CFSG.Assembly.RankThreeEven.projSU 5 2 1) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  obtain ⟨p, f, hp', hf'⟩ := q
  obtain rfl : p = 2 := h1
  obtain rfl : f = 1 := h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 4 _ hv)⟩

theorem three_le_rank_u5two {M : Type} [Group M] [Finite M] (h : catalogIs M S9.isU5two) :
    3 ≤ CFSG.Open.twoLocalPrimeRank 3 M := by
  obtain ⟨e⟩ := equiv_projSU_five h
  haveI : Finite (CFSG.Assembly.RankThreeEven.projSU 5 2 1) := Finite.of_equiv M e.toEquiv
  have hloc := localRank_eq_of_mulEquiv e Nat.prime_three
  change 3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 M
  rw [hloc]
  exact CFSG.RankThree.PartTwo.Sec4.Census.three_le_localRank_projSU_two (by norm_num)
    (by norm_num) (by norm_num) (Or.inr (by norm_num))

theorem three_le_rank_d4two {M : Type} [Group M] [Finite M] (h : catalogIs M S9.isD4two) :
    3 ≤ CFSG.Open.twoLocalPrimeRank 3 M := by
  obtain ⟨E, W, hE, hEc, hW2, hW1, hEW⟩ := D4XF.d4two_rank3 h
  exact le_localRank_of_le_normalizer Nat.prime_three hW1 hW2 hE hEc hEW

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_center_u5two (hGA : GriessAllModelsStatement) {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU5two) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  intro h3
  have := h3.trans hdvd
  omega

theorem not_three_dvd_center_sp8two (hGA : GriessAllModelsStatement) {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isSp8two) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isSp8two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
  · rw [h1, h2] at hm
    have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 1) (d := 1)
      (by decide) (by decide) (by norm_num)
    intro h3
    have := h3.trans hdvd
    omega
  · rw [h1, h2] at hm
    exact absurd hm.admissible.2.2.2 (by norm_num)

theorem not_three_dvd_center_d4two (hGA : GriessAllModelsStatement) {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isD4two) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 2) (d := 2)
    (by decide) (by decide) (by norm_num)
  intro h3
  have := h3.trans hdvd
  omega

theorem four_noThree_types (hGA : GriessAllModelsStatement) {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU5two ∨
      catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isSp8two ∨
      catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isD4two) :
    ∃ F T : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ T ≤ K ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      F ≤ Subgroup.normalizer (T : Set G) ∧
      3 ^ 3 * Nat.card ↥(F ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card F := by
  rcases h with h | h | h
  · exact four_of_rank_noThree (not_three_dvd_center_u5two hGA hK h) (three_le_rank_u5two h)
  · exact four_of_rank_noThree (not_three_dvd_center_sp8two hGA hK h) (three_le_rank_sp8two h)
  · exact four_of_rank_noThree (not_three_dvd_center_d4two hGA hK h) (three_le_rank_d4two h)

end Types

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
