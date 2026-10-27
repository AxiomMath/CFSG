module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3A6CubeN

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactBlockThreeASixCubeShort : Prop :=
  CubeNStmt fun _ _ L _ => IsShort2 L

@[expose] def centBase (M R L : Subgroup G) (hRM : R ≤ M) : Subgroup G :=
  ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hRM))).map R.subtype

omit [Finite G] in
theorem centBase_le {M R L : Subgroup G} (hRM : R ≤ M) : centBase M R L hRM ≤ R :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem centBase_comm {M R L : Subgroup G} (hRM : R ≤ M) (hLM : L ≤ M) :
    ∀ b ∈ centBase M R L hRM, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  rintro _ ⟨⟨b, hbR⟩, hb, rfl⟩ l hl
  have hb' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hRM hbR⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hb
  have hcomm := Subgroup.mem_centralizer_iff.mp hb'
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩) ⟨⟨l, hLM hl⟩, hl, rfl⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ((⟨b, hRM hbR⟩ : M) * ⟨l, hLM hl⟩ * (⟨b, hRM hbR⟩ : M)⁻¹ * (⟨l, hLM hl⟩ : M)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hcomm]
    group
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨_, h1, rfl⟩

namespace TwoRest3A6

theorem rankThreeGamma_le {M F : Subgroup G} (hF : IsElemAbelian 3 F)
    (hFcard : Nat.card F = 3 ^ 2) (hNF : Subgroup.normalizer (F : Set G) ≤ M)
    (hNa : ∀ a ∈ F, a ≠ 1 → Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M) :
    rankThreeGamma 1 3 F ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQF, hQr, rfl⟩
  by_cases hQ : Q = F
  · subst hQ; exact hNF
  have hQ1 : Q ≠ ⊥ := by
    rintro rfl
    have := CFSG.SectionRank.pRank_le (p := 3) (k := 0) (H := (⊥ : Subgroup G)) (by norm_num)
      (fun E hE _ => by rw [le_bot_iff.mp hE, Subgroup.card_bot]; norm_num)
    omega
  have hQc : Nat.card Q = 3 := by
    have hd : Nat.card Q ∣ 3 ^ 2 := hFcard ▸ Subgroup.card_dvd_of_le hQF
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases i
    · exact absurd (Subgroup.eq_bot_of_card_eq Q (by simpa using hci)) hQ1
    · simpa using hci
    · exact absurd (Subgroup.eq_of_le_of_card_ge hQF (by rw [hci, hFcard])) hQ
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQ1
  have hne : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have h3 : (a : G) ^ 3 = 1 := hF.2 a (hQF a.2)
  have hzp : Subgroup.zpowers (a : G) = Q := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.2)
    rw [hQc, Nat.card_zpowers, orderOf_eq_prime h3 hne]
  rw [← hzp]
  exact hNa a (hQF a.2) hne

end TwoRest3A6

end CFSG.LocalAnalysis.RankThreeTheoremC
