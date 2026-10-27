module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3L3U3Core
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ConjThree
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3L3Model
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3U3Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

theorem isLThreeUThreeIndex_cases (dd : TauCeti.LieTypeIndex) (h : IsLThreeUThreeIndex dd) :
    (∃ q : TauCeti.PrimePower, dd = .A 2 q ∧ q.p ≠ 2) ∨
      (∃ q : TauCeti.PrimePower, dd = .twistedA 2 q ∧ q.p ≠ 2) := by
  rcases dd with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q |
    q | q | q | q | m | m | m | _
  · by_cases hn : n = 2
    · subst hn
      exact Or.inl ⟨q, rfl, h⟩
    · exfalso
      simp [IsLThreeUThreeIndex, hn] at h
  · by_cases hn : n = 2
    · subst hn
      exact Or.inr ⟨q, rfl, h⟩
    · exfalso
      simp [IsLThreeUThreeIndex, hn] at h
  all_goals (exfalso; simp [IsLThreeUThreeIndex] at h)

theorem field_facts_of_card_eq {F₀ : Type} [Field F₀] [Finite F₀] {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hcard : Nat.card F₀ = p ^ e) :
    5 ≤ Nat.card F₀ ∧ ringChar F₀ ≠ 2 ∧ ringChar F₀ ≠ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F₀
  have hcharP : CharP F₀ p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hring : ringChar F₀ = p := ringChar.eq F₀ p
  refine ⟨?_, by rw [hring]; exact hp2, by rw [hring]; exact hp3⟩
  rw [hcard]
  have hp5 : 5 ≤ p := by
    have h2 : 2 ≤ p := hp.two_le
    have hne4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  calc 5 ≤ p := hp5
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he

theorem kFactL3U3SL2Three_holds : KFactL3U3SL2Three := by
  intro A _ _ L z hcat hrk hzL hz3
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 1 := by
    have h1 : CFSG.Open.pRank 3 L = CFSG.pRank 3 ↥L :=
      (CFSG.SectionRank.pRank_coe_eq_openPRank 3 L).symm
    have h2 : CFSG.pRank 3 ↥L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
      CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥L
    rw [← h2, ← h1]
    exact hrk
  have hconj : ∀ a b : ↥L, orderOf a = 3 → orderOf b = 3 →
      ∃ g : ↥L, g * a * g⁻¹ ∈ Subgroup.zpowers b :=
    fun a b ha hb => exists_conj_mem_zpowers_of_pRank_le_one hrk' a b ha hb
  cases i with
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    obtain ⟨hidx, hchar⟩ := hi
    rcases isLThreeUThreeIndex_cases dd hidx with ⟨q, rfl, hq2⟩ | ⟨q, rfl, hq2⟩
    · have hq3 : q.p ≠ 3 := by simpa using hchar
      obtain ⟨F₀, _, _, hcard, ι, hι⟩ := exists_sl2_embedding_of_A2 hv e
      obtain ⟨h5, hp2, hp3⟩ :=
        field_facts_of_card_eq q.prime_p q.exponent_pos hq2 hq3 hcard
      exact l3u3_exists_section L z h5 hp2 hp3 ι hι hconj hzL hz3
    · have hq3 : q.p ≠ 3 := by simpa using hchar
      obtain ⟨F₀, _, _, hcard, ι, hι⟩ := exists_sl2_embedding_of_twistedA2 hv e
      obtain ⟨h5, hp2, hp3⟩ :=
        field_facts_of_card_eq q.prime_p q.exponent_pos hq2 hq3 hcard
      exact l3u3_exists_section L z h5 hp2 hp3 ι hι hconj hzL hz3
  | _ => exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
