module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRank
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Families
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Convert

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le_elemAbelian {p : ℕ} {A B : Subgroup G} (hBA : B ≤ A)
    (hA : IsElemAbelian p A) : IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA hBA

theorem exists_elemAbelian_sq_of_two_le_pRank {K : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥K)) :
    ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E₀, -, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup ↥K)
  have hdvd : p ^ 2 ∣ Nat.card E₀ := by
    rw [hcard]
    exact pow_dvd_pow p h
  obtain ⟨F, hFcard, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 2)
    (H := (⊥ : Subgroup ↥K)) (L := E₀) (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd bot_le
  refine ⟨F.map K.subtype, Subgroup.map_subtype_le _,
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_of_le_elemAbelian hFE hE₀) K.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, hFcard]

end Convert

theorem oddRankTwoFacts : OddRankTwoFacts := by
  intro G _ _ K h
  suffices hrk : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r ↥K by
    obtain ⟨r, hr, hr2, hrk⟩ := hrk
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrk
    exact ⟨r, hr, hr2, exists_elemAbelian_sq_of_two_le_pRank hr hrk⟩
  rcases h with ⟨hrt, hL2p⟩ | hL33 | hM11
  · rcases hrt with ⟨n, hn, hmod⟩ | ⟨n, hn, hmod⟩ | hA6 | hcov
    ·
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn1 : n = 1 := by omega
        subst hn1
        exact hL2p (Or.inr hmod)
      exact Vol2Native.EvenWit.exists_two_le_pRank_psl_three_even (S := ↥K) (f := n) hn2 hmod
    ·
      exact Vol2Native.EvenWit.exists_two_le_pRank_psp_of_two_le (S := ↥K) (n := 2) (f := n)
        le_rfl hmod
    ·
      obtain ⟨e⟩ := hA6
      exact ⟨3, Nat.prime_three, by norm_num,
        Vol2Native.two_le_pRank_three_of_alternating (le_refl 6) e⟩
    ·
      obtain ⟨r, hr, hr2, hrk⟩ := Vol2Native.EvenWit.exists_two_le_pRank_psl_three_even
        (S := ↥K ⧸ CFSG.pCore 2 ↥K) (f := 2) le_rfl hcov
      refine ⟨r, hr, hr2, ?_⟩
      have : Fact r.Prime := ⟨hr⟩
      have hZn : (CFSG.pCore 2 ↥K).Normal := inferInstance
      have hN : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥K) := by
        intro hdvd
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
        rw [hk] at hdvd
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrk ⊢
      rwa [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥K) hN] at hrk
  ·
    obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (G := ↥K) (t := .PSL) (n := 3)
      (p := 3) (f := 1) (by norm_num) hL33
    refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    rcases hr with ⟨-, ⟨hn, -⟩ | ⟨-, h2⟩ | h4⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
    · omega
    · omega
    · omega
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · omega
  ·
    obtain ⟨e⟩ := hM11
    exact ⟨3, Nat.prime_three, by norm_num, Vol2Native.two_le_pRank_three_M11 e⟩

end CFSG.QuasithinUnique.Fin253
