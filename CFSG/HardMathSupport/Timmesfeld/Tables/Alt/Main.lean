module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Alt

open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem alt_data {L : Type} [Group L] (hF : AltCentralQuotient L) (hq : CFSG.Open.IsQuasisimple L) :
    ∃ n : ℕ, 5 ≤ n ∧ Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) := by
  obtain ⟨n, ⟨e⟩⟩ := hF
  have := hq.2
  exact ⟨n, five_le_of_centerQuotient hq.1 e, ⟨e⟩⟩

theorem pRank_aut_le_top {L : Type} [Group L] [Finite L] (hF : AltCentralQuotient L)
    (hq : CFSG.Open.IsQuasisimple L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) := by
  have : Group.IsPerfect L := ⟨hq.1⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := alt_data hF hq
  exact (pRank_aut_le hn e hp hp2).trans (le_pRank_top hn e hp hp2)

theorem two_dvd_card {L : Type} [Group L] [Finite L] (hF : AltCentralQuotient L)
    (hq : CFSG.Open.IsQuasisimple L) : 2 ∣ Nat.card L := by
  obtain ⟨n, hn, ⟨e⟩⟩ := alt_data hF hq
  have h1 : Nat.card L = Nat.card (L ⧸ Subgroup.center L) * Nat.card (Subgroup.center L) :=
    (Subgroup.center L).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv] at h1
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h2 : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  have h3 : 4 ∣ n.factorial := by
    have := Nat.factorial_dvd_factorial (show 4 ≤ n by omega)
    exact (show 4 ∣ Nat.factorial 4 by decide).trans this
  rw [h1, h2]
  exact Dvd.dvd.mul_right (Nat.dvd_div_of_mul_dvd (by simpa using h3)) _

theorem tables112On_alt : Tables112On AltCentralQuotient where
  T0 L _ _ hF hq _ := by
    have := Fact.mk Nat.prime_two
    exact exists_prime_orderOf_dvd_card' (G := L) 2 (two_dvd_card hF hq)
  T1a L _ _ hF hq _ p hp hp2 := by
    have := pRank_aut_le_top hF hq hp hp2
    omega
  T1b L _ _ hF hq _ p hp hp2 _ := by
    have := pRank_aut_le_top hF hq hp hp2
    omega
  T2 L _ _ hF hq _ p hp hp2 := by
    have : Group.IsPerfect L := ⟨hq.1⟩
    obtain ⟨n, hn, ⟨e⟩⟩ := alt_data hF hq
    have h1 := pRank_center_le_one hn e hp hp2
    have h2 := le_pRank_top hn e hp hp2
    by_cases h0 : CFSG.Open.pRank p (Subgroup.center L) = 0
    · omega
    · have h3 : CFSG.Open.pRank p (Subgroup.center L) = 1 := by omega
      obtain ⟨rfl, hn67⟩ := (center_facts hn e hp hp2).2
        (dvd_of_pos_pRank_center hp (by omega))
      omega
  T3 L _ _ hF hq _ p hp hp2 hZ hr := by
    have : Group.IsPerfect L := ⟨hq.1⟩
    obtain ⟨n, hn, ⟨e⟩⟩ := alt_data hF hq
    have hd := dvd_of_pos_pRank_center hp (by omega : 1 ≤ CFSG.Open.pRank p (Subgroup.center L))
    obtain ⟨rfl, hn67⟩ := (center_facts hn e hp hp2).2 hd
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    have hf := (center_facts hn e hp hp2).1
    rw [hk, Nat.Prime.factorization_pow hp] at hf
    simp only [Finsupp.single_eq_same] at hf
    rw [hk] at hd ⊢
    rcases k with _ | _ | k
    · simp at hd
    · simp
    · omega
  T11 L _ _ hF hq _ p hp hp2 _ hr := by
    have : Group.IsPerfect L := ⟨hq.1⟩
    obtain ⟨n, hn, ⟨e⟩⟩ := alt_data hF hq
    have := pRank_center_le_one hn e hp hp2
    omega
  T9 L _ _ hF hq _ _ h2 _ := by
    have := pRank_aut_le_top hF hq Nat.prime_three (by norm_num)
    omega
  TFA_a L _ _ hF hq _ _ h1 _ H hH hcard := by
    exfalso
    have h2 := pRank_aut_le_top hF hq Nat.prime_three (by norm_num)
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) le_top hH
      (k := 2) (by rw [hcard]; norm_num)
    omega
  TFA_b L _ _ hF hq _ _ h1 _ H hH hcard := by
    exfalso
    have h2 := pRank_aut_le_top hF hq Nat.prime_three (by norm_num)
    have h3 := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := ⊤) le_top hH
      (k := 3) (by rw [hcard]; norm_num)
    omega

end CFSG.HardMathSupport.Timmesfeld.Tables.Alt
