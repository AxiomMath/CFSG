module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLemma49
public import CFSG.GroupTheory.SylowAutTrivialPerfect
public import CFSG.GroupTheory.SylowIntersectionControl.CharPair

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.Quasithin
  CFSG.RankThree.PartOne Subgroup

variable {Ω : Type} [Group Ω] {G B : Subgroup Ω}

@[expose] def IsGomi410Type (G B : Subgroup Ω) : Prop :=
  (IsGomiChevTwo (↥B ⧸ CFSG.pCore 2 ↥B) ∧
      ¬ IsGomiL2 ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) ∧
      ¬ IsGomiU3 ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) ∧
      ¬ IsGomiSz ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B))) ∨
    (∃ m : ℕ, 3 ≤ m ∧ Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin (2 * m)))) ∨
    (Nonempty ((↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card ↥⁅gomiV G, B⁆ = 16)

private theorem even_card_alternatingGroup_t410 {n : ℕ} (hn : 4 ≤ n) :
    Even (Nat.card (alternatingGroup (Fin n))) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  rw [even_iff_two_dvd]
  have h4 : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  rw [← h2] at h4
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using h4)

private theorem center_eq_bot_of_mulEquiv_alternating_t410 {L : Type*} [Group L] {n : ℕ}
    (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) : center L = ⊥ := by
  have hmap : Subgroup.map (e : L →* alternatingGroup (Fin n)) (Subgroup.center L) = ⊥ := by
    rw [Subgroup.map_center_eq e]
    exact alternatingGroup.center_eq_bot (α := Fin n) (by simpa using hn)
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center L)
    (f := (e : L →* alternatingGroup (Fin n))) e.injective).mp hmap

private theorem not_prime_odd_card_of_mulEquiv_alternating_t410 {L : Type*} [Group L] {n : ℕ}
    (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) :
    ¬ ((Nat.card L).Prime ∧ Odd (Nat.card L)) := by
  rintro ⟨-, hodd⟩
  exact (Nat.not_even_iff_odd.mpr hodd) (by
    rw [Nat.card_congr e.toEquiv]
    exact even_card_alternatingGroup_t410 hn)

theorem IsGomi410Type.isQuasisimple (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B) :
    CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) := by
  rcases hBt with h | h | h
  · exact h.1.1
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    rcases hB.quotient with hq | hbad
    · exact hq
    · exact absurd hbad
        (not_prime_odd_card_of_mulEquiv_alternating_t410 (n := 2 * m) (by omega) e)
  · obtain ⟨⟨e⟩, _⟩ := h
    rcases hB.quotient with hq | hbad
    · exact hq
    · exact absurd hbad
        (not_prime_odd_card_of_mulEquiv_alternating_t410 (n := 7) (by norm_num) e)

theorem IsGomi410Type.sylowAutTrivial [Finite Ω] (h49 : GomiLemma49)
    (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B) :
    SylowAutTrivial ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ center (↥B ⧸ CFSG.pCore 2 ↥B)) := by
  have hQ := IsGomi410Type.isQuasisimple hB hBt
  refine h49 _ hQ.2.1 ?_
  rcases hBt with h | h | h
  · exact Or.inl h.1.2.2
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    refine Or.inr ⟨2 * m, by omega, ?_⟩
    have hc := center_eq_bot_of_mulEquiv_alternating_t410 (L := ↥B ⧸ CFSG.pCore 2 ↥B)
      (by omega) e
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot.trans e)⟩
  · obtain ⟨⟨e⟩, _⟩ := h
    refine Or.inr ⟨7, by norm_num, ?_⟩
    have hc := center_eq_bot_of_mulEquiv_alternating_t410 (L := ↥B ⧸ CFSG.pCore 2 ↥B)
      (by norm_num) e
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot.trans e)⟩

theorem IsGomi410Type.even_card [Finite Ω] (h49 : GomiLemma49) (hB : IsGomiTwoComponent G B)
    (hBt : IsGomi410Type G B) : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) := by
  have hQ := IsGomi410Type.isQuasisimple hB hBt
  have hR := IsGomi410Type.sylowAutTrivial h49 hB hBt
  obtain ⟨a, b, hab⟩ := hQ.2.2
  have heven : Even (Nat.card ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸
      center (↥B ⧸ CFSG.pCore 2 ↥B))) := SylowAutTrivial.even_card hR ⟨a, b, hab⟩
  exact even_iff_two_dvd.mpr
    ((even_iff_two_dvd.mp heven).trans (Subgroup.card_quotient_dvd_card _))

end CFSG.GroupTheory
