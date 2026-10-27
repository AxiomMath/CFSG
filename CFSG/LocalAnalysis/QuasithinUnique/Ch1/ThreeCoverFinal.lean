module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadic
public import CFSG.Quasithin.Background.KnownMultTypes
import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique.Ch1

variable {X : Type} [Group X] [Finite X]

theorem false_of_a134TypesCentral (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) (h : A134TypesCentral X) : False :=
  false_of_isPGroup_two_of_card_three (CFSG.Quasithin.mult2Fact X hX h) h3

theorem a36Case2List_of_alt (hX : CFSG.IsQuasisimple X) (h3 : Nat.card (Subgroup.center X) = 3)
    {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n)) :
    A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  interval_cases n
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      (CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num) (by norm_num) π hπ hC
        hodd).1 (Or.inl rfl)).elim
  · exact Or.inr (Or.inl ⟨hX, h3, ⟨e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hX, h3, ⟨e⟩⟩))
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      (CFSG.SectionRank.alternating_small_odd_cover_bound (by norm_num) (by norm_num) π hπ hC
        hodd).1 (Or.inr rfl)).elim

theorem alternating_six_of_psl_two_nine {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 3 2) : Nonempty (S ≃* alternatingGroup (Fin 6)) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h

theorem a36Case2List_of_odd
    (hX : CFSG.IsQuasisimple X) (h3 : Nat.card (Subgroup.center X) = 3)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 p f) ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 p 1 ∨
      StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 p 1) : A36Case2List X := by
  rcases h with ⟨f, hf, h⟩ | h | h
  · by_cases hp3 : p = 3
    · subst hp3
      rcases hf with rfl | rfl
      · exact absurd (by norm_num : ((2 : ℕ), 3 ^ 1) = (2, 3)) h.1.2.2.2.2
      · exact Or.inr (Or.inl ⟨hX, h3, alternating_six_of_psl_two_nine h⟩)
    · have hp5 : 3 < p := by
        have := hp.two_le
        omega
      exact (false_of_a134TypesCentral hX h3
        (Or.inr (Or.inr (Or.inr ⟨p, f, hp, hp5, by omega, by omega, h⟩)))).elim
  · exact a36Case2List_of_classical_odd_three hX h3 hp hp2 (Or.inl rfl) h
  · exact a36Case2List_of_classical_odd_three hX h3 hp hp2 (Or.inr rfl) h

theorem a36Case2List_of_charTwo
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3)
    (h : (∃ f : ℕ,
      (2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 2 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel (X ⧸ Subgroup.center X) .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ SuzukiModel (X ⧸ Subgroup.center X) 2 f)) ∨
      ReeTitsModel (X ⧸ Subgroup.center X) .Tits 2 1) : A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  have hodd : Odd (Nat.card (Subgroup.center X)) := by rw [h3]; decide
  rcases h with ⟨f, h | h | h | h | h | h | h | h⟩ | h
  ·
    exact (false_of_a134TypesCentral hX h3 (Or.inl ⟨f, h.2⟩)).elim
  ·
    exact a36Case2List_of_linear_even hX h3 h.1 h.2
  ·
    exact a36Case2List_of_unitary_even hX h3 h.1 h.2
  ·
    exfalso
    have hZ := (CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hX hodd h.2).1
    rw [hZ, Subgroup.card_bot] at h3
    omega
  ·
    exact (false_of_odd_cover_trivial h3 (MulEquiv.refl _) fun π hπ hC hodd =>
      CFSG.SectionRank.g2_even_perfect_odd_cover_trivial h.2 π hπ hC hodd).elim
  ·
    exact (false_of_odd_cover_trivial h3 (MulEquiv.refl _) fun π hπ hC hodd =>
      CFSG.SectionRank.triality_even_perfect_odd_cover_trivial h.2 π hπ hC hodd).elim
  ·
    obtain ⟨K, _, _, _, a, ha, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_reeFixed_of_model h.2.2
    exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
        CFSG.SectionRank.LargeRee.suzukiBlockInputs ha hK π hπ hC hodd).elim
  ·
    exact (false_of_a134TypesCentral hX h3 (Or.inr (Or.inl ⟨f, h.2.2⟩))).elim
  ·
    obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
    exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.Tits_perfect_odd_cover_trivial (K := K) hK π hπ hC hodd).elim

theorem false_of_linear_four_five
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 1) : False :=
  false_of_linear_even_cover hX h3 (by omega) (by omega) h

theorem a36Case2List_of_sporadic
    (hX : CFSG.IsQuasisimple X)
    (h3 : Nat.card (Subgroup.center X) = 3) {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) (e : X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier s) :
    A36Case2List X := by
  have : Group.IsPerfect X := hX.1
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      M11_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact Or.inr (Or.inr (Or.inr ⟨hX, h3, ⟨e⟩⟩))
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      M23_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_a134TypesCentral hX h3 (Or.inr (Or.inr (Or.inl ⟨e⟩)))).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hC
        hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd).elim
  · exact (false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
      CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd).elim

theorem threeCoverFactCat
    : ThreeCoverFactCat := by
  intro X _ _ hX h3 hK
  rcases hK with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, h⟩ | h | ⟨n, hn, h⟩ | ⟨s, hs, ⟨e⟩⟩
  · exact a36Case2List_of_alt hX h3 h5 h8 e
  · exact a36Case2List_of_odd hX h3 hp hp2 h
  · exact a36Case2List_of_charTwo hX h3 h
  · exact (false_of_linear_four_five hX h3 hn h).elim
  · exact a36Case2List_of_sporadic hX h3 hs e

end CFSG.QuasithinUnique.Vol2Native
