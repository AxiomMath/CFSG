module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenResidualAssembly

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenResidual

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition.Exact
  CFSG.Assembly.LowTwoRank

theorem admissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem admissible_menu_case_cover (X : Type) [Group X] (hX : ¬ EvenStandardException X)
    (hBN : EvenBNRankTwoType X) :
    (∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 4 2 f) ∨
      LieModel X .PSU 5 2 1 ∨
      (∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 5 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSp 2 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ LieModel X .G2 0 2 f) ∨
      (∃ f : ℕ, 1 ≤ f ∧ LieModel X .trialityD4 0 2 f) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel X .twistedF4 0 2 f) ∨
      LieModel X .Tits 0 2 1 := by
  obtain ⟨t, n, f, hf, htn, hL⟩ := hBN
  have hadm := admissible_of_lieModel hL
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at htn
  rcases htn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    refine Or.inl ⟨f, ?_, hL⟩
    by_contra h
    interval_cases f
    · exact hX (Or.inr (Or.inl hL))
    · exact hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))))
  ·
    refine Or.inr (Or.inl ⟨f, ?_, hL⟩)
    by_contra h
    interval_cases f
    exact hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))))
  ·
    rcases Nat.lt_or_ge f 2 with h | h
    · obtain rfl : f = 1 := by omega
      exact Or.inr (Or.inr (Or.inl hL))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h, hL⟩)))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, ?_, hL⟩))))
    obtain ⟨-, -, -, h⟩ := hadm
    by_contra hf2
    obtain rfl : f = 1 := by omega
    exact h rfl
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, ?_, hL⟩)))))
    obtain ⟨-, -, -, h⟩ := hadm
    by_contra hf2
    obtain rfl : f = 1 := by omega
    norm_num at h
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hL⟩))))))
  ·
    obtain ⟨-, -, -, -, hodd, h3⟩ := hadm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f, hodd, h3, hL⟩)))))))
  ·
    obtain ⟨-, -, -, -, rfl⟩ := hadm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL)))))))

@[expose] def BNFamilyStatement (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    EvenStandardType (L ⧸ center L) → ¬ EvenStandardException (L ⧸ center L) →
    P (L ⧸ center L) → Even (Nat.card (center L))

theorem bnRankTwoCenter_of_families
    (hPSL3 : BNFamilyStatement fun X _ => ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 3 2 f)
    (hPSU4 : BNFamilyStatement fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 4 2 f)
    (hPSU5two : BNFamilyStatement fun X _ => LieModel X .PSU 5 2 1)
    (hPSU5 : BNFamilyStatement fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 5 2 f)
    (hPSp2 : BNFamilyStatement fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSp 2 2 f)
    (hG2 : BNFamilyStatement fun X _ => ∃ f : ℕ, 2 ≤ f ∧ LieModel X .G2 0 2 f)
    (hD4 : BNFamilyStatement fun X _ => ∃ f : ℕ, 1 ≤ f ∧ LieModel X .trialityD4 0 2 f)
    (hF4 : BNFamilyStatement fun X _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ LieModel X .twistedF4 0 2 f)
    (hTits : BNFamilyStatement fun X _ => LieModel X .Tits 0 2 1) :
    BNRankTwoCenterStatement := by
  intro G _ _ _ hnonab hK L hL hcore S hS htype hexc hBN
  rcases admissible_menu_case_cover _ hexc hBN with h | h | h | h | h | h | h | h | h
  · exact hPSL3 G hnonab hK L hL hcore S hS htype hexc h
  · exact hPSU4 G hnonab hK L hL hcore S hS htype hexc h
  · exact hPSU5two G hnonab hK L hL hcore S hS htype hexc h
  · exact hPSU5 G hnonab hK L hL hcore S hS htype hexc h
  · exact hPSp2 G hnonab hK L hL hcore S hS htype hexc h
  · exact hG2 G hnonab hK L hL hcore S hS htype hexc h
  · exact hD4 G hnonab hK L hL hcore S hS htype hexc h
  · exact hF4 G hnonab hK L hL hcore S hS htype hexc h
  · exact hTits G hnonab hK L hL hcore S hS htype hexc h

end CFSG.LocalAnalysis.ComponentInitial.EvenResidual
