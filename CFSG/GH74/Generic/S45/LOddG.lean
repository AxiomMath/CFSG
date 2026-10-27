module

public import CFSG.GH74.Generic.S45.LOdd
public import CFSG.GH74.Generic.S45.LG4Defs
public import CFSG.GH74.Generic.S45.LOddPSU
public import CFSG.GH74.Filter.Orthogonal.OddReflections
public import CFSG.GH74.Filter.ClassicalOdd.Linear
public import CFSG.GH74.Filter.ClassicalOdd.Symplectic
public import CFSG.GH74.Filter.ClassicalOdd.Unitary
public import CFSG.GH74.Generic.S45.LAltMain
public import CFSG.GH74.Generic.S45.LSporRows
public import CFSG.LieType.Chevalley.OddE6AllInvolutionComponents
public import CFSG.LieType.Chevalley.OddTrialityAllInvolutionComponents
public import CFSG.LieType.Chevalley.OddTwistedE6InnerInvolutionComponents
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank

@[expose] def OddRowG_PSL2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → StatedClassicalModel (K ⧸ center K) .PSL 2 r f → False

@[expose] def OddRowG_PSL3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → StatedClassicalModel (K ⧸ center K) .PSL 3 r f → False

@[expose] def OddRowG_PSL4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → r ^ f % 8 ≠ 1 → StatedClassicalModel (K ⧸ center K) .PSL 4 r f → False

@[expose] def OddRowG_PSL5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → r ^ f % 4 = 3 → StatedClassicalModel (K ⧸ center K) .PSL 5 r f → False

@[expose] def OddRowG_PSU3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → StatedClassicalModel (K ⧸ center K) .PSU 3 r f → False

@[expose] def OddRowG_PSU4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → r ^ f % 8 ≠ 7 → StatedClassicalModel (K ⧸ center K) .PSU 4 r f → False

@[expose] def OddRowG_PSp4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r f : ℕ, r ≠ 2 → StatedClassicalModel (K ⧸ center K) .PSp 2 r f → False

@[expose] def B_1310_odd_rest_g4 : Prop :=
  OddRowG_PSL2 ∧ OddRowG_PSL3 ∧ OddRowG_PSL4 ∧ OddRowG_PSL5 ∧ OddRowG_PSU3 ∧ OddRowG_PSU4 ∧
    OddRowG_PSp4

@[expose] def B_1310_odd_g4 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310g K y L →
    ∀ r : ℕ, r.Prime → r ≠ 2 → LieTypeChar (K ⧸ center K) r → False

theorem b_1310_odd_rest_g4
    (hrest : B_1310_odd_rest_g4) : B_1310_odd_g4 := by
  obtain ⟨hL2, hL3, hL4, hL5, hU3, hU4, hSp4⟩ := hrest
  intro K _ _ y L hypg r hr hr2 hlie
  have hyp : Hyp1310 K y L := hypg.2
  have hg : Gen4 (K ⧸ center K) := Gen4.quotient _ hypg.1
  obtain ⟨yb, Lb, q, -, hQ, -⟩ := hyp.quot_data
  have hmod4 : ∀ f : ℕ, r ^ f % 4 = 1 ∨ r ^ f % 4 = 3 := by
    intro f
    have hodd : Odd (r ^ f) := (hr.odd_of_ne_two hr2).pow
    have h2 : r ^ f % 2 = 1 := Nat.odd_iff.1 hodd
    omega
  have hmod8 : ∀ f : ℕ, r ^ f % 8 = 1 ∨ r ^ f % 8 ≠ 1 := fun f => by omega
  rcases hlie with ⟨t, n, f, hmodel⟩ | ⟨t, f, ht, hmodel⟩ | ⟨t, f, ht, hmodel⟩ | ⟨f, hmodel⟩
  · cases t
    ·
      have hn : 2 ≤ n := hmodel.1.2.2.1
      by_cases hn6 : 6 ≤ n
      · by_cases hn7 : 7 ≤ n
        · exact CFSG.GH74.Filter.t_PSL_ge_seven_odd _ n r f hr2 hn7 hmodel hg
        · obtain rfl : n = 6 := by omega
          exact CFSG.GH74.Filter.t_PSL_six_odd _ r f hr2 hmodel hg
      · interval_cases n
        · exact hL2 K y L hypg r f hr2 hmodel
        · exact hL3 K y L hypg r f hr2 hmodel
        · by_cases h8 : r ^ f % 8 = 1
          · exact CFSG.GH74.Filter.t_PSL_four_odd _ r f hr2 h8 hmodel hg
          · exact hL4 K y L hypg r f hr2 h8 hmodel
        · rcases hmod4 f with h4 | h4
          · exact CFSG.GH74.Filter.t_PSL_five_odd _ r f hr2 h4 hmodel hg
          · exact hL5 K y L hypg r f hr2 h4 hmodel
    ·
      have hn : 3 ≤ n := hmodel.1.2.2.1
      by_cases hn5 : 5 ≤ n
      · exact oddRow_psu_ge_five hyp hr2 hn5 hmodel
      · interval_cases n
        · exact hU3 K y L hypg r f hr2 hmodel
        · by_cases h7 : r ^ f % 8 = 7
          · exact CFSG.GH74.Filter.t_PSU_four_odd _ r f hr2 h7 hmodel hg
          · exact hU4 K y L hypg r f hr2 h7 hmodel
    ·
      have hn : 2 ≤ n := hmodel.1.2.2.1
      by_cases hn3 : 3 ≤ n
      · exact CFSG.GH74.Filter.t_PSp_odd_ge_three _ n r f hr2 hn3 hmodel hg
      · obtain rfl : n = 2 := by omega
        exact hSp4 K y L hypg r f hr2 hmodel
    · exact CFSG.GH74.Filter.t_POmegaOdd _ n r f hr2 hmodel.1.2.2.1 hmodel hg
    · exact CFSG.GH74.Filter.t_POmegaPlus_odd _ n r f hr2 hmodel hg
    · exact CFSG.GH74.Filter.t_POmegaMinus_odd _ n r f hr2 hmodel hg
    all_goals exact hmodel.2
  · exact odd_exc_false hr2 hmodel hQ
  · have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      simpa [reeTitsTags] using ht
    rcases ht' with rfl | rfl | rfl
    · obtain rfl : r = 3 := hmodel.1.2.2.2.1
      exact odd_twistedG2_false hyp hmodel
    · exact hr2 hmodel.1.2.2.2.1
    · exact hr2 hmodel.1.2.2.2.1
  · exact hr2 hmodel.1

theorem b_III11_13_10_g4_of_leaves_odd (hAlt : B_1310_alt) (hSpor : B_1310_spor_g4)
    (hEven : B_1310_even) (hOdd : B_1310_odd_g4) : B_III11_13_10_g4 := by
  intro K _ _ hg hK y hy L hL hsub hL2 hA hb1 hb2
  have hyp : Hyp1310 K y L := ⟨hK, hy, hL, hsub, hL2, hA, hb1, hb2⟩
  have hcat := catalog_of_inCalK2 hK
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.1.2.2
  have hLie : ∀ p : ℕ, p.Prime → LieTypeChar (K ⧸ center K) p → Concl1310 K y L := by
    intro p hp hlie
    by_cases h2 : p = 2
    · subst h2
      exact hEven K y L hyp hlie
    · exact (hOdd K y L ⟨hg, hyp⟩ p hp h2 hlie).elim
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, he⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, he⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (hAlt K y L hyp ⟨n, hn, he⟩).elim
  · exact hLie p hm.1.1 (Or.inl ⟨t, n, f, hm⟩)
  · rcases hex with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact hLie p hm.1.1 (Or.inr (Or.inl ⟨t, f, ht, hm⟩))
    · exact hLie p hm.1.1 (Or.inr (Or.inr (Or.inl ⟨t, f, ht, hm⟩)))
    · have hp2 : p = 2 := hm.1
      subst hp2
      exact hEven K y L hyp (Or.inr (Or.inr (Or.inr ⟨f, hm⟩)))
  · exact hSpor K y L ⟨hg, hyp⟩ ⟨s, he⟩

end CFSG.GH74.Generic.S45
