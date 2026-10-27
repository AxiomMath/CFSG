module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3NL


variable {G : Type} [Group G] [Finite G]

@[expose] def SecNoExitAt (Ω : Set (Subgroup G)) (c : G) : Prop :=
  NoExit (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c)

@[expose] def SecMemberLifted (Ω : Set (Subgroup G)) (c : G) (J : Subgroup G) : Prop :=
  IsPGroup 2 (secImg Ω c J) ∧
    (∃ (L : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)))
        (u : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      IsLiftOf (secImg Ω c J) L u) ∧
    ∀ u : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J) u →
        Balance.oddCoreIn (Subgroup.centralizer ({u} : Set _)) = ⊥

theorem secMemberLifted_of_noExit {Ω : Set (Subgroup G)} {c : G} {n : ℕ}
    (hP : TL4.TightBelowRPlus 3 n)
    (hlt : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < n)
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c))
    (hno : SecNoExitAt Ω c) {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) :
    SecMemberLifted Ω c J := by
  obtain ⟨h2, hl, -⟩ := lifts_of_noExit hP hlt hS hno
  have hm := secImg_mem_secFam hJ
  exact ⟨h2 _ hm, hl _ hm, fun u hu => (hno _ hm u hu).1⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
