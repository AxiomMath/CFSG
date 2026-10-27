module

public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Nbr
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AET
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Gen
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkE2_of (hP : TightBelowRPlus 3 n) (hL : TightLargeHypR 3 n Y R S t)
    (hT : ¬ TriNbrAll R t)
    (htr : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
      ∀ L' ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
        ∃ g : ↥(linkGrp R t), conjSub g L = L')
    (hnc : ¬ DConnected (restrictFamily (coreLinkFam R t) (linkGrp R t)))
    {R' : Subgroup ↥(linkGrp R t)} {S' : Sylow 2 R'} {t' : ↥(linkGrp R t)}
    (hd' : TightDatum R' S' t') (hc' : TightCls ↥(linkGrp R t) R' S' t')
    (heq : CoreAssembly.conjClass (tightCore R') =
      restrictFamily (coreLinkFam R t) (linkGrp R t))
    (hO2 : TightInO2 t') :
    LinkS3S4 R t ∨ LinkAEAt R t := by
  have hL₁ : tightCore R' ∈ restrictFamily (coreLinkFam R t) (linkGrp R t) := by
    rw [← heq]
    exact CoreAssembly.mem_conjClass_self _
  have hD := thmDHyp_linkFam hL htr ⟨_, hL₁, t', hd'.isUniqueInvolution_core, hO2⟩
  have hsub := subsingleton_omegaNbr_link hL hT htr
  rcases TC.Thin.thmDAbsAt_iff.mp (hP.thmD.d2 _ (natCard_linkGrp_lt hL)) _ hD with
    h1 | ⟨W, hW1⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, ⟨I⟩⟩ | h29
  · refine absurd (fun K hK J hJ => ?_) hnc
    obtain rfl := h1 K hK J hJ
    exact Relation.ReflTransGen.refl
  · have hW1' : WSet (CoreAssembly.conjClass (tightCore R')) = {W} := by rw [heq]; exact hW1
    have hDS := SecIdE2.dstarConnected_of_wSet hd' hc' hO2 hW1'
    rw [heq] at hDS
    refine Or.inl ⟨htr, hnc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨W, hW1⟩, ?_, hDS⟩)))))⟩
    intro A hA B hB C hC hCB
    exact hCB.2.1 (hsub A hA C hC B hB)
  · have hDS := SecIdE2.dstarConnected_of_e8 hd' hc' hO2 hE
    rw [heq] at hDS
    exact Or.inl ⟨htr, hnc, Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨E, hE⟩, hDS⟩)))⟩
  · have h64' := h64
    rw [← heq] at h64'
    obtain ⟨I⟩ := h64'
    have hDS := SecIdE2.dstarConnected_of_e64 hd' hc' hO2 I
    rw [heq] at hDS
    exact Or.inl ⟨htr, hnc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h64, hDS⟩))))⟩
  · by_cases hm7 : m ≤ 7
    · exact Or.inr ⟨m, hm, hm7, nonempty_aeIdent_of_restrict rfl I⟩
    · obtain ⟨A, hA, B, hB, C, hC, hBC⟩ := exists_two_nbrs_of_aeIdent hD (by omega) I
      exact absurd (hsub A hA B hB C hC) hBC
  · obtain ⟨I⟩ := h29
    obtain ⟨A, hA, B, hB, C, hC, hBC⟩ := exists_two_nbrs_of_e29 hD I hL₁
    exact absurd (hsub A hA B hB C hC) hBC

theorem tightLinkE2R_plus (n : ℕ) : PlusLeaf TightLinkE2R n := by
  intro _ hP _ _ _ _ _ _ hL _ hT htr hnc _ _ _ hd' hc' heq hO2
  exact linkE2_of hP hL hT htr hnc hd' hc' heq hO2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.LinkE2
