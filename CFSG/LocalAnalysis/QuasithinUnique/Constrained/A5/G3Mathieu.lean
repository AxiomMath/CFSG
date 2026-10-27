module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Hat

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank

theorem noDelta5Norm_sub {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (h : NoDelta5Norm ↥L) (hT : IsSylowTwoOf T L) (hBL : B ≤ L)
    (hTB : T ≤ Subgroup.normalizer (B : Set G)) : ¬ IsDelta5Group ↥B := by
  intro hD
  have hT' : IsSylowTwoOf (T.subgroupOf L) (⊤ : Subgroup ↥L) := isSylowTwoOf_top_subgroupOf hT
  have hD' : IsDelta5Group ↥(B.subgroupOf L) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hBL).symm
  exact h _ _ hT' (subgroupOf_le_normalizer hTB) hD'

theorem noDelta5Norm_hat_m22
    {L : Type} [Group L] [Finite L]
    (h : IsHat L (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : NoDelta5Norm L := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  refine noDelta5Norm_of_central_quotient (Subgroup.center L) le_rfl ?_
    (NoDelta5Norm.of_mulEquiv e.symm (noDelta5Norm_m22 ⟨MulEquiv.refl _⟩))
  rw [hc]
  omega

@[expose] def M23NoDelta5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSporadic .M23 X → NoDelta5Norm X

theorem mathieuNoDelta5_of
    (h23 : M23NoDelta5) : MathieuNoDelta5 := by
  intro G _ _ L T B hL hT hBL hTB
  rcases hL with hL | hL | hL
  · exact noDelta5Norm_sub (noDelta5Norm_m22 hL) hT hBL hTB
  · exact noDelta5Norm_sub (noDelta5Norm_hat_m22 hL) hT hBL hTB
  · exact noDelta5Norm_sub (h23 ↥L hL) hT hBL hTB

end CFSG.QuasithinUnique.A5.G3
