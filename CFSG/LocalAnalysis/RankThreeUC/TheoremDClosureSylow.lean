module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks
import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Quasithin.Background.GoldschmidtE23Fam

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
  {I : Finset (Subgroup (MulAut W))}

namespace BlockData

omit [Finite W] in
private theorem iSup_le_normalizer (hI : BlockData X I) {L : Subgroup (MulAut W)}
    (hL : L ∈ I) : (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · subst h
    exact Subgroup.le_normalizer
  · intro a ha
    have hc : a ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hI.comm L' hL' L hL h a ha b hb).symm
    exact Subgroup.centralizer_le_normalizer _ hc

private theorem isSylowTwoOf_inf_block (hI : BlockData X I) {J : Subgroup (MulAut W)}
    (hJ : CFSG.QuasithinUnique.IsSylowTwoOf J (⨆ L ∈ I, L)) {L : Subgroup (MulAut W)}
    (hL : L ∈ I) : CFSG.QuasithinUnique.IsSylowTwoOf (J ⊓ L) L := by
  have h : CFSG.ABGLocalTools.IsSylowOf 2 J (⨆ L ∈ I, L) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr hJ
  exact CFSG.ABGLocalTools.isSylowOf_iff.mp
    (h.inf_of_le_normalizer (le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL)
      (hI.iSup_le_normalizer hL))

private theorem card_eq_two_of_isSylowTwoOf {G : Type*} [Group G] [Finite G] {P L : Subgroup G}
    (hP : CFSG.QuasithinUnique.IsSylowTwoOf P L) (hL : Nat.card L = 6) : Nat.card P = 2 := by
  have h : CFSG.ABGLocalTools.IsSylowOf 2 P L := CFSG.ABGLocalTools.isSylowOf_iff.mpr hP
  rw [h.card_eq, hL]
  norm_num [Nat.factorization]

theorem exists_sylow_two_decomp (hI : BlockData X I) {J : Subgroup (MulAut W)}
    (hJ : CFSG.QuasithinUnique.IsSylowTwoOf J (⨆ L ∈ I, L)) :
    J = ⨆ L ∈ I, (J ⊓ L) ∧
      ∀ L ∈ I, ∃ t ∈ J ⊓ L, t ^ 2 = 1 ∧ t ≠ 1 ∧ ∀ y ∈ J ⊓ L, y = 1 ∨ y = t := by
  classical
  refine ⟨?_, fun L hL => ?_⟩
  · have hsyl : CFSG.QuasithinUnique.IsSylowTwoOf (⨆ L ∈ I, J ⊓ L) (⨆ L ∈ I, L) :=
      GE23.isSylowTwoOf_iSup I (fun L => L) (fun L => J ⊓ L)
        (fun L hL => hI.isSylowTwoOf_inf_block hJ hL) hI.comm hI.indep
    exact GE23.eq_of_isSylowTwoOf_le hsyl (iSup₂_le fun L _ => inf_le_left) hJ.1 hJ.2.1
  · have hcardL : Nat.card L = 6 := (S1417.card_of_actsAsNaturalL2 (hI.natural L hL)).1
    have hcard : Nat.card ↥(J ⊓ L) = 2 :=
      card_eq_two_of_isSylowTwoOf (hI.isSylowTwoOf_inf_block hJ hL) hcardL
    obtain ⟨t, ht1, hty⟩ := (Nat.card_eq_two_iff' (1 : ↥(J ⊓ L))).1 hcard
    have ht2 : t ^ 2 = 1 := by
      by_contra h
      have h' := hty _ h
      rw [pow_two, mul_eq_left] at h'
      exact ht1 h'
    refine ⟨(t : MulAut W), t.2, congrArg Subtype.val ht2, fun h => ht1 (Subtype.ext h),
      fun y hy => ?_⟩
    by_cases h1 : (⟨y, hy⟩ : ↥(J ⊓ L)) = 1
    · exact Or.inl (congrArg Subtype.val h1)
    · exact Or.inr (congrArg Subtype.val (hty _ h1))

end BlockData

end CFSG.LocalAnalysis.RankThreeUC
