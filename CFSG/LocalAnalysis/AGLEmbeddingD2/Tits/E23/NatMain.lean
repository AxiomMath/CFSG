module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatS3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatSL

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS5 CFSG.RankThree.PartOne

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)} {ℰ : Set (Subgroup (MulAut V))}

theorem natCore (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) (hF : FiveFive P T M ℰ)
    (hnat : ∀ E ∈ ℰ, SLType2 (Hyp51.offSet P) E ∨
      (SymType (genD P ⊓ M) (Hyp51.offSet P) E ∧ Nat.card E = 6))
    {X : Subgroup (MulAut V)} (hXT : X ≤ T) (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V)))
    (hX₀ : ∃ B ∈ Hyp51.offSet P, B ≤ X)
    (hXgen : X ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ X}, B) :
    cenIn T (fixV X) ≤ X ∧ IsSylowOf 2 X (genD P) := by
  classical
  have hsyl := isSylowOf_of_nat h hV hnat
  have hR : ∀ E ∈ ℰ, T ⊓ E ∈ Hyp51.offSet P := fun E hE =>
    (inf_mem_offSet_and_le h hV hF hsyl hXT hTX hX₀ hE).1
  have hx2 : ∀ y ∈ T, ∃ k : ℕ, y ^ 2 ^ k = 1 := fun y hy => by
    obtain ⟨k, hk⟩ := h.minpar.syl.2.1 ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨?_, ?_⟩
  · rintro x ⟨hxT, hxfix⟩
    refine mem_of_fixV h hV hF hsyl hXT hTX hX₀ hXgen ?_ ?_ ?_ hxT hxfix
    · intro E hE
      rcases hnat E hE with hSL | ⟨hSym, h6⟩
      · exact exists_fixed_of_slType2 h hV hF hE hSL (hR E hE) inf_le_right
      · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
        exact hc.exists_fixed_of_six h6 (hR E hE) inf_le_right
    · intro E hE y hyT hyE hyfix
      rcases hnat E hE with hSL | ⟨hSym, h6⟩
      · exact exists_agree_of_slType2 h hV hF hE hSL (hR E hE) inf_le_right hyE (hx2 y hyT) hyfix
      · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
        exact hc.exists_agree_of_six h6 h hV (hR E hE) inf_le_right hyE hyfix
    · intro E hE e he htriv
      rcases hnat E hE with hSL | ⟨hSym, -⟩
      · exact eq_one_of_slType2 hSL he htriv
      · obtain ⟨m, θ, β, i₀, hc⟩ := SymComp.exists_of_symType hSym
        exact hc.eq_one he htriv
  · have hXeq := eq_iSup_inf h hV hF hsyl hXT hTX hX₀ hXgen
    let : Fintype ↥ℰ := Fintype.ofFinite _
    have key := isSylowOf_iSup_of_iSupIndep (ι := ↥ℰ) (A := fun E => (E : Subgroup (MulAut V)))
      (S := fun E => T ⊓ (E : Subgroup (MulAut V)))
      (fun i j hij x y hx hy => hF.comm i i.2 j j.2 (fun h' => hij (Subtype.ext h')) x hx y hy)
      (fun i => (hF.indep i i.2).mono_right (iSup₂_le fun j hj =>
        le_iSup₂_of_le (f := fun (E' : Subgroup (MulAut V))
          (_ : E' ∈ {E' | E' ∈ ℰ ∧ E' ≠ (i : Subgroup (MulAut V))}) => E') (j : Subgroup (MulAut V))
          ⟨j.2, fun h' => hj (Subtype.ext h')⟩ le_rfl))
      (fun i => hsyl i i.2 _ (hR i i.2) inf_le_right)
    rw [hXeq, ← hF.iSup_eq, iSup_subtype', iSup_subtype']
    exact key

end CFSG.AGLEmbeddingD2.Tits.E23
