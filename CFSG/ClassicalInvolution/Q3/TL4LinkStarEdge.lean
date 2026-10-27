module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Exit
public import CFSG.ClassicalInvolution.Q3.TL4LinkLie
public import CFSG.ClassicalInvolution.Q3.TL4LinkDatum
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2
public import CFSG.ClassicalInvolution.Q3.TL4LinkE4
public import CFSG.ClassicalInvolution.Q3.TL4LinkTrans
public import CFSG.ClassicalInvolution.Q3.TL4AECommon

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Cit3

variable {n : ℕ}

theorem tightLinkStarEdgeR_of (hZα : TightLinkZ2AlphaR 3 n) (hL2 : TightLinkZ2L2R 3 n)
    (hE3 : SecIdE3MuZ2) (hTab : MuZ2Table) (hStar : SecIdStarNbrId3) (hD : SecIdE4DStar)
    (h8 : SecIdE4O8TwoNbrs) (h2 : LieKindTwoNbrs) (hE : LieKindE4Edge) (h117 : Model117)
    (h117p : Model117Pair) (hAEx : TightAE286ExistR 3 n) (hAEn : TightAE286NoneR 3 n)
    (hA : CIT3Below n) (hP : TightBelowRPlus 3 n) : TightLinkStarEdgeR 3 n := by
  intro Y _ _ R S t hL hc hT hα htr hnc hed
  by_contra hno
  have hemp : ∀ L ∈ linkFam R t, omegaStarNbr (linkFam R t) L = ∅ := fun L hLm =>
    Set.not_nonempty_iff_eq_empty.mp fun hne => hno ⟨L, hLm, hne⟩
  have hZ2 : LinkZ2 R t := ⟨htr, hnc, hed, hemp⟩
  have hsec := lieLinkSection_of hL htr
  have hfin : (LinkZ2Model ↥(linkGrp R t) (linkFam R t) ∨ LinkZ2LieShape R t) → False := by
    intro hm
    obtain ⟨J, hJ, u, hu, hne⟩ := hα
    exact hne (hZα Y R S t hL hc hT hZ2 hm J hJ u hu)
  have hedge : (∃ L ∈ linkFam R t, (omegaNbr (linkFam R t) L).Nonempty) → False := by
    rintro ⟨L, hLm, M, hM⟩
    exact hed L hLm M hM.1 (Or.inl hM)
  obtain ⟨R', S', t', hd', hc', heq⟩ := tightLinkDatumR_three n Y R S t hL hc hT htr
  have hmem : tightCore R' ∈ linkFam R t := heq ▸ CoreAssembly.mem_conjClass_self _
  have hS3 : LinkS3S4 R t → False := by
    rintro ⟨-, hmu⟩
    obtain ⟨L', -, hst, -⟩ := hStar _ _ hsec.1 hsec.2.1 hsec.2.2.1 hsec.2.2.2 hmu _ hmem
    rw [hemp _ hmem] at hst
    exact hst
  have hed' : TightEdgeless R' := by
    show Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R'))
    rw [heq]
    exact hed
  have hEM : EdgelessMember3 R' S' t' := ⟨hd', hc', hed'⟩
  have hMu : MuZ2Member R' := fun W hW =>
    Q3T6.Mu.muIsoZ2_of_shape hd'.partIHypG hW ⟨_, CoreAssembly.mem_conjClass_self _⟩
      (by rw [heq]; exact hemp)
  have hlt := natCard_linkGrp_lt_of_large hL
  by_cases hO2 : TightInO2 t'
  · rcases LinkE2.tightLinkE2R_plus n hA hP Y R S t hL hc hT htr hnc R' S' t' hd' hc' heq hO2
      with h | h
    · exact hS3 h
    · exact not_linkAEAt_of_not_triNbrAll h117 h117p hAEx hAEn tightAECommonNbrR_holds hL hc
        hT h
  have hexit : ((¬ TightActs3 R' t' ∧ (Thm6Exit ↥(linkGrp R t) ∨ TightTwisted ↥(linkGrp R t) t'))
      ∨ Nonempty (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t) ≃*
        NativeSporadic.Carrier .M12)) → False := by
    intro hx
    obtain ⟨hsimp, hidx, hkind⟩ := hE3 _ R' S' t' hEM hMu hO2 hx
    have h6 : (genFittingFStar ↥(linkGrp R t)).index ∣ 6 := by
      have h0 : (genFittingFStar ↥(linkGrp R t)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (show (genFittingFStar ↥(linkGrp R t)).index = 1 ∨
          (genFittingFStar ↥(linkGrp R t)).index = 2 by omega) with h1 | h1 <;>
        rw [h1] <;> norm_num
    have hT6 := hTab _ R' S' t' hEM hMu hsimp h6
    have hmod : ¬ TightActs3 R' t' → IsSimpleGroup ↥(linkGrp R t) → ∀ p f : ℕ, p.Prime →
        p ≠ 2 → (LieModel ↥(linkGrp R t) .PSL 3 p f ∨ LieModel ↥(linkGrp R t) .PSU 3 p f) →
          False := fun h3 hXs p f hp hp2 hl =>
      hfin (Or.inl (heq ▸ Z2Exit.linkZ2Model_of_exit hXs hEM h3 hp hp2 hl))
    rcases hkind with ⟨p, f, hp, hp2, hk⟩ | hM12
    · rcases hk with ⟨hf, hk2⟩ | hk3 | hk3
      · exact hL2 Y R S t hL hc hT hα hZ2 hsimp hidx ⟨p, f, hp, hp2, hf, hk2⟩
      · obtain ⟨hXs, hX⟩ := hT6.1 p f hk3
        rcases hx with ⟨h3, -⟩ | ⟨⟨e⟩⟩
        · exact hmod h3 hXs p f hp hp2 (Or.inl hX)
        · exact hT6.2.2.2.2 (Z2Exit.isSporadic_fstarQuot_of_simple
            (Z2Exit.nonabelian_of_member hEM) e)
      · obtain ⟨hXs, hX, -⟩ := hT6.2.1 p f hk3
        rcases hx with ⟨h3, -⟩ | ⟨⟨e⟩⟩
        · exact hmod h3 hXs p f hp hp2 (Or.inr hX)
        · exact hT6.2.2.2.2 (Z2Exit.isSporadic_fstarQuot_of_simple
            (Z2Exit.nonabelian_of_member hEM) e)
    · exact hT6.2.2.2.2 hM12
  rcases secIdentDatum3_of hP hA _ hlt R' S' t' hd' hc' with hO2' | hE3a | hE3b | hE4 | hLie
  · exact hO2 hO2'
  · exact hexit (Or.inl hE3a.2)
  · exact hexit (Or.inr hE3b.2)
  · obtain ⟨hZ, hSp | hO8⟩ := hE4
    · have hds := hD _ R' S' t' hd' hc' hO2 hZ (Or.inl hSp)
      rw [heq] at hds
      apply hnc
      intro K hK J hJ
      by_contra hKJ
      have hpath := hds K hK J hJ
      rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨K₁, ⟨hK₁, hst | hst⟩, -⟩
      · exact hKJ Relation.ReflTransGen.refl
      · rw [hemp K hK] at hst
        exact hst
      · rw [hemp K₁ hK₁] at hst
        exact hst
    · obtain ⟨L, hLm, M, hM, -, -, -⟩ := h8 _ R' S' t' hd' hc' hO2 hZ hO8
      rw [heq] at hLm hM
      exact hedge ⟨L, hLm, M, hM⟩
  · obtain ⟨c, hcv, hsh⟩ := exists_q8Shape_of_lie hL heq hLie
    rcases hcv with ⟨tg, m, hft, hadm, rfl⟩ | rfl | rfl
    · by_cases hnm : LieKindNamed tg m
      · rcases hnm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hfin (Or.inr ⟨_, Or.inl rfl, hsec, hsh⟩)
        · exact hS3 ⟨htr, hnc, Or.inl (Or.inl hsh)⟩
        · exact hedge (hE _ _ _ (Or.inl rfl) hsec hsh)
        · exact hedge (hE _ _ _ (Or.inr rfl) hsec hsh)
        · exact hS3 ⟨htr, hnc, Or.inr (Or.inl (Or.inl hsh))⟩
        · exact hS3 ⟨htr, hnc, Or.inr (Or.inl (Or.inr (Or.inl hsh)))⟩
        · exact hS3 ⟨htr, hnc, Or.inr (Or.inl (Or.inr (Or.inr hsh)))⟩
        · exact hS3 ⟨htr, hnc, Or.inl (Or.inr (Or.inl hsh))⟩
        · exact hS3 ⟨htr, hnc, Or.inl (Or.inr (Or.inr hsh))⟩
      · obtain ⟨L, hLm, M, hM, -, -, -⟩ := h2 _ _ tg m hft hadm hnm hsec hsh
        exact hedge ⟨L, hLm, M, hM⟩
    · refine hnc fun K hK J hJ => ?_
      obtain rfl := lieKindSl23One_proved _ _ hsec hsh K hK J hJ
      exact Relation.ReflTransGen.refl
    · exact hfin (Or.inr ⟨_, Or.inr rfl, hsec, hsh⟩)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
