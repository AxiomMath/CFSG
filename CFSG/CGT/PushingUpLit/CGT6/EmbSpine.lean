module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEightFive

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

@[expose] def O2Step4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Pre G T Y → conjClosure Y G ⊔ T = G → pCore 2 ↥G = ⊥

@[expose] def CommStep4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb4Pre G T Y → conjClosure Y G ⊔ T = G →
      pCore 2 ↥G = ⊥ → commV G = ⊤

@[expose] def O2Step5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb5Pre G T Y → conjClosure Y G ⊔ T = G → pCore 2 ↥G = ⊥

@[expose] def CommStep5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), Emb5Pre G T Y → conjClosure Y G ⊔ T = G →
      pCore 2 ↥G = ⊥ → commV G = ⊤

theorem emb4All_of_end (hO : O2Step4) (hC : CommStep4) (hEnd : Emb4End) : Emb4All := by
  by_contra h
  obtain ⟨V, _, _, hV, G, T, Y, hpre⟩ := exists_emb4Pre h
  have hgen := hpre.gen hV
  have ho2 := hO V hV G T Y hpre hgen
  exact hEnd V hV G T Y
    { adm := hpre.adm, kgroup := hpre.kgroup, sylow := hpre.sylow, nolift := hpre.nolift,
      ih := hpre.ih, maxY := hpre.maxY, o2 := ho2, comm := hC V hV G T Y hpre hgen ho2,
      cent := hpre.cent hV ho2, gen := hgen }

theorem emb5All_of_end (h4 : Emb4All) (hM6 : Omega4OrderThree) (hO : O2Step5) (hC : CommStep5)
    (hEnd : Emb5End) : Emb5All := by
  by_contra h
  obtain ⟨V, _, _, hV, G, T, Y, hpre⟩ := exists_emb5Pre h
  have hgen := hpre.gen hV
  have ho2 := hO V hV G T Y hpre hgen
  exact hEnd V hV G T Y
    { adm := hpre.adm, kgroup := hpre.kgroup, sylow := hpre.sylow, nolift := hpre.nolift,
      ih := hpre.ih, h4 := h4, m6 := hM6, o2 := ho2, comm := hC V hV G T Y hpre hgen ho2,
      cent := hpre.cent hV h4 hM6 ho2, gen := hgen }

theorem aschbacherEmbeddingFourK_of_all (h : Emb4All) : AschbacherEmbeddingFourK :=
  fun V _ _ hV G hK T Y hTG hT1 hT2 hYC hsub hperf hcl =>
    h V hV G hK T Y ⟨hTG, hT1, hT2, hYC, hsub, hperf, Or.inl hcl⟩

theorem aschbacherEmbeddingFiveK_of_all (h : Emb5All) : AschbacherEmbeddingFiveK :=
  fun V _ _ hV G hK T Y hTG hT1 hT2 hYC hsub h3 h4 =>
    h V hV G hK T Y ⟨hTG, hT1, hT2, hYC, hsub, h3, h4⟩

theorem aschbacherEmbeddingK_of_end (hM6 : Omega4OrderThree) (hO4 : O2Step4) (hC4 : CommStep4)
    (hO5 : O2Step5) (hC5 : CommStep5) (h4End : Emb4End) (h5End : Emb5End) :
    AschbacherEmbeddingK := by
  have h4 := emb4All_of_end hO4 hC4 h4End
  exact ⟨aschbacherEmbeddingFourK_of_all h4,
    aschbacherEmbeddingFiveK_of_all (emb5All_of_end h4 hM6 hO5 hC5 h5End)⟩

end CFSG.CGT.PushingUpLit.CGT6
