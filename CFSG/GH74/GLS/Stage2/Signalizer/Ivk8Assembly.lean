module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8CompNC
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem ghList_of_comp {G : Type} [Group G] (hK : KGH G) {H : Subgroup G} (hH : H ≠ ⊤)
    {J : Subgroup (HBar H)} (hJ : IsComponent J) : GHList (↥J ⧸ center ↥J) := by
  have hq : IsQuasisimple ↥J := hJ.1
  let π : ↥H →* HBar H := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let Kpre : Subgroup ↥H := J.comap π
  let Hs : Subgroup G := Kpre.map H.subtype
  have hHle : Hs ≤ H := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hHs : Hs ≠ ⊤ := fun h => hH (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥Hs := Kpre.equivMapOfInjective H.subtype H.subtype_injective
  let q : ↥Kpre →* ↥J := (π.comp Kpre.subtype).codRestrict J fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) (k : HBar H)
    exact ⟨⟨c, show π c ∈ J by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥Hs →* ↥J ⧸ center ↥J :=
    ((QuotientGroup.mk' (center ↥J)).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact Generic.ghList_of_surjection hK hHs f hf hq.2.1 hq.2.2

theorem ivk812CoreA_of_exists_comp (hT : AFrameThm) (hC : CellsAbs)
    (hX : ∀ (A : Type) [Group A] [Finite A] (zb : A) (Sb Vb : Subgroup A), AFrame A zb Sb Vb →
      ∃ J : Subgroup A, IsComponent J ∧ ¬ Vb ≤ centralizer (J : Set A)) : IVK812CoreA := by
  intro G _ _ z S hctx H hH hSH V hV hVO
  obtain ⟨zb, hfr⟩ := hT G z S hctx H hH hSH V hV hVO
  obtain ⟨J, hJ, hnc⟩ := hX (HBar H) zb (barIn H S) (barIn H V) hfr
  rcases ghList_cases (ghList_of_comp hctx.std.kgh hH hJ) with
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hC.alt (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.spor (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.mcly (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.two (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.l2 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.l3 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.u3 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.sp4 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.g2 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.d4 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.l4 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.u4 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.l5 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.u5 (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h
  · exact hC.ree (HBar H) zb (barIn H S) (barIn H V) J hfr hJ hnc h

theorem ivk812CoreA_of (hT : AFrameThm) (hC : CellsAbs) : IVK812CoreA :=
  ivk812CoreA_of_exists_comp hT hC fun _ _ _ _ _ _ hfr => hfr.exists_comp_nc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
