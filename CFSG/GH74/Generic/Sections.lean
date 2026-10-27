module

public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.Conclusion
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.GH74

theorem ghList_of_surjection {G : Type} [Group G] (hK : KGH G) {H : Subgroup G} (hH : H ≠ ⊤)
    {S : Type} [Group S] (f : H →* S) (hf : Function.Surjective f) (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) : GHList S := by
  let e : (H ⧸ f.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hsimple : IsSimpleGroup (H ⧸ f.ker) := (e.isSimpleGroup_congr).2 hs
  have hnonab : ∃ a b : H ⧸ f.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  exact GHList.of_mulEquiv e (hK H hH f.ker inferInstance hsimple hnonab)

theorem ghList_of_quasisimple {G : Type} [Group G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hK : KGH G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hq : IsQuasisimple ↥K) :
    GHList (↥K ⧸ center ↥K) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hCtop : C ≠ ⊤ := GLS.centralizer_involution_ne_top hs hn hx
  let π : ↥C →* CentralizerBar x := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  let Kpre : Subgroup ↥C := K.comap π
  let H : Subgroup G := Kpre.map C.subtype
  have hHle : H ≤ C := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hH : H ≠ ⊤ := fun h => hCtop (top_le_iff.1 (h ▸ hHle))
  let e₁ : ↥Kpre ≃* ↥H := Kpre.equivMapOfInjective C.subtype C.subtype_injective
  let q : ↥Kpre →* ↥K := (π.comp Kpre.subtype).codRestrict K fun k => k.2
  have hq' : Function.Surjective q := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥C) (k : CentralizerBar x)
    exact ⟨⟨c, show π c ∈ K by rw [hc]; exact k.2⟩, Subtype.ext hc⟩
  let f : ↥H →* ↥K ⧸ center ↥K := ((QuotientGroup.mk' (center ↥K)).comp q).comp e₁.symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.mk'_surjective _).comp hq').comp e₁.symm.surjective
  exact ghList_of_surjection hK hH f hf hq.2.1 hq.2.2

end CFSG.GH74.Generic
