module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrVtx
public import CFSG.ClassicalInvolution.Q3.TL4MF165A
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2Defs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrDisc
public import CFSG.ClassicalInvolution.Q3.TL4GLinkAlpha

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open scoped commutatorElement Pointwise

section Cert



variable {r n : ℕ}

theorem tightAlphaNoNbrR_of_four_le (hr : 4 ≤ r) (hNo : NoQ16E4)
    (h4 : CIT3Below n → TightBelowR r n → Thm4RBelow r n) (hG : GH74SectionalModels)
    (h6 : ∀ m, TightLargeEdgeSR r m) (hZ : TightLinkZ2L2BigR r n) : TightAlphaNoNbrR r n := by
  intro Y _ _ R S t hL hc hA J hJ u hu
  by_contra hbad
  have hbad' : LinkAlphaBad R t := ⟨J, hJ, u, hu, hbad⟩
  have hdisc : TightLinkDiscR r n :=
    tightLinkDiscR_of_four_le hr hNo h4 CFSG.Goldschmidt.topStatement
  have hα : ∀ (M : Type) [Group M] [Finite M], IsSimpleGroup M →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (CFSG.Blueprint.LieModel M .PSL 3 p f ∨ CFSG.Blueprint.LieModel M .PSU 3 p f)) →
      ∀ 𝒳 : Subgroup (MulAut M), Q3NM.innSubgroup M ≤ 𝒳 →
        ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut M) ∈ Q3NM.innSubgroup M) →
          (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥ :=
    fun M _ _ hs hm => model165Aut_proved M (Or.inl ⟨hs, Or.inl hm⟩)
  obtain ⟨hnc, htr, hshape⟩ := linkShape_four_le hr hNo hG h6 h4 hdisc hL hc hA hbad'
  rcases hshape with hW | hS | hZs
  · exact hbad (alphaOf_eq_bot_of_shape hr hNo (h4 hL.below hL.tbelow) hα hL hc hA hnc htr
      (Or.inl hW) J hJ u hu)
  · exact hbad (alphaOf_eq_bot_of_shape hr hNo (h4 hL.below hL.tbelow) hα hL hc hA hnc htr
      (Or.inr hS) J hJ u hu)
  · obtain ⟨hDE, -, hSimple, hIdx, hModel, hStar⟩ := hZs
    exact hZ Y R S t hL hc hA hbad' ⟨htr, hnc, hDE, hStar⟩ hSimple hIdx hModel

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
