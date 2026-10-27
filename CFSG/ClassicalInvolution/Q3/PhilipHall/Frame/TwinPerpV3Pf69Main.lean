module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf67Print
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

section ApplyW

variable {n : ℕ}

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW in
theorem thmEW_apply (hEW : ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (h : TwinCoreHyp n Y R S t) {K K' : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : K' ≠ K) {H : Subgroup Y}
    (htrans : ∀ J ∈ dstarComp (CoreAssembly.conjClass (tightCore R)) K, ∃ g ∈ H, conjSub g K = J)
    (hcent : ∀ W' ∈ WSet (CoreAssembly.conjClass (tightCore R)),
      K ⊓ W' ∈ USet (CoreAssembly.conjClass (tightCore R)) →
        CentralizersPrinted (CoreAssembly.conjClass (tightCore R)) K W' H) : H = ⊤ := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := h.hyp
  obtain ⟨W, hWP, hKW⟩ := exists_printedWT hΩ hK hK' hne
  obtain ⟨S₀, hWP'⟩ := hWP
  obtain ⟨R₀, -, -, hWΩ, -⟩ := id hWP'
  exact twinThmEPrintedAllT_of_thmEQ8 hEW hcit hP Y R S t h K H W S₀ hK hWP'
    ⟨htrans, (centAll_of_centAllK hΩ hK hWΩ hKW htrans
      (fun x _ hU => hcent _ (WSet.conj hΩ.conjInvariant hWΩ x) hU)).toPairs _⟩

end ApplyW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
