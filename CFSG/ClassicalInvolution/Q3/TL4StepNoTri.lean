module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu6
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4D
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Defs

variable {Y : Type} [Group Y]

@[expose] def LinkAlphaBad (R : Subgroup Y) (t : Y) : Prop :=
  ∃ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∃ u : Y,
    IsUniqueInvolution J u ∧ alphaOf (Subgroup.closure ({t, u} : Set Y)) ≠ ⊥

end Defs

section Cit3

@[expose] def TightLinkCasesR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkS3S4 R t ∨ LinkE4 R t ∨ LinkAEAt R t

@[expose] def TightAECommonNbrR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      LinkAEAt R t → ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
        ∃ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem not_linkAEAt_of_not_triNbrAll (h117 : Model117) (h117p : Model117Pair)
    (hE : TightAE286ExistR r n) (hN : TightAE286NoneR r n) (hC : TightAECommonNbrR r n)
    (hL : TightLargeHypR r n Y R S t) (hc : DConnected (CoreAssembly.conjClass (tightCore R)))
    (hA : ¬ TriNbrAll R t) : ¬ LinkAEAt R t := by
  intro hAE
  obtain ⟨J, hJ, hbad⟩ := exists_noGNbr_of_not_triNbrAll hA
  obtain ⟨J', hJ', hJJ'⟩ := hC Y R S t hL hc hAE J hJ
  exact not_linkAEAt_of_noGNbr h117 h117p hE hN hL hc hJ hbad hJ' hJJ' hAE

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
