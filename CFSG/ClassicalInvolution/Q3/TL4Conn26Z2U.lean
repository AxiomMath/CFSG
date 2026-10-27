module

public import CFSG.ClassicalInvolution.Q3.TL4OddMu9V
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Defs
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2F

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Cit3


@[expose] def TightZ2TFreeR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      (∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
        ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M →
          ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ x ∈ P, β x = x) →
            β = 1 ∨ β = MulAut.conj a) →
      ∀ (J J₂ J₃ : Subgroup Y) (u v : Y), Z2FrameAt R t J J₂ J₃ u v →
        ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) (L : Subgroup (OddQuot u)),
          CFSG.IsComponent L → MovedByAll (Subgroup.closure ({t, u, v} : Set Y)) u L →
          Vtx.TwinFreeAt (vtxFam (CoreAssembly.conjClass (tightCore R)) u)
            (modOdd u (coreAt u (tightCore R))) (oddQuotMk u ⟨t, htu⟩) L →
          alphaOf (inducedImage L (modOdd u (Subgroup.closure ({t, u, v} : Set Y)))) = ⊥

end Cit3

section Cit3b


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem hyp51At_u (h4 : Thm4RBelow 3 n) (htw : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n)
    (hOm : OmegaAutOddFreeR) (hfree : TightZ2TFreeR 3 n) (hL : TightLargeHypR 3 n Y R S t)
    (hc : DConnected (CoreAssembly.conjClass (tightCore R))) (hA : ¬ TriNbrAll R t)
    (hcase : LinkZ2 R t)
    (hD : ∀ M ∈ linkFam R t, ∀ a : ↥(linkGrp R t), IsUniqueInvolution M a →
      ∀ P : Subgroup ↥(linkGrp R t), IsSylow2In P M →
        ∀ β : MulAut ↥(linkGrp R t), β * β = 1 → (∀ x ∈ P, β x = x) →
          β = 1 ∨ β = MulAut.conj a)
    (hF : Z2FrameAt R t J J₂ J₃ u v) :
    Hyp51At (Subgroup.closure ({t, u, v} : Set Y)) u := by
  have h := TightLargeHypR.typeRFam hL
  have ht := hL.datum.isUniqueInvolution_core
  have hK₀ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htu' : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL)
  exact hyp51At_of_member h4 htw hOm hL.below hL.center hL.card.le h (hF.isElemAbelian hL)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hF.invJ.ne_one
    ht.ne_one (hF.ne_tu hL) (xMem_of_mem_omegaNbr_nbr h hK₀ hF.memJ ht hF.invJ) ht htu'
    (hfree Y R S t hL hc hA hcase hD J J₂ J₃ u v hF htu')

end Z2FrameAt

end Cit3b

end CFSG.ClassicalInvolution.Q3.TL4
