module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuPf2Mu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MLab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitE4
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE



variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem secMuExcl_of_frame (hO8 : E4O8TwinModel)
    (hSp : E4Sp6FrameModel) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (hodd : ∀ K ∈ Φ, ∀ z : X, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set X)) = ⊥)
    {A A' B : Subgroup X} {z u₁ u₂ τ ε : X} (F : TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') : TwinPerpV3.SecMuExcl X Φ := by
  have hnbr : A' ∈ omegaNbr Φ A :=
    Q3CL.T3.twin_mem_omegaNbr hS.hyp F.hA F.hA' F.hne.symm F.hzA F.hzA'
  have hTO : TwinOnlyNbr Φ := twinOnly_of_trans hS.hyp.conjInvariant htrans F.hA (fun M hM => hnb M hM.1 hM)
  have h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J := fun J hJ =>
    (ExitU.members hS htrans F.hA F.hzA (hodd A F.hA z F.hzA) J hJ).1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a :=
    TL4.commutes_of_mem_omegaNbr hS.hyp h2 F.hA hnbr
  have hDof : (∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb) → ThmDHyp 3 Φ := by
    rintro ⟨M, hM, zb, hzb, hO⟩
    have FF := ExitU.q8Fam_of_q8Section hS htrans hM hzb (hodd M hM zb hzb) hO
    exact ⟨FF.hyp, FF.two, FF.card, FF.aEmpty, FF.gen, FF.trans, FF.oddFree, FF.inO2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hno hE
    exact false_of_twinFrame_twinE4 hO8 hSp hS htrans h2
      (fun K hK zb hzb hO => hno ⟨K, hK, zb, hzb, hO⟩) hTO hE F hnbr
  · intro hO2m hW m hm hI
    obtain ⟨I⟩ := hI
    by_cases hm7 : m = 7
    · subst hm7
      exact false_of_twinFrame_aeIdent7 hS I F hcomm
    · obtain ⟨B', hB', C, hC, D, hD', hCD⟩ :=
        TL4.LinkE2.exists_two_nbrs_of_aeIdent (hDof hO2m) (by omega) I
      exact hCD (hTO B' hB' C hC D hD')
  · intro hO2m hW hI
    obtain ⟨I⟩ := hI
    exact false_of_twinFrame_e64 hS I F hcomm
  · intro hO2m hW hI
    obtain ⟨I⟩ := hI
    obtain ⟨B', hB', C, hC, D, hD', hCD⟩ :=
      TL4.LinkE2.exists_two_nbrs_of_e29 (hDof hO2m) I F.hA
    exact hCD (hTO B' hB' C hC D hD')
  · intro hO2m hW hI
    obtain ⟨E, hE⟩ := hI
    exact F.hne (TC.Thin.eq_of_inv_e8 (hDof hO2m) hE F.hA F.hA' F.hzA F.hzA')

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E4M
