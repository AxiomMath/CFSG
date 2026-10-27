module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3GXAE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3GXW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4MGlue

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Sec




variable {n : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem secGen_of_exit_conj
    (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (hO8 : TwinDisc.ExitE4.E4O8TwinModel) (hSp : TwinPerp23.E4M.E4Sp6FrameModel)
    (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    {A A' B B' : Subgroup X} {z u₁ u₂ τ ε : X} (F : Asc77.TwinFrame Φ A A' B z u₁ u₂ τ ε)
    (hB' : B' ∈ Φ) (hτB' : IsUniqueInvolution B' τ) (hBB' : B' ≠ B) (hτz : τ ≠ z)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (hconj : ∃ g : X, conjSub g A = A') (hno : ¬ NoExit X Φ) :
    ∀ g : X, g ∈ Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({τ} : Set X) := by
  classical
  have htrans := transitive_of_conj_twin h4 hlt hS F.hA F.hA' hnb hnb' hconj
  have hnbr : A' ∈ omegaNbr Φ A :=
    Q3CL.T3.twin_mem_omegaNbr hS.hyp F.hA F.hA' F.hne.symm F.hzA F.hzA'
  have hedge : ∃ M ∈ Φ, ∃ N : Subgroup X, N ∈ omegaNbr Φ M := ⟨A, F.hA, A', hnbr⟩
  have hodd := TwinDisc.oddCentEdge_proved n hcit hP X hlt Φ hS htrans hedge
  have hMu := TwinPerp23.E4M.secMuExcl_of_frame hO8 hSp hS htrans hodd F hnb
  have hTO : TwinOnlyNbr Φ :=
    twinOnly_of_trans hS.hyp.conjInvariant htrans F.hA (fun M hM => hnb M hM.1 hM)
  have h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J := fun J hJ =>
    (members hS htrans F.hA F.hzA (hodd A F.hA z F.hzA) J hJ).1
  have hcomm : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a :=
    TL4.commutes_of_mem_omegaNbr hS.hyp h2 F.hA hnbr
  by_cases hO2m : ∃ M ∈ Φ, ∃ zb : X, IsUniqueInvolution M zb ∧ TightInO2 zb
  · obtain ⟨M, hM, zb, hzb, hO⟩ := hO2m
    have FF := q8Fam_of_q8Section hS htrans hM hzb (hodd M hM zb hzb) hO
    by_cases hW : ∃ V : Subgroup X, WSet Φ = {V}
    · obtain ⟨V, hV⟩ := hW
      exact gen_of_wUnique hS htrans hTO h2 hV F hcomm hnb hnb' hτz
    · rcases FF.thmDConcl hP.thmD.d2 hlt with h1 | ⟨W', hW'⟩ | ⟨E, hE⟩ | I64 | ⟨m, hm5, ⟨I⟩⟩ | I29
      · exact absurd (h1 A F.hA A' F.hA') F.hne
      · exact absurd ⟨W', hW'⟩ hW
      · exact absurd ⟨E, hE⟩ (hMu.noE8 ⟨M, hM, zb, hzb, hO⟩ hW)
      · exact absurd I64 (hMu.noE64 ⟨M, hM, zb, hzb, hO⟩ hW)
      · by_cases hm6 : m ≤ 6
        · exact gen_of_aeIdent (m := m) (by omega) hS I F.hA F.hA' F.hB hB' F.hne hBB'.symm F.hzA
            F.hzA' F.htB hτB' hτz
        · exact absurd ⟨I⟩ (hMu.noAE ⟨M, hM, zb, hzb, hO⟩ hW m (by omega))
      · exact absurd I29 (hMu.noE29 ⟨M, hM, zb, hzb, hO⟩ hW)
  · exfalso
    rcases noExit_or_o2_or_e4 hS htrans hedge hodd with hN | hO | hE4
    · exact hno hN
    · obtain ⟨K, hK, w, hw, hO'⟩ := hO
      exact hO2m ⟨K, hK, w, hw, hO'⟩
    · exact hMu.noE4 hO2m hE4

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.GX
