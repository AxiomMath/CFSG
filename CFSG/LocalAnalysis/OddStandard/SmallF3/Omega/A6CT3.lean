module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CRed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CXFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem a6c_autCentOmega5_of_check
    (hc : ∀ (Γ : Type) [Group Γ], A6CModel 5 Γ → A6CPairFacts Γ (fun _ => True) 10 2) :
    Asc82AutCentOmega5 := by
  intro G _ _ X J R hX hJ hXL hJ5 hXJ hR2 hR
  obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_five (L := J) ⟨hJ, hJ5⟩
  have hsh : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) := Or.inl ⟨hdim, hsgn⟩
  obtain ⟨φ, ψ, hker, -, hcomm, hψ⟩ := a6c_theta_homs hQ hsh hJ.1.commutator_eq_top e hXJ
    (fun r hr => (hR hr).1) (fun r hr => (hR hr).2)
  obtain ⟨⟨eA⟩, hodd⟩ := a6c_X_facts hX hXL
  obtain ⟨c, hc0, ⟨fr⟩⟩ := exists_nframe_five hQ hdim
  obtain ⟨m, -⟩ := a6c_model_of_frame fr hc0
  have hcard : Nat.card (ProjSim Q) = 51840 := ff_natCard_projSim_five hQ hdim
  haveI : Finite (ProjSim Q) := Nat.finite_of_card_ne_zero (by omega)
  have hΓ : ¬ 25 ∣ Nat.card (ProjSim Q) := by rw [hcard]; norm_num
  obtain ⟨hle, -⟩ := a6c_red (P := fun _ => True) (kc := 10) (bound := 2)
    (fun _ _ _ => trivial) hΓ (by norm_num) (hc _ m) φ ψ eA hodd hker
    (fun _ _ _ _ => trivial) hcomm
  rw [Subgroup.relIndex, ← hψ, Subgroup.index_ker]
  exact hle

end CFSG.OddStandard.SmallF3.Omega
