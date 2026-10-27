module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenF
public import CFSG.CGT.PushingUpLit.BHS7.SevenTwelveZ
public import CFSG.CGT.PushingUpLit.BHS7.SevenSix
public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenA

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def Seven135 (G T : Subgroup Γ) : Prop :=
  ∀ E H P : Subgroup Γ, E ∈ bStarT G T → ⁅vSub G T, zSub T⁆ ≠ ⊥ → IsMaximalSubgroup G H →
    E ⊔ baum T ≤ H → IsSubnormal E H →
    (∀ H' : Subgroup Γ, IsMaximalSubgroup G H' → E ⊔ baum T ≤ H' → H' = H) →
    T ≤ H → G ⊓ Subgroup.normalizer (T : Set Γ) ≤ H →
    G ⊓ Subgroup.centralizer (vSub G T : Set Γ) ≤ H → T ≤ P → P < G → ¬ P ≤ H →
    (∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ H) → P ⊔ E = G →
    zSub T ⊓ pCoreOf 2 P ≤ Subgroup.centralizer (vSub G T : Set Γ)

section Finite

variable [Finite Γ] {G T : Subgroup Γ}

theorem seven_thirteen_z (h : MinCex G T)
    (h5 : Seven5 G T) (h7 : Seven7 G T) (h135 : Seven135 G T)
    (hZ : ⁅vSub G T, zSub T⁆ ≠ ⊥) : False := by
  have hT : IsSylowTwoOf T G := h.sylow
  have h5' : ¬ IsMinParabolic2 T G := h5
  obtain ⟨⟨F, hF, hFn⟩, hmax⟩ := seven_six h h5'
  obtain ⟨E, hE, -⟩ := hmax F hF hFn
  obtain ⟨H, hH, hEH, hsub, huniq⟩ := h7 E hE
  have hcomm := seven_twelve_of_ne h hE hH hEH hZ
  have hne : ¬ tZero G T ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
    rw [tZero_of_ne hZ]
    intro hle
    apply hZ
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv z hz
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hle hz) v hv
  obtain ⟨-, hTH, hNH, hCH⟩ := seven_thirteen_one h hE hcomm hne huniq
  obtain ⟨P, hTP, hPG, hPH, hmin⟩ := exists_minimal_overgroup h h5' hH hTH hNH
  have hEG : E ≤ G := hE.1.2.le
  have hPE : P ⊔ E = G := sup_eq_top_of_not_le huniq hPG.le hEG hTP hPH
  have hA := h135 E H P hE hZ hH hEH hsub huniq hTH hNH hCH hTP hPG hPH hmin hPE
  exact branch_z_false h hTH hNH hCH hTP hPG hPH hmin hZ hA

end Finite

end CFSG.CGT.PushingUpLit.BHS7
