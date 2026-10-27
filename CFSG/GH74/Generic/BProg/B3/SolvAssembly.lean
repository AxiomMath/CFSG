module

public import CFSG.GH74.Generic.BProg.B3.SolvStabNbhd
public import CFSG.GH74.Generic.BProg.B3.SolvStab
public import CFSG.GH74.Generic.BProg.B1.Nontriv
public import CFSG.GH74.Generic.BProg.B1.ThetaPrime

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B1
  Subgroup
open scoped commutatorElement

@[expose] def Prop10_1Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp2 G → ∀ (x y : G) (K E : Subgroup G)
    (Lb Ib : Subgroup (CentralizerBar x)) (I0 I1 : Subgroup G), orderOf x = 2 →
    IsPCompIn 2 (centralizer ({x} : Set G)) K → SolvAdm x y K E Lb Ib → SolvLift x y E Lb I0 I1 →
      ∀ d ∈ closure ({x, y} : Set G), d ≠ 1 → ∀ e ∈ E, e ≠ 1 →
        ⁅I0, pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({e} : Set G)⁆ ≤
          pPrimeCoreOf 2 (centralizer ({e} : Set G))

variable {G : Type} [Group G]

theorem solvAdm_dichotomy [Finite G] (h101 : Prop10_1Stmt) (hyp : Hyp2 G) {x y : G} {K E : Subgroup G}
    {Lb Ib : Subgroup (CentralizerBar x)} (hx : orderOf x = 2)
    (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) (h : SolvAdm x y K E Lb Ib) (hk : 2 ≤ pRank 2 ↥E) :
    thetaHalf (pRank 2 ↥E - 1) E ≠ ⊥ ∨ NbhdSemisimple x y Lb := by
  obtain ⟨I0, I1, hI⟩ := exists_solvLift hx hK h
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := by rw [← h.setup.y_ord]; exact pow_orderOf_eq_one y
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 h.setup.y_mem).symm
  have hD := isElementaryAbelian_closure_pair hxy hx2 hy2
  have hEC : E ≤ centralizer ((closure ({x, y} : Set G) : Subgroup G) : Set G) := by
    intro e he
    rw [centralizer_closure_pair]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact h.setup.E_le he
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h.centE e he)
  have hDE : ∀ d ∈ closure ({x, y} : Set G), ∀ e ∈ E, d * e = e * d := fun d hd e he =>
    (Subgroup.mem_centralizer_iff.1 (hEC he) d hd)
  have hI0I1 : I0 ≤ I1 := by
    rw [← hI.res_I1]
    exact Balance.oPrimeResidualOf_le_self I1
  rcases stability_DE hD h.setup.E_ea hk hDE (hI0I1.trans hI.le_cent) hI.res
      (h101 G hyp x y K E Lb Ib I0 I1 hx hK h hI) with h1 | h2
  · exact Or.inr (nbhdSemisimple_of_centralizes hx hK h hI h1)
  · left
    intro hbot
    apply h2
    rw [hbot]
    exact Subgroup.commutator_bot_right _

theorem stage1NontrivSolv_of_prop10_1 (h101 : Prop10_1Stmt) : B1.Stage1NontrivSolv := by
  intro G _ _ hyp _ x K hcirc _ A hsrc y Lb E Ib hE hs hns hbot
  rcases solvAdm_dichotomy h101 hyp hcirc.1.1.1.1 hcirc.1.1.1.2.2 hs hE.2.2 with h1 | h2
  · exact h1 (le_bot_iff.1 (hbot ▸ thetaHalf_le_thetaHalfPrime hsrc.2.1 hE))
  · exact hns h2

end CFSG.GH74.Generic.BProg.B3
