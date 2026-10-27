module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Extra
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

theorem lemma6_12_of (h611 : Lemma6_11) (h67 : Prop6_7) (hplane : OddNoncyclicPlane) : Lemma6_12 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  obtain ⟨-, -, -, hd, he, hf⟩ := h611 G z k S M p hC Q X hmin
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hmin.Q_mem.2.2.2.1
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hZc : zOf Q ≤ centralizer (Q : Set G) := inf_le_right
  have hcyc : IsCyclic ↥(zOf Q) := by
    by_contra hnc
    obtain ⟨V, hVZ, hVe, hV2⟩ := hplane G p hp hp2 (zOf Q) (hQp.to_le hZQ) hnc
    apply hmin.X_not
    have hVX : V ≤ normalizer (X : Set G) :=
      (hVZ.trans hZc).trans ((Subgroup.centralizer_le (fun x hx => hmin.X_le hx)).trans
        (Subgroup.centralizer_le_normalizer _))
    exact h67 G z k S M p hC p V hp (le_inf ((hVZ.trans hZQ).trans hQP) (hVZ.trans he)) hVe hV2
      (fun v hv hv1 => hf v (hVZ hv) hv1) X (hmin.X_le.trans (hQP.trans (Op_le_Fm p hp M))) hmin.X_ne
      (sup_le hVX (Subgroup.zpowers_le.mpr hmin.X_inv))
  exact isExtraspecial_of_extraG hp hQp hexp (extraG_of_cyclic_center hp hexp hcl hd hcyc)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
