module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLogic

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G] [Finite G] {t : G} {L S T₂ : Subgroup G}
  {x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G} {π : Model →* G}

theorem fzfus_rows (hC : ClassFact) (hR : RowsFact)
    (h : FzSetting7 t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂)
    (hd : FzfDict t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ π) :
    ∀ e u v, (e, u, v) ∈ rowTable → ConjClasses.mk (π (rep e)) = ConjClasses.mk t →
      FzfRow (ConjClasses.mk t) (ConjClasses.mk ((x₁ * x₂) ^ 2)) (ConjClasses.mk tau)
        (ConjClasses.mk (t * tau)) (ConjClasses.mk (π (rep u))) (ConjClasses.mk (π (rep v))) := by
  have hP := fzProdLemma
  intro e u v hrow hconj
  obtain ⟨w, hwcomm, hw2, hwne, hw4, hw5, hw6⟩ := hR (e, u, v) hrow
  have hEt : IsConj t (π (rep e)) := (ConjClasses.mk_eq_mk_iff_isConj.mp hconj).symm
  have hcomm : π w * π (rep e) = π (rep e) * π w := by
    simp only [← map_mul]
    exact (hd.eq_iff (w * rep e) (rep e * w)).mpr hwcomm
  have hU2 : π w ^ 2 = 1 := by
    rw [pow_two]
    exact ((hd.isInvM_iff w).mp hw2).1
  have hU1 : π w ≠ 1 := ((hd.isInvM_iff w).mp hw2).2
  have hUE : π w ≠ π (rep e) := fun hh => hwne ((hd.eq_iff w (rep e)).mp hh)
  have hw5' : clsOf w = u := hw5
  have hw6' : clsOf (w * rep e) = v := hw6
  have hcu : ConjClasses.mk (π (rep u)) = ConjClasses.mk (π w) := by
    rw [← hw5']
    exact (hd.cl_eq hC hw2).symm
  have hcv : ConjClasses.mk (π (rep v)) = ConjClasses.mk (π w * π (rep e)) := by
    rw [← hw6', ← map_mul]
    exact (hd.cl_eq hC hw4).symm
  rcases hP G t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ h (π (rep e)) (π w) hEt hcomm hU2 hU1
    hUE with h1 | h2 | h3 | h4
  · unfold FzfRow
    exact Or.inl ⟨hcu.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h1.1.symm),
      hcv.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h1.2.symm)⟩
  · unfold FzfRow
    exact Or.inr (Or.inl ⟨hcu.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h2.1.symm),
      hcv.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h2.2.symm)⟩)
  · unfold FzfRow
    exact Or.inr (Or.inr (Or.inl ⟨hcu.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h3.1.symm),
      hcv.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h3.2.symm)⟩))
  · unfold FzfRow
    exact Or.inr (Or.inr (Or.inr ⟨hcu.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h4.1.symm),
      hcv.trans (ConjClasses.mk_eq_mk_iff_isConj.mpr h4.2.symm)⟩))

end CFSG.OddStandard.SmallF3.FritzII
