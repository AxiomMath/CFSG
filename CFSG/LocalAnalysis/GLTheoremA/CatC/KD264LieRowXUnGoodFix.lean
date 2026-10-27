module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

open CFSG.ComponentClassification.Burgoyne.U
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.Burgoyne.Proj

theorem exists_conj_eq_mul_central {N : ℕ} (hN : 1 ≤ N) (d : uU xunH N)
    (u : StatedSU N (2 ^ 1) xunK)
    (hfix : xunConj N hN d (projH _ u) = projH _ u) :
    ∃ s : GL (Fin N) xunK, s ∈ Subgroup.center (GL (Fin N) xunK) ∧
      (d : GL (Fin N) xunK) * (u : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹ =
        (u : GL (Fin N) xunK) * s := by
  have h1 : projH _ (⟨(d : GL (Fin N) xunK) * (u : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹,
      uConjSU_mem xunH d u⟩ : StatedSU N (2 ^ 1) xunK) = projH _ u := by
    rw [← uConjAut_proj xunH hN d u]
    exact hfix
  rw [projH, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h1
  have hc' : ((⟨(d : GL (Fin N) xunK) * (u : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹,
      uConjSU_mem xunH d u⟩ : StatedSU N (2 ^ 1) xunK) : GL (Fin N) xunK)⁻¹ *
      (u : GL (Fin N) xunK) = Matrix.GeneralLinearGroup.scalar (Fin N) c := hc.symm
  simp only [Subgroup.coe_mk] at hc'
  have hinv := eq_mul_inv_of_mul_eq hc'
  refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, map_inv _ _⟩
  · calc (d : GL (Fin N) xunK) * (u : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹
        = (((d : GL (Fin N) xunK) * (u : GL (Fin N) xunK) * (d : GL (Fin N) xunK)⁻¹)⁻¹)⁻¹ :=
          (inv_inv _).symm
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin N) c) * (u : GL (Fin N) xunK)⁻¹)⁻¹ := by
          rw [hinv]
      _ = (u : GL (Fin N) xunK) * (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ := by
          rw [mul_inv_rev, inv_inv]

theorem commute_conj_of_conj_eq {G : Type*} [Group G] {d u g s : G}
    (hu : d * u * d⁻¹ = u * s) (hs : Commute s g) (hdg : d * g = g * d) :
    d * (u * g * u⁻¹) = (u * g * u⁻¹) * d := by
  have hdg' : d * g * d⁻¹ = g := by rw [hdg, mul_inv_cancel_right]
  have hdu : d * u⁻¹ * d⁻¹ = s⁻¹ * u⁻¹ := by
    have h := congrArg (fun x => x⁻¹) hu
    simp only [mul_inv_rev, inv_inv] at h
    rw [mul_assoc]
    exact h
  have key : d * (u * g * u⁻¹) * d⁻¹ = u * g * u⁻¹ := by
    calc d * (u * g * u⁻¹) * d⁻¹ = (d * u * d⁻¹) * (d * g * d⁻¹) * (d * u⁻¹ * d⁻¹) := by group
      _ = (u * s) * g * (s⁻¹ * u⁻¹) := by rw [hu, hdg', hdu]
      _ = u * (s * g * s⁻¹) * u⁻¹ := by group
      _ = u * (g * s * s⁻¹) * u⁻¹ := by rw [hs.eq]
      _ = u * g * u⁻¹ := by group
  calc d * (u * g * u⁻¹) = (d * (u * g * u⁻¹) * d⁻¹) * d := by group
    _ = (u * g * u⁻¹) * d := by rw [key]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Good

end
