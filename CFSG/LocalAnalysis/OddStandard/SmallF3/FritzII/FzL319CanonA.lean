module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319CanonG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319SpecA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

theorem canon_of_autW (h : FzAutW D.cT D.cS D.cL) : FzCanon T W := by
  intro α hα g
  let f : FzElt → ↥T := fun x => ⟨D.mu x, D.mu_mem x⟩
  have hf : Function.Injective f := fun x y hxy => D.mu_injective (Subtype.ext_iff.mp hxy)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := D.mu_surj y.2
    exact ⟨x, Subtype.ext hx⟩
  let μ' : FzElt ≃ ↥T := Equiv.ofBijective f ⟨hf, hfs⟩
  let αT : ↥T ≃ ↥T :=
    { toFun := fun x => ⟨α x, (hα x).mp x.2⟩
      invFun := fun x => ⟨α.symm x, (hα (α.symm x)).mpr (by simpa using x.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  let σ : FzElt ≃ FzElt := μ'.trans (αT.trans μ'.symm)
  have hsigma : ∀ x : FzElt, D.mu (σ x) = α (D.mu x) := by
    intro x
    have h1 : μ' (σ x) = αT (μ' x) := by
      change μ' (μ'.symm (αT (μ' x))) = αT (μ' x)
      rw [Equiv.apply_symm_apply]
    calc D.mu (σ x) = (μ' (σ x) : G) := rfl
      _ = (αT (μ' x) : G) := by rw [h1]
      _ = α (D.mu x) := rfl
  have hm : ∀ x y : FzElt,
      σ (fzMulC D.cT D.cS D.cL x y) = fzMulC D.cT D.cS D.cL (σ x) (σ y) := by
    intro x y
    apply D.mu_injective
    calc D.mu (σ (fzMulC D.cT D.cS D.cL x y))
        = α (D.mu (fzMulC D.cT D.cS D.cL x y)) := hsigma _
      _ = α (D.mu x * D.mu y) := by rw [D.mu_mul]
      _ = α (D.mu x) * α (D.mu y) := map_mul α _ _
      _ = D.mu (σ x) * D.mu (σ y) := by rw [← hsigma x, ← hsigma y]
      _ = D.mu (fzMulC D.cT D.cS D.cL (σ x) (σ y)) := (D.mu_mul (σ x) (σ y)).symm
  by_cases hgT : g ∈ T
  · obtain ⟨x, hx⟩ := D.mu_surj hgT
    have hWx : g ∈ W ↔ fzInW D.cT x := by
      rw [D.mu_W hgT]
      constructor
      · rintro ⟨y, hy, hyW⟩
        have hyx : y = x := D.mu_injective (by rw [hy, hx])
        rwa [hyx] at hyW
      · intro hxW
        exact ⟨x, hx, hxW⟩
    have hWy : α g ∈ W ↔ fzInW D.cT (σ x) := by
      have hαgT : α g ∈ T := (hα g).mp hgT
      rw [D.mu_W hαgT]
      constructor
      · rintro ⟨y, hy, hyW⟩
        have hyσ : y = σ x := D.mu_injective (by rw [hy, hsigma, hx])
        rwa [hyσ] at hyW
      · intro hsW
        exact ⟨σ x, by rw [hsigma, hx], hsW⟩
    rw [hWx, hWy]
    exact (h σ hm x).symm
  · have hWleT : W ≤ T := D.str.WQ.trans (D.str.QR.trans D.str.RT)
    have hαgT : α g ∉ T := fun hcon => hgT ((hα g).mpr hcon)
    exact ⟨fun hw => absurd (hWleT hw) hgT, fun hw => absurd (hWleT hw) hαgT⟩

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
