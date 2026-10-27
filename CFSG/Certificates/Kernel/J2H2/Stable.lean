module

public import CFSG.RankThree.PartTwo.J2Residue.H2Transfer

public section

namespace CFSG.RankThree.PartTwo.J2Residue.H2

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem conj_cob {ρ : G →* Module.End (ZMod 2) V} {c : G → G → V} (hc : IsNormCoc ρ c) (g : G) :
    ∀ s t, ρ g⁻¹ (c (g * s * g⁻¹) (g * t * g⁻¹)) - c s t =
      cob ρ (fun s => ρ g⁻¹ (c (g * s * g⁻¹) g - c g s)) s t := by
  intro s t
  have h1 := hc.2.2 (g * s * g⁻¹) (g * t * g⁻¹) g
  have h2 := hc.2.2 g s t
  have h3 := hc.2.2 (g * s * g⁻¹) g t
  have e1 : g * t * g⁻¹ * g = g * t := by group
  have e2 : g * s * g⁻¹ * g = g * s := by group
  have e3 : g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
  have e4 : g * s * g⁻¹ * (g * t) = g * (s * t) := by group
  rw [e1] at h1
  rw [e2] at h3
  rw [e3] at h1
  have hs : ∀ y, ρ s (ρ g⁻¹ y) = ρ g⁻¹ (ρ (g * s * g⁻¹) y) := by
    intro y
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  have hc' : c s t = ρ g⁻¹ (ρ g (c s t)) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [cob]
  rw [hs, hc']
  simp only [← map_sub, ← map_add]
  congr 1
  rw [← sub_eq_zero]
  have key : -(ρ (g * s * g⁻¹) (c (g * t * g⁻¹) g) - c (g * (s * t) * g⁻¹) g +
      c (g * s * g⁻¹) (g * t) - c (g * s * g⁻¹) (g * t * g⁻¹)) +
      (ρ (g * s * g⁻¹) (c g t) - c (g * s) t + c (g * s * g⁻¹) (g * t) - c (g * s * g⁻¹) g) -
      (ρ g (c s t) - c (g * s) t + c g (s * t) - c g s) = 0 := by
    rw [h1, h2, h3]
    simp
  rw [← key, map_sub]
  abel

theorem conjDiff_cob {ρ : G →* Module.End (ZMod 2) V} {c : G → G → V} (hc : IsNormCoc ρ c) (g : G) :
    ∃ γ : G → V, ∀ s t, c s t - ρ g⁻¹ (c (g * s * g⁻¹) (g * t * g⁻¹)) = cob ρ γ s t := by
  refine ⟨fun s => -ρ g⁻¹ (c (g * s * g⁻¹) g - c g s), fun s t => ?_⟩
  have h := conj_cob hc g s t
  simp only [cob, map_neg] at h ⊢
  rw [← neg_sub, h]
  abel

end CFSG.RankThree.PartTwo.J2Residue.H2

end
