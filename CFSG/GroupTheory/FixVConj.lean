module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.UCK

variable {G V : Type} [Group G] {p : ℕ}
  [AddCommGroup V] [Module (ZMod p) V] (ρ : Representation (ZMod p) G V)

theorem fixV_map_conj (A : Subgroup G) (g : G) :
    fixV ρ (A.map (MulAut.conj g).toMonoidHom) = (fixV ρ A).map (ρ g) := by
  have hpg : ∀ x : V, (ρ g⁻¹) ((ρ g) x) = x := fun x => by
    change (ρ g⁻¹ * ρ g) x = x
    rw [← MonoidHom.map_mul, inv_mul_cancel, MonoidHom.map_one]
    rfl
  ext v
  constructor
  · intro hv
    refine ⟨(ρ g⁻¹) v, ?_, ?_⟩
    · intro a ha
      have hmemA : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hfix := hv (g * a * g⁻¹) hmemA
      have hfix' : ρ g (ρ a ((ρ g⁻¹) v)) = v := by
        simpa [MonoidHom.map_mul, mul_assoc] using hfix
      have h2 := congrArg (fun w => (ρ g⁻¹) w) hfix'
      simpa only [hpg] using h2
    · simp
  · rintro ⟨w, hw, rfl⟩
    intro b hb
    obtain ⟨a, ha, hba⟩ := Subgroup.mem_map.mp hb
    have hwa : ρ a w = w := hw a ha
    have hba' : ρ b = ρ g * ρ a * ρ g⁻¹ := by
      rw [← hba]
      change ρ (g * a * g⁻¹) = ρ g * ρ a * ρ (g⁻¹)
      rw [MonoidHom.map_mul, MonoidHom.map_mul]
    rw [hba']
    change ρ g (ρ a ((ρ g⁻¹) ((ρ g) w))) = ρ g w
    rw [hpg, hwa]

theorem fixV_map_conj_eq_bot (A : Subgroup G) (g : G) (h : fixV ρ A = ⊥) :
    fixV ρ (A.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  rw [fixV_map_conj, h, Submodule.map_bot]

end CFSG.GroupTheory

end
