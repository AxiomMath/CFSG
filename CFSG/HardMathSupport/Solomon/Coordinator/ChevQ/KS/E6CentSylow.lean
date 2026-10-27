module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

theorem exists_conj_mem_centralizer_of_threeCentral {G : Type*} [Group G] [Finite G]
    {E H : Subgroup G} (hE : IsPGroup 3 E) (hH : IsPGroup 3 H)
    (hHE : H ≤ Subgroup.normalizer (E : Set G)) {z : G}
    (hz : ∃ S : Sylow 3 G, (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer (E : Set G) ∧
      g * z * g⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 G) :=
    Finite.of_injective (fun P : Sylow 3 G => (P : Set G)) SetLike.coe_injective
  obtain ⟨S, hS⟩ := hz
  obtain ⟨Q, hQ⟩ := (hH.to_sup_of_normal_right' hE hHE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have hcomm : ∀ x ∈ H ⊔ E, x * (g * z * g⁻¹) = g * z * g⁻¹ * x := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup G) := hQ hx
    rw [← hg, Sylow.coe_subgroup_smul] at hxQ
    obtain ⟨s, hs, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) S).mp hxQ
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    rw [MulAut.smul_def, MulAut.conj_apply]
    calc g * s * g⁻¹ * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by group
      _ = g * (z * s) * g⁻¹ := by rw [hsz]
      _ = g * z * g⁻¹ * (g * s * g⁻¹) := by group
  have hE' : E ≤ H ⊔ E := le_sup_right
  have hH' : H ≤ H ⊔ E := le_sup_left
  exact ⟨g, Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x (hE' hx),
    Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x (hH' hx)⟩

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
