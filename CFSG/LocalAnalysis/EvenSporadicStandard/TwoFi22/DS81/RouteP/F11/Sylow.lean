module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem exists_sylow_le_of_odd_index {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Odd N.index) : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := N)
  have hQodd : Odd (Q : Subgroup N).index :=
    Nat.not_even_iff_odd.mp fun h => Q.not_dvd_index (even_iff_two_dvd.mp h)
  refine ⟨IsPGroup.toSylow (Q.isPGroup'.map N.subtype) ?_, ?_⟩
  · rw [Subgroup.index_map_subtype, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr (hQodd.mul hN)
  · exact Subgroup.map_subtype_le (Q : Subgroup N)

theorem exists_conj_of_odd_index_normalizer {G : Type*} [Group G] [Finite G] {E F : Subgroup G}
    (hodd : Odd (Subgroup.normalizer (E : Set G)).index) (hF : IsPGroup 2 F)
    (huniq : ∀ B : Subgroup G, B ≤ Subgroup.normalizer (E : Set G) → Nonempty (↥B ≃* ↥F) →
      B = E) :
    ∃ c : G, ∀ x : G, x ∈ F ↔ c⁻¹ * x * c ∈ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', hP'⟩ := exists_sylow_le_of_odd_index hodd
  obtain ⟨P, hFP⟩ := hF.exists_le_sylow
  haveI : Finite (Sylow 2 G) := by
    obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := G)
    exact Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' P
  refine ⟨g, fun x => ?_⟩
  have hB_le : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.normalizer (E : Set G) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hzF, rfl⟩ := hy
    change MulAut.conj g⁻¹ z ∈ Subgroup.normalizer (E : Set G)
    have hzP : z ∈ (P : Set G) := hFP hzF
    rw [← hg, Sylow.coe_smul, Set.mem_smul_set] at hzP
    obtain ⟨p, hp, hp_eq⟩ := hzP
    have hzp : MulAut.conj g⁻¹ z = p := by
      rw [← hp_eq]
      simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
      group
    rw [hzp]
    exact hP' hp
  have hiso : Nonempty (↥(F.map (MulAut.conj g⁻¹).toMonoidHom) ≃* ↥F) :=
    ⟨(Subgroup.equivMapOfInjective F (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm⟩
  have hB_eq : F.map (MulAut.conj g⁻¹).toMonoidHom = E := huniq _ hB_le hiso
  rw [← hB_eq, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := by
      have h2 : g⁻¹ * z * g = g⁻¹ * x * g := by
        simpa [MulAut.conj_apply] using hzx
      have := congr_arg (fun w => g * w * g⁻¹) h2
      simpa [mul_assoc] using this
    rwa [hzx'] at hz

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
