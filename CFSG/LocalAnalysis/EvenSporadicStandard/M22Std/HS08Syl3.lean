module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Syl

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le_sylow_two {Γ : Type*} [Group Γ] [Finite Γ] (Q : Sylow 2 Γ)
    {W : Subgroup Γ} (hW : IsPGroup 2 W) :
    ∃ c : Γ, ∀ x ∈ W, c * x * c⁻¹ ∈ (Q : Subgroup Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ R Q
  refine ⟨g, fun x hx => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hR hx

theorem exists_normalizing_conj_of_weakly_closed (P : Sylow 2 G) {E : Subgroup G}
    (hEP : E ≤ (P : Subgroup G)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hwc : ∀ g : G, (∀ x ∈ E, g * x * g⁻¹ ∈ (P : Subgroup G)) →
      ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ E)
    {x y g : G} (hx : x ∈ E) (hy : y ∈ E) (hg : g * x * g⁻¹ = y) :
    ∃ n : G, (∀ w, w ∈ E ↔ n * w * n⁻¹ ∈ E) ∧ n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({y} : Set G) with hC
  have hEC : E ≤ C := fun w hw => Subgroup.mem_centralizer_singleton_iff.2 (hEc w hw y hy)
  have hEp : IsPGroup 2 E := (P.isPGroup').to_le hEP
  have hgEC : ∀ w ∈ E, g * w * g⁻¹ ∈ C := by
    intro w hw
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    calc g * w * g⁻¹ * y = g * (w * x) * g⁻¹ := by rw [← hg]; group
      _ = g * (x * w) * g⁻¹ := by rw [hEc w hw x hx]
      _ = y * (g * w * g⁻¹) := by rw [← hg]; group
  have hE' : IsPGroup 2 (E.subgroupOf C) := hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEC).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hQp : IsPGroup 2 (Q.map C.subtype) := Q.isPGroup'.map C.subtype
  obtain ⟨c, hc⟩ := exists_conj_le_sylow_two P hQp
  have hcE : ∀ w ∈ E, c * w * c⁻¹ ∈ (P : Subgroup G) := by
    intro w hw
    apply hc
    refine ⟨⟨w, hEC hw⟩, hQ (Subgroup.mem_subgroupOf.2 hw), rfl⟩
  have hcN := hwc c hcE
  have hW : IsPGroup 2 ((E.map (MulAut.conj g).toMonoidHom).subgroupOf C) := by
    have : IsPGroup 2 (E.map (MulAut.conj g).toMonoidHom) :=
      hEp.map (MulAut.conj g).toMonoidHom
    have hle : E.map (MulAut.conj g).toMonoidHom ≤ C := by
      rintro _ ⟨w, hw, rfl⟩
      exact hgEC w hw
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  obtain ⟨c₂, hc₂⟩ := exists_conj_le_sylow_two Q hW
  set d : G := (c₂ : G) with hd
  have hc₂E : ∀ w ∈ E, d * (g * w * g⁻¹) * d⁻¹ ∈ Q.map C.subtype := by
    intro w hw
    have hmem : (⟨g * w * g⁻¹, hgEC w hw⟩ : ↥C) ∈
        (E.map (MulAut.conj g).toMonoidHom).subgroupOf C := ⟨w, hw, rfl⟩
    exact ⟨_, hc₂ _ hmem, rfl⟩
  have hcc₂ : ∀ w ∈ E, (c * d * g) * w * (c * d * g)⁻¹ ∈ (P : Subgroup G) := by
    intro w hw
    have := hc _ (hc₂E w hw)
    simpa [mul_assoc] using this
  have hn := hwc _ hcc₂
  refine ⟨d * g, fun w => ?_, ?_⟩
  · set z := (c * d * g) * w * (c * d * g)⁻¹ with hz
    have e1 : w ∈ E ↔ z ∈ E := hn w
    have e2 : c⁻¹ * z * c ∈ E ↔ z ∈ E := by
      have := hcN (c⁻¹ * z * c)
      rw [show c * (c⁻¹ * z * c) * c⁻¹ = z by group] at this
      exact this
    have e3 : d * g * w * (d * g)⁻¹ = c⁻¹ * z * c := by rw [hz]; group
    rw [e3, e2, e1]
  · have hcy : d * y = y * d := Subgroup.mem_centralizer_singleton_iff.1 c₂.2
    calc d * g * x * (d * g)⁻¹ = d * (g * x * g⁻¹) * d⁻¹ := by group
      _ = y := by rw [hg, hcy]; group

end CFSG.EvenSporadicStandard.M22Std
