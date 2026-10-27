module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Syl

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_two_sylow {C T : Subgroup G} (hTC : T ≤ C) (hTp : IsPGroup 2 T)
    (hTodd : ¬ 2 ∣ T.relIndex C) {w : G} (hwC : w ∈ C) (hw : IsPGroup 2 (zpowers w)) :
    ∃ c ∈ C, c * w * c⁻¹ ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp₁ : IsPGroup 2 (T.subgroupOf C) :=
    hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  let S₁ : Sylow 2 ↥C := hp₁.toSylow hTodd
  have hwle : zpowers w ≤ C := by rw [zpowers_le]; exact hwC
  have hp₂ : IsPGroup 2 ((zpowers w).subgroupOf C) :=
    hw.of_equiv (Subgroup.subgroupOfEquivOfLe hwle).symm
  obtain ⟨Q, hQ⟩ := hp₂.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C Q S₁
  refine ⟨g, g.2, ?_⟩
  have hwQ : (⟨w, hwC⟩ : ↥C) ∈ (Q : Subgroup ↥C) :=
    hQ (Subgroup.mem_subgroupOf.2 (mem_zpowers w))
  have h1 : g * ⟨w, hwC⟩ * g⁻¹ ∈ (S₁ : Subgroup ↥C) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hwQ
  have h2 : g * ⟨w, hwC⟩ * g⁻¹ ∈ T.subgroupOf C := h1
  exact Subgroup.mem_subgroupOf.1 h2

theorem exists_sq_mem_sylow {T : Subgroup G} (hTp : IsPGroup 2 T) (hTodd : ¬ 2 ∣ T.index) {u w : G}
    (hu : ∀ x ∈ T, u * x = x * u) (hw : IsPGroup 2 (zpowers w)) (hwu : w * w = u) :
    ∃ w' ∈ T, w' * w' = u := by
  set C : Subgroup G := centralizer ({u} : Set G) with hC
  have hTC : T ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hu x hx).symm
  have hodd : ¬ 2 ∣ T.relIndex C := by
    intro hd
    have h1 := Subgroup.relIndex_mul_index hTC
    exact hTodd (by rw [← h1]; exact Dvd.dvd.mul_right hd _)
  have hwC : w ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    calc w * u = w * (w * w) := by rw [hwu]
      _ = (w * w) * w := by group
      _ = u * w := by rw [hwu]
  obtain ⟨c, hcC, hcT⟩ := exists_conj_mem_two_sylow hTC hTp hodd hwC hw
  refine ⟨c * w * c⁻¹, hcT, ?_⟩
  have hcu : c * u = u * c := (Subgroup.mem_centralizer_singleton_iff.1 hcC).symm ▸ rfl
  calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
    _ = c * u * c⁻¹ := by rw [hwu]
    _ = u := by rw [hcu]; group

end CFSG.EvenSporadicStandard.M22Std
