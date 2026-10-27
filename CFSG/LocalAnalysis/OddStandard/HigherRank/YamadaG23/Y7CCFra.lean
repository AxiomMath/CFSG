module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

open scoped Pointwise

theorem y7c_frattini {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (K K0 Q : Subgroup G) (hK0K : K0 ≤ K) (hK0n : ∀ k ∈ K, ∀ x ∈ K0, k * x * k⁻¹ ∈ K0)
    (hS : IsSylowIn p K0 Q) :
    ∀ k ∈ K, ∃ x ∈ K0, ∃ n ∈ K, (∀ q ∈ Q, n * q * n⁻¹ ∈ Q) ∧ k = x * n := by
  intro k hk
  have hK0norm : K ≤ normalizer (K0 : Set G) := Subgroup.le_normalizer_iff.mpr hK0n
  let fk : G →* G := MulAut.conj (k : G)
  have hK0map : K0.map fk = K0 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK0norm hk)
  let D : Subgroup G := Q.map fk
  have hDK0 : D ≤ K0 := by
    rintro d ⟨q, hq, rfl⟩
    show k * q * k⁻¹ ∈ K0
    exact hK0n k hk q (hS.1 hq)
  have hD2 : IsPGroup p D := hS.2.1.map fk
  have hDrel : D.relIndex K0 = Q.relIndex K0 := by
    have h := Subgroup.relIndex_map_map_of_injective (f := fk) Q K0
      (MulAut.conj (k : G)).injective
    rw [hK0map] at h
    exact h
  let Qk : Subgroup ↥K0 := Q.subgroupOf K0
  have hQk : IsPGroup p Qk := hS.2.1.comap_of_injective K0.subtype Subtype.coe_injective
  have hQkidx : ¬ p ∣ Qk.index := hS.2.2
  let Dk : Subgroup ↥K0 := D.subgroupOf K0
  have hDk : IsPGroup p Dk := hD2.comap_of_injective K0.subtype Subtype.coe_injective
  have hDkidx : ¬ p ∣ Dk.index := by
    show ¬ p ∣ D.relIndex K0
    rw [hDrel]
    exact hS.2.2
  let P₁ : Sylow p ↥K0 := hQk.toSylow hQkidx
  let P₂ : Sylow p ↥K0 := hDk.toSylow hDkidx
  haveI : P₁.FiniteIndex := inferInstance
  haveI : Finite (Sylow p ↥K0) := Sylow.finite_of_finiteIndex P₁
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥K0) P₁ P₂
  have hcoe : MulAut.conj x • Qk = Dk := by
    have h := congrArg (fun Q : Sylow p ↥K0 => (Q : Subgroup ↥K0)) hx
    simpa only [P₁, P₂, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using h
  have hsub : (MulAut.conj (x : G) • Q).subgroupOf K0 = D.subgroupOf K0 := by
    rw [← Subgroup.conj_smul_subgroupOf hS.1 x]
    simpa only [Qk, Dk] using hcoe
  have hfinal : MulAut.conj (x : G) • Q = D := by
    have hinf := Subgroup.subgroupOf_inj.mp hsub
    rw [inf_eq_left.mpr (Subgroup.conj_smul_le_of_le hS.1 x), inf_eq_left.mpr hDK0] at hinf
    exact hinf
  refine ⟨(x : G), x.2, (x : G)⁻¹ * k, K.mul_mem (K.inv_mem (hK0K x.2)) hk, ?_, ?_⟩
  · intro q hq
    have hfk : fk q = k * q * k⁻¹ := rfl
    have hkq : fk q ∈ D := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    have hy : fk q ∈ MulAut.conj (x : G) • Q := hfinal.symm ▸ hkq
    have hmem := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hy
    have hxq : (x : G)⁻¹ * fk q * (x : G) ∈ Q := by
      simpa only [MulAut.smul_def, MulAut.conj_inv_apply] using hmem
    have hL : ((x : G)⁻¹ * k) * q * ((x : G)⁻¹ * k)⁻¹
        = (x : G)⁻¹ * fk q * (x : G) := by
      rw [hfk]
      group
    rw [hL]
    exact hxq
  · group

end CFSG.OddStandard.HigherRank.YamadaG23
