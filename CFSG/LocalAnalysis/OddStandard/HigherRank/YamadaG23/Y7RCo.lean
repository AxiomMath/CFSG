module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] {t : G} {P U : Subgroup G}

private lemma conj_conj_of_sq {H : Type} [Group H] {s x : H} (hs : s ^ 2 = 1) :
    s * (s * x * s⁻¹) * s⁻¹ = x := by
  have hs' : s * s = 1 := by simpa [pow_two] using hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs'
  rw [hsinv]
  calc s * (s * x * s) * s = (s * s) * x * (s * s) := by group
    _ = x := by rw [hs']; simp

theorem Wr7.exists_fixed (h : Wr7 t P U) {x : G} (hc : x⁻¹ * (t * x * t⁻¹) ∈ P) :
    ∃ p ∈ P, t * (x * p) * t⁻¹ = x * p := by
  obtain ⟨u, hu, v, hv, hcuv⟩ := h.decomp hc
  obtain ⟨u₁, hu₁, hv_eq⟩ := (mem_conjSub_iff' t U v).mp hv
  have hu'U' : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
  have hv'U : t * v * t⁻¹ ∈ U := by
    rw [hv_eq, conj_conj_of_sq h.t_sq]
    exact hu₁
  have hcomm1 : (t * v * t⁻¹) * v = v * (t * v * t⁻¹) := h.direct.2.2 _ hv'U _ hv
  have hcomm2 : (t * v * t⁻¹) * (t * u * t⁻¹) = (t * u * t⁻¹) * (t * v * t⁻¹) :=
    h.direct.2.2 _ hv'U _ hu'U'
  have hcinv : t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹ = (x⁻¹ * (t * x * t⁻¹))⁻¹ := by
    have hsplit : t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹
        = (t * x⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
    rw [hsplit, conj_conj_of_sq h.t_sq, mul_inv_rev, inv_inv, conj_inv]
  have hc1 : (x⁻¹ * (t * x * t⁻¹)) * (t * (x⁻¹ * (t * x * t⁻¹)) * t⁻¹) = 1 := by
    rw [hcinv, mul_inv_cancel]
  have hprod : (u * (t * v * t⁻¹)) * (v * (t * u * t⁻¹)) = 1 := by
    rw [← hc1, hcuv]
    have htc : t * (u * v) * t⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹) := by group
    rw [htc]
    calc (u * (t * v * t⁻¹)) * (v * (t * u * t⁻¹))
        = u * ((t * v * t⁻¹) * v) * (t * u * t⁻¹) := by group
        _ = u * (v * (t * v * t⁻¹)) * (t * u * t⁻¹) := by rw [hcomm1]
        _ = u * v * ((t * v * t⁻¹) * (t * u * t⁻¹)) := by group
        _ = u * v * ((t * u * t⁻¹) * (t * v * t⁻¹)) := by rw [hcomm2]
        _ = (u * v) * ((t * u * t⁻¹) * (t * v * t⁻¹)) := by group
  obtain ⟨-, hv1⟩ := h.unique (U.mul_mem hu hv'U) U.one_mem
    ((conjSub t U).mul_mem hv hu'U') (conjSub t U).one_mem (by simpa using hprod)
  refine ⟨u, h.le_left.1 hu, ?_⟩
  calc t * (x * u) * t⁻¹
      = (t * x * t⁻¹) * (t * u * t⁻¹) := by group
      _ = (x * (x⁻¹ * (t * x * t⁻¹))) * (t * u * t⁻¹) := by group
      _ = (x * (u * v)) * (t * u * t⁻¹) := by rw [hcuv]
      _ = x * u * (v * (t * u * t⁻¹)) := by group
      _ = x * u := by rw [hv1]; group

end CFSG.OddStandard.HigherRank.YamadaG23
