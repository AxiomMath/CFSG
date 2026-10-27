module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise

variable {G : Type} [Group G]

structure Wr7 (t : G) (P U : Subgroup G) : Prop where
  t_sq : t ^ 2 = 1
  direct : IsInternalDirect P U (conjSub t U)

private lemma conj_conj_of_sq {t : G} (ht : t ^ 2 = 1) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have ht' : t * t = 1 := by simpa [pow_two] using ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht'
  rw [htinv]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht']; simp

theorem mem_conjSub_iff' (c : G) (Y : Subgroup G) (x : G) :
    x ∈ conjSub c Y ↔ ∃ y ∈ Y, x = c * y * c⁻¹ := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨y, hy, ?_⟩
    rw [← hyx]
    change MulAut.conj c y = c * y * c⁻¹
    rw [MulAut.conj_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    rw [hxy]
    change MulAut.conj c y = c * y * c⁻¹
    rw [MulAut.conj_apply]

theorem conjSub_conjSub_of_sq {t : G} (ht : t ^ 2 = 1) (Y : Subgroup G) :
    conjSub t (conjSub t Y) = Y := by
  ext x
  constructor
  · intro hx
    rw [mem_conjSub_iff'] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [mem_conjSub_iff'] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [hxy, hyz, conj_conj_of_sq ht]
    exact hz
  · intro hx
    rw [mem_conjSub_iff']
    exact ⟨t * x * t⁻¹, ⟨x, hx, rfl⟩, (conj_conj_of_sq ht x).symm⟩

theorem Wr7.le_left {t : G} {P U : Subgroup G} (h : Wr7 t P U) : U ≤ P ∧ conjSub t U ≤ P := by
  constructor
  · rw [← h.direct.1]
    exact le_sup_left
  · rw [← h.direct.1]
    exact le_sup_right

theorem Wr7.mul_mem' {t : G} {P U : Subgroup G} (h : Wr7 t P U) {u v : G} (hu : u ∈ U)
    (hv : v ∈ conjSub t U) : u * v ∈ P := by
  obtain ⟨hUP, hU'P⟩ := h.le_left
  exact P.mul_mem (hUP hu) (hU'P hv)

theorem Wr7.decomp {t : G} {P U : Subgroup G} (h : Wr7 t P U) {x : G} (hx : x ∈ P) :
    ∃ u ∈ U, ∃ v ∈ conjSub t U, x = u * v := by
  have hcent : U ≤ Subgroup.centralizer (conjSub t U : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (h.direct.2.2 u hu v hv).symm
  have hLE : U ≤ Subgroup.normalizer (conjSub t U : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcoe : (↑(U ⊔ conjSub t U) : Set G) = (U : Set G) * (conjSub t U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U (conjSub t U) hLE
  rw [← h.direct.1] at hx
  change x ∈ (↑(U ⊔ conjSub t U) : Set G) at hx
  rw [hcoe, Set.mem_mul] at hx
  obtain ⟨u, hu, v, hv, huv⟩ := hx
  exact ⟨u, hu, v, hv, huv.symm⟩

theorem Wr7.unique {t : G} {P U : Subgroup G} (h : Wr7 t P U) {u u' v v' : G} (hu : u ∈ U)
    (hu' : u' ∈ U) (hv : v ∈ conjSub t U) (hv' : v' ∈ conjSub t U) (e : u * v = u' * v') :
    u = u' ∧ v = v' := by
  have h1 : u'⁻¹ * u = v' * v⁻¹ := by
    have := congrArg (fun x => u'⁻¹ * x * v⁻¹) e
    simpa [mul_assoc] using this
  have hmem : u'⁻¹ * u ∈ U ⊓ conjSub t U := by
    constructor
    · exact U.mul_mem (U.inv_mem hu') hu
    · rw [h1]
      exact (conjSub t U).mul_mem hv' ((conjSub t U).inv_mem hv)
  rw [h.direct.2.1, Subgroup.mem_bot] at hmem
  have huu : u = u' := by
    rw [inv_mul_eq_one] at hmem
    exact hmem.symm
  have hvv : v = v' := by
    rw [huu] at e
    exact mul_left_cancel e
  exact ⟨huu, hvv⟩

theorem Wr7.conj_mem {t : G} {P U : Subgroup G} (h : Wr7 t P U) {x : G} (hx : x ∈ P) :
    t * x * t⁻¹ ∈ P := by
  obtain ⟨u, hu, v, hv, rfl⟩ := h.decomp hx
  obtain ⟨u₁, hu₁, rfl⟩ := (mem_conjSub_iff' t U v).mp hv
  have hU' : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
  have hcomm : (t * u * t⁻¹) * u₁ = u₁ * (t * u * t⁻¹) :=
    (h.direct.2.2 u₁ hu₁ _ hU').symm
  have heq : t * (u * (t * u₁ * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * u₁ := by
    calc t * (u * (t * u₁ * t⁻¹)) * t⁻¹
        = (t * u * t⁻¹) * (t * (t * u₁ * t⁻¹) * t⁻¹) := by group
      _ = (t * u * t⁻¹) * u₁ := by rw [conj_conj_of_sq h.t_sq]
  rw [heq, hcomm]
  exact h.mul_mem' hu₁ hU'

theorem Wr7.conjSub_eq {t : G} {P U : Subgroup G} (h : Wr7 t P U) : conjSub t P = P := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_conjSub_iff'] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h.conj_mem hy
  · intro x hx
    rw [mem_conjSub_iff']
    have ht' : t * t = 1 := by simpa [pow_two] using h.t_sq
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht'
    refine ⟨t⁻¹ * x * t, ?_, by group⟩
    have hEq : t⁻¹ * x * t = t * x * t⁻¹ := by rw [htinv]
    rw [hEq]
    exact h.conj_mem hx

theorem Wr7.mem_cent {t : G} {P U : Subgroup G} (h : Wr7 t P U) {x : G} :
    x ∈ P ⊓ centralizer ({t} : Set G) ↔ ∃ u ∈ U, x = u * (t * u * t⁻¹) := by
  constructor
  · rintro ⟨hxP, hxC⟩
    have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    obtain ⟨u, hu, v, hv, hxuv⟩ := h.decomp hxP
    obtain ⟨u₁, hu₁, rfl⟩ := (mem_conjSub_iff' t U v).mp hv
    have hU' : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
    have hU₁' : t * u₁ * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u₁, hu₁, rfl⟩
    have hconj : t * x * t⁻¹ = x := by
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [← hcomm]
        _ = x := by group
    have htx : t * x * t⁻¹ = (t * u * t⁻¹) * u₁ := by
      rw [hxuv]
      calc t * (u * (t * u₁ * t⁻¹)) * t⁻¹
          = (t * u * t⁻¹) * (t * (t * u₁ * t⁻¹) * t⁻¹) := by group
        _ = (t * u * t⁻¹) * u₁ := by rw [conj_conj_of_sq h.t_sq]
    have heq : u * (t * u₁ * t⁻¹) = u₁ * (t * u * t⁻¹) := by
      calc u * (t * u₁ * t⁻¹) = x := hxuv.symm
        _ = t * x * t⁻¹ := hconj.symm
        _ = (t * u * t⁻¹) * u₁ := htx
        _ = u₁ * (t * u * t⁻¹) := (h.direct.2.2 u₁ hu₁ _ hU').symm
    obtain ⟨huu, -⟩ := h.unique hu hu₁ hU₁' hU' heq
    refine ⟨u, hu, ?_⟩
    rw [hxuv, ← huu]
  · rintro ⟨u, hu, rfl⟩
    have hU' : t * u * t⁻¹ ∈ conjSub t U := (mem_conjSub_iff' t U _).mpr ⟨u, hu, rfl⟩
    refine ⟨h.mul_mem' hu hU', ?_⟩
    change u * (t * u * t⁻¹) ∈ Subgroup.centralizer {t}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
      calc t * (u * (t * u * t⁻¹)) * t⁻¹
          = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) := by group
        _ = (t * u * t⁻¹) * u := by rw [conj_conj_of_sq h.t_sq]
        _ = u * (t * u * t⁻¹) := (h.direct.2.2 u hu _ hU').symm
    have htx : t * (u * (t * u * t⁻¹)) = (u * (t * u * t⁻¹)) * t := by
      have h := congrArg (fun y => y * t) hconj
      simpa [mul_assoc] using h
    exact htx.symm

end CFSG.OddStandard.HigherRank.YamadaG23
