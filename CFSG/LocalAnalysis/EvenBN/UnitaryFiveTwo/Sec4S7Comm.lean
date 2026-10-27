module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem mul_conj_comm_of_comm {G : Type*} [Group G] {u X T : G} (hu : u * u = 1)
    (h : X * T = T * X) : (u * X * u) * (u * T * u) = (u * T * u) * (u * X * u) := by
  calc (u * X * u) * (u * T * u) = u * (X * (u * u) * T) * u := by group
    _ = u * (X * T) * u := by rw [hu, mul_one]
    _ = u * (T * X) * u := by rw [h]
    _ = u * (T * (u * u) * X) * u := by rw [hu, mul_one]
    _ = (u * T * u) * (u * X * u) := by group

theorem mem_comap_centralizer_conj {G : Type*} [Group G] {s w x : G} (hs : s * s = 1) :
    x ∈ (Subgroup.centralizer ({w} : Set G)).comap (MulAut.conj s).toMonoidHom ↔
      (s * x * s) * w = w * (s * x * s) := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  show (s * x * s⁻¹) * w = w * (s * x * s⁻¹) ↔ _
  rw [hs']

theorem commute_conj_of_generation {G : Type*} [Group G] (N B₁ : Subgroup G) (u v t : G)
    (hu : u * u = 1) (hv : v * v = 1) (ht : t * t = 1) (htu : t * u = u * t)
    (htv : t * v = v * t) (huv : (u * v) ^ 4 = 1) (hB₁N : B₁ ≤ N)
    (hB₁u : ∀ x ∈ B₁, u * x * u ∈ B₁) (hvN : ∀ x ∈ N, v * x * v ∈ N)
    (hNt : ∀ x ∈ N, ∀ y ∈ N, x * (t * y * t) = (t * y * t) * x)
    (hgen : N = B₁ ⊔ ((B₁ ⊓ B₁.map (MulAut.conj v).toMonoidHom).map
      (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom) :
    ∀ x ∈ N, ∀ y ∈ N, (u * x * u) * (t * y * t) = (t * y * t) * (u * x * u) := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  set C' : Subgroup G := ((B₁ ⊓ B₁.map (MulAut.conj v).toMonoidHom).map
      (MulAut.conj u).toMonoidHom).map (MulAut.conj v).toMonoidHom with hC'def
  have hgen' : N = B₁ ⊔ C' := hgen
  have hC' : ∀ x ∈ C', ∃ c ∈ B₁, ∃ b ∈ B₁, c = v * b * v ∧ x = v * u * c * u * v := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨hcB, hcv⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨b, hb, hbc⟩ := Subgroup.mem_map.1 hcv
    refine ⟨c, hcB, b, hb, ?_, ?_⟩
    · rw [← hbc]
      show v * b * v⁻¹ = v * b * v
      rw [hv']
    · show v * (u * c * u⁻¹) * v⁻¹ = v * u * c * u * v
      rw [hu', hv']
      group
  have hcomm : u * v * u * v = v * u * v * u := by
    have h4 : (u * v) ^ 4 = (u * v) * (u * v) * (u * v) * (u * v) := by
      rw [pow_succ, pow_succ, pow_succ, pow_one]
    have hX : (u * v * u * v) * (u * v * u * v) = 1 := by
      calc (u * v * u * v) * (u * v * u * v) = (u * v) * (u * v) * (u * v) * (u * v) := by group
        _ = (u * v) ^ 4 := h4.symm
        _ = 1 := huv
    have hXinv : (u * v * u * v)⁻¹ = u * v * u * v := inv_eq_of_mul_eq_one_right hX
    have e : (u * v * u * v)⁻¹ = v * u * v * u := by
      rw [show (u * v * u * v)⁻¹ = v⁻¹ * u⁻¹ * v⁻¹ * u⁻¹ by group, hu', hv']
    exact hXinv.symm.trans e
  have hug : u * (v * u * v) = (v * u * v) * u := by
    calc u * (v * u * v) = u * v * u * v := by group
      _ = v * u * v * u := hcomm
      _ = (v * u * v) * u := by group
  have htg : t * (v * u * v) = (v * u * v) * t := by
    calc t * (v * u * v) = (t * v) * u * v := by group
      _ = (v * t) * u * v := by rw [htv]
      _ = v * (t * u) * v := by group
      _ = v * (u * t) * v := by rw [htu]
      _ = v * u * (t * v) := by group
      _ = v * u * (v * t) := by rw [htv]
      _ = (v * u * v) * t := by group
  have hgg : (v * u * v) * (v * u * v) = 1 := by
    calc (v * u * v) * (v * u * v) = v * (u * (v * v) * u) * v := by group
      _ = v * (u * 1 * u) * v := by rw [hv]
      _ = v * (u * u) * v := by rw [mul_one]
      _ = v * 1 * v := by rw [hu]
      _ = v * v := by rw [mul_one]
      _ = 1 := hv
  have hutu : u * t * u = t := by rw [← htu, mul_assoc, hu, mul_one]
  have hA : ∀ x ∈ B₁, ∀ y ∈ N, (u * x * u) * (t * y * t) = (t * y * t) * (u * x * u) :=
    fun x hx y hy => hNt _ (hB₁N (hB₁u x hx)) y hy
  have hB : ∀ x ∈ C', ∀ y ∈ B₁, (u * x * u) * (t * y * t) = (t * y * t) * (u * x * u) := by
    intro x hx y hy
    obtain ⟨c, hc, b, hb, hcb, rfl⟩ := hC' x hx
    have hX : v * (u * c * u) * v ∈ N := hvN _ (hB₁N (hB₁u c hc))
    have hb₂ : u * y * u ∈ N := hB₁N (hB₁u y hy)
    have key : (v * (u * c * u) * v) * (t * (u * y * u) * t) =
        (t * (u * y * u) * t) * (v * (u * c * u) * v) := hNt _ hX _ hb₂
    have e1 : u * (v * u * c * u * v) * u = u * (v * (u * c * u) * v) * u := by group
    have e2 : t * y * t = u * (t * (u * y * u) * t) * u := by
      calc t * y * t = (u * t * u) * y * (u * t * u) := by rw [hutu]
        _ = u * (t * (u * y * u) * t) * u := by group
    rw [e1, e2]
    exact mul_conj_comm_of_comm hu key
  have hC : ∀ x ∈ C', ∀ y ∈ C', (u * x * u) * (t * y * t) = (t * y * t) * (u * x * u) := by
    intro x hx y hy
    obtain ⟨c, hc, b, hb, rfl, rfl⟩ := hC' x hx
    obtain ⟨c', hc', b', hb', rfl, rfl⟩ := hC' y hy
    have hub : u * b * u ∈ N := hB₁N (hB₁u b hb)
    have key : (u * b * u) * (t * b' * t) = (t * b' * t) * (u * b * u) :=
      hNt _ hub _ (hB₁N hb')
    have e1 : u * (v * u * (v * b * v) * u * v) * u = (v * u * v) * (u * b * u) * (v * u * v) := by
      calc u * (v * u * (v * b * v) * u * v) * u
          = (u * (v * u * v)) * b * ((v * u * v) * u) := by group
        _ = ((v * u * v) * u) * b * (u * (v * u * v)) := by rw [hug]
        _ = (v * u * v) * (u * b * u) * (v * u * v) := by group
    have e2 : t * (v * u * (v * b' * v) * u * v) * t =
        (v * u * v) * (t * b' * t) * (v * u * v) := by
      calc t * (v * u * (v * b' * v) * u * v) * t
          = (t * (v * u * v)) * b' * ((v * u * v) * t) := by group
        _ = ((v * u * v) * t) * b' * (t * (v * u * v)) := by rw [htg]
        _ = (v * u * v) * (t * b' * t) * (v * u * v) := by group
    rw [e1, e2]
    exact mul_conj_comm_of_comm hgg key
  have hstage1 : ∀ y, (y ∈ B₁ ∨ y ∈ C') → ∀ x ∈ N,
      (u * x * u) * (t * y * t) = (t * y * t) * (u * x * u) := by
    intro y hy x hx
    have hyN : y ∈ N := by
      rcases hy with hy | hy
      · exact hB₁N hy
      · rw [hgen']
        exact mem_sup_right hy
    have hS : B₁ ⊔ C' ≤ (Subgroup.centralizer ({t * y * t} : Set G)).comap
        (MulAut.conj u).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact (mem_comap_centralizer_conj hu).2 (hA x hx y hyN)
      · refine (mem_comap_centralizer_conj hu).2 ?_
        rcases hy with hy | hy
        · exact hB x hx y hy
        · exact hC x hx y hy
    exact (mem_comap_centralizer_conj hu).1 (hS (by rw [← hgen']; exact hx))
  intro x hx y hy
  have hS : B₁ ⊔ C' ≤ (Subgroup.centralizer ({u * x * u} : Set G)).comap
      (MulAut.conj t).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact (mem_comap_centralizer_conj ht).2 (hstage1 y (Or.inl hy) x hx).symm
    · exact (mem_comap_centralizer_conj ht).2 (hstage1 y (Or.inr hy) x hx).symm
  exact ((mem_comap_centralizer_conj ht).1 (hS (by rw [← hgen']; exact hy))).symm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
