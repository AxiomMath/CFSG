module

public import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen

section Pure

variable {G : Type*} [Group G]

theorem mem_map_conj_iff (Q : Subgroup G) (n h : G) :
    h ∈ Q.map (MulAut.conj n).toMonoidHom ↔ n⁻¹ * h * n ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h'
    exact ⟨n⁻¹ * h * n, h', by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_normalizer_of_mem_normalizer_map (X : Subgroup G) (n g : G)
    (hg : g ∈ Subgroup.normalizer ((X.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) :
    n⁻¹ * g * n ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  have key := hg (n * h * n⁻¹)
  rw [mem_map_conj_iff, mem_map_conj_iff] at key
  have e1 : n⁻¹ * (n * h * n⁻¹) * n = h := by group
  have e2 : n⁻¹ * (g * (n * h * n⁻¹) * g⁻¹) * n = n⁻¹ * g * n * h * (n⁻¹ * g * n)⁻¹ := by group
  rw [e1, e2] at key
  exact key

theorem normal_closure_union_conj {P Q : Subgroup G} {n : G}
    (hmax : ∀ H : Subgroup G, P ≤ H → H = P ∨ H = ⊤)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hfac : ∀ g ∈ P, ∃ q ∈ Q, ∃ m ∈ P, n⁻¹ * m * n ∈ P ∧ g = q * m)
    (hn : n ∉ P) (hn2 : n * n ∈ P) :
    (Subgroup.closure ((Q : Set G) ∪
      ((Q.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G))).Normal := by
  set Qn : Subgroup G := Q.map (MulAut.conj n).toMonoidHom with hQn
  set s : Set G := (Q : Set G) ∪ (Qn : Set G) with hs
  set H : Subgroup G := Subgroup.closure s with hH
  have hQH : Q ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hP : P ≤ Subgroup.normalizer (H : Set G) := by
    rw [hH, Subgroup.le_normalizer_closure_iff]
    intro g hg x hx
    obtain ⟨q, hq, m, hmP, hnm, rfl⟩ := hfac g hg
    have hmx : m * x * m⁻¹ ∈ s := by
      rcases hx with hx | hx
      · exact Or.inl ((Subgroup.mem_normalizer_iff.1 (hPQ hmP) x).1 hx)
      · refine Or.inr ?_
        have hx' : n⁻¹ * x * n ∈ Q := (mem_map_conj_iff Q n x).1 hx
        have h3 := (Subgroup.mem_normalizer_iff.1 (hPQ hnm) (n⁻¹ * x * n)).1 hx'
        have e : n⁻¹ * m * n * (n⁻¹ * x * n) * (n⁻¹ * m * n)⁻¹ = n⁻¹ * (m * x * m⁻¹) * n := by
          group
        rw [e] at h3
        exact (mem_map_conj_iff Q n _).2 h3
    have h2 : q * (m * x * m⁻¹) * q⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hQH hq) (Subgroup.subset_closure hmx)) (H.inv_mem (hQH hq))
    have e3 : q * m * x * (q * m)⁻¹ = q * (m * x * m⁻¹) * q⁻¹ := by group
    rw [e3]
    exact h2
  have hnN : n ∈ Subgroup.normalizer (H : Set G) := by
    have hconj : (MulAut.conj n) '' (Qn : Set G) = (Q : Set G) := by
      have h := Subgroup.mem_normalizer_iff_conj_image_eq.1 (hPQ hn2)
      rw [← h, hQn, Subgroup.coe_map, Set.image_image]
      exact Set.image_congr' fun y => by simp [MulAut.conj_apply, mul_assoc]
    have hQ' : (MulAut.conj n) '' (Q : Set G) = (Qn : Set G) := by
      rw [hQn, Subgroup.coe_map]
      rfl
    have hs' : (MulAut.conj n) '' s = s := by
      rw [hs, Set.image_union, hconj, hQ', Set.union_comm]
    exact Subgroup.normalizer_le_normalizer_closure s
      (Subgroup.mem_normalizer_iff_conj_image_eq.2 hs')
  have htop : Subgroup.normalizer (H : Set G) = ⊤ := by
    rcases hmax _ hP with h | h
    · exact absurd (h ▸ hnN) hn
    · exact h
  exact Subgroup.normalizer_eq_top_iff.1 htop

end Pure

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen
