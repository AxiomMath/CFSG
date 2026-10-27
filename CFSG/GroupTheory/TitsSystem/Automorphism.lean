module

public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.GroupTheory.TitsSystem.Atoms
import CFSG.GroupTheory.TitsSystem.Exchange

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type*} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

namespace IsBNPair

theorem exists_map_parabolic_singleton (h : IsBNPair B N S) {σ : MulAut G}
    (hσ : B.map σ.toMonoidHom = B) {s : WeylGroup B N} (hs : s ∈ S) :
    ∃ t ∈ S, (parabolic B N {s}).map σ.toMonoidHom = parabolic B N {t} := by
  have hcov : B.map σ.toMonoidHom ⋖ (parabolic B N {s}).map σ.toMonoidHom := by
    have h := (apply_covBy_apply_iff (σ.mapSubgroup)).2 (h.covBy_parabolic_singleton hs)
    simpa only [MulEquiv.coe_mapSubgroup] using h
  rw [hσ] at hcov
  exact (h.covBy_iff).1 hcov

private theorem mul_mem_dc_union_of_mem_parabolic_singleton (h : IsBNPair B N S)
    {σ : MulAut G} {t : WeylGroup B N} (ht : t ∈ S) {y z : G} {v : WeylGroup B N}
    (hy : σ y ∈ parabolic B N {t}) (hz : σ z ∈ dc B N v) :
    σ y * σ z ∈ dc B N v ∪ dc B N (t * v) := by
  obtain ⟨v₀, hv₀, hyv₀⟩ := (h.mem_parabolic_iff (Set.singleton_subset_iff.2 ht)).1 hy
  rcases eq_one_or_eq_of_mem_closure_singleton (h.mul_self_eq_one ht) hv₀ with hv₀1 | hv₀t
  · rw [hv₀1] at hyv₀
    exact Or.inl (by simpa using mul_mem_dc hz (mem_dc_one.1 hyv₀) B.one_mem)
  · rw [hv₀t] at hyv₀
    have hprod : σ y * σ z ∈ dc B N t * dc B N v :=
      Set.mem_mul.2 ⟨σ y, hyv₀, σ z, hz, rfl⟩
    rcases h.length_mul_eq_or ht v with hl | hl
    · rw [h.dc_mul_dc_of_lt ht (by omega)] at hprod
      exact Or.inr hprod
    · rw [h.dc_mul_dc_of_gt ht (by omega)] at hprod
      exact hprod

private theorem wordLength_le_of_map_mem_dc_zero (h : IsBNPair B N S) {σ : MulAut G}
    (hσ : B.map σ.toMonoidHom = B) {x : G} {w w' : WeylGroup B N} (hw : wordLength S w = 0)
    (hx : x ∈ dc B N w) (hx' : σ x ∈ dc B N w') : wordLength S w' ≤ wordLength S w := by
  have hw1 : w = 1 :=
    (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure w)).1 hw
  have hxB : x ∈ B := by
    rw [hw1] at hx
    exact mem_dc_one.1 hx
  have hσB : σ x ∈ B := by
    have hmem : σ x ∈ B.map σ.toMonoidHom := Subgroup.mem_map_of_mem σ.toMonoidHom hxB
    rwa [hσ] at hmem
  have hw'1 : w' = 1 := h.eq_of_mem_dc hx' (mem_dc_one.2 hσB)
  simp [hw'1, hw1]

private theorem wordLength_le_of_map_mem_dc_aux (h : IsBNPair B N S) {σ : MulAut G}
    (hσ : B.map σ.toMonoidHom = B) :
    ∀ k : ℕ, ∀ (w : WeylGroup B N) (x : G) (w' : WeylGroup B N), wordLength S w = k →
      x ∈ dc B N w → σ x ∈ dc B N w' → wordLength S w' ≤ wordLength S w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w x w' hw hx hx'
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact wordLength_le_of_map_mem_dc_zero h hσ (by omega) hx hx'
    · have hw1 : w ≠ 1 := by
        intro h1
        rw [h1, wordLength_one] at hw
        omega
      obtain ⟨s, hs, hdesc⟩ :=
        exists_left_descent h.bnCore.mul_self_eq_one (h.mem_closure w) hw1
      set u := s * w with hu
      have hdesc' : wordLength S u + 1 = wordLength S w := by rw [hu]; exact hdesc
      have huk : wordLength S u < k := by omega
      have hwu : w = s * u := by rw [hu, ← mul_assoc, h.mul_self_eq_one hs, one_mul]
      have hxmul : x ∈ dc B N s * dc B N u := by
        rw [hwu] at hx
        exact dc_mul_subset_of s u hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hxmul
      rw [map_mul] at hx'
      obtain ⟨t, ht, hpt⟩ := h.exists_map_parabolic_singleton hσ hs
      have hmem_t : σ y ∈ parabolic B N {t} := by
        rw [← hpt]
        exact Subgroup.mem_map_of_mem σ.toMonoidHom
          (h.dc_subset_parabolic (Set.singleton_subset_iff.2 hs)
            (Subgroup.subset_closure rfl) hy)
      obtain ⟨v, hzv⟩ := h.exists_mem_dc (σ z)
      have hvle : wordLength S v ≤ wordLength S u :=
        ih (wordLength S u) huk u z v rfl hz hzv
      have hmem := mul_mem_dc_union_of_mem_parabolic_singleton h ht hmem_t hzv
      rcases hmem with hmem | hmem
      · have hw'v : w' = v := h.eq_of_mem_dc hx' hmem
        rw [hw'v]
        omega
      · have hw'tv : w' = t * v := h.eq_of_mem_dc hx' hmem
        rw [hw'tv]
        have := h.length_mul_le ht v
        omega

theorem wordLength_eq_of_map_mem_dc (h : IsBNPair B N S) {σ : MulAut G}
    (hσ : B.map σ.toMonoidHom = B) {x : G} {w w' : WeylGroup B N} (hx : x ∈ dc B N w)
    (hx' : σ x ∈ dc B N w') : wordLength S w' = wordLength S w := by
  have hle : wordLength S w' ≤ wordLength S w :=
    wordLength_le_of_map_mem_dc_aux h hσ (wordLength S w) w x w' rfl hx hx'
  have hσ' : B.map σ.symm.toMonoidHom = B := by
    have h := congrArg (Subgroup.map σ.symm.toMonoidHom) hσ
    rw [Subgroup.map_map] at h
    rw [show σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G from by
      ext x; simp, Subgroup.map_id] at h
    exact h.symm
  have hge : wordLength S w ≤ wordLength S w' :=
    wordLength_le_of_map_mem_dc_aux h hσ' (wordLength S w') w' (σ x) w rfl hx'
      (by simpa using hx)
  omega

end IsBNPair

end CFSG.GroupTheory.TitsSystem
