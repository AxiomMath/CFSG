module

public import CFSG.LieType.Steinberg.Bruhat
import Mathlib.Tactic.Group

public section

namespace CFSG.LieType.TitsSimplicity

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem not_isLeftDescent_of_coord_pos {w : W} {i k : Fin D.rank}
    (h : 0 < ρ w⁻¹ (Pi.single i 1) k) : ¬ (cs).IsLeftDescent w i := by
  rw [← CoxeterSystem.isRightDescent_inv_iff, isRightDescent_iff]
  intro hle
  exact (hle k).not_gt h

theorem not_isLeftDescent_simple {i j : Fin D.rank} (hij : i ≠ j) :
    ¬ (cs).IsLeftDescent ((cs).simple j) i := by
  refine not_isLeftDescent_of_coord_pos (k := i) ?_
  rw [CoxeterSystem.inv_simple, weylAction_simple_apply_of_ne _ _ _ hij]
  simp

theorem not_isLeftDescent_simple_mul_simple {i j : Fin D.rank} (hij : i ≠ j)
    (hA : D.cartan i j ≠ 0) :
    ¬ (cs).IsLeftDescent ((cs).simple i * (cs).simple j) j := by
  refine not_isLeftDescent_of_coord_pos (k := i) ?_
  rw [mul_inv_rev, CoxeterSystem.inv_simple, CoxeterSystem.inv_simple, weylAction_mul_apply,
    weylAction_simple_apply_of_ne _ _ _ hij, weylAction_simple, reflection_apply_coroot,
    coroot_single]
  have h := D.isFiniteType.apply_le_zero_of_ne hij
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, smul_eq_mul,
    mul_one, zero_sub]
  omega

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem exists_conj_n_notMem_borel (i : Fin D.rank) :
    ∃ b ∈ borel D H, n i * b * (n i)⁻¹ ∉ borel D H := by
  by_contra! h
  exact not_map_conj_n_borel_le hct hext i (map_conj_le_iff.2 h)

include hext in
theorem n_mul_mul_n_mem_bruhatCell {i : Fin D.rank} {b : K} (hb : b ∈ borel D H)
    (h : n i * b * (n i)⁻¹ ∉ borel D H) :
    n i * b * n i ∈ bruhatCell hct ((cs).simple i) := by
  have h3 := n_mul_mul_nrep_mem hct hext ((cs).simple i) i hb
  rw [nrep_simple, CoxeterSystem.simple_mul_simple_self, bruhatCell_one] at h3
  rcases h3 with h3 | h3
  · exact h3
  · refine absurd ?_ h
    have hsq : (n i ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
    rw [show n i * b * (n i)⁻¹ = n i * b * n i * (n i ^ 2)⁻¹ by group]
    exact mul_mem h3 hsq

include hext in
theorem n_mem_of_nrep_simple_mul_mem {P : Subgroup K} (hP : borel D H ≤ P) {w : W}
    {i : Fin D.rank} (hw : ¬ (cs).IsLeftDescent w i) (h : nrep hct ((cs).simple i * w) ∈ P) :
    n i ∈ P := by
  obtain ⟨b₀, hb₀, hnot⟩ := exists_conj_n_notMem_borel hct hext i
  obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := n_mul_mul_n_mem_bruhatCell hct hext hb₀ hnot
  rw [nrep_simple] at he
  obtain ⟨b', hb', x, hx, he'⟩ := exists_n_mul_mul_nrep hct hext hw hb₀
  have hxB : x ∈ borel D H := rootGroup_le_borel (weylAction_mem_roots _ _ ((Φ).single_mem i))
    (ht_weylAction_inv_single_pos hw) hx
  have hnw := nrep_simple_mul hct hw
  have hsq : n i ^ 2 ∈ P := hP (iSup_le_borel (sq_n_mem_iSup hct i))
  have key : n i * b₀ * n i = b' * nrep hct ((cs).simple i * w) * x *
      (nrep hct ((cs).simple i * w))⁻¹ * n i ^ 2 := by
    rw [← he', hnw]
    group
  have hmem : n i * b₀ * n i ∈ P := by
    rw [key]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hP hb') h) (hP hxB)) (inv_mem h)) hsq
  have e : n i = b₁⁻¹ * (n i * b₀ * n i) * b₂⁻¹ := by
    rw [he]
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (hP hb₁)) hmem) (inv_mem (hP hb₂))

include hext in
theorem n_mem_of_nrep_mem_of_isLeftDescent {P : Subgroup K} (hP : borel D H ≤ P) {w : W}
    {i : Fin D.rank} (hi : (cs).IsLeftDescent w i) (h : nrep hct w ∈ P) : n i ∈ P := by
  have hw : ¬ (cs).IsLeftDescent ((cs).simple i * w) i :=
    (cs).isLeftDescent_iff_not_isLeftDescent_mul.mp hi
  refine n_mem_of_nrep_simple_mul_mem hct hext hP hw ?_
  rwa [(cs).simple_mul_simple_cancel_left]

include hext in
theorem eq_one_of_nrep_mem {P : Subgroup K} (hP : borel D H ≤ P) (hn : ∀ i, n i ∉ P) {w : W}
    (h : nrep hct w ∈ P) : w = 1 := by
  by_contra hw
  obtain ⟨i, hi⟩ := (cs).exists_leftDescent_of_ne_one hw
  exact hn i (n_mem_of_nrep_mem_of_isLeftDescent hct hext hP hi h)

include hct hext in
theorem le_borel_of_forall_n_notMem {P : Subgroup K} (hP : borel D H ≤ P) (hn : ∀ i, n i ∉ P) :
    P ≤ borel D H := by
  intro g hg
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext g
  have hw : nrep hct w ∈ P := by
    have e : nrep hct w = b₁⁻¹ * (b₁ * nrep hct w * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hP hb₁)) hg) (inv_mem (hP hb₂))
  rw [eq_one_of_nrep_mem hct hext hP hn hw, nrep_one, mul_one]
  exact mul_mem hb₁ hb₂

include hct in
theorem eq_top_of_forall_n_mem {P : Subgroup K} (hP : borel D H ≤ P) (hn : ∀ i, n i ∈ P) :
    P = ⊤ := by
  rw [eq_top_iff, ← closure_borel_union_range hct, Subgroup.closure_le]
  rintro x (hx | ⟨i, rfl⟩)
  exacts [hP hx, hn i]

include hct hext in
theorem normalizer_borel : Subgroup.normalizer (borel D H : Set K) = borel D H :=
  le_antisymm (le_borel_of_forall_n_notMem hct hext Subgroup.le_normalizer fun i hi =>
    not_map_conj_n_borel_le hct hext i (mem_normalizer_iff_map_conj.1 hi).le)
    Subgroup.le_normalizer

include hct hext in
theorem cartan_eq_zero_of_n_mem_sup {M : Subgroup K} [hM : M.Normal] {i j : Fin D.rank}
    (hi : n i ∈ M ⊔ borel D H) (hj : n j ∉ M ⊔ borel D H) : D.cartan i j = 0 := by
  by_contra hA
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  have hP : borel D H ≤ M ⊔ borel D H := le_sup_right
  obtain ⟨m, hm, b, hb, hmb⟩ : ∃ m ∈ M, ∃ b ∈ borel D H, m * b = n i := by
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hi
    exact hi
  have hw₁ : ¬ (cs).IsLeftDescent ((cs).simple j) i := not_isLeftDescent_simple hij
  have hw₂ := not_isLeftDescent_simple_mul_simple hij hA
  obtain ⟨b', hb', x, hx, he⟩ := exists_n_mul_mul_nrep hct hext hw₁ (inv_mem hb)
  obtain ⟨b'', hb'', x', hx', he'⟩ := exists_n_mul_mul_nrep hct hext hw₂ hb'
  rw [nrep_simple] at he
  have hxB : x ∈ borel D H := rootGroup_le_borel (weylAction_mem_roots _ _ ((Φ).single_mem i))
    (ht_weylAction_inv_single_pos hw₁) hx
  have hx'B : x' ∈ borel D H := rootGroup_le_borel (weylAction_mem_roots _ _ ((Φ).single_mem j))
    (ht_weylAction_inv_single_pos hw₂) hx'
  have hsq : (n j ^ 2)⁻¹ ∈ borel D H := inv_mem (iSup_le_borel (sq_n_mem_iSup hct j))
  have hconj : n j * m * (n j)⁻¹ ∈ M := hM.conj_mem m hm (n j)
  have key : n j * m * (n j)⁻¹ =
      b'' * nrep hct ((cs).simple j * ((cs).simple i * (cs).simple j)) *
        (x' * x * (n j ^ 2)⁻¹) := by
    have hm' : m = n i * b⁻¹ := by
      rw [← hmb]
      group
    calc n j * m * (n j)⁻¹ = n j * (n i * b⁻¹ * n j) * (n j ^ 2)⁻¹ := by
          rw [hm']
          group
      _ = n j * b' * nrep hct ((cs).simple i * (cs).simple j) * x * (n j ^ 2)⁻¹ := by
          rw [he]
          group
      _ = _ := by
          rw [he']
          group
  have hv : nrep hct ((cs).simple j * ((cs).simple i * (cs).simple j)) ∈ M ⊔ borel D H := by
    have e : nrep hct ((cs).simple j * ((cs).simple i * (cs).simple j)) =
        b''⁻¹ * (n j * m * (n j)⁻¹) * (x' * x * (n j ^ 2)⁻¹)⁻¹ := by
      rw [key]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hP hb'')) (Subgroup.mem_sup_left hconj))
      (inv_mem (hP (mul_mem (mul_mem hx'B hxB) hsq)))
  exact hj (n_mem_of_nrep_simple_mul_mem hct hext hP hw₂ hv)

end CFSG.LieType.TitsSimplicity
