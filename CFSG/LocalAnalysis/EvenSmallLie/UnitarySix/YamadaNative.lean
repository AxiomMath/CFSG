module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeCheck
import all CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeParabolic

public section

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Fischer
open scoped commutatorElement

theorem comm_facts
    : kappaOne * j1 = j1 * kappaOne ∧ ⁅alphaOne, kappaOne⁆ = j1 ∧
    kappaTwo * j2 = j2 * kappaTwo ∧ ⁅alphaTwo, kappaTwo⁆ = j2 := by
  have h := comm_check
  simp only [commCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨eq_of_commT (rep_toTable hn693 _) (rep_toTable hn693 _) h1,
    (tblEq_true_iff (rep_toTable hn693 _) (rep_toTable hn693 _)).1 h2,
    eq_of_commT (rep_toTable hn693 _) (rep_toTable hn693 _) h3,
    (tblEq_true_iff (rep_toTable hn693 _) (rep_toTable hn693 _)).1 h4⟩

theorem alphaOne_mem : alphaOne ∈ uA := evalCodes_mem _ aGens_mem _

theorem alphaTwo_mem : alphaTwo ∈ uA := evalCodes_mem _ aGens_mem _

theorem kappaOne_mem : kappaOne ∈ uK := evalCodes_mem _ kGens_mem _

theorem kappaTwo_mem : kappaTwo ∈ uK := evalCodes_mem _ kGens_mem _

theorem stabElt_mem
    (m : ℕ) : stabElt m ∈ uK := evalCodes_mem _ kGens_mem _

theorem orbitElt_zero : orbitElt 0 = j1 := by
  simp [orbitElt, orbitWords, evalCodes]

theorem trans_facts :
    (∀ g ∈ kGens ++ kGens.map (·⁻¹), ∀ i < 21, ∃ j < 21, g * orbitElt i * g⁻¹ = orbitElt j) ∧
      ∀ m < 21, m ≠ 0 → stabElt m * j1 = j1 * stabElt m ∧
        stabElt m * orbitElt 1 * (stabElt m)⁻¹ = orbitElt m := by
  have h := trans_check
  simp only [transCheck, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
    List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g hg i hi => ?_, fun m hm hm0 => ?_⟩
  · obtain ⟨j, hj, hj'⟩ := h1 g hg i hi
    exact ⟨j, hj, (tblEq_true_iff (rep_toTable hn693 _) (rep_toTable hn693 _)).1 hj'⟩
  · rcases h2 m hm with h | ⟨h3, h4⟩
    · exact absurd h hm0
    · exact ⟨eq_of_commT (rep_toTable hn693 _) (rep_toTable hn693 _) h3,
        (tblEq_true_iff (rep_toTable hn693 _) (rep_toTable hn693 _)).1 h4⟩

theorem conj_orbitElt
    {k : Equiv.Perm (Fin 693)} (hk : k ∈ uK) :
    ∀ i < 21, ∃ j < 21, k * orbitElt i * k⁻¹ = orbitElt j := by
  rw [uK_eq] at hk
  induction hk using Subgroup.closure_induction'' with
  | mem x hx => exact trans_facts.1 x (List.mem_append_left _ hx)
  | inv_mem x hx => exact trans_facts.1 x⁻¹ (List.mem_append_right _ (List.mem_map_of_mem hx))
  | one => exact fun i hi => ⟨i, hi, by group⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨j, hj, hj'⟩ := hy i hi
    obtain ⟨l, hl, hl'⟩ := hx j hj
    exact ⟨l, hl, by rw [← hl', ← hj']; group⟩

theorem exists_conj_base
    {x y : Equiv.Perm (Fin 693)} (hx : x ∈ conjClass uK j1)
    (hy : y ∈ conjClass uK j1) (hxy : x ≠ y) :
    ∃ u ∈ uK, u * x * u⁻¹ = j1 ∧ u * y * u⁻¹ = orbitElt 1 := by
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨k', hk', rfl⟩ := hy
  obtain ⟨m, hm, hm'⟩ := conj_orbitElt (uK.mul_mem (uK.inv_mem hk) hk') 0 (by norm_num)
  rw [orbitElt_zero] at hm'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [orbitElt_zero] at hm'
    apply hxy
    calc k * j1 * k⁻¹ = k * (k⁻¹ * k' * j1 * (k⁻¹ * k')⁻¹) * k⁻¹ := by rw [hm']
      _ = k' * j1 * k'⁻¹ := by group
  obtain ⟨hc, hs⟩ := trans_facts.2 m hm hm0
  refine ⟨(stabElt m)⁻¹ * k⁻¹, uK.mul_mem (uK.inv_mem (stabElt_mem m)) (uK.inv_mem hk), ?_, ?_⟩
  · calc (stabElt m)⁻¹ * k⁻¹ * (k * j1 * k⁻¹) * ((stabElt m)⁻¹ * k⁻¹)⁻¹ =
          (stabElt m)⁻¹ * (j1 * stabElt m) := by group
      _ = j1 := by rw [← hc]; group
  · calc (stabElt m)⁻¹ * k⁻¹ * (k' * j1 * k'⁻¹) * ((stabElt m)⁻¹ * k⁻¹)⁻¹ =
          (stabElt m)⁻¹ * (k⁻¹ * k' * j1 * (k⁻¹ * k')⁻¹) * stabElt m := by group
      _ = orbitElt 1 := by rw [hm', ← hs]; group

theorem two_trans_uK
    : ∀ x ∈ conjClass uK j1, ∀ y ∈ conjClass uK j1, ∀ z ∈ conjClass uK j1,
    ∀ w ∈ conjClass uK j1, x ≠ y → z ≠ w → ∃ k ∈ uK, k * x * k⁻¹ = z ∧ k * y * k⁻¹ = w := by
  intro x hx y hy z hz w hw hxy hzw
  obtain ⟨u, hu, hux, huy⟩ := exists_conj_base hx hy hxy
  obtain ⟨v, hv, hvz, hvw⟩ := exists_conj_base hz hw hzw
  refine ⟨v⁻¹ * u, uK.mul_mem (uK.inv_mem hv) hu, ?_, ?_⟩
  · calc v⁻¹ * u * x * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * x * u⁻¹) * v := by group
      _ = z := by rw [hux, ← hvz]; group
  · calc v⁻¹ * u * y * (v⁻¹ * u)⁻¹ = v⁻¹ * (u * y * u⁻¹) * v := by group
      _ = w := by rw [huy, ← hvw]; group

section Transport

variable
    {Q : Type} [Group Q] (e : Q ≃* T46)

theorem symm_mem_commutator_centralizer
    {j g h : Equiv.Perm (Fin 693)} (hj : j ∈ T46)
    (hg : g ∈ T46) (hh : h ∈ T46) (hgj : g * j = j * g) (hhj : h * j = j * h)
    (hc : ⁅g, h⁆ = j) :
    e.symm ⟨j, hj⟩ ∈ ⁅centralizer ({e.symm ⟨j, hj⟩} : Set Q),
      centralizer ({e.symm ⟨j, hj⟩} : Set Q)⁆ := by
  have key : ∀ (x : Equiv.Perm (Fin 693)) (hx : x ∈ T46), x * j = j * x →
      e.symm ⟨x, hx⟩ ∈ centralizer ({e.symm ⟨j, hj⟩} : Set Q) := by
    intro x hx hxj
    rw [mem_centralizer_singleton_iff]
    refine embT46_injective e ?_
    rw [map_mul, map_mul, embT46_symm, embT46_symm]
    exact hxj
  have hj' : ⁅e.symm ⟨g, hg⟩, e.symm ⟨h, hh⟩⁆ = e.symm ⟨j, hj⟩ := by
    refine embT46_injective e ?_
    rw [map_commutatorElement, embT46_symm, embT46_symm, embT46_symm, hc]
  have := commutator_mem_commutator (key g hg hgj) (key h hh hhj)
  rwa [hj'] at this

theorem comm_a₁_ofMulEquivT46 :
    (ToddParabolic.ofMulEquivT46 e).a₁ ∈
      ⁅centralizer ({(ToddParabolic.ofMulEquivT46 e).a₁} : Set Q),
        centralizer ({(ToddParabolic.ofMulEquivT46 e).a₁} : Set Q)⁆ :=
  symm_mem_commutator_centralizer e (uA_le_T46 j1_mem) (uA_le_T46 alphaOne_mem)
    (uK_le_T46 kappaOne_mem) (uA_comm _ alphaOne_mem _ j1_mem) comm_facts.1 comm_facts.2.1

theorem comm_a₂_ofMulEquivT46 :
    (ToddParabolic.ofMulEquivT46 e).a₂ ∈
      ⁅centralizer ({(ToddParabolic.ofMulEquivT46 e).a₂} : Set Q),
        centralizer ({(ToddParabolic.ofMulEquivT46 e).a₂} : Set Q)⁆ :=
  symm_mem_commutator_centralizer e (uA_le_T46 j2_mem) (uA_le_T46 alphaTwo_mem)
    (uK_le_T46 kappaTwo_mem) (uA_comm _ alphaTwo_mem _ j2_mem) comm_facts.2.2.1
    comm_facts.2.2.2

theorem two_trans_ofMulEquivT46 :
    ∀ x ∈ conjClass (ToddParabolic.ofMulEquivT46 e).K (ToddParabolic.ofMulEquivT46 e).a₁,
    ∀ y ∈ conjClass (ToddParabolic.ofMulEquivT46 e).K (ToddParabolic.ofMulEquivT46 e).a₁,
    ∀ z ∈ conjClass (ToddParabolic.ofMulEquivT46 e).K (ToddParabolic.ofMulEquivT46 e).a₁,
    ∀ w ∈ conjClass (ToddParabolic.ofMulEquivT46 e).K (ToddParabolic.ofMulEquivT46 e).a₁,
      x ≠ y → z ≠ w → ∃ k ∈ (ToddParabolic.ofMulEquivT46 e).K, k * x * k⁻¹ = z ∧
        k * y * k⁻¹ = w := by
  intro x hx y hy z hz w hw hxy hzw
  have hmem : ∀ v ∈ conjClass (uK.comap (embT46 e)) (e.symm ⟨j1, uA_le_T46 j1_mem⟩),
      embT46 e v ∈ conjClass uK j1 := by
    intro v hv
    rw [← embT46_symm e (uA_le_T46 j1_mem), ← image_conjClass_embT46]
    exact ⟨v, hv, rfl⟩
  have hne : ∀ {u v : Q}, u ≠ v → embT46 e u ≠ embT46 e v :=
    fun huv h => huv (embT46_injective e h)
  obtain ⟨k, hk, h1, h2⟩ := two_trans_uK _ (hmem x hx) _ (hmem y hy) _ (hmem z hz) _
    (hmem w hw) (hne hxy) (hne hzw)
  obtain ⟨k', rfl⟩ := exists_embT46 e (uK_le_T46 hk)
  refine ⟨k', hk, embT46_injective e ?_, embT46_injective e ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact h1
  · rw [map_mul, map_mul, map_inv]
    exact h2

end Transport

end CFSG.EvenSmallLie.UnitarySix.Yamada
