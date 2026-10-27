module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G}

private lemma sec5p510_permVec_single (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    permVec σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext j
  rw [permVec, Function.comp_apply]
  by_cases h : σ.symm j = i
  · have hj : j = σ i := (Equiv.symm_apply_eq σ).mp h
    rw [h, Pi.single_eq_same, hj, Pi.single_eq_same]
  · have hj : j ≠ σ i := fun hh => h (by rw [hh, Equiv.symm_apply_apply])
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hj]

private lemma sec5p510_weight_one_eq_single {v : Fin 6 → ZMod 2} (hv : vecWeight v = 1) :
    ∃ i : Fin 6, v = Pi.single i 1 := by
  revert v
  decide +kernel

private lemma sec5p510_weight_four_eq (v : Fin 6 → ZMod 2) (hv : vecWeight v = 4) :
    ∃ j k : Fin 6, j ≠ k ∧
      v = (1 : Fin 6 → ZMod 2) + Pi.single j 1 + Pi.single k 1 := by
  revert v
  decide +kernel

private lemma sec5p510_conj_mem_conjClassIn {x m : G}
    (hx : x ∈ conjClassIn (normalizer (A : Set G)) t)
    (hm : m ∈ normalizer (A : Set G)) :
    m * x * m⁻¹ ∈ conjClassIn (normalizer (A : Set G)) t := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨m * h, Subgroup.mul_mem _ hm hh, by group⟩

private lemma sec5p510_mem_wclass_one_of_mem_delta (h : Sec510Ctx G t L S z r ρ B A φ)
    {u : G} (hu : u ∈ conjClassIn (normalizer (A : Set G)) t) (hu_ne : u ≠ t) :
    u ∈ wclass φ 1 := by
  have h6 : (wclass φ 6 : Set G) = {t} := by
    simpa only [Pi.one_def, h.model.map_one] using h.model.perm.wclass_six
  rw [h.delta] at hu
  rcases hu with hu6 | hu1
  · exact absurd (by simpa [h6] using hu6) hu_ne
  · exact hu1

private theorem sec5p510_W1_two_trans_aux (h : Sec510Ctx G t L S z r ρ B A φ)
    {x y x' y' : G} (hx : x ∈ wclass φ 1) (hy : y ∈ wclass φ 1)
    (hx' : x' ∈ wclass φ 1) (hy' : y' ∈ wclass φ 1) (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ a ∈ L ⊓ normalizer (A : Set G), a * x * a⁻¹ = x' ∧ a * y * a⁻¹ = y' ∧
      a * t * a⁻¹ = t := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hx'
  obtain ⟨w', hw', rfl⟩ := hy'
  obtain ⟨i, rfl⟩ := sec5p510_weight_one_eq_single hv
  obtain ⟨j, rfl⟩ := sec5p510_weight_one_eq_single hw
  obtain ⟨i', rfl⟩ := sec5p510_weight_one_eq_single hv'
  obtain ⟨j', rfl⟩ := sec5p510_weight_one_eq_single hw'
  have hij : i ≠ j := by
    intro hij
    exact hxy (by rw [hij])
  have hij' : i' ≠ j' := by
    intro hij
    exact hxy' (by rw [hij])
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 := by
    haveI h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 4 := by
      simpa [Nat.card_fin] using alternatingGroup.isMultiplyPretransitive (α := Fin 6)
    exact MulAction.isMultiplyPretransitive_of_le (m := 2) (n := 4) (by norm_num) (by norm_num)
  obtain ⟨σ, hσi, hσj⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hij hij'
  have hσi' : (σ : Equiv.Perm (Fin 6)) i = i' := by
    simpa [Subgroup.smul_def] using hσi
  have hσj' : (σ : Equiv.Perm (Fin 6)) j = j' := by
    simpa [Subgroup.smul_def] using hσj
  obtain ⟨a, ha, ha_act⟩ := h.model.perm.2.2.2.2 σ σ.2
  have hperm_i : permVec (σ : Equiv.Perm (Fin 6)) (Pi.single i 1) = Pi.single i' 1 := by
    rw [sec5p510_permVec_single, hσi']
  have hperm_j : permVec (σ : Equiv.Perm (Fin 6)) (Pi.single j 1) = Pi.single j' 1 := by
    rw [sec5p510_permVec_single, hσj']
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · rw [ha_act (Pi.single i 1) trivial, hperm_i]
  · rw [ha_act (Pi.single j 1) trivial, hperm_j]
  · rw [← h.model.map_one, ha_act (fun _ : Fin 6 => (1 : ZMod 2)) trivial]
    rfl

theorem sec5p510_triple (h : Sec510Ctx G t L S z r ρ B A φ) {x y w x' y' w' : G}
    (hx : x ∈ conjClassIn (normalizer (A : Set G)) t)
    (hy : y ∈ conjClassIn (normalizer (A : Set G)) t)
    (hw : w ∈ conjClassIn (normalizer (A : Set G)) t)
    (hx' : x' ∈ conjClassIn (normalizer (A : Set G)) t)
    (hy' : y' ∈ conjClassIn (normalizer (A : Set G)) t)
    (hw' : w' ∈ conjClassIn (normalizer (A : Set G)) t)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) (hxy' : x' ≠ y') (hxw' : x' ≠ w')
    (hyw' : y' ≠ w') :
    ∃ m ∈ normalizer (A : Set G), m * x * m⁻¹ = x' ∧ m * y * m⁻¹ = y' ∧ m * w * m⁻¹ = w' := by
  obtain ⟨mx, hmx, hxe⟩ := hx
  obtain ⟨mx', hmx', hx'e⟩ := hx'
  set m1 : G := mx' * mx⁻¹ with hm1_def
  set y1 : G := m1 * y * m1⁻¹ with hy1_def
  set w1 : G := m1 * w * m1⁻¹ with hw1_def
  set u : G := mx'⁻¹ * y1 * mx' with hu_def
  set v : G := mx'⁻¹ * w1 * mx' with hv_def
  set u' : G := mx'⁻¹ * y' * mx' with hu'_def
  set v' : G := mx'⁻¹ * w' * mx' with hv'_def
  have hm1_mem : m1 ∈ normalizer (A : Set G) := by
    rw [hm1_def]
    exact Subgroup.mul_mem _ hmx' (Subgroup.inv_mem _ hmx)
  have hm1x : m1 * x * m1⁻¹ = x' := by
    rw [hm1_def, hxe, hx'e]
    group
  have hy1_delta : y1 ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hy1_def]
    exact sec5p510_conj_mem_conjClassIn hy hm1_mem
  have hw1_delta : w1 ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hw1_def]
    exact sec5p510_conj_mem_conjClassIn hw hm1_mem
  have hy1x' : y1 ≠ x' := by
    intro heq
    have hconj : m1 * y * m1⁻¹ = m1 * x * m1⁻¹ := by
      rw [← hy1_def, heq, hm1x]
    exact hxy (conj_injective (x := m1) hconj).symm
  have hw1x' : w1 ≠ x' := by
    intro heq
    have hconj : m1 * w * m1⁻¹ = m1 * x * m1⁻¹ := by
      rw [← hw1_def, heq, hm1x]
    exact hxw (conj_injective (x := m1) hconj).symm
  have hy1w1 : y1 ≠ w1 := by
    intro heq
    have hconj : m1 * y * m1⁻¹ = m1 * w * m1⁻¹ := by
      rw [← hy1_def, heq, ← hw1_def]
    exact hyw (conj_injective (x := m1) hconj)
  have hx't : mx'⁻¹ * x' * mx' = t := by
    rw [hx'e]
    group
  have hu_delta : u ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hu_def]
    simpa using sec5p510_conj_mem_conjClassIn hy1_delta (Subgroup.inv_mem _ hmx')
  have hv_delta : v ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hv_def]
    simpa using sec5p510_conj_mem_conjClassIn hw1_delta (Subgroup.inv_mem _ hmx')
  have hu'_delta : u' ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hu'_def]
    simpa using sec5p510_conj_mem_conjClassIn hy' (Subgroup.inv_mem _ hmx')
  have hv'_delta : v' ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [hv'_def]
    simpa using sec5p510_conj_mem_conjClassIn hw' (Subgroup.inv_mem _ hmx')
  have hu_ne_t : u ≠ t := by
    intro heq
    apply hy1x'
    have hconj : mx'⁻¹ * y1 * mx' = mx'⁻¹ * x' * mx' := by
      rw [← hu_def, heq, hx't]
    exact mul_left_cancel (mul_right_cancel hconj)
  have hv_ne_t : v ≠ t := by
    intro heq
    apply hw1x'
    have hconj : mx'⁻¹ * w1 * mx' = mx'⁻¹ * x' * mx' := by
      rw [← hv_def, heq, hx't]
    exact mul_left_cancel (mul_right_cancel hconj)
  have hu'_ne_t : u' ≠ t := by
    intro heq
    apply hxy'
    have hconj : mx'⁻¹ * y' * mx' = mx'⁻¹ * x' * mx' := by
      rw [← hu'_def, heq, hx't]
    exact (mul_left_cancel (mul_right_cancel hconj)).symm
  have hv'_ne_t : v' ≠ t := by
    intro heq
    apply hxw'
    have hconj : mx'⁻¹ * w' * mx' = mx'⁻¹ * x' * mx' := by
      rw [← hv'_def, heq, hx't]
    exact (mul_left_cancel (mul_right_cancel hconj)).symm
  have hu_w1 : u ∈ wclass φ 1 :=
    sec5p510_mem_wclass_one_of_mem_delta h hu_delta hu_ne_t
  have hv_w1 : v ∈ wclass φ 1 :=
    sec5p510_mem_wclass_one_of_mem_delta h hv_delta hv_ne_t
  have hu'_w1 : u' ∈ wclass φ 1 :=
    sec5p510_mem_wclass_one_of_mem_delta h hu'_delta hu'_ne_t
  have hv'_w1 : v' ∈ wclass φ 1 :=
    sec5p510_mem_wclass_one_of_mem_delta h hv'_delta hv'_ne_t
  have huv : u ≠ v := by
    intro heq
    apply hy1w1
    have hconj : mx'⁻¹ * y1 * mx' = mx'⁻¹ * w1 * mx' := by
      rw [← hu_def, heq, ← hv_def]
    exact mul_left_cancel (mul_right_cancel hconj)
  have hu'v' : u' ≠ v' := by
    intro heq
    apply hyw'
    have hconj : mx'⁻¹ * y' * mx' = mx'⁻¹ * w' * mx' := by
      rw [← hu'_def, heq, ← hv'_def]
    exact mul_left_cancel (mul_right_cancel hconj)
  obtain ⟨a, ha, hau, hav, hat⟩ :=
    sec5p510_W1_two_trans_aux h hu_w1 hv_w1 hu'_w1 hv'_w1 huv hu'v'
  have haM : a ∈ normalizer (A : Set G) := (Subgroup.mem_inf.mp ha).2
  refine ⟨mx' * a * mx'⁻¹ * m1, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hmx' haM) (Subgroup.inv_mem _ hmx')) hm1_mem
  · have key : (mx' * a * mx'⁻¹ * m1) * x * (mx' * a * mx'⁻¹ * m1)⁻¹ =
        mx' * (a * t * a⁻¹) * mx'⁻¹ := by
      rw [hm1_def, hxe]
      group
    rw [key, hat, hx'e]
  · have key : (mx' * a * mx'⁻¹ * m1) * y * (mx' * a * mx'⁻¹ * m1)⁻¹ =
        mx' * (a * u * a⁻¹) * mx'⁻¹ := by
      rw [hu_def, hy1_def, hm1_def]
      group
    rw [key, hau, hu'_def]
    group
  · have key : (mx' * a * mx'⁻¹ * m1) * w * (mx' * a * mx'⁻¹ * m1)⁻¹ =
        mx' * (a * v * a⁻¹) * mx'⁻¹ := by
      rw [hv_def, hw1_def, hm1_def]
      group
    rw [key, hav, hv'_def]
    group

theorem sec5p510_exists_cycle (h : Sec510Ctx G t L S z r ρ B A φ) :
    ∃ a b : G, a ∈ wclass φ 1 ∧ b ∈ wclass φ 1 ∧ a ≠ b ∧ t * a * b = z ∧
      ∃ c ∈ normalizer (A : Set G), c * t * c⁻¹ = a ∧ c * a * c⁻¹ = b ∧ c * b * c⁻¹ = t := by
  obtain ⟨v, hv, hvz⟩ := h.model.z_mem
  obtain ⟨j, k, hjk, hvjk⟩ := sec5p510_weight_four_eq v hv
  have hone : φ (1 : Fin 6 → ZMod 2) = t := by
    rw [Pi.one_def]
    exact h.model.map_one
  have ha_w1 : φ (Pi.single j 1) ∈ wclass φ 1 :=
    ⟨Pi.single j 1, sec5b6_vecWeight_single j, rfl⟩
  have hb_w1 : φ (Pi.single k 1) ∈ wclass φ 1 :=
    ⟨Pi.single k 1, sec5b6_vecWeight_single k, rfl⟩
  have hab : φ (Pi.single j 1) ≠ φ (Pi.single k 1) := by
    intro heq
    have h1 := congrFun (h.model.perm.injective heq) j
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hjk] at h1
    exact one_ne_zero h1
  have hz : t * φ (Pi.single j 1) * φ (Pi.single k 1) = z := by
    calc t * φ (Pi.single j 1) * φ (Pi.single k 1)
        = φ (1 : Fin 6 → ZMod 2) * φ (Pi.single j 1) * φ (Pi.single k 1) := by
          rw [← hone]
      _ = φ ((1 : Fin 6 → ZMod 2) + Pi.single j 1) * φ (Pi.single k 1) := by
          simp only [h.model.perm.map_add]
      _ = φ (((1 : Fin 6 → ZMod 2) + Pi.single j 1) + Pi.single k 1) := by
          simp only [h.model.perm.map_add]
      _ = φ v := by rw [← hvjk]
      _ = z := hvz
  have ht_delta : t ∈ conjClassIn (normalizer (A : Set G)) t :=
    ⟨1, Subgroup.one_mem _, by group⟩
  have ha_delta : φ (Pi.single j 1) ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [h.delta]
    exact Or.inr ha_w1
  have hb_delta : φ (Pi.single k 1) ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [h.delta]
    exact Or.inr hb_w1
  have hta : t ≠ φ (Pi.single j 1) := by
    intro heq
    have ht6 : t ∈ wclass φ 6 := h.model.t_mem_wclass
    exact Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (6 : ℕ) ≠ 1))
      (heq.symm ▸ ht6) ha_w1
  have htb : t ≠ φ (Pi.single k 1) := by
    intro heq
    have ht6 : t ∈ wclass φ 6 := h.model.t_mem_wclass
    exact Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (6 : ℕ) ≠ 1))
      (heq.symm ▸ ht6) hb_w1
  obtain ⟨c, hc_mem, hct, hca, hcb⟩ :=
    sec5p510_triple h ht_delta ha_delta hb_delta ha_delta hb_delta ht_delta
      hta htb hab hab (Ne.symm hta) (Ne.symm htb)
  exact ⟨φ (Pi.single j 1), φ (Pi.single k 1), ha_w1, hb_w1, hab, hz,
    c, hc_mem, hct, hca, hcb⟩

end CFSG.OddStandard.SmallF3.Omega
