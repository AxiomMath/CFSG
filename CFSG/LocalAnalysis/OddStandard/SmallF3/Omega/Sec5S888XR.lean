module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888XP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private abbrev permMoved (π : Equiv.Perm (Fin 4)) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => π i ≠ i).card

private lemma permMoved_le_mval (hS : PlaneSys V W) (y : normalizer (V : Set X)) :
    permMoved (planeHom hS y) ≤ mval hS y := by
  unfold mval
  exact Nat.le_add_right _ _

private lemma mval_le_of_card (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    {n : ℕ} (hn3 : n ≤ 3)
    (hcard : ∀ u ∈ F, u ∉ centralizer (V : Set X) →
      2 ^ (8 - n) ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v}) :
    ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ n := by
  intro y hy hyC
  have h1 : 2 ^ (8 - n) ≤ Nat.card {v : V // (y : X) * (v : X) * (y : X)⁻¹ = v} :=
    hcard (y : X) hy hyC
  have h2 : Nat.card {v : V // (y : X) * (v : X) * (y : X)⁻¹ = v} ≤ 2 ^ (8 - mval hS y) :=
    card_centralizer_le_mval hS y (hF.sq (y : X) hy)
  have h3 : 2 ^ (8 - n) ≤ 2 ^ (8 - mval hS y) := h1.trans h2
  have h4 : 8 - n ≤ 8 - mval hS y :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

private lemma planeHom_eq_one_of_mem_centralizer (hS : PlaneSys V W)
    (y : normalizer (V : Set X)) (hy : (y : X) ∈ centralizer (V : Set X)) :
    planeHom hS y = 1 := by
  apply planeHom_eq_one_of_centralizes hS y
  intro v hv
  have hcomm := (Subgroup.mem_centralizer_iff.mp hy) v hv
  rw [← hcomm]
  group

private lemma planeHom_mul_comm (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    {y y' : normalizer (V : Set X)} (hy : (y : X) ∈ F) (hy' : (y' : X) ∈ F) :
    planeHom hS (y * y') = planeHom hS (y' * y) := by
  let c : normalizer (V : Set X) := (y * y') * (y' * y)⁻¹
  have hcX : (c : X) ∈ centralizer (V : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hu : ((y' : X) * (y : X))⁻¹ * v * ((y' : X) * (y : X)) ∈ V := by
      have hBn : ((y' : X) * (y : X))⁻¹ ∈ normalizer (V : Set X) := by
        simpa only [Subgroup.coe_inv, Subgroup.coe_mul] using
          ((y' * y)⁻¹ : normalizer (V : Set X)).2
      simpa using (Subgroup.mem_normalizer_iff.mp hBn v).mp hv
    have hgoal : (c : X) * v * (c : X)⁻¹ = v := by
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show ((y : X) * (y' : X)) * ((y' : X) * (y : X))⁻¹ * v *
            (((y : X) * (y' : X)) * ((y' : X) * (y : X))⁻¹)⁻¹ =
          (y : X) * (y' : X) *
            (((y' : X) * (y : X))⁻¹ * v * ((y' : X) * (y : X))) *
            ((y : X) * (y' : X))⁻¹ by group]
      rw [hF.comm (y : X) hy (y' : X) hy'
        (((y' : X) * (y : X))⁻¹ * v * ((y' : X) * (y : X))) hu]
      group
    have hcv : (c : X) * v = v * (c : X) := by
      calc (c : X) * v = ((c : X) * v * (c : X)⁻¹) * (c : X) := by group
        _ = v * (c : X) := by rw [hgoal]
    exact hcv.symm
  have h1 : planeHom hS c = 1 := planeHom_eq_one_of_mem_centralizer hS c hcX
  have h2 : planeHom hS c = planeHom hS (y * y') * (planeHom hS (y' * y))⁻¹ := by
    simp only [c, map_mul, map_inv]
  rw [h2] at h1
  rwa [mul_inv_eq_one] at h1

private lemma permMoved_le_of_mem_planeImage (hS : PlaneSys V W) {F : Subgroup X}
    (hF : ActsElemAb V F) {n : ℕ}
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ n)
    {a : Equiv.Perm (Fin 4)} (ha : a ∈ planeImage hS F) (ha1 : a ≠ 1) :
    permMoved a ≤ n := by
  obtain ⟨y, hy, rfl⟩ := (mem_planeImage hS).mp ha
  have hyC : (y : X) ∉ centralizer (V : Set X) := fun hC =>
    ha1 (planeHom_eq_one_of_mem_centralizer hS y hC)
  exact (permMoved_le_mval hS y).trans (hmv y hy hyC)

private lemma planeImage_eq_of_ne_one (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ 3)
    {a b : Equiv.Perm (Fin 4)} (ha : a ∈ planeImage hS F) (hb : b ∈ planeImage hS F)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, hy, rfl⟩ := (mem_planeImage hS).mp ha
  obtain ⟨y', hy', rfl⟩ := (mem_planeImage hS).mp hb
  by_contra hne
  have hsq_a : planeHom hS y * planeHom hS y = 1 :=
    (planeImage_group hS hF).2.2 _ ((mem_planeImage hS).mpr ⟨y, hy, rfl⟩)
  have hsq_b : planeHom hS y' * planeHom hS y' = 1 :=
    (planeImage_group hS hF).2.2 _ ((mem_planeImage hS).mpr ⟨y', hy', rfl⟩)
  have hcomm : planeHom hS y * planeHom hS y' = planeHom hS y' * planeHom hS y := by
    rw [← map_mul (planeHom hS) y y', ← map_mul (planeHom hS) y' y]
    exact planeHom_mul_comm hS hF hy hy'
  have hma : permMoved (planeHom hS y) ≤ 3 :=
    permMoved_le_of_mem_planeImage hS hF hmv ((mem_planeImage hS).mpr ⟨y, hy, rfl⟩) ha1
  have hmb : permMoved (planeHom hS y') ≤ 3 :=
    permMoved_le_of_mem_planeImage hS hF hmv ((mem_planeImage hS).mpr ⟨y', hy', rfl⟩) hb1
  have hmoved4 : permMoved (planeHom hS y * planeHom hS y') = 4 :=
    perm_moved_four hsq_a hsq_b hcomm hne ha1 hb1 hma hmb
  have hab_ne : planeHom hS y * planeHom hS y' ≠ 1 := by
    intro h
    rw [h] at hmoved4
    have h0 : permMoved (1 : Equiv.Perm (Fin 4)) = 0 := by simp [permMoved]
    rw [h0] at hmoved4
    omega
  have hyy'F : ((y * y' : normalizer (V : Set X)) : X) ∈ F := by
    simpa only [Subgroup.coe_mul] using F.mul_mem hy hy'
  have hyy'C : ((y * y' : normalizer (V : Set X)) : X) ∉ centralizer (V : Set X) := by
    intro hC
    exact hab_ne (by
      have h := planeHom_eq_one_of_mem_centralizer hS (y * y') hC
      rwa [map_mul] at h)
  have hmv' : mval hS (y * y') ≤ 3 := hmv (y * y') hyy'F hyy'C
  have hmoved_le : permMoved (planeHom hS (y * y')) ≤ 3 :=
    (permMoved_le_mval hS (y * y')).trans hmv'
  rw [map_mul] at hmoved_le
  omega

private lemma planeImage_card_le_two (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ 3) :
    (planeImage hS F).card ≤ 2 := by
  classical
  by_cases hex : ∃ a ∈ planeImage hS F, a ≠ 1
  · obtain ⟨a₀, ha₀, ha₀1⟩ := hex
    have hsub : planeImage hS F ⊆ ({1, a₀} : Finset (Equiv.Perm (Fin 4))) := by
      intro b hb
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (planeImage_eq_of_ne_one hS hF hmv hb ha₀ hb1 ha₀1)
    calc (planeImage hS F).card
        ≤ ({1, a₀} : Finset (Equiv.Perm (Fin 4))).card := Finset.card_le_card hsub
      _ = 2 := Finset.card_pair_eq_two_iff.mpr ha₀1.symm
  · push Not at hex
    have hsub : planeImage hS F ⊆ ({1} : Finset (Equiv.Perm (Fin 4))) := by
      intro b hb
      rw [Finset.mem_singleton]
      exact hex b hb
    calc (planeImage hS F).card ≤ ({1} : Finset (Equiv.Perm (Fin 4))).card :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton 1
      _ ≤ 2 := by norm_num

private lemma suppSet_weight_le_three (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ 3) :
    ∀ x ∈ suppSet hS F, vecWeight x ≤ 3 := by
  intro x hx
  rw [mem_suppSet] at hx
  obtain ⟨y, hy, hy1, rfl⟩ := hx
  by_cases hyC : (y : X) ∈ centralizer (V : Set X)
  · rw [suppVec_eq_zero_of_mem_centralizer hS y hyC]
    simp [vecWeight]
  · rw [← mval_eq_vecWeight hS y hy1]
    exact hmv y hy hyC

private lemma suppSet_card_le_seven (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hpar : PlaneParity V W)
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ 3) :
    (suppSet hS F).card ≤ 7 := by
  classical
  have hw := suppSet_weight_le_three hS hF hmv
  have he := suppSet_even hS hpar hF
  have hsub : suppSet hS F ⊆ Finset.univ.filter
      (fun s : Fin 4 → ZMod 2 => IsEvenVec s ∧ vecWeight s ≤ 3) := by
    intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, he x hx, hw x hx⟩
  have hcard : (Finset.univ.filter
      (fun s : Fin 4 → ZMod 2 => IsEvenVec s ∧ vecWeight s ≤ 3)).card = 7 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_even_weight_le_three
  exact (Finset.card_le_card hsub).trans hcard.le

private lemma suppSet_card_le_three (hS : PlaneSys V W) {F : Subgroup X} (hF : ActsElemAb V F)
    (hpar : PlaneParity V W)
    (hmv : ∀ y : normalizer (V : Set X), (y : X) ∈ F →
      (y : X) ∉ centralizer (V : Set X) → mval hS y ≤ 3)
    {a₀ : Equiv.Perm (Fin 4)} (ha₀ : a₀ ∈ planeImage hS F) (ha₀1 : a₀ ≠ 1) :
    (suppSet hS F).card ≤ 3 := by
  classical
  have hsq : a₀ * a₀ = 1 := (planeImage_group hS hF).2.2 a₀ ha₀
  have hmoved : permMoved a₀ ≤ 3 :=
    permMoved_le_of_mem_planeImage hS hF hmv ha₀ ha₀1
  have hw := suppSet_weight_le_three hS hF hmv
  have he := suppSet_even hS hpar hF
  have hfix := suppSet_fixed hS hF
  have hsub : suppSet hS F ⊆ Finset.univ.filter
      (fun s : Fin 4 → ZMod 2 =>
        IsEvenVec s ∧ vecWeight s ≤ 3 ∧ ∀ i, s (a₀ i) = s i) := by
    intro x hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, he x hx, hw x hx, fun i => hfix x hx a₀ ha₀ i⟩
  have hcard : (Finset.univ.filter
      (fun s : Fin 4 → ZMod 2 =>
        IsEvenVec s ∧ vecWeight s ≤ 3 ∧ ∀ i, s (a₀ i) = s i)).card ≤ 3 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_even_weight_le_three_fixed hsq ha₀1 hmoved
  exact (Finset.card_le_card hsub).trans hcard

theorem rank_eq_two [Finite X] (hS : PlaneSys V W) (hpar : PlaneParity V W) {F : Subgroup X}
    (hF : ActsElemAb V F) {n : ℕ} (hn1 : 1 ≤ n) (hn3 : n ≤ 3)
    (hrk : (centralizer (V : Set X)).relIndex F = 2 ^ n)
    (hcard : ∀ u ∈ F, u ∉ centralizer (V : Set X) →
      2 ^ (8 - n) ≤ Nat.card {v : V // u * (v : X) * u⁻¹ = v}) : n = 2 := by
  classical
  have hmv := mval_le_of_card hS hF hn3 hcard
  have hn1' : n ≠ 1 := by
    intro hn
    subst hn
    have hnotle : ¬ F ≤ centralizer (V : Set X) := by
      intro hle
      have h1 : (centralizer (V : Set X)).relIndex F = 1 :=
        Subgroup.relIndex_eq_one.mpr hle
      rw [h1] at hrk
      norm_num at hrk
    obtain ⟨u, hu, huC⟩ : ∃ u ∈ F, u ∉ centralizer (V : Set X) := by
      by_contra h
      push Not at h
      exact hnotle h
    have hyN : u ∈ normalizer (V : Set X) := hF.le_normalizer hu
    have hmv1 : mval hS ⟨u, hyN⟩ ≤ 1 := hmv ⟨u, hyN⟩ hu huC
    have h2 : 2 ≤ mval hS ⟨u, hyN⟩ :=
      two_le_mval hS hpar ⟨u, hyN⟩ (hF.sq u hu) huC
    omega
  have hn3' : n ≠ 3 := by
    intro hn
    subst hn
    have hprod : (planeImage hS F).card * (suppSet hS F).card = 8 := by
      rw [← relIndex_centralizer_eq hS hF, hrk]
      norm_num
    have hHcard : (planeImage hS F).card ≤ 2 := planeImage_card_le_two hS hF hmv
    have hD7 : (suppSet hS F).card ≤ 7 := suppSet_card_le_seven hS hF hpar hmv
    have hHpos : 0 < (planeImage hS F).card :=
      Finset.card_pos.mpr ⟨1, (planeImage_group hS hF).1⟩
    have hH12 : (planeImage hS F).card = 1 ∨ (planeImage hS F).card = 2 := by omega
    rcases hH12 with h1 | h2
    · have hD8 : (suppSet hS F).card = 8 := by
        rw [h1, one_mul] at hprod
        exact hprod
      omega
    · have hD4 : (suppSet hS F).card = 4 := by
        rw [h2] at hprod
        omega
      have hex : ∃ a₀ ∈ planeImage hS F, a₀ ≠ 1 := by
        by_contra h
        push Not at h
        have hsub : planeImage hS F ⊆ ({1} : Finset (Equiv.Perm (Fin 4))) := by
          intro b hb
          rw [Finset.mem_singleton]
          exact h b hb
        have := Finset.card_le_card hsub
        rw [Finset.card_singleton] at this
        omega
      obtain ⟨a₀, ha₀, ha₀1⟩ := hex
      have hD3 : (suppSet hS F).card ≤ 3 :=
        suppSet_card_le_three hS hF hpar hmv ha₀ ha₀1
      omega
  interval_cases n
  · exfalso; exact hn1' rfl
  · rfl
  · exfalso; exact hn3' rfl

end CFSG.OddStandard.SmallF3.Omega
