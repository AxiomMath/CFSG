module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeCore
public import CFSG.Sporadic.Bridge.Y443Split

public section

namespace CFSG.AGLEmbedding.MonsterThree

open CFSG.Sporadic.Bridge.Y443 CFSG.Blueprint.NativeSporadic
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem x_zero_mul_mem (k : Fin 12) : x 0 * x k ∈ commutator Y443 := by
  have h := x0_inv_mul_mem k
  rwa [x_inv] at h

theorem x_mul_mem {a b : Fin 12} (hne : a ≠ b) (hadj : y443Adjacent a b) :
    x a * x b ∈ commutator Y443 := by
  have h := inv_mul_mem_commutator hne hadj
  rwa [x_inv] at h

private theorem conj_x_zero_mul (j k : Fin 12) :
    x j * (x 0 * x k) * (x j)⁻¹ = (x 0 * x j)⁻¹ * (x 0 * x k)⁻¹ * (x 0 * x j) := by
  have h00 : x 0 * (x 0 * x j) = x j := by rw [← mul_assoc, x_mul_self, one_mul]
  simp only [mul_inv_rev, x_inv, mul_assoc]
  rw [h00]

theorem closure_x_zero_mul :
    Subgroup.closure (Set.range fun k : Fin 12 => x 0 * x k) = commutator Y443 := by
  set N : Subgroup Y443 := Subgroup.closure (Set.range fun k : Fin 12 => x 0 * x k) with hN
  have hmem : ∀ k, x 0 * x k ∈ N := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  have hle : N ≤ commutator Y443 := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact x_zero_mul_mem k
  have hconj : ∀ j k, x j * (x 0 * x k) * (x j)⁻¹ ∈ N := fun j k => by
    rw [conj_x_zero_mul]
    exact N.mul_mem (N.mul_mem (N.inv_mem (hmem j)) (N.inv_mem (hmem k))) (hmem j)
  have hconj' : ∀ j k, (x j)⁻¹ * (x 0 * x k) * x j ∈ N := fun j k => by
    have h := hconj j k
    rw [x_inv] at h ⊢
    exact h
  have hnormalizer : ∀ j, x j ∈ Subgroup.normalizer (N : Set Y443) := fun j =>
    mem_normalizer_closure_of_conj_mem_inv
      (by rintro _ ⟨k, rfl⟩; exact hconj j k)
      (by rintro _ ⟨k, rfl⟩; exact hconj' j k)
  have hnormal : N.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← PresentedGroup.closure_range_of,
      Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact hnormalizer k
  have htop : ∀ g : Y443, g ∈ N ⊔ Subgroup.zpowers (x 0) := fun g => by
    have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 12 → Y443)) := by
      rw [PresentedGroup.closure_range_of]
      exact Subgroup.mem_top g
    refine (Subgroup.closure_le (N ⊔ Subgroup.zpowers (x 0))).2 ?_ hg
    rintro _ ⟨k, rfl⟩
    refine Subgroup.mem_sup_of_normal_left.2 ⟨x k * x 0, ?_, x 0, Subgroup.mem_zpowers _, ?_⟩
    · have : x k * x 0 = (x 0 * x k)⁻¹ := by rw [mul_inv_rev, x_inv, x_inv]
      rw [this]
      exact N.inv_mem (hmem k)
    · rw [mul_assoc, x_mul_self, mul_one]
  refine le_antisymm hle (fun g hg => ?_)
  obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (htop g)
  obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hx2 : x 0 ^ 2 = 1 := by rw [pow_two, x_mul_self]
  rw [commutator_eq_ker_sgn] at hg
  rcases Int.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rw [zpow_mul, zpow_two, ← pow_two, hx2, one_zpow, mul_one]
    exact hn
  · exfalso
    rw [MonoidHom.mem_ker, map_mul, commutator_le_ker_sgn (hle hn), one_mul, zpow_add, zpow_mul,
      zpow_two, ← pow_two, hx2, one_zpow, one_mul, zpow_one, sgn_x] at hg
    exact absurd hg (by decide)

private theorem ne_of_adjB : ∀ a b : Fin 12, adjB a b = true → a ≠ b := by decide

private theorem adjB_false_of_path :
    ∀ a b c : Fin 12, adjB a b = true → adjB b c = true → a ≠ c → adjB a c = false := by decide

theorem x_eq_of_path {a b c : Fin 12} (hab : adjB a b = true) (hbc : adjB b c = true)
    (h : x a = x b) : x b = x c := by
  by_cases hac : a = c
  · rw [← hac]
    exact h.symm
  · have hna : ¬ y443Adjacent a c := by
      rw [adjacent_iff_adjB, adjB_false_of_path a b c hab hbc hac]
      exact Bool.false_ne_true
    have h2 : (x a * x c) ^ 2 = 1 := x_nadj hac hna
    have h3 : (x b * x c) ^ 3 = 1 := x_adj (ne_of_adjB b c hbc) (adj_of_adjB hbc)
    rw [h] at h2
    have h1 : x b * x c = 1 := by
      calc x b * x c = (x b * x c) ^ 3 * ((x b * x c) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact (mul_eq_one_iff_eq_inv.1 h1).trans (x_inv c)

private theorem x_eq_zero_of_01 (h : x 0 = x 1) : ∀ k, x k = x 0 := by
  have e5 : x 0 = x 5 := x_eq_of_path (a := 1) (b := 0) (c := 5) (by decide) (by decide) h.symm
  have e9 : x 0 = x 9 := x_eq_of_path (a := 1) (b := 0) (c := 9) (by decide) (by decide) h.symm
  have e2 : x 1 = x 2 := x_eq_of_path (a := 0) (b := 1) (c := 2) (by decide) (by decide) h
  have e3 : x 2 = x 3 := x_eq_of_path (a := 1) (b := 2) (c := 3) (by decide) (by decide) e2
  have e4 : x 3 = x 4 := x_eq_of_path (a := 2) (b := 3) (c := 4) (by decide) (by decide) e3
  have e6 : x 5 = x 6 := x_eq_of_path (a := 0) (b := 5) (c := 6) (by decide) (by decide) e5
  have e7 : x 6 = x 7 := x_eq_of_path (a := 5) (b := 6) (c := 7) (by decide) (by decide) e6
  have e8 : x 7 = x 8 := x_eq_of_path (a := 6) (b := 7) (c := 8) (by decide) (by decide) e7
  have e10 : x 9 = x 10 := x_eq_of_path (a := 0) (b := 9) (c := 10) (by decide) (by decide) e9
  have e11 : x 10 = x 11 :=
    x_eq_of_path (a := 9) (b := 10) (c := 11) (by decide) (by decide) e10
  have a1 : x 1 = x 0 := h.symm
  have a2 : x 2 = x 0 := e2.symm.trans a1
  have a3 : x 3 = x 0 := e3.symm.trans a2
  have a4 : x 4 = x 0 := e4.symm.trans a3
  have a5 : x 5 = x 0 := e5.symm
  have a6 : x 6 = x 0 := e6.symm.trans a5
  have a7 : x 7 = x 0 := e7.symm.trans a6
  have a8 : x 8 = x 0 := e8.symm.trans a7
  have a9 : x 9 = x 0 := e9.symm
  have a10 : x 10 = x 0 := e10.symm.trans a9
  have a11 : x 11 = x 0 := e11.symm.trans a10
  intro k
  fin_cases k
  exacts [rfl, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]

private theorem x_eq_01_of_34 (h : x 3 = x 4) : x 0 = x 1 := by
  have h1 : x 3 = x 2 := x_eq_of_path (a := 4) (b := 3) (c := 2) (by decide) (by decide) h.symm
  have h2 : x 2 = x 1 := x_eq_of_path (a := 3) (b := 2) (c := 1) (by decide) (by decide) h1
  exact (x_eq_of_path (a := 2) (b := 1) (c := 0) (by decide) (by decide) h2).symm

private theorem x_eq_01_of_78 (h : x 7 = x 8) : x 0 = x 1 := by
  have h1 : x 7 = x 6 := x_eq_of_path (a := 8) (b := 7) (c := 6) (by decide) (by decide) h.symm
  have h2 : x 6 = x 5 := x_eq_of_path (a := 7) (b := 6) (c := 5) (by decide) (by decide) h1
  have h3 : x 5 = x 0 := x_eq_of_path (a := 6) (b := 5) (c := 0) (by decide) (by decide) h2
  exact x_eq_of_path (a := 5) (b := 0) (c := 1) (by decide) (by decide) h3

private theorem x_eq_01_of_1011 (h : x 10 = x 11) : x 0 = x 1 := by
  have h1 : x 10 = x 9 := x_eq_of_path (a := 11) (b := 10) (c := 9) (by decide) (by decide) h.symm
  have h2 : x 9 = x 0 := x_eq_of_path (a := 10) (b := 9) (c := 0) (by decide) (by decide) h1
  exact x_eq_of_path (a := 9) (b := 0) (c := 1) (by decide) (by decide) h2

private theorem not_forall_x_eq (h : Nontrivial (commutator Y443)) : ¬ ∀ k, x k = x 0 := by
  intro hall
  have hbot : commutator Y443 = ⊥ := by
    rw [← closure_x_zero_mul, eq_bot_iff, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    show x 0 * x k ∈ (⊥ : Subgroup Y443)
    rw [hall k, x_mul_self]
    exact Subgroup.one_mem _
  obtain ⟨g, hg⟩ := exists_ne (1 : commutator Y443)
  apply hg
  apply Subtype.ext
  have hg' : (g : Y443) ∈ (⊥ : Subgroup Y443) := by
    rw [← hbot]
    exact g.2
  exact Subgroup.mem_bot.1 hg'

theorem x_ne_of_nontrivial (h : Nontrivial (commutator Y443)) :
    x 3 ≠ x 4 ∧ x 7 ≠ x 8 ∧ x 10 ≠ x 11 :=
  ⟨fun e => not_forall_x_eq h (x_eq_zero_of_01 (x_eq_01_of_34 e)),
    fun e => not_forall_x_eq h (x_eq_zero_of_01 (x_eq_01_of_78 e)),
    fun e => not_forall_x_eq h (x_eq_zero_of_01 (x_eq_01_of_1011 e))⟩

private def pa : Fin 3 → Fin 12 := ![3, 7, 10]

private def pb : Fin 3 → Fin 12 := ![4, 8, 11]

private noncomputable def qY (j : Fin 3) : Y443 := x (pa j) * x (pb j)

private abbrev Far (u v : Fin 12) : Prop := u ≠ v ∧ adjB u v = false

private theorem adj_pair : ∀ j : Fin 3, adjB (pa j) (pb j) = true := by decide

private theorem ne_pair : ∀ j : Fin 3, pa j ≠ pb j := by decide

private theorem far_pairs : ∀ i j : Fin 3, i ≠ j →
    Far (pa i) (pa j) ∧ Far (pa i) (pb j) ∧ Far (pb i) (pa j) ∧ Far (pb i) (pb j) := by decide

private theorem far_zero : ∀ j : Fin 3, Far 0 (pa j) ∧ Far 0 (pb j) := by decide

private theorem good_table : ∀ k : Fin 12, ∃ m : Fin 3, ∀ j : Fin 3, j ≠ m →
    k = pa j ∨ k = pb j ∨ (Far k (pa j) ∧ Far k (pb j)) := by decide

private theorem commute_of_far {u v : Fin 12} (h : Far u v) : Commute (x u) (x v) :=
  commute_nadj h.1 (by rw [adjacent_iff_adjB, h.2]; exact Bool.false_ne_true)

private theorem qY_cube (j : Fin 3) : qY j ^ 3 = 1 :=
  x_adj (ne_pair j) (adj_of_adjB (adj_pair j))

private theorem qY_mem (j : Fin 3) : qY j ∈ commutator Y443 :=
  x_mul_mem (ne_pair j) (adj_of_adjB (adj_pair j))

private theorem qY_comm (i j : Fin 3) : Commute (qY i) (qY j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · obtain ⟨h1, h2, h3, h4⟩ := far_pairs i j hij
    exact ((commute_of_far h1).mul_right (commute_of_far h2)).mul_left
      ((commute_of_far h3).mul_right (commute_of_far h4))

private theorem qY_ne_one (hnt : Nontrivial (commutator Y443)) (j : Fin 3) : qY j ≠ 1 := by
  intro h
  have h1 : x (pa j) = x (pb j) := (mul_eq_one_iff_eq_inv.1 h).trans (x_inv _)
  obtain ⟨h34, h78, h1011⟩ := x_ne_of_nontrivial hnt
  fin_cases j
  · exact h34 h1
  · exact h78 h1
  · exact h1011 h1

private theorem conj_left (a b : Fin 12) : x a * (x a * x b) * (x a)⁻¹ = (x a * x b)⁻¹ := by
  rw [mul_inv_rev, x_inv, x_inv, ← mul_assoc, x_mul_self, one_mul]

private theorem conj_right (a b : Fin 12) : x b * (x a * x b) * (x b)⁻¹ = (x a * x b)⁻¹ := by
  rw [mul_inv_rev, x_inv, x_inv, mul_assoc, mul_assoc, x_mul_self, mul_one]

private theorem conj_far {k : Fin 12} {j : Fin 3} (h1 : Far k (pa j)) (h2 : Far k (pb j)) :
    x k * qY j * (x k)⁻¹ = qY j := by
  have hc : Commute (x k) (qY j) := (commute_of_far h1).mul_right (commute_of_far h2)
  rw [hc.eq, mul_inv_cancel_right]

private theorem zero_far (j : Fin 3) : x 0 * qY j * (x 0)⁻¹ = qY j :=
  conj_far (far_zero j).1 (far_zero j).2

private theorem y_conj_eq (k : Fin 12) (j : Fin 3) (h : x k * qY j * (x k)⁻¹ = qY j) :
    (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = qY j := by
  calc (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = x 0 * (x k * qY j * (x k)⁻¹) * (x 0)⁻¹ := by group
    _ = qY j := by rw [h]; exact zero_far j

private theorem y_conj_inv (k : Fin 12) (j : Fin 3) (h : x k * qY j * (x k)⁻¹ = (qY j)⁻¹) :
    (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = (qY j)⁻¹ := by
  calc (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = x 0 * (x k * qY j * (x k)⁻¹) * (x 0)⁻¹ := by group
    _ = x 0 * (qY j)⁻¹ * (x 0)⁻¹ := by rw [h]
    _ = (x 0 * qY j * (x 0)⁻¹)⁻¹ := by group
    _ = (qY j)⁻¹ := by rw [zero_far j]

private theorem y_act (k : Fin 12) (j : Fin 3)
    (hk : k = pa j ∨ k = pb j ∨ (Far k (pa j) ∧ Far k (pb j))) :
    (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = qY j ∨
      (x 0 * x k) * qY j * (x 0 * x k)⁻¹ = (qY j)⁻¹ := by
  rcases hk with rfl | rfl | ⟨h1, h2⟩
  · exact Or.inr (y_conj_inv _ _ (conj_left _ _))
  · exact Or.inr (y_conj_inv _ _ (conj_right _ _))
  · exact Or.inl (y_conj_eq _ _ (conj_far h1 h2))

private theorem y_flip (j : Fin 3) :
    (x 0 * x (pa j)) * qY j * (x 0 * x (pa j))⁻¹ = (qY j)⁻¹ :=
  y_conj_inv _ _ (conj_left _ _)

private theorem y_fix (i j : Fin 3) (hij : i ≠ j) :
    (x 0 * x (pa i)) * qY j * (x 0 * x (pa i))⁻¹ = qY j := by
  obtain ⟨h1, h2, -, -⟩ := far_pairs i j hij
  exact y_conj_eq _ _ (conj_far h1 h2)

private noncomputable def datum (hnt : Nontrivial (commutator Y443)) :
    Datum (commutator Y443) (Fin 12) where
  y k := ⟨x 0 * x k, x_zero_mul_mem k⟩
  q j := ⟨qY j, qY_mem j⟩
  w j := ⟨x 0 * x (pa j), x_zero_mul_mem _⟩
  gen := by
    apply Subgroup.map_injective (commutator Y443).subtype_injective
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact closure_x_zero_mul
  comm i j := Subtype.ext (by simpa using (qY_comm i j).eq)
  ord j := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (Subtype.ext (by simpa using qY_cube j))
      fun h => qY_ne_one hnt j (congrArg Subtype.val h)
  inv j := Subtype.ext (by simpa using y_flip j)
  fix i j hij := Subtype.ext (by simpa using y_fix i j hij)
  act k := by
    obtain ⟨m, hm⟩ := good_table k
    refine ⟨m, fun j hj => ?_⟩
    rcases y_act k j (hm j hj) with h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Subtype.ext (by simpa using h))

theorem liftableNormalizerGen_M (hnt : Nontrivial (Carrier .M)) :
    LiftableNormalizerGen (Carrier .M) :=
  (datum hnt).liftableNormalizerGen

theorem fusionGenerationOf_M_three (hnt : Nontrivial (Carrier .M)) :
    FusionGenerationOf (Carrier .M) 3 :=
  (datum hnt).fusionGenerationOf

end CFSG.AGLEmbedding.MonsterThree
