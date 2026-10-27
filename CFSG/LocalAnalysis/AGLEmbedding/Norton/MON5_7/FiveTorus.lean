module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.OddTorus
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.GmatGen
public import Certificates.Certificate125200
public import Certificates.Certificate125201
public import Certificates.Certificate125202
public import Certificates.Certificate125203
public import Certificates.Certificate125204
public import Certificates.Certificate125205
public import Certificates.Certificate125206

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native


theorem gw_powL (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (wordLin_powL k w)

@[expose] noncomputable def qG (j : ℕ) : Gmat := gw (qW j)

@[expose] noncomputable def wG (j : ℕ) : Gmat := gw (wW j)

@[expose] noncomputable def yG (n : ℕ) : Gmat := gw (nodeW n)

theorem qOrder_check : agreeAll qOrderPairs = true := Certificates.certificate125200

theorem qComm_wInv_check : agreeAll qCommPairs = true ∧ agreeAll wInvPairs = true :=
  Certificates.certificate125201

theorem wAction_check : agreeAll wQSelfPairs = true ∧ agreeAll wQOtherPairs = true :=
  Certificates.certificate125202

theorem nodeQ_zero_check : agreeAll (nodeQPairs 0) = true := Certificates.certificate125203

theorem nodeQ_one_check : agreeAll (nodeQPairs 1) = true := Certificates.certificate125204

theorem nodeQ_two_check : agreeAll (nodeQPairs 2) = true := Certificates.certificate125205

theorem qMove_check :
    EdgeNoncomm.moveCheck (qW 0) (aV ()) = true ∧ EdgeNoncomm.moveCheck (qW 1) (aV ()) = true ∧
      EdgeNoncomm.moveCheck (qW 2) (aV ()) = true := Certificates.certificate125206

theorem qG_pow_five {i : ℕ} (hi : i < 3) : qG i ^ 5 = 1 := by
  have h := agreeAll_sound qOrder_check (powL 5 (qW i), [])
    (List.mem_map.2 ⟨i, by simp; omega, rfl⟩)
  simpa [gw_powL, gw_nil, qG] using h

theorem qG_ne_one {i : ℕ} (hi : i < 3) : qG i ≠ 1 := by
  have h := qMove_check
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact gw_ne_one_of_moveCheck h.1
  · exact gw_ne_one_of_moveCheck h.2.1
  · exact gw_ne_one_of_moveCheck h.2.2

theorem qG_orderOf {i : ℕ} (hi : i < 3) : orderOf (qG i) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (qG_pow_five hi) (qG_ne_one hi)

theorem qG_comm_aux {a b : ℕ} (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2)] : List (ℕ × ℕ))) :
    qG a * qG b = qG b * qG a := by
  have := agreeAll_sound qComm_wInv_check.1 (qW b ++ qW a, qW a ++ qW b)
    (List.mem_map.2 ⟨(a, b), hab, rfl⟩)
  simpa [gw_append, qG] using this

theorem qG_comm (i j : Fin 3) : Commute (qG i) (qG j) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have h01 : qG 0 * qG 1 = qG 1 * qG 0 := qG_comm_aux (by simp)
  have h02 : qG 0 * qG 2 = qG 2 * qG 0 := qG_comm_aux (by simp)
  have h12 : qG 1 * qG 2 = qG 2 * qG 1 := qG_comm_aux (by simp)
  show Commute (qG i) (qG j)
  interval_cases i <;> interval_cases j
  · exact Commute.refl _
  · exact h01
  · exact h02
  · exact h01.symm
  · exact Commute.refl _
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _

theorem wG_sq {i : ℕ} (hi : i < 3) : wG i * wG i = 1 := by
  have := agreeAll_sound qComm_wInv_check.2 (wW i ++ wW i, [])
    (List.mem_map.2 ⟨i, by simp; omega, rfl⟩)
  simpa [gw_append, gw_nil, wG] using this

theorem wG_inv {i : ℕ} (hi : i < 3) : (wG i)⁻¹ = wG i := inv_eq_of_mul_eq_one_right (wG_sq hi)

theorem wG_qG_self {i : ℕ} (hi : i < 3) : wG i * qG i * wG i = qG i ^ 4 := by
  have := agreeAll_sound wAction_check.1 (wW i ++ qW i ++ wW i, powL 4 (qW i))
    (List.mem_map.2 ⟨i, by simp; omega, rfl⟩)
  simpa [gw_append, gw_powL, wG, qG, mul_assoc] using this

theorem wG_qG_other {i j : ℕ} (hij : (i, j) ∈
    ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)] : List (ℕ × ℕ))) :
    wG i * qG j * wG i = qG j := by
  have := agreeAll_sound wAction_check.2 (wW i ++ qW j ++ wW i, qW j)
    (List.mem_map.2 ⟨(i, j), hij, rfl⟩)
  simpa [gw_append, wG, qG, mul_assoc] using this

theorem wG_inverts (j : Fin 3) : wG j * qG j * (wG j)⁻¹ = (qG j)⁻¹ := by
  have hj : (j : ℕ) < 3 := j.2
  rw [wG_inv hj, wG_qG_self hj]
  have h5 := qG_pow_five hj
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ]
  exact h5

theorem wG_fixes (i j : Fin 3) (hij : i ≠ j) : wG i * qG j * (wG i)⁻¹ = qG j := by
  rw [wG_inv i.2]
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hne : i ≠ j := fun h => hij (Fin.ext h)
  show wG i * qG j * wG i = qG j
  refine wG_qG_other ?_
  interval_cases i <;> interval_cases j <;> first | exact absurd rfl hne | simp

theorem yG_comm_aux {a k j : ℕ} (ha : a < 3) (hk : k < 5) (hj : j < 3) (hja : j ≠ a) :
    yG (5 * a + k) * qG j = qG j * yG (5 * a + k) := by
  have hmem : (qW j ++ nodeW (5 * a + k), nodeW (5 * a + k) ++ qW j) ∈ nodeQPairs a := by
    unfold nodeQPairs
    refine List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩
    refine List.mem_filterMap.2 ⟨j, ?_, ?_⟩
    · simp; omega
    · simp [hja]
  have hall : agreeAll (nodeQPairs a) = true := by
    have : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact nodeQ_zero_check
    · exact nodeQ_one_check
    · exact nodeQ_two_check
  have := agreeAll_sound hall _ hmem
  simpa [gw_append, yG, qG] using this

@[expose] def nodeIdx (v : ℕ) : ℕ := if v < 4 then v else if v < 8 then v + 1 else v + 2

theorem nodeIdx_spec {v : ℕ} (hv : v < 11) : nodeIdx v < 15 ∧ nodeW (nodeIdx v) = L v := by
  interval_cases v <;> exact ⟨by decide, rfl⟩

theorem gGen_mem_range (g : CFSG.YGroups.E443Gen) : gGen g ∈ Set.range (fun n : Fin 15 => yG n) := by
  obtain ⟨hlt, hw⟩ := nodeIdx_spec (wIdx_lt g)
  refine ⟨⟨nodeIdx (wIdx g), hlt⟩, ?_⟩
  apply Subtype.ext
  show wordLin (nodeW (nodeIdx (wIdx g))) = M (wIdx g)
  rw [hw]
  rfl

theorem closure_yG : Subgroup.closure (Set.range fun n : Fin 15 => yG n) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← closure_range_gGen_eq_top]
  exact Subgroup.closure_mono (by rintro _ ⟨g, rfl⟩; exact gGen_mem_range g)

theorem yG_act (n : Fin 15) : ∃ m : Fin 3, ∀ j : Fin 3, j ≠ m →
    yG n * qG j * (yG n)⁻¹ = qG j ∨ yG n * qG j * (yG n)⁻¹ = (qG j)⁻¹ := by
  have hm : (n : ℕ) / 5 < 3 := by have := n.2; omega
  refine ⟨⟨(n : ℕ) / 5, hm⟩, fun j hj => Or.inl ?_⟩
  have hja : (j : ℕ) ≠ (n : ℕ) / 5 := fun h => hj (Fin.ext h)
  have h := yG_comm_aux (a := (n : ℕ) / 5) (k := (n : ℕ) % 5) hm (Nat.mod_lt _ (by norm_num)) j.2 hja
  rw [Nat.div_add_mod] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem nonempty_torusDatum_gmat_five : Nonempty (TorusDatumP 5 Gmat (Fin 15)) :=
  ⟨{ y := fun n => yG n
     q := fun j => qG j
     w := fun j => wG j
     gen := closure_yG
     comm := qG_comm
     ord := fun j => qG_orderOf j.2
     inv := wG_inverts
     fix := wG_fixes
     act := yG_act }⟩

end CFSG.AGLEmbedding.Norton.MON5_7
