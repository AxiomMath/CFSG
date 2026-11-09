module

public import CFSG.Certificates.SchreierChainOrder
public import Mathlib.Algebra.BigOperators.Intervals

public section

namespace CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} (Q : RawSchreierDatum n)

@[expose] noncomputable def orbCardAt (j : ℕ) : ℕ :=
  if h : j < Q.baseCount then Nat.card (Q.orbitPoints ⟨j, h⟩) else 1

theorem orbCardAt_fin (i : Fin Q.baseCount) : Q.orbCardAt i.val = Nat.card (Q.orbitPoints i) := by
  simp [orbCardAt]

theorem orbCardAt_pos (j : ℕ) : 0 < Q.orbCardAt j := by
  unfold orbCardAt
  split_ifs with h
  · have hb : Q.base.get ⟨j, h⟩ ∈ Q.orbitPoints ⟨j, h⟩ := by
      rw [Q.orbitPoints_eq_orbit]
      exact MulAction.mem_orbit_self _
    exact Nat.card_pos_iff.2 ⟨⟨⟨_, hb⟩⟩, Set.toFinite _⟩
  · exact Nat.one_pos

theorem orderCertificate_eq_prod_range :
    Q.orderCertificate = ∏ j ∈ Finset.range Q.baseCount, Q.orbCardAt j := by
  rw [← Fin.prod_univ_eq_prod_range, orderCertificate, ← Fin.prod_univ_def]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [orbCardAt, orbitSize_eq_card]

theorem card_level_eq_orbit_mul_stab (i : Fin Q.baseCount) :
    Nat.card (Q.levelSubgroup i.val) = Nat.card (Q.orbitPoints i) *
      Nat.card ↥(Q.levelSubgroup i.val ⊓
        MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i)) := by
  have hcard := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup (Q.levelSubgroup i.val) (Q.base.get i))
  rw [Nat.card_prod, ← Q.orbitPoints_eq_orbit i] at hcard
  rw [← hcard]
  congr 1
  exact Nat.card_congr
    { toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
      invFun := fun h => ⟨⟨h.val, h.property.1⟩, h.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_level_chain (a d : ℕ) (h : a + d ≤ Q.baseCount) :
    (∏ j ∈ Finset.Ico a (a + d), Q.orbCardAt j) * Nat.card (Q.levelSubgroup (a + d)) ≤
      Nat.card (Q.levelSubgroup a) := by
  induction d generalizing a with
  | zero => simp
  | succ d ih =>
    let i : Fin Q.baseCount := ⟨a, by omega⟩
    have e : a + (d + 1) = a + 1 + d := by omega
    have ho : Q.orbCardAt a = Nat.card (Q.orbitPoints i) := Q.orbCardAt_fin i
    calc (∏ j ∈ Finset.Ico a (a + (d + 1)), Q.orbCardAt j) *
          Nat.card (Q.levelSubgroup (a + (d + 1)))
        = Q.orbCardAt a * ((∏ j ∈ Finset.Ico (a + 1) (a + 1 + d), Q.orbCardAt j) *
            Nat.card (Q.levelSubgroup (a + 1 + d))) := by
          rw [e, Finset.prod_eq_prod_Ico_succ_bot (by omega), mul_assoc]
      _ ≤ Q.orbCardAt a * Nat.card (Q.levelSubgroup (a + 1)) :=
          Nat.mul_le_mul_left _ (ih (a + 1) (by omega))
      _ ≤ Q.orbCardAt a * Nat.card ↥(Q.levelSubgroup i.val ⊓
            MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (Q.levelSubgroup_succ_le_stabilizer i))
      _ = Nat.card (Q.levelSubgroup a) := by
          rw [ho]
          exact (Q.card_level_eq_orbit_mul_stab i).symm

variable {Q}

theorem levelSubgroup_terminal_of_card
    (hc : Nat.card (Q.levelSubgroup 0) ≤ Q.orderCertificate) :
    Q.levelSubgroup Q.baseCount = ⊥ := by
  have hF := Q.card_level_chain 0 Q.baseCount (by omega)
  rw [zero_add, ← Finset.range_eq_Ico, ← orderCertificate_eq_prod_range] at hF
  have hP : 0 < Q.orderCertificate := by
    rw [orderCertificate_eq_prod_range]
    exact Finset.prod_pos fun j _ => Q.orbCardAt_pos j
  apply Subgroup.eq_bot_of_card_le
  exact Nat.le_of_mul_le_mul_left (by rw [mul_one]; exact hF.trans hc) hP

theorem level_stab_le_of_card (hc : Nat.card (Q.levelSubgroup 0) ≤ Q.orderCertificate)
    (i : Fin Q.baseCount) :
    Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) ≤
      Q.levelSubgroup (i.val + 1) := by
  have h1 := Q.card_level_chain 0 i.val (by omega)
  have h2 := Q.card_level_chain (i.val + 1) (Q.baseCount - (i.val + 1)) (by omega)
  have e2 : i.val + 1 + (Q.baseCount - (i.val + 1)) = Q.baseCount := by omega
  rw [zero_add] at h1
  rw [e2] at h2
  have hk : 1 ≤ Nat.card (Q.levelSubgroup Q.baseCount) := Nat.card_pos
  have hP : Q.orderCertificate = (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) *
      (Q.orbCardAt i.val * ∏ j ∈ Finset.Ico (i.val + 1) Q.baseCount, Q.orbCardAt j) := by
    rw [orderCertificate_eq_prod_range, Finset.range_eq_Ico,
      ← Finset.prod_eq_prod_Ico_succ_bot i.isLt,
      Finset.prod_Ico_consecutive _ (Nat.zero_le _) i.isLt.le]
  have ho : Q.orbCardAt i.val = Nat.card (Q.orbitPoints i) := Q.orbCardAt_fin i
  have hlev := Q.card_level_eq_orbit_mul_stab i
  rw [← ho] at hlev
  have hA : 0 < (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) * Q.orbCardAt i.val :=
    Nat.mul_pos (Finset.prod_pos fun j _ => Q.orbCardAt_pos j) (Q.orbCardAt_pos _)
  have hle : Nat.card ↥(Q.levelSubgroup i.val ⊓
      MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i)) ≤
        Nat.card (Q.levelSubgroup (i.val + 1)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hA
    calc (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) * Q.orbCardAt i.val *
          Nat.card ↥(Q.levelSubgroup i.val ⊓
            MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i))
        = (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) * Nat.card (Q.levelSubgroup i.val) := by
          rw [hlev, mul_assoc]
      _ ≤ Q.orderCertificate := h1.trans hc
      _ = (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) * Q.orbCardAt i.val *
            ∏ j ∈ Finset.Ico (i.val + 1) Q.baseCount, Q.orbCardAt j := by
          rw [hP, mul_assoc]
      _ ≤ (∏ j ∈ Finset.Ico 0 i.val, Q.orbCardAt j) * Q.orbCardAt i.val *
            Nat.card (Q.levelSubgroup (i.val + 1)) :=
          Nat.mul_le_mul_left _ ((Nat.le_mul_of_pos_right _ hk).trans h2)
  exact (Subgroup.eq_of_le_of_card_ge (Q.levelSubgroup_succ_le_stabilizer i) hle).ge

theorem siftResidual_one_of_chain
    (hS : ∀ i : Fin Q.baseCount, Q.levelSubgroup i.val ⊓
      MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) ≤ Q.levelSubgroup (i.val + 1))
    (hT : Q.levelSubgroup Q.baseCount = ⊥) (i : ℕ) (hi : i ≤ Q.baseCount)
    (h : Equiv.Perm (Fin n)) (hh : h ∈ Q.levelSubgroup i) :
    schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 := by
  have go : ∀ d i, i + d = Q.baseCount → ∀ h : Equiv.Perm (Fin n),
      h ∈ Q.levelSubgroup i →
      schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 := by
    intro d
    induction d with
    | zero =>
      intro i hi h hh
      have hi' : i = Q.baseCount := by omega
      subst i
      rw [hT] at hh
      have hh' : h = 1 := Subgroup.mem_bot.1 hh
      subst h
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [siftLevels, hdrop, List.map_nil, schreierSiftResidual]
    | succ d ih =>
      intro i hi h hh
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      have hx : h (Q.base.get j) ∈ Q.orbitPoints j := by
        rw [Q.orbitPoints_eq_orbit j]
        exact MulAction.mem_orbit_iff.2 ⟨⟨h, hh⟩, rfl⟩
      obtain ⟨t, ht, htH, _, htb⟩ := Q.orbitPoint_transversal j (h (Q.base.get j)) hx
      have hnext : t⁻¹ * h ∈ Q.levelSubgroup (i + 1) := by
        apply hS j
        refine ⟨(Q.levelSubgroup i).mul_mem ((Q.levelSubgroup i).inv_mem htH) hh, ?_⟩
        apply MulAction.mem_stabilizer_iff.2
        change t⁻¹ (h (Q.base.get j)) = Q.base.get j
        rw [← htb]
        simp
      rw [Q.siftResidual_strip j h t ht]
      exact ih (i + 1) (by omega) (t⁻¹ * h) hnext
  exact go (Q.baseCount - i) i (by omega) h hh

theorem schTests_of_card (hc : Nat.card (Q.levelSubgroup 0) ≤ Q.orderCertificate) :
    (∀ s ∈ Q.levelGenerators Q.baseCount, s = 1) ∧
      (∀ (i : Fin Q.baseCount) (x : Fin n) (tx : Equiv.Perm (Fin n)),
        (Q.orbitTables.get i).transversal? x = some tx →
        ∀ s ∈ Q.levelSteps i.val, ∃ ty : Equiv.Perm (Fin n),
          (Q.orbitTables.get i).transversal? (s x) = some ty ∧
          schreierSiftSucceeds (Q.siftLevels Q.orbitTables (i.val + 1)) (ty⁻¹ * s * tx) =
            true) := by
  have hT := levelSubgroup_terminal_of_card hc
  refine ⟨fun s hs => ?_, fun i x tx htx s hs => ?_⟩
  · have hm : s ∈ Q.levelSubgroup Q.baseCount := Subgroup.subset_closure hs
    rw [hT] at hm
    exact Subgroup.mem_bot.1 hm
  rw [orbitTables_get] at htx ⊢
  obtain ⟨htxH, -, htxb⟩ := Q.transversal_sound i x tx htx
  have hsH : s ∈ Q.levelSubgroup i.val := by
    rcases List.mem_append.1 hs with hs | hs
    · exact Subgroup.subset_closure hs
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
      exact (Q.levelSubgroup i.val).inv_mem (Subgroup.subset_closure hg)
  have hx : s x ∈ Q.orbitPoints i := by
    rw [Q.orbitPoints_eq_orbit i]
    refine MulAction.mem_orbit_iff.2 ⟨⟨s * tx, (Q.levelSubgroup i.val).mul_mem hsH htxH⟩, ?_⟩
    change (s * tx) (Q.base.get i) = s x
    rw [Equiv.Perm.mul_apply, htxb]
  obtain ⟨ty, hty, htyH, -, htyb⟩ := Q.orbitPoint_transversal i (s x) hx
  refine ⟨ty, hty, (schreierSiftSucceeds_eq_true_iff _ _).2 ?_⟩
  refine siftResidual_one_of_chain (level_stab_le_of_card hc) hT (i.val + 1) i.isLt _ ?_
  apply level_stab_le_of_card hc i
  refine ⟨(Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).mul_mem
    ((Q.levelSubgroup i.val).inv_mem htyH) hsH) htxH, ?_⟩
  apply MulAction.mem_stabilizer_iff.2
  change ty⁻¹ (s (tx (Q.base.get i))) = Q.base.get i
  rw [htxb, ← htyb]
  simp

end CFSG.Certificates.RawSchreierDatum

end
