module

public import CFSG.Certificates.SchreierChainOrderMembership

public section

namespace CFSG.KS.PK

open CFSG.Certificates

private theorem rt_base_get {n : ℕ} {Q Q' : RawSchreierDatum n}
    (hbase : Q.base.toList = Q'.base.toList) (i : Fin Q.baseCount) (i' : Fin Q'.baseCount)
    (h : i.val = i'.val) : Q.base.get i = Q'.base.get i' := by
  have h1 : Q.base.toList[i.val]'(by simp) = Q'.base.toList[i'.val]'(by simp) := by
    have := List.getElem_of_eq hbase (i := i.val) (by simp)
    rw [this]
    simp [h]
  simpa [Vector.getElem_toList, Vector.get] using h1

private theorem rt_strip_mem_next_level {n : ℕ} (Q : RawSchreierDatum n)
    (hstab : ∀ i : Fin Q.baseCount, Q.levelSubgroup (i.val + 1) =
      Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i))
    (i : Fin Q.baseCount) (h : Equiv.Perm (Fin n)) (hh : h ∈ Q.levelSubgroup i.val) :
    ∃ t, Q.transversal? i (h (Q.base.get i)) = some t ∧
      t⁻¹ * h ∈ Q.levelSubgroup (i.val + 1) := by
  have hx : h (Q.base.get i) ∈ Q.orbitPoints i := by
    rw [Q.orbitPoints_eq_orbit i]
    exact MulAction.mem_orbit_iff.2 ⟨⟨h, hh⟩, rfl⟩
  obtain ⟨t, ht, htH, _, htb⟩ := Q.orbitPoint_transversal i (h (Q.base.get i)) hx
  refine ⟨t, ht, ?_⟩
  rw [hstab i]
  refine ⟨(Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).inv_mem htH) hh, ?_⟩
  apply MulAction.mem_stabilizer_iff.2
  change t⁻¹ (h (Q.base.get i)) = Q.base.get i
  rw [← htb]
  simp

private theorem rt_siftResidual_eq_one {n : ℕ} (Q : RawSchreierDatum n)
    (hstab : ∀ i : Fin Q.baseCount, Q.levelSubgroup (i.val + 1) =
      Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i))
    (hterm : Q.levelSubgroup Q.baseCount = ⊥) (i : ℕ) (hi : i ≤ Q.baseCount)
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
      rw [hterm] at hh
      have hh' : h = 1 := Subgroup.mem_bot.1 hh
      subst h
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [RawSchreierDatum.siftLevels, hdrop, List.map_nil, schreierSiftResidual]
    | succ d ih =>
      intro i hi h hh
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      obtain ⟨t, ht, hnext⟩ := rt_strip_mem_next_level Q hstab j h hh
      rw [Q.siftResidual_strip j h t ht]
      exact ih (i + 1) (by omega) (t⁻¹ * h) hnext
  exact go (Q.baseCount - i) i (by omega) h hh

theorem check_of_levelSubgroup_eq {n : Nat} {Q Q' : RawSchreierDatum n} (hQ' : Q'.check = true)
    (hk : Q.baseCount = Q'.baseCount) (hbase : Q.base.toList = Q'.base.toList)
    (hH : ∀ i, Q.levelSubgroup i = Q'.levelSubgroup i)
    (hinit : ∀ j : Fin Q.originalCount,
      Q.strong.get (Fin.castLE Q.originalCount_le j) = Q.original.get j)
    (hwords : ∀ (j : Fin Q.strongCount) (hj : Q.originalCount ≤ j.val),
      Q.strong.get j = Q.derivationValue j hj) :
    Q.check = true := by
  have hstab : ∀ i : Fin Q.baseCount, Q.levelSubgroup (i.val + 1) =
      Q.levelSubgroup i.val ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (Q.base.get i) := by
    intro i
    have h' := Q'.levelSubgroup_succ_eq_stabilizer hQ' ⟨i.val, by have := i.isLt; omega⟩
    rw [hH, hH, rt_base_get hbase i ⟨i.val, by have := i.isLt; omega⟩ rfl]
    exact h'
  have hterm : Q.levelSubgroup Q.baseCount = ⊥ := by
    rw [hH, hk]
    exact Q'.levelSubgroup_terminal_eq_bot hQ'
  rw [RawSchreierDatum.check_eq_true_iff]
  refine ⟨hinit, hwords, ?_, ?_⟩
  · intro s hs
    have hs' : s ∈ Q.levelSubgroup Q.baseCount := Subgroup.subset_closure hs
    rw [hterm] at hs'
    exact Subgroup.mem_bot.1 hs'
  · intro i x tx htx s hs
    rw [RawSchreierDatum.orbitTables_get] at htx ⊢
    have htx' : Q.transversal? i x = some tx := htx
    obtain ⟨htxH, _, htxb⟩ := Q.transversal_sound i x tx htx'
    have hsH : s ∈ Q.levelSubgroup i.val :=
      SchreierOrbitState.signed_steps_mem_closure _ s hs
    have hy : s x ∈ Q.orbitPoints i := by
      rw [Q.orbitPoints_eq_orbit i]
      exact MulAction.mem_orbit_iff.2
        ⟨⟨s * tx, (Q.levelSubgroup i.val).mul_mem hsH htxH⟩, by simp [← htxb]⟩
    obtain ⟨ty, hty, htyH, _, htyb⟩ := Q.orbitPoint_transversal i (s x) hy
    refine ⟨ty, hty, ?_⟩
    rw [schreierSiftSucceeds_eq_true_iff]
    apply rt_siftResidual_eq_one Q hstab hterm (i.val + 1) (by have := i.isLt; omega)
    rw [hstab i]
    refine ⟨?_, ?_⟩
    · exact (Q.levelSubgroup i.val).mul_mem
        ((Q.levelSubgroup i.val).mul_mem ((Q.levelSubgroup i.val).inv_mem htyH) hsH) htxH
    · apply MulAction.mem_stabilizer_iff.2
      change (ty⁻¹ * s * tx) (Q.base.get i) = Q.base.get i
      simp only [Equiv.Perm.mul_apply, htxb, ← htyb]
      simp

end CFSG.KS.PK

end
