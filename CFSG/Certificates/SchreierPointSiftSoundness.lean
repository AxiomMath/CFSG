module

public import CFSG.Certificates.SchreierChainOrder
public import CFSG.Certificates.SchreierPointSift
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Certificates.RawSchreierDatum

variable {n : ℕ} (Q : RawSchreierDatum n)

theorem strong_get_mem_originalSubgroup_of_point (hQ : ValidPointSchreier Q)
    (j : Fin Q.strongCount) : Q.strong.get j ∈ Q.originalSubgroup := by
  have hvalid := (validPointSchreier_iff Q).1 hQ
  have all : ∀ a : ℕ, ∀ j : Fin Q.strongCount,
      j.val = a → Q.strong.get j ∈ Q.originalSubgroup := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja
      by_cases hj : j.val < Q.originalCount
      · let l : Fin Q.originalCount := ⟨j.val, hj⟩
        have hcast : Fin.castLE Q.originalCount_le l = j := Fin.ext rfl
        rw [← hcast, hvalid.1 l]
        exact Subgroup.subset_closure (schreier_vector_get_mem_toList Q.original l)
      · rw [hvalid.2.1 j (Nat.le_of_not_gt hj)]
        apply schreierWordValue_mem_subgroup Q.strong.get
          (Nat.le_of_lt j.isLt) (Q.derivation j (Nat.le_of_not_gt hj)) Q.originalSubgroup
        intro l
        exact ih l.val (by omega) ⟨l.val, l.isLt.trans j.isLt⟩ rfl
  exact all j.val j rfl

theorem strong_mem_originalSubgroup_of_point (hQ : ValidPointSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.strong.toList) : g ∈ Q.originalSubgroup := by
  obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get Q.strong g).1 hg
  exact Q.strong_get_mem_originalSubgroup_of_point hQ j

theorem levelSubgroup_le_originalSubgroup_of_point (hQ : ValidPointSchreier Q) (i : ℕ) :
    Q.levelSubgroup i ≤ Q.originalSubgroup :=
  (Subgroup.closure_le _).2 fun _ hs =>
    Q.strong_mem_originalSubgroup_of_point hQ ((Q.mem_levelGenerators_iff i _).1 hs).1

theorem mem_base_take_succ {i : Fin Q.baseCount} {b : Fin n} :
    b ∈ Q.base.toList.take (i.val + 1) ↔ b ∈ Q.base.toList.take i.val ∨ b = Q.base.get i := by
  rw [Q.base_take_succ i, List.mem_append, List.mem_singleton]

theorem base_take_baseCount : Q.base.toList.take Q.baseCount = Q.base.toList :=
  List.take_of_length_le (by simp)

theorem siftResidual_eq_one_of_pointSift (hQ : ValidPointSchreier Q)
    (hstab : Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥)
    (i : ℕ) (hi : i ≤ Q.baseCount) (h : Equiv.Perm (Fin n)) (hP : h ∈ Q.originalSubgroup)
    (hfix : ∀ b ∈ Q.base.toList.take i, h b = b) (r : Equiv.Perm (Fin n))
    (hr : schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some r) : r = 1 := by
  have go : ∀ d i, i + d = Q.baseCount → ∀ h : Equiv.Perm (Fin n), h ∈ Q.originalSubgroup →
      (∀ b ∈ Q.base.toList.take i, h b = b) →
      schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some r → r = 1 := by
    intro d
    induction d with
    | zero =>
      intro i hi h hP hfix hr
      have hi' : i = Q.baseCount := by omega
      subst i
      have hdrop : (List.finRange Q.baseCount).drop Q.baseCount = [] :=
        List.drop_eq_nil_iff.2 (by simp)
      simp only [siftLevels, hdrop, List.map_nil, schreierSiftResidual,
        Option.some.injEq] at hr
      subst hr
      have hmem : h ∈ Q.originalSubgroup ⊓
          fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} := by
        refine Subgroup.mem_inf.2 ⟨hP,
          (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).2 fun b hb => ?_⟩
        rw [Equiv.Perm.smul_def]
        exact hfix b (Q.base_take_baseCount.symm ▸ hb)
      rw [hstab] at hmem
      exact Subgroup.mem_bot.1 hmem
    | succ d ih =>
      intro i hi h hP hfix hr
      let j : Fin Q.baseCount := ⟨i, by omega⟩
      rw [Q.siftLevels_cons Q.orbitTables j] at hr
      cases ht : (Q.orbitTables.get j).transversal? (h (Q.base.get j)) with
      | none =>
        rw [schreierSiftResidual_unavailable _ _ _ _ ht] at hr
        exact absurd hr (by simp)
      | some t =>
        rw [schreierSiftResidual_available _ _ _ _ _ ht] at hr
        have ht' : Q.transversal? j (h (Q.base.get j)) = some t := by
          simpa only [orbitTables_get, transversal?] using ht
        obtain ⟨htL, htfix, htb⟩ := Q.transversal_sound j _ t ht'
        refine ih (i + 1) (by omega) (t⁻¹ * h) (mul_mem (inv_mem
          (Q.levelSubgroup_le_originalSubgroup_of_point hQ i htL)) hP) (fun b hb => ?_) hr
        rcases (Q.mem_base_take_succ (i := j)).1 hb with hb | hb
        · rw [Equiv.Perm.mul_apply, hfix b hb, Equiv.Perm.inv_eq_iff_eq, htfix b hb]
        · rw [hb, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, htb]
  exact go (Q.baseCount - i) i (by omega) h hP hfix hr

theorem sift_eq_true_of_pointSift (hQ : ValidPointSchreier Q)
    (hstab : Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥)
    (i : ℕ) (hi : i ≤ Q.baseCount) {h : Equiv.Perm (Fin n)} (hP : h ∈ Q.originalSubgroup)
    (hfix : ∀ b ∈ Q.base.toList.take i, h b = b)
    (hpt : schreierPointSiftSucceeds (Q.siftLevels Q.orbitTables i) h = true) :
    schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 := by
  obtain ⟨r, hr⟩ := (schreierPointSiftSucceeds_eq_true_iff _ h).1 hpt
  rw [hr, Q.siftResidual_eq_one_of_pointSift hQ hstab i hi h hP hfix r hr]

theorem validSchreier_of_point (hQ : ValidPointSchreier Q)
    (hstab : Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥) :
    ValidSchreier Q := by
  obtain ⟨h1, h2, h3⟩ := (validPointSchreier_iff Q).1 hQ
  refine (validSchreier_iff Q).2 ⟨h1, h2, fun s hs => ?_, fun i x tx hx s hs => ?_⟩
  ·
    obtain ⟨hstrong, hfix⟩ := (Q.mem_levelGenerators_iff Q.baseCount s).1 hs
    have hmem : s ∈ Q.originalSubgroup ⊓
        fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} := by
      refine Subgroup.mem_inf.2 ⟨Q.strong_mem_originalSubgroup_of_point hQ hstrong,
        (mem_fixingSubgroup_iff (Equiv.Perm (Fin n))).2 fun b hb => ?_⟩
      rw [Equiv.Perm.smul_def]
      exact hfix b (Q.base_take_baseCount.symm ▸ hb)
    rw [hstab] at hmem
    exact Subgroup.mem_bot.1 hmem
  ·
    obtain ⟨ty, hty, hpt⟩ := h3 i x tx hx s hs
    refine ⟨ty, hty, (schreierSiftSucceeds_eq_true_iff _ _).2 ?_⟩
    have htx := Q.transversal_sound i x tx hx
    have hty' := Q.transversal_sound i (s x) ty hty
    have hsL : s ∈ Q.levelSubgroup i.val ∧ ∀ b ∈ Q.base.toList.take i.val, s b = b := by
      rcases List.mem_append.1 hs with hs | hs
      · exact ⟨Subgroup.subset_closure hs, ((Q.mem_levelGenerators_iff i.val s).1 hs).2⟩
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
        refine ⟨inv_mem (Subgroup.subset_closure hg), fun b hb => ?_⟩
        rw [Equiv.Perm.inv_eq_iff_eq, ((Q.mem_levelGenerators_iff i.val g).1 hg).2 b hb]
    have hP : ty⁻¹ * s * tx ∈ Q.originalSubgroup :=
      mul_mem (mul_mem (inv_mem (Q.levelSubgroup_le_originalSubgroup_of_point hQ _ hty'.1))
        (Q.levelSubgroup_le_originalSubgroup_of_point hQ _ hsL.1))
        (Q.levelSubgroup_le_originalSubgroup_of_point hQ _ htx.1)
    refine Q.sift_eq_true_of_pointSift hQ hstab (i.val + 1) i.isLt hP (fun b hb => ?_) hpt
    rcases (Q.mem_base_take_succ (i := i)).1 hb with hb | hb
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htx.2.1 b hb, hsL.2 b hb,
        Equiv.Perm.inv_eq_iff_eq, hty'.2.1 b hb]
    · rw [hb, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htx.2.2, Equiv.Perm.inv_eq_iff_eq,
        hty'.2.2]

theorem certified_base_point_sift_soundness (hQ : ValidPointSchreier Q)
    (hstab : Q.originalSubgroup ⊓
      fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList} = ⊥) :
    ValidSchreier Q ∧
      (∀ i ≤ Q.baseCount, Q.levelSubgroup i = Q.originalSubgroup ⊓
        fixingSubgroup (Equiv.Perm (Fin n)) {b | b ∈ Q.base.toList.take i}) ∧
      Nat.card Q.originalSubgroup = ∏ i : Fin Q.baseCount, Nat.card (Q.orbitPoints i) ∧
      ∀ i ≤ Q.baseCount, ∀ h ∈ Q.originalSubgroup, (∀ b ∈ Q.base.toList.take i, h b = b) →
        Q.pointSift h i = true →
          schreierSiftResidual (Q.siftLevels Q.orbitTables i) h = some 1 ∧ Q.sift h i = true := by
  have hV := Q.validSchreier_of_point hQ hstab
  obtain ⟨hlevels, -, hcard, -⟩ := Q.schreier_chain_order hV
  refine ⟨hV, hlevels, hcard, fun i hi h hP hfix hpt => ?_⟩
  have hres := Q.sift_eq_true_of_pointSift hQ hstab i hi hP hfix hpt
  exact ⟨hres, (schreierSiftSucceeds_eq_true_iff _ _).2 hres⟩

end CFSG.Certificates.RawSchreierDatum
