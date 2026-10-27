module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvGa
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.QzBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

variable {G : Type} [Group G]

private theorem t3_orderOf_eq_of_isConj {b c : G} (h : IsConj b c) : orderOf b = orderOf c := by
  obtain ⟨k, hk⟩ := isConj_iff.mp h
  rw [← hk]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj k) b).symm

private theorem t3_pow_two_eq_one_of_isConj {b c : G} (hord : orderOf b = 2)
    (hc : IsConj b c) : c ^ 2 = 1 := by
  have hc2 : orderOf c = 2 := (t3_orderOf_eq_of_isConj hc).symm.trans hord
  rw [← hc2]
  exact pow_orderOf_eq_one c

private theorem t3_ncard_sdiff_pair {α : Type} {S : Set α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (h2 : 2 ≤ S.ncard) :
    (S \ {x, y}).ncard = S.ncard - 2 := by
  have hset : S \ ({x, y} : Set α) = (S \ {x}) \ {y} := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hy' : y ∈ S \ {x} := ⟨hy, by simpa [Set.mem_singleton_iff, eq_comm] using hxy⟩
  rw [hset, Set.ncard_sdiff_singleton_of_mem hy', Set.ncard_sdiff_singleton_of_mem hx]
  omega

private theorem t3_conj_fix {x k : G} (hk : x * k = k * x) : k * x * k⁻¹ = x := by
  have h := congrArg (fun t => t * k⁻¹) hk
  simpa [mul_assoc] using h.symm

theorem tableIII_card_base (hI : TwoHSInterface) [Finite G] {a z a' : G} (h : IsF5Type a z)
    (hOrb : GzOrbitFacts a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') :
    Nat.card ↥(tab3Base a z a') = 118 := by
  classical
  obtain ⟨ha'2, ha'1, ha'z, ha'comm, hz2, hz1, hazQ, hazA⟩ := tableIII_basic hI h ha'Q ha'
  set S : Set G := {q : G | q ∈ Qz z ∧ IsConj a q} with hSdef
  have ha'S : a' ∈ S := ⟨ha'Q, ha'⟩
  have hazS : a' * z ∈ S := ⟨hazQ, hazA⟩
  have hstab : Nat.card ↥(Gx z ⊓ Gx a') = 2 ^ 11 * 15 :=
    hOrb.orbit_QA.2 a' ⟨ha'Q, ha'⟩
  have hS : S.ncard = 120 := by
    have hmul := IsConjOrbit.card_mul_card_stab (K := Gx z) hOrb.orbit_QA.1 (c := a')
      ⟨ha'Q, ha'⟩
    rw [Nat.card_coe_set_eq, hstab, card_centralizer_z_of_isF5Type h] at hmul
    have h120 : (120 : ℕ) * (2 ^ 11 * 15) = 2 ^ 9 * 7200 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) (hmul.trans h120.symm)
  have hne : a' ≠ a' * z := by
    intro hcon
    apply hz1
    have hEq : a' * 1 = a' * z := by
      rw [mul_one]
      exact hcon
    exact (mul_left_cancel hEq).symm
  have hbase : tab3Base a z a' = S \ ({a', a' * z} : Set G) := by
    ext c
    rw [hSdef]
    simp only [tab3Base, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, ne_eq, not_or]
    tauto
  have hpair : (S \ ({a', a' * z} : Set G)).ncard = S.ncard - 2 :=
    t3_ncard_sdiff_pair ha'S hazS hne (by rw [hS]; norm_num)
  rw [Nat.card_coe_set_eq, hbase, hpair, hS]

theorem tableIII_subset {a z a' : G} (i : Fin 3) : tab3Set a z a' i ⊆ tab3Base a z a' := by
  intro c hc
  fin_cases i <;>
    simp only [tab3Set, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Set.mem_setOf_eq] at hc <;>
    exact hc.1

theorem tableIII_cover {a z a' : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') :
    ∀ c ∈ tab3Base a z a', ∃ i, c ∈ tab3Set a z a' i := by
  intro c hc
  simp only [tab3Base, Set.mem_setOf_eq] at hc
  obtain ⟨hcQ, hcA, hca', hcaz⟩ := hc
  have ha'2 : a' ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_a ha'
  have hc2 : c ^ 2 = 1 := t3_pow_two_eq_one_of_isConj h.orderOf_a hcA
  have hinvA : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha'2)
  have hinvC : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc2)
  have hcomm_mem : ⁅a', c⁆ ∈ Subgroup.zpowers z :=
    commutatorElement_mem_zpowers_of_mem_Qz h ha'Q hcQ
  rcases (tableIII_mem_zpowers_iff h).mp hcomm_mem with hcomm1 | hcommz
  · have hcommute : a' * c = c * a' := commutatorElement_eq_one_iff_mul_comm.mp hcomm1
    have ht2 : (a' * c) ^ 2 = 1 := by
      rw [pow_two]
      calc a' * c * (a' * c) = a' * (c * a') * c := by group
        _ = a' * (a' * c) * c := by rw [hcommute]
        _ = (a' * a') * (c * c) := by group
        _ = 1 := by rw [← pow_two, ha'2, ← pow_two, hc2, mul_one]
    have ht1 : a' * c ≠ 1 := by
      intro h1
      apply hca'
      calc c = a'⁻¹ := eq_inv_of_mul_eq_one_right h1
        _ = a' := hinvA
    have hty : (a' * c) * a' = a' * (a' * c) := by
      rw [mul_assoc, ← hcommute]
    rcases isConj_of_commute hF1 hF2 ha' hty ht2 ht1 with h0 | h1
    · refine ⟨0, ?_⟩
      simp only [tab3Set, Matrix.cons_val_zero, Set.mem_setOf_eq]
      exact ⟨⟨hcQ, hcA, hca', hcaz⟩, h0⟩
    · refine ⟨1, ?_⟩
      simp only [tab3Set, Matrix.cons_val_one, Matrix.head_cons, Set.mem_setOf_eq]
      exact ⟨⟨hcQ, hcA, hca', hcaz⟩, h1⟩
  · have hsq : (a' * c) ^ 2 = z := by
      rw [pow_two]
      calc a' * c * (a' * c) = a' * c * a' * c := by group
        _ = a' * c * a'⁻¹ * c⁻¹ := by rw [hinvA, hinvC]
        _ = ⁅a', c⁆ := by rw [commutatorElement_def]
        _ = z := hcommz
    refine ⟨2, ?_⟩
    simp only [tab3Set, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Set.mem_setOf_eq]
    exact ⟨⟨hcQ, hcA, hca', hcaz⟩, hsq⟩

theorem tableIII_disjoint (hI : TwoHSInterface) {a z a' : G} (h : IsF5Type a z) (i j : Fin 3)
    (hij : i ≠ j) : Disjoint (tab3Set a z a' i) (tab3Set a z a' j) := by
  have hz1 : z ≠ 1 := by
    intro hz
    have := h.orderOf_z
    rw [hz, orderOf_one] at this
    omega
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hAc : ∀ t : G, IsConj a t → t ^ 2 = 1 := fun t ht =>
    t3_pow_two_eq_one_of_isConj h.orderOf_a ht
  have hBc : ∀ t : G, IsConj z t → t ^ 2 = 1 := fun t ht =>
    t3_pow_two_eq_one_of_isConj h.orderOf_z ht
  rw [Set.disjoint_left]
  intro c hi hj
  fin_cases i <;> fin_cases j <;>
    simp only [tab3Set, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Set.mem_setOf_eq] at hi hj
  · exact absurd rfl hij
  · exact hnot (hi.2.trans hj.2.symm)
  · have h2 := hAc _ hi.2
    rw [hj.2] at h2
    exact hz1 h2
  · exact hnot (hj.2.trans hi.2.symm)
  · exact absurd rfl hij
  · have h2 := hBc _ hi.2
    rw [hj.2] at h2
    exact hz1 h2
  · have h2 := hAc _ hj.2
    rw [hi.2] at h2
    exact hz1 h2
  · have h2 := hBc _ hj.2
    rw [hi.2] at h2
    exact hz1 h2
  · exact absurd rfl hij

theorem tableIII_conj_mem {a z a' : G} (i : Fin 3) {k : G} (hk : k ∈ Gxy a' z) {c : G}
    (hc : c ∈ tab3Set a z a' i) : k * c * k⁻¹ ∈ tab3Set a z a' i := by
  have hka : a' * k = k * a' := mem_Gx.mp (mem_Gxy.mp hk).1
  have hkz : z * k = k * z := mem_Gx.mp (mem_Gxy.mp hk).2
  have hfixA : k * a' * k⁻¹ = a' := t3_conj_fix hka
  have hfixZ : k * z * k⁻¹ = z := t3_conj_fix hkz
  have hka' : k⁻¹ * a' * k = a' := by
    have := congrArg (fun t => k⁻¹ * t) hka
    simpa [mul_assoc] using this
  have hkz' : k⁻¹ * z * k = z := by
    have := congrArg (fun t => k⁻¹ * t) hkz
    simpa [mul_assoc] using this
  have hc' : c ∈ tab3Base a z a' := tableIII_subset i hc
  simp only [tab3Base, Set.mem_setOf_eq] at hc'
  obtain ⟨hcQ, hcA, hca', hcaz⟩ := hc'
  have hbase : k * c * k⁻¹ ∈ tab3Base a z a' := by
    simp only [tab3Base, Set.mem_setOf_eq]
    refine ⟨tableIII_conj_mem_Qz (mem_Gxy.mp hk).2 hcQ, ?_, ?_, ?_⟩
    · exact hcA.trans (isConj_iff.2 ⟨k, rfl⟩)
    · intro h
      apply hca'
      calc c = k⁻¹ * (k * c * k⁻¹) * k := by group
        _ = k⁻¹ * a' * k := by rw [h]
        _ = a' := hka'
    · intro h
      apply hcaz
      calc c = k⁻¹ * (k * c * k⁻¹) * k := by group
        _ = k⁻¹ * (a' * z) * k := by rw [h]
        _ = a' * z := by
          rw [show k⁻¹ * (a' * z) * k = (k⁻¹ * a' * k) * (k⁻¹ * z * k) by group,
            hka', hkz']
  have heqA : a' * (k * c * k⁻¹) = k * (a' * c) * k⁻¹ := mul_conj_of_fix hfixA
  have hrowA : ∀ t : G, IsConj a t → IsConj a (k * t * k⁻¹) := fun t ht =>
    ht.trans (isConj_iff.2 ⟨k, rfl⟩)
  have hrowB : ∀ t : G, IsConj z t → IsConj z (k * t * k⁻¹) := fun t ht =>
    ht.trans (isConj_iff.2 ⟨k, rfl⟩)
  fin_cases i <;>
    simp only [tab3Set, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Set.mem_setOf_eq] at hc
  · exact ⟨hbase, by rw [heqA]; exact hrowA _ hc.2⟩
  · exact ⟨hbase, by rw [heqA]; exact hrowB _ hc.2⟩
  · exact ⟨hbase, by
      rw [heqA]
      have hpow : (k * (a' * c) * k⁻¹) ^ 2 = k * (a' * c) ^ 2 * k⁻¹ := by
        simpa [MulAut.conj_apply] using (map_pow (MulAut.conj k) (a' * c) 2).symm
      rw [hpow, hc.2, hfixZ]⟩

theorem tableIII_set0_eq (hI : TwoHSInterface) {a z a' : G} (h : IsF5Type a z)
    (hX : XStruct a z a') (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') :
    tab3Set a z a' 0 = orb2A a a' ∩ orb2A a (a' * z) := by
  have hnot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have ha1 : a ≠ 1 := by
    intro ha
    have := h.orderOf_a
    rw [ha, orderOf_one] at this
    omega
  have hazA : IsConj a (a' * z) := (tableIII_basic hI h ha'Q ha').2.2.2.2.2.2.2
  have haz2 : (a' * z) ^ 2 = 1 :=
    t3_pow_two_eq_one_of_isConj h.orderOf_a hazA
  have ha'2 : a' ^ 2 = 1 := (tableIII_basic hI h ha'Q ha').1
  ext c
  constructor
  · intro hc
    simp only [tab3Set, Matrix.cons_val_zero, Set.mem_setOf_eq] at hc
    obtain ⟨hcBase, hrow⟩ := hc
    simp only [tab3Base, Set.mem_setOf_eq] at hcBase
    obtain ⟨hcQ, hcA, hca', hcaz⟩ := hcBase
    have hsQ : a' * c ∈ Qz z := (Qz z).mul_mem ha'Q hcQ
    have hsz : a' * c ≠ z := by
      intro hsz
      exact hnot (hrow.trans (isConj_iff.2 ⟨1, by simp [hsz]⟩))
    have hcz : c * z = z * c := by
      have hcGz : c ∈ Gx z := tableIII_Qz_le z hcQ
      exact (mem_Gx.mp hcGz).symm
    have hord_s : orderOf (a' * c) = 2 :=
      (t3_orderOf_eq_of_isConj hrow).symm.trans h.orderOf_a
    have hsmul : IsConj (a' * c) ((a' * c) * z) :=
      isConj_mul_of_mem_Qz h.cent_z h.orderOf_z hord_s hsz hsQ
    have heq : (a' * z) * c = (a' * c) * z := by
      rw [mul_assoc, ← hcz, ← mul_assoc]
    simp only [orb2A, Set.mem_setOf_eq, Set.mem_inter_iff]
    exact ⟨⟨hcA, hrow⟩, ⟨hcA, by rw [heq]; exact hrow.trans hsmul⟩⟩
  · intro hc
    simp only [orb2A, Set.mem_setOf_eq, Set.mem_inter_iff] at hc
    obtain ⟨⟨hcA, hrow⟩, ⟨-, hrow2⟩⟩ := hc
    have hcQ : c ∈ Qz z := hX.o1_mem c ⟨⟨hcA, hrow⟩, ⟨hcA, hrow2⟩⟩
    have hca' : c ≠ a' := by
      intro h
      have h1 : a' * c = 1 := by rw [h, ← pow_two, ha'2]
      exact ha1 (isConj_one_left.mp (by rwa [h1] at hrow))
    have hcaz : c ≠ a' * z := by
      intro h
      have h1 : (a' * z) * c = 1 := by rw [h, ← pow_two, haz2]
      exact ha1 (isConj_one_left.mp (by rwa [h1] at hrow2))
    simp only [tab3Set, Matrix.cons_val_zero, Set.mem_setOf_eq, tab3Base,
      Set.mem_setOf_eq]
    exact ⟨⟨hcQ, hcA, hca', hcaz⟩, hrow⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
