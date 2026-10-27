module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p : G}

private theorem fourBFig_aux (H : FourBHyps a z) (hp : IsConj a p) {b' : G}
    (hb : b' ∈ orb2A p p) :
    p ^ 2 = 1 ∧ b' ^ 2 = 1 ∧ p * b' = b' * p ∧ p ≠ 1 ∧ b' ≠ 1 ∧ p ≠ b' := by
  have hpord : orderOf p = 2 := perp_orderOf_of_isConj_a H.h hp
  have hp2 : p ^ 2 = 1 := by rw [← hpord]; exact pow_orderOf_eq_one p
  have hbA : IsConj a b' := (fourB_isConj_iff hp).mp hb.1
  have hbord : orderOf b' = 2 := perp_orderOf_of_isConj_a H.h hbA
  have hb2 : b' ^ 2 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b'
  have hpbA : IsConj a (p * b') := (fourB_isConj_iff hp).mp hb.2
  have hpbord : orderOf (p * b') = 2 := perp_orderOf_of_isConj_a H.h hpbA
  have hpb2 : (p * b') ^ 2 = 1 := by rw [← hpbord]; exact pow_orderOf_eq_one (p * b')
  have hcomm : p * b' = b' * p := fourB_comm_of_orders hpord hbord hpbord
  have hp1 : p ≠ 1 := by
    intro h
    have ha1 : a = 1 := isConj_one_left.mp (h ▸ hp)
    have h2 := H.h.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  have hb1 : b' ≠ 1 := by
    intro h
    have ha1 : a = 1 := isConj_one_left.mp (h ▸ hbA)
    have h2 := H.h.orderOf_a
    rw [ha1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  have hne : p ≠ b' := by
    intro h
    have h1 : p * b' = 1 := by rw [h, ← pow_two, hb2]
    have h2 := hpbord
    rw [h1, orderOf_one] at h2
    exact (by decide : (1 : ℕ) ≠ 2) h2
  exact ⟨hp2, hb2, hcomm, hp1, hb1, hne⟩

theorem fourB_decomp (H : FourBHyps a z) (hp : IsConj a p) {b' t : G} (hb : b' ∈ orb2A p p)
    (ht : t ∈ Gxy p b') (ht2 : orderOf t = 2) :
    ∃ s ∈ derivedOf (Gxy p b'), s ^ 2 = 1 ∧
      (t = s ∨ t = p * s ∨ t = b' * s ∨ t = p * b' * s) := by
  obtain ⟨hp2, hb2, hcomm, hp1, hb1, hne⟩ := fourBFig_aux H hp hb
  have hF3p : Fusion3Facts p z := H.hF3 p z hp (IsConj.refl z)
  have hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b') := hF3p.shape_2A b' hb
  obtain ⟨u, hu, s, hs, ht_eq⟩ :=
    exists_mul_eq_of_isShapeTwoTwoTimesA8 hX hp2 hb2 hcomm hp1 hb1 hne t ht
  have hsG : s ∈ Gxy p b' := derivedOf_le _ hs
  have hsp : p * s = s * p := mem_Gx.mp (mem_Gxy.mp hsG).1
  have hsb : b' * s = s * b' := mem_Gx.mp (mem_Gxy.mp hsG).2
  have hsu : u * s = s * u := by
    have hle : Subgroup.closure ({p, b'} : Set G) ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsp
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hu)
  have hu2 : u ^ 2 = 1 := by
    rcases eq_of_mem_closure_two hp2 hb2 hcomm hu with h | h | h | h
    · rw [h]; exact one_pow 2
    · rw [h]; exact hp2
    · rw [h]; exact hb2
    · rw [h, pow_two]
      calc (p * b') * (p * b') = p * (b' * p) * b' := by group
        _ = p * (p * b') * b' := by rw [← hcomm]
        _ = (p * p) * (b' * b') := by group
        _ = 1 := by rw [← pow_two, hp2, ← pow_two, hb2, one_mul]
  have ht_sq : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  have hus : (u * s) ^ 2 = 1 := by rw [← ht_eq]; exact ht_sq
  have hcomm_us : (u * s) ^ 2 = u ^ 2 * s ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    calc (u * s) * (u * s) = u * (s * u) * s := by group
      _ = u * (u * s) * s := by rw [← hsu]
      _ = (u * u) * (s * s) := by group
  have hs2 : s ^ 2 = 1 := by
    have h := hus
    rw [hcomm_us, hu2, one_mul] at h
    exact h
  refine ⟨s, hs, hs2, ?_⟩
  rcases eq_of_mem_closure_two hp2 hb2 hcomm hu with h | h | h | h
  · left; rw [ht_eq, h, one_mul]
  · right; left; rw [ht_eq, h]
  · right; right; left; rw [ht_eq, h]
  · right; right; right; rw [ht_eq, h]

theorem fourB_fig (H : FourBHyps a z) (hp : IsConj a p) {b' s : G} (hb : b' ∈ orb2A p p)
    (hs : s ∈ derivedOf (Gxy p b')) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    (IsConj a s ∧ IsConj z (p * s) ∧ IsConj z (b' * s) ∧ IsConj z (p * (b' * s))) ∨
      (IsConj z s ∧ IsConj a (p * s) ∧ IsConj a (b' * s) ∧ IsConj a (p * (b' * s))) := by
  have hF3p : Fusion3Facts p z := H.hF3 p z hp (IsConj.refl z)
  have hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b') := hF3p.shape_2A b' hb
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  let s' : alternatingGroup (Fin 8) := φ.symm ⟨s, hs⟩
  have hφs : (φ s' : G) = s := by
    have h := MulEquiv.apply_symm_apply φ ⟨s, hs⟩
    exact congrArg Subtype.val h
  have hs'2 : s' ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    change ((φ s' : ↥(derivedOf (Gxy p b'))) : G) ^ 2 = 1
    rw [hφs, hs2]
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hs1
    calc s = (φ s' : G) := hφs.symm
      _ = (φ 1 : G) := by rw [h]
      _ = 1 := by rw [map_one]; rfl
  have hPicp : A8Pictures p z := H.hPic p z hp (IsConj.refl z)
  rcases cycleType_eq_of_sq_eq_one hs'2 hs'1 with h22 | h24
  · left
    have h := hPicp.fig8a b' hb φ s' h22
    rw [hφs, mul_assoc] at h
    exact ⟨(fourB_isConj_iff hp).mp h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · right
    have h := hPicp.fig8b b' hb φ s' h24
    rw [hφs, mul_assoc] at h
    exact ⟨h.1, (fourB_isConj_iff hp).mp h.2.1, (fourB_isConj_iff hp).mp h.2.2.1,
      (fourB_isConj_iff hp).mp h.2.2.2⟩

theorem fourB_coset (H : FourBHyps a z) (hp : IsConj a p) {b' t : G} (hb : b' ∈ orb2A p p)
    (ht : t ∈ Gxy p b') (ht2 : orderOf t = 2) (h1 : IsConj z t) (h2 : IsConj a (b' * t)) :
    (IsConj z (p * t) ∧ IsConj z (p * (b' * t))) ∨
      (IsConj a (p * t) ∧ IsConj a (p * (b' * t))) := by
  obtain ⟨hp2, hb2, hcomm, -, hb1, -⟩ := fourBFig_aux H hp hb
  have hbA : IsConj a b' := (fourB_isConj_iff hp).mp hb.1
  have hpbA : IsConj a (p * b') := (fourB_isConj_iff hp).mp hb.2
  obtain ⟨s, hs, hs2, hcases⟩ := fourB_decomp H hp hb ht ht2
  have hsG : s ∈ Gxy p b' := derivedOf_le _ hs
  have hsp : p * s = s * p := mem_Gx.mp (mem_Gxy.mp hsG).1
  have hsb : b' * s = s * b' := mem_Gx.mp (mem_Gxy.mp hsG).2
  have hs1 : s ≠ 1 := by
    intro hs_eq
    have hcases' := hcases
    have ht_cases : t = 1 ∨ t = p ∨ t = b' ∨ t = p * b' := by
      rcases hcases' with h | h | h | h
      · left; rw [h, hs_eq]
      · right; left; rw [h, hs_eq, mul_one]
      · right; right; left; rw [h, hs_eq, mul_one]
      · right; right; right; rw [h, hs_eq, mul_one]
    rcases ht_cases with h | h | h | h
    · have hz1 : z = 1 := isConj_one_left.mp (h ▸ h1)
      have hzo := H.h.orderOf_z
      rw [hz1, orderOf_one] at hzo
      exact (by decide : (1 : ℕ) ≠ 2) hzo
    · exact False.elim (fourB_not_both H hp (h ▸ h1))
    · exact False.elim (fourB_not_both H hbA (h ▸ h1))
    · exact False.elim (fourB_not_both H hpbA (h ▸ h1))
  have hfig := fourB_fig H hp hb hs hs2 hs1
  rcases hfig with hA | hB
  · rcases hcases with h | h | h | h
    · exact False.elim (fourB_not_both H hA.1 (h ▸ h1))
    · have h' : b' * (p * s) = p * (b' * s) := by
        calc b' * (p * s) = (b' * p) * s := (mul_assoc b' p s).symm
          _ = (p * b') * s := by rw [← hcomm]
          _ = p * (b' * s) := mul_assoc p b' s
      have h2' : IsConj a (p * (b' * s)) := by
        rw [← h', ← h]
        exact h2
      exact False.elim (fourB_not_both H h2' hA.2.2.2)
    · left
      refine ⟨?_, ?_⟩
      · rw [h]; exact hA.2.2.2
      · have hbt : b' * t = s := by rw [h, ← mul_assoc, ← pow_two, hb2, one_mul]
        rw [hbt]; exact hA.2.1
    · have hbt : b' * t = p * s := by
        rw [h]
        calc b' * (p * b' * s) = (b' * (p * b')) * s := by group
          _ = (b' * (b' * p)) * s := by rw [hcomm]
          _ = ((b' * b') * p) * s := by group
          _ = p * s := by rw [← pow_two, hb2, one_mul]
      have h2' : IsConj a (p * s) := by
        rw [← hbt]
        exact h2
      exact False.elim (fourB_not_both H h2' hA.2.1)
  · rcases hcases with h | h | h | h
    · right
      refine ⟨?_, ?_⟩
      · rw [h]; exact hB.2.1
      · rw [h]; exact hB.2.2.2
    · exact False.elim (fourB_not_both H hB.2.1 (h ▸ h1))
    · exact False.elim (fourB_not_both H hB.2.2.1 (h ▸ h1))
    · have h1' : IsConj z (p * (b' * s)) := by
        rw [← mul_assoc, ← h]
        exact h1
      exact False.elim (fourB_not_both H hB.2.2.2 h1')

end CFSG.EvenSporadicStandard.HNRecog.Section3
