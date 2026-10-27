module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p b' : G}

theorem lines_pair (h : IsF5Type a z) (hp : IsConj a p) (hb : b' ∈ orb2A p p) :
    p ^ 2 = 1 ∧ b' ^ 2 = 1 ∧ p * b' = b' * p ∧ p ≠ 1 ∧ b' ≠ 1 ∧ p ≠ b' := by
  have hpord : orderOf p = 2 := perp_orderOf_of_isConj_a h hp
  have hbord : orderOf b' = 2 := perp_orderOf_of_isConj_a h (hp.trans hb.1)
  have hpbord : orderOf (p * b') = 2 := perp_orderOf_of_isConj_a h (hp.trans hb.2)
  have hp2 : p ^ 2 = 1 := by rw [← hpord]; exact pow_orderOf_eq_one p
  have hb2 : b' ^ 2 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b'
  have hpb2 : (p * b') ^ 2 = 1 := by rw [← hpbord]; exact pow_orderOf_eq_one (p * b')
  refine ⟨hp2, hb2, comm_of_sq_mul hp2 hb2 hpb2, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hpord
    exact absurd hpord (by decide)
  · intro h1
    rw [h1, orderOf_one] at hbord
    exact absurd hbord (by decide)
  · intro h1
    have h11 : p * b' = 1 := by rw [← h1, ← pow_two, hp2]
    rw [h11, orderOf_one] at hpbord
    exact absurd hpbord (by decide)

theorem lines_decomp (h : IsF5Type a z) (hp : IsConj a p) (hb : b' ∈ orb2A p p)
    (hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b')) {t : G} (ht : t ∈ Gxy p b') (ht2 : t ^ 2 = 1) :
    ∃ s ∈ derivedOf (Gxy p b'), s ^ 2 = 1 ∧
      (t = s ∨ t = p * s ∨ t = b' * s ∨ t = p * b' * s) := by
  obtain ⟨hp2, hb2, hcomm, hp1, hb1, hne⟩ := lines_pair h hp hb
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
  have hus : (u * s) ^ 2 = 1 := by rw [← ht_eq]; exact ht2
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

theorem lines_fig (hp : IsConj a p) (hb : b' ∈ orb2A p p) (hPic : A8Pictures p z)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy p b'))) {s : G}
    (hs : s ∈ derivedOf (Gxy p b')) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    ((φ.symm ⟨s, hs⟩ : Equiv.Perm (Fin 8)).cycleType = {2, 2} ∧
      IsConj a s ∧ IsConj z (p * s) ∧ IsConj z (b' * s) ∧ IsConj z (p * b' * s)) ∨
    ((φ.symm ⟨s, hs⟩ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} ∧
      IsConj z s ∧ IsConj a (p * s) ∧ IsConj a (b' * s) ∧ IsConj a (p * b' * s)) := by
  have hφs : (φ (φ.symm ⟨s, hs⟩) : G) = s := by rw [MulEquiv.apply_symm_apply]
  have hs'2 : φ.symm ⟨s, hs⟩ ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    change ((φ (φ.symm ⟨s, hs⟩) : ↥(derivedOf (Gxy p b'))) : G) ^ 2 = 1
    rw [hφs, hs2]
  have hs'1 : φ.symm ⟨s, hs⟩ ≠ 1 := by
    intro h1
    apply hs1
    rw [← hφs, h1, map_one, OneMemClass.coe_one]
  rcases cycleType_eq_of_sq_eq_one hs'2 hs'1 with h22 | h24
  · left
    have h := hPic.fig8a b' hb φ _ h22
    rw [hφs] at h
    exact ⟨h22, hp.trans h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  · right
    have h := hPic.fig8b b' hb φ _ h24
    rw [hφs] at h
    exact ⟨h24, h.1, hp.trans h.2.1, hp.trans h.2.2.1, hp.trans h.2.2.2⟩

private theorem lines_not_isConj_z_one (h : IsF5Type a z) : ¬ IsConj z 1 := by
  intro hz
  have hzo := h.orderOf_z
  rw [isConj_one_left.mp hz, orderOf_one] at hzo
  exact absurd hzo (by decide)

theorem lines_cycleType_of_isConj_z (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hp : IsConj a p)
    (hb : b' ∈ orb2A p p) (hPic : A8Pictures p z)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy p b'))) {s : G}
    (hs : s ∈ derivedOf (Gxy p b')) (hs2 : s ^ 2 = 1) (hsB : IsConj z s) :
    (φ.symm ⟨s, hs⟩ : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  have hs1 : s ≠ 1 := by
    intro h1
    exact lines_not_isConj_z_one h (h1 ▸ hsB)
  rcases lines_fig hp hb hPic φ hs hs2 hs1 with hA | hB
  · exact absurd (hA.2.1.trans hsB.symm) hnc
  · exact hB.1

private theorem lines_not_mem_aux (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hp : IsConj a p)
    (hb : b' ∈ orb2A p p) (hPic : A8Pictures p z)
    (φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gxy p b'))) {u : G} (huA : IsConj a u)
    (hone : p * u = 1 ∨ b' * u = 1 ∨ p * b' * u = 1) : u ∉ derivedOf (Gxy p b') := by
  intro hu
  have huo : orderOf u = 2 := perp_orderOf_of_isConj_a h huA
  have hu2 : u ^ 2 = 1 := by rw [← huo]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    exact absurd huo (by decide)
  rcases lines_fig hp hb hPic φ hu hu2 hu1 with hA | hB
  · rcases hone with h1 | h1 | h1
    · exact lines_not_isConj_z_one h (by rw [← h1]; exact hA.2.2.1)
    · exact lines_not_isConj_z_one h (by rw [← h1]; exact hA.2.2.2.1)
    · exact lines_not_isConj_z_one h (by rw [← h1]; exact hA.2.2.2.2)
  · exact hnc (huA.trans hB.2.1.symm)

theorem lines_not_mem_derived (h : IsF5Type a z) (hnc : ¬ IsConj a z) (hp : IsConj a p)
    (hb : b' ∈ orb2A p p) (hX : IsShapeTwoTwoTimesA8 ↥(Gxy p b')) (hPic : A8Pictures p z) :
    p ∉ derivedOf (Gxy p b') ∧ b' ∉ derivedOf (Gxy p b') ∧ p * b' ∉ derivedOf (Gxy p b') := by
  obtain ⟨hp2, hb2, -, -, -, -⟩ := lines_pair h hp hb
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hX
  have hpbA : IsConj a (p * b') := hp.trans hb.2
  have hpb2 : (p * b') ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hpbA]; exact pow_orderOf_eq_one _
  exact ⟨lines_not_mem_aux h hnc hp hb hPic φ hp (Or.inl ((pow_two p).symm.trans hp2)),
    lines_not_mem_aux h hnc hp hb hPic φ (hp.trans hb.1)
      (Or.inr (Or.inl ((pow_two b').symm.trans hb2))),
    lines_not_mem_aux h hnc hp hb hPic φ hpbA
      (Or.inr (Or.inr ((pow_two (p * b')).symm.trans hpb2)))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
