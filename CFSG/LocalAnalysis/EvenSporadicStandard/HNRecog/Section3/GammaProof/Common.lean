module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem gamma_common_of_orbit {x c b' d : G} (hb' : b' ∈ orb2A a x)
    (hbd : b' ∈ orb2A a d) {S : Set G} (horb : IsConjOrbit (Gx x) S) (hdS : d ∈ S)
    (hcS : c ∈ S) : (orb2A a x ∩ orb2A a c).Nonempty := by
  obtain ⟨k, hk, hkd⟩ := horb.transitive d hdS c hcS
  have hkx : k * x * k⁻¹ = x := by
    rw [← mem_Gx.mp hk]
    group
  refine ⟨k * b' * k⁻¹, ?_, ?_⟩
  · have h := gamma_orb2A_conj k hb'
    rwa [hkx] at h
  · have h := gamma_orb2A_conj k hbd
    rwa [hkd] at h

private theorem gamma_mem_orb2A_of_mem_sBase {x b' d : G} (H : GammaHyps a z)
    (hx : IsConj a x) (hb' : b' ∈ orb2A a x) (hbase : d ∈ sBase x b') : b' ∈ orb2A a d := by
  have hparts : IsConj x d ∧ IsConj x (b' * d) ∧ d ≠ x ∧ d ≠ x * b' := by
    have h := hbase
    simp only [sBase] at h
    exact h
  have hdb : IsConj x (b' * d) := hparts.2.1
  have hbd_A : IsConj a (b' * d) := (gamma_isConj_iff hx (b' * d)).mp hdb
  have hconj : IsConj (b' * d) (d * b') := by
    refine isConj_iff.mpr ⟨b', ?_⟩
    calc b' * (b' * d) * b'⁻¹ = (b' * b') * d * b'⁻¹ := by group
      _ = d * b'⁻¹ := by rw [H.mul_self_a hb'.1, one_mul]
      _ = d * b' := by rw [H.inv_a hb'.1]
  exact ⟨hb'.1, hbd_A.trans hconj⟩

private theorem gamma_row_twoB {x b' d : G} (H : GammaHyps a z) (hx : IsConj a x)
    (hb' : b' ∈ orb2A a x) (hd : d ∈ sSet x z b' 1) : d ∈ orb2B a z x ∧ b' ∈ orb2A a d := by
  have hd' : d ∈ sBase x b' ∧ IsConj z (x * d) := by
    have h := hd
    simp only [sSet] at h
    exact h
  have hparts : IsConj x d ∧ IsConj x (b' * d) ∧ d ≠ x ∧ d ≠ x * b' := by
    have h := hd'.1
    simp only [sBase] at h
    exact h
  exact ⟨⟨(gamma_isConj_iff hx d).mp hparts.1, hd'.2⟩,
    gamma_mem_orb2A_of_mem_sBase H hx hb' hd'.1⟩

private theorem gamma_row_4A {x b' d : G} (H : GammaHyps a z) (hx : IsConj a x)
    (hb' : b' ∈ orb2A a x) (hd : d ∈ sSet x z b' 3) : d ∈ orb4A a z x ∧ b' ∈ orb2A a d := by
  have hd' : d ∈ sBase x b' ∧ IsConj z ((x * d) ^ 2) := by
    have h := hd
    simp only [sSet] at h
    exact h
  have hparts : IsConj x d ∧ IsConj x (b' * d) ∧ d ≠ x ∧ d ≠ x * b' := by
    have h := hd'.1
    simp only [sBase] at h
    exact h
  exact ⟨⟨(gamma_isConj_iff hx d).mp hparts.1, hd'.2⟩,
    gamma_mem_orb2A_of_mem_sBase H hx hb' hd'.1⟩

theorem gamma_common (H : GammaHyps a z) {x c : G} (hx : IsConj a x) (hc : IsConj a c)
    (he : Even (orderOf (x * c))) : (orb2A a x ∩ orb2A a c).Nonempty := by
  have hcv : c ∈ tab5Base x := ⟨(gamma_isConj_iff hx c).mpr hc, he⟩
  have T5 : TableVFacts x z := H.hT5 x z hx (IsConj.refl z)
  have T4 : TableIVFacts x z := H.hT4 x z hx (IsConj.refl z)
  obtain ⟨i, hi⟩ := T5.partition.cover c hcv
  fin_cases i
  ·
    simp only [tab5Set] at hi
    have hcA : c ∈ orb2A a x := by
      have h := hi
      rw [gamma_orb2A_eq hx x] at h
      exact h
    exact ⟨x * c, H.mul_mem_orb2A hx hcA⟩
  ·
    have hb'0ne : (orb2A x x).Nonempty := by
      have h := (T5.partition.orbit 0).nonempty
      simp only [tab5Set] at h
      exact h
    obtain ⟨b', hb'0⟩ := hb'0ne
    have hb'a : b' ∈ orb2A a x := by
      have h := hb'0
      rw [gamma_orb2A_eq hx x] at h
      exact h
    have hd0ne : (sSet x z b' 1).Nonempty := ((T4.partition b' hb'0).orbit 1).nonempty
    obtain ⟨d, hd0⟩ := hd0ne
    obtain ⟨hdB, hb'd⟩ := gamma_row_twoB H hx hb'a hd0
    have hd_orbit : d ∈ tab5Set x z 1 := by
      have h := hdB
      rw [← gamma_orb2B_eq hx z x] at h
      simp only [tab5Set]
      exact h
    exact gamma_common_of_orbit hb'a hb'd (T5.partition.orbit 1) hd_orbit hi
  ·
    have hb'0ne : (orb2A x x).Nonempty := by
      have h := (T5.partition.orbit 0).nonempty
      simp only [tab5Set] at h
      exact h
    obtain ⟨b', hb'0⟩ := hb'0ne
    have hb'a : b' ∈ orb2A a x := by
      have h := hb'0
      rw [gamma_orb2A_eq hx x] at h
      exact h
    have hd0ne : (sSet x z b' 3).Nonempty := ((T4.partition b' hb'0).orbit 3).nonempty
    obtain ⟨d, hd0⟩ := hd0ne
    obtain ⟨hd4A, hb'd⟩ := gamma_row_4A H hx hb'a hd0
    have hd_orbit : d ∈ tab5Set x z 2 := by
      have h := hd4A
      rw [← gamma_orb4A_eq hx z x] at h
      simp only [tab5Set]
      exact h
    exact gamma_common_of_orbit hb'a hb'd (T5.partition.orbit 2) hd_orbit hi
  ·
    simp only [tab5Set] at hi
    have hc4B : c ∈ orb4B a x := by
      have h := hi
      rw [gamma_orb4B_eq hx x] at h
      exact h
    exact ⟨(x * c) ^ 2, (H.sq_mem_orb2A hx hc4B).2⟩
  ·
    simp only [tab5Set] at hi
    have hc6A : c ∈ orb6A a x := by
      have h := hi
      rw [gamma_orb6A_eq hx x] at h
      exact h
    exact ⟨(x * c) ^ 3, H.cube_mem_orb2A hx hc6A⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
