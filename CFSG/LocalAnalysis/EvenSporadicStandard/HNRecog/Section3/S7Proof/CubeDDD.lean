module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.CubeDD

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_DDD {a z x t t' t'' : G} (H : S7Hyps a z) (hx : IsConj a x)
    (hord : orderOf (a * x) = 3) (ht : t ∈ orb2A a a ∩ orb2A a x)
    (ht' : t' ∈ orb2A a a ∩ orb2A a x) (ht'' : t'' ∈ orb2A a a ∩ orb2A a x) (h12 : t ≠ t')
    (h31 : t'' ≠ t) (h32 : t'' ≠ t') (h3 : t'' ≠ t * t') (c12 : t * t' = t' * t)
    (c13 : t * t'' = t'' * t) (c23 : t' * t'' = t'' * t') :
    IsConj z (t * t' * t'') ∧ IsConj z (a * (t * t' * t'')) := by
  have hmem : ∀ {b : G}, b ∈ orb2A a a ∩ orb2A a x →
      IsConj a b ∧ IsConj a (a * b) := by
    intro b hb
    have h : b ∈ orb2A a a := hb.1
    simpa only [orb2A, Set.mem_setOf_eq] using h
  have htA : IsConj a t := (hmem ht).1
  have htaA : IsConj a (a * t) := (hmem ht).2
  have ht'A : IsConj a t' := (hmem ht').1
  have ht''A : IsConj a t'' := (hmem ht'').1
  have hDD12 : IsConj a (t * t') ∧ IsConj z (a * (t * t')) :=
    s7_DD H hx hord ht ht' h12 c12
  have hDD13 : IsConj a (t * t'') ∧ IsConj z (a * (t * t'')) :=
    s7_DD H hx hord ht ht'' (Ne.symm h31) c13
  have hDD23 : IsConj a (t' * t'') ∧ IsConj z (a * (t' * t'')) :=
    s7_DD H hx hord ht' ht'' (Ne.symm h32) c23
  have ht2 : t ^ 2 = 1 := s7_sq_of_isConj_a H htA
  have ht'2 : t' ^ 2 = 1 := s7_sq_of_isConj_a H ht'A
  have ht''2 : t'' ^ 2 = 1 := s7_sq_of_isConj_a H ht''A
  have ht2m : t * t = 1 := by simpa [pow_two] using ht2
  have ht'2m : t' * t' = 1 := by simpa [pow_two] using ht'2
  have ht''2m : t'' * t'' = 1 := by simpa [pow_two] using ht''2
  have hx2 : x ^ 2 = 1 := s7_sq_of_isConj_a H hx
  have hx2m : x * x = 1 := by simpa [pow_two] using hx2
  have ha2 : a ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [H.isF5.orderOf_a] at h
  have ha2m : a * a = 1 := by simpa [pow_two] using ha2
  have ha1 : a ≠ 1 := by
    intro h
    have hord := H.isF5.orderOf_a
    rw [h, orderOf_one] at hord
    omega
  have ht1 : t ≠ 1 := s7_ne_one_of_isConj_a H htA
  have ht'1 : t' ≠ 1 := s7_ne_one_of_isConj_a H ht'A
  have ha_t : a * t = t * a := s7_comm_orb2A H (IsConj.refl a) ht.1
  have ha_t' : a * t' = t' * a := s7_comm_orb2A H (IsConj.refl a) ht'.1
  have ha_t'' : a * t'' = t'' * a := s7_comm_orb2A H (IsConj.refl a) ht''.1
  have hx_t : x * t = t * x := s7_comm_orb2A H hx ht.2
  have hx_t' : x * t' = t' * x := s7_comm_orb2A H hx ht'.2
  have hx_t'' : x * t'' = t'' * x := s7_comm_orb2A H hx ht''.2
  have hpr : a * (t' * t'') = (t' * t'') * a := Commute.mul_right ha_t' ha_t''
  have hqr : t * (t' * t'') = (t' * t'') * t := Commute.mul_right c12 c13
  have hprx : x * (t' * t'') = (t' * t'') * x := Commute.mul_right hx_t' hx_t''
  have ht_Gxy : t ∈ Gxy a x := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr ha_t, mem_Gx.mpr hx_t⟩
  have hw_Gxy : t' * t'' ∈ Gxy a x := by
    rw [mem_Gxy]
    exact ⟨mem_Gx.mpr hpr, mem_Gx.mpr hprx⟩
  have ha_notGxy : a ∉ Gxy a x := by
    intro hmemg
    have hxa : x * a = a * x := (mem_Gx.mp (mem_Gxy.mp hmemg).2)
    have h1 : (a * x) ^ 2 = 1 := by
      rw [pow_two]
      calc (a * x) * (a * x) = a * (x * (a * x)) := mul_assoc a x (a * x)
        _ = a * ((x * a) * x) := by rw [← mul_assoc x a x]
        _ = a * ((a * x) * x) := by rw [hxa]
        _ = a * (a * (x * x)) := by rw [mul_assoc a x x]
        _ = (a * a) * (x * x) := (mul_assoc a a (x * x)).symm
        _ = 1 := by rw [ha2m, hx2m, one_mul]
    have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hord] at hdvd
    norm_num at hdvd
  have ha_ne_t : a ≠ t := by
    intro h
    exact ha_notGxy (h.symm ▸ ht_Gxy)
  have ht''_not : t'' ∉ Subgroup.closure ({t, t'} : Set G) := by
    intro hmemc
    rcases eq_of_mem_closure_two ht2 ht'2 c12 hmemc with h1 | h1 | h1 | h1
    · exact (s7_ne_one_of_isConj_a H ht''A) h1
    · exact h31 h1
    · exact h32 h1
    · exact h3 h1
  let C : Subgroup G := Subgroup.closure ({t, t', t''} : Set G)
  have hC : IsElemTwo 3 C :=
    s7_isElemTwo_closure_three ht2 ht'2 ht''2 c12 c13 c23 ht1 ht'1 h12 ht''_not
  have hV : ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ IsConj a u ∧ IsConj a v ∧ IsConj a (u * v) :=
    ⟨t, Subgroup.subset_closure (by simp), t', Subgroup.subset_closure (by simp),
      h12, htA, ht'A, hDD12.1⟩
  have hsB : IsConj z (t * t' * t'') := by
    by_contra hns
    obtain ⟨-, hcnt⟩ := s7_cube_B H hC hV
    have hBempty : {y : G | y ∈ C ∧ IsConj z y} = ∅ := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyC, hyz⟩ := hy
        rcases eq_of_mem_closure_three ht2 ht'2 ht''2 c12 c13 c23 hyC with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (s7_ne_one_of_isConj_z H hyz) rfl
        · exact s7_not_both H htA hyz
        · exact s7_not_both H ht'A hyz
        · exact s7_not_both H hDD12.1 hyz
        · exact s7_not_both H ht''A hyz
        · exact s7_not_both H hDD13.1 hyz
        · exact s7_not_both H hDD23.1 hyz
        · exact hns hyz
      · intro hy
        exact absurd hy (by simp)
    rw [hBempty, Set.ncard_empty] at hcnt
    norm_num at hcnt
  have hw2 : (t' * t'') ^ 2 = 1 := s7_sq_of_isConj_a H hDD23.1
  have hw_not_mem : t' * t'' ∉ Subgroup.closure ({a, t} : Set G) := by
    intro hmemc
    rcases eq_of_mem_closure_two ha2 ht2 ha_t hmemc with h1 | h1 | h1 | h1
    · exact (s7_ne_one_of_isConj_a H hDD23.1) h1
    · have hz1 : IsConj z (1 : G) := by
        have h2 := hDD23.2
        rw [h1] at h2
        rwa [show a * a = 1 by simpa [pow_two] using ha2] at h2
      exact (s7_ne_one_of_isConj_z H hz1) rfl
    · apply h3
      calc t'' = (t' * t') * t'' := by rw [ht'2m, one_mul]
        _ = t' * (t' * t'') := mul_assoc t' t' t''
        _ = t' * (t'' * t') := by rw [c23]
        _ = (t' * t'') * t' := (mul_assoc t' t'' t').symm
        _ = t * t' := by rw [h1]
    · apply ha_notGxy
      have ha_eq : a = (t' * t'') * t := by
        calc a = a * (t * t) := by rw [ht2m, mul_one]
          _ = (a * t) * t := (mul_assoc a t t).symm
          _ = (t' * t'') * t := by rw [← h1]
      have hmemg : (t' * t'') * t ∈ Gxy a x := (Gxy a x).mul_mem hw_Gxy ht_Gxy
      rwa [← ha_eq] at hmemg
  let E' : Subgroup G := Subgroup.closure ({a, t, t' * t''} : Set G)
  have hE' : IsElemTwo 3 E' :=
    s7_isElemTwo_closure_three ha2 ht2 hw2 ha_t hpr hqr ha1 ht1 ha_ne_t hw_not_mem
  have hV' : ∃ u ∈ E', ∃ v ∈ E', u ≠ v ∧ IsConj a u ∧ IsConj a v ∧ IsConj a (u * v) :=
    ⟨a, Subgroup.subset_closure (by simp), t, Subgroup.subset_closure (by simp),
      ha_ne_t, IsConj.refl a, htA, htaA⟩
  have hasB : IsConj z (a * (t * t' * t'')) := by
    by_contra hnas
    have hB'eq : {y : G | y ∈ E' ∧ IsConj z y} =
        ({a * (t' * t''), t * (t' * t'')} : Set G) := by
      apply Set.Subset.antisymm
      · intro y hy
        obtain ⟨hyE', hyz⟩ := hy
        rcases eq_of_mem_closure_three ha2 ht2 hw2 ha_t hpr hqr hyE' with
          h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        · subst y
          exact ((s7_ne_one_of_isConj_z H hyz) rfl).elim
        · subst y
          exact (s7_not_both H (IsConj.refl a) hyz).elim
        · subst y
          exact (s7_not_both H htA hyz).elim
        · subst y
          exact (s7_not_both H htaA hyz).elim
        · subst y
          exact (s7_not_both H hDD23.1 hyz).elim
        · subst y
          simp
        · subst y
          simp
        · subst y
          exact (hnas (by simpa only [mul_assoc] using hyz)).elim
      · intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · refine ⟨?_, hDD23.2⟩
          exact E'.mul_mem (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        · refine ⟨?_, ?_⟩
          · exact E'.mul_mem (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
          · simpa only [mul_assoc] using hsB
    obtain ⟨-, hE'cnt⟩ := s7_cube_B H hE' hV'
    have hne_pair : a * (t' * t'') ≠ t * (t' * t'') := by
      intro h
      exact ha_ne_t (mul_right_cancel h)
    rw [hB'eq, Set.ncard_pair hne_pair] at hE'cnt
    norm_num at hE'cnt
  exact ⟨hsB, hasB⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
