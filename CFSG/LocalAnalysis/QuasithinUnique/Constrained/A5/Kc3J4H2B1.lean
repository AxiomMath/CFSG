module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Xf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B1
public import CFSG.Sporadic.J4.QT2LocBasicRep

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.QT2A

theorem a941Words_eq : a941Words = vlA941Strs.map vlW5 := by decide +kernel

theorem b336Word_eq : b336Word = vlB336Word := rfl

theorem xiGens_getD (t : ↥J) {i : ℕ} (hi : i < 4) : (xiGens t).getD i 1 = vlCj t i := by
  interval_cases i <;> simp [xiGens, vlCj_eq]

theorem Mx_b336Gen (hM : MatFacts) (e : ℕ) :
    Mx (b336Gen e) = rowsMatrix (Native.mulRows (etaE e) (wR vlB336Word)) := by
  unfold b336Gen
  rw [map_mul, Mx_eta hM 11 le_rfl e, QT2A.Mx_el5 hM, ← rowsMatrix_mulRows, b336Word_eq]
  rfl

theorem hgs_xi (hM : MatFacts) (e : ℕ) {i : ℕ} (hi : i < 4) :
    Mx ((xiGens (b336Gen e)).getD i 1) = rowsMatrix (gsXi e)[i]! := by
  rw [xiGens_getD _ hi]
  obtain ⟨h0, h1, h2, h3⟩ := Mx_vlCj hM (Mx_b336Gen hM e)
  unfold gsXi
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem reps_ok
    (hM : MatFacts) : ∀ r ∈ vlRepIdx, ∃ R ∈ reps2A ++ reps2B1, Nat.card R = 16 ∧
    ∀ u ∈ R, ∃ M ∈ vlAll[r]!, Mx u = rowsMatrix M := by
  intro r hr
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 hr
  have hk10 : k < 10 := by rw [vlRepIdx_length] at hk; exact hk
  have e : vlRepIdx[k]! = r := by
    rw [← hkr]
    exact getElem!_pos vlRepIdx k (by exact hk)
  subst e
  clear hr hkr hk
  interval_cases k
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 0) hk10 (vlA21Masks.map (eta uJ 11)) (by simp [vlA21Masks])
      (fun i hi => hgs_masks hM vlA21Masks (by simp [vlA21Masks]) hi)
    exact ⟨A21, List.mem_append_left _ A21_mem_reps2A, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 1) hk10 (vlA77Masks.map (eta uJ 11)) (by simp [vlA77Masks])
      (fun i hi => hgs_masks hM vlA77Masks (by simp [vlA77Masks]) hi)
    exact ⟨A77, List.mem_append_left _ A77_mem_reps2A, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 2) hk10 ((vlA941Strs.map vlW5).map el5)
      (by simp [vlA941Strs])
      (fun i hi => hgs_words hM (vlA941Strs.map vlW5) (by simp [vlA941Strs]) hi)
    have hA : A941 = Subgroup.closure {x | x ∈ (vlA941Strs.map vlW5).map el5} := by
      unfold A941 a941Gens
      rw [a941Words_eq]
    exact ⟨A941, List.mem_append_left _ A941_mem_reps2A, by rw [hA]; exact hc,
      by rw [hA]; exact hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 3) hk10
      (CFSG.QuasithinUnique.A5.B7.b7ExplicitWords.map el5)
      (by simp [CFSG.QuasithinUnique.A5.B7.b7ExplicitWords])
      (fun i hi => hgs_words hM CFSG.QuasithinUnique.A5.B7.b7ExplicitWords
        (by simp [CFSG.QuasithinUnique.A5.B7.b7ExplicitWords]) hi)
    exact ⟨B7, List.mem_append_right _ B7_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 4) hk10 (Dec2.wsB336.map el5) (by simp [Dec2.wsB336])
      (fun i hi => hgs_words hM Dec2.wsB336 (by simp [Dec2.wsB336]) hi)
    exact ⟨B336x, List.mem_append_right _ B336x_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 5) hk10 (vlB56Masks.map (eta uJ 11)) (by simp [vlB56Masks])
      (fun i hi => hgs_masks hM vlB56Masks (by simp [vlB56Masks]) hi)
    exact ⟨B56, List.mem_append_right _ B56_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 6) hk10 (xiGens (b336Gen 37)) rfl
      (fun i hi => hgs_xi hM 37 hi)
    exact ⟨B336a, List.mem_append_right _ B336a_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 7) hk10 (xiGens (b336Gen 97)) rfl
      (fun i hi => hgs_xi hM 97 hi)
    exact ⟨B336b, List.mem_append_right _ B336b_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 8) hk10 (xiGens (b336Gen 236)) rfl
      (fun i hi => hgs_xi hM 236 hi)
    exact ⟨B336c, List.mem_append_right _ B336c_mem_reps2B1, hc, hs⟩
  ·
    obtain ⟨hc, hs⟩ := named_facts (k := 9) hk10 (xiGens (b336Gen 491)) rfl
      (fun i hi => hgs_xi hM 491 hi)
    exact ⟨B336d, List.mem_append_right _ B336d_mem_reps2B1, hc, hs⟩

theorem j4_cH
    : ∀ V : Subgroup ↥J, FpfV V → HasCommonFixedPt V →
    ∃ V' ∈ reps2A ++ reps2B1, ∃ g : ↥J, V = V'.map (cm g) := by
  intro V hV h
  obtain ⟨k, hk⟩ := fpfV_common_fixed_xfv hV h
  obtain ⟨R, hR, x, hx⟩ := xfV_conj_named_b Certificates.certificate4029.basic hk
    (reps2A ++ reps2B1) (reps_ok Certificates.certificate4029.basic.mat)
  refine ⟨R, hR, k⁻¹ * x, ?_⟩
  have e1 : (V.map (cm k)).map (cm k⁻¹) = V := map_cm_inv_map_cm k V
  have e2 : (R.map (cm x)).map (cm k⁻¹) = R.map (cm (k⁻¹ * x)) := map_cm_map_cm x k⁻¹ R
  rw [← e1]
  show (V.map (cm k)).map (cm k⁻¹) = R.map (cm (k⁻¹ * x))
  rw [show V.map (cm k) = R.map (cm x) from hx, e2]

theorem card_B56
    : Nat.card B56 = 16 :=
  (named_facts (k := 5) (by norm_num) (vlB56Masks.map (eta uJ 11)) (by simp [vlB56Masks])
    (fun i hi => hgs_masks Certificates.certificate4029.basic.mat vlB56Masks
      (by simp [vlB56Masks]) hi)).1

theorem B56_le_E : B56 ≤ Eg uJ 11 := by
  unfold B56
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact eta_mem_Eg 11 le_rfl c

theorem noNonHBlockAt_B56
    : NoNonHBlockAt Hj B56 := by
  refine noNonHBlockAt_of_normalizer_le 1 ?_
  intro n hn
  exact ⟨n, normalizer_le_Hj_of_le_E_b Certificates.certificate4029.basic B56_le_E card_B56 hn,
    by simp⟩

end CFSG.QuasithinUnique.A5
