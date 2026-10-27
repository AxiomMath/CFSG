module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import Certificates.Data.TabCo1Census
public import Certificates.Certificate17327
public import Certificates.Kernel.Co1B.Tri2045

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
  CFSG.HardMathSupport.Dickson.I271.TabCo1Census

section Fused

@[expose] def Fused (s : ↥GA) : Prop :=
  ∃ c : ↥GA, MRep repD0 ((c * s * c⁻¹ : ↥GA) : GL24) ∨ MRep repD1 ((c * s * c⁻¹ : ↥GA) : GL24) ∨
    MRep repZ ((c * s * c⁻¹ : ↥GA) : GL24)

theorem Fused.conj {s : ↥GA} (h : Fused s) (n : ↥GA) : Fused (n * s * n⁻¹) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c * n⁻¹, ?_⟩
  have e : c * n⁻¹ * (n * s * n⁻¹) * (c * n⁻¹)⁻¹ = c * s * c⁻¹ := by group
  rw [e]
  exact hc

theorem fused_of_rep {s : ↥GA}
    (h : MRep repD0 (s : GL24) ∨ MRep repD1 (s : GL24) ∨ MRep repZ (s : GL24)) : Fused s :=
  ⟨1, by simpa using h⟩

end Fused

section Step

theorem step_core {n p k : ↥GA} {nR nIR aR kR : Native.Rows} (rn : MRep nR (n : GL24))
    (rnI : MRep nIR (n : GL24)⁻¹) (rp : MRep aR (p : GL24)) (rk : MRep kR (k : GL24))
    (h : Native.mul (Native.mul nR aR) nIR = kR) : k = n * p * n⁻¹ := by
  have h1 : MRep kR ((n : GL24) * (p : GL24) * (n : GL24)⁻¹) := h ▸ (rn.mul rp).mul rnI
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact rk.eq h1


theorem step_sound (hG : GOK) (hD : (kDag ext).2.2 = true) {cov : List ℕ}
    (hcov : ∀ k ∈ cov, k < 125 ∧ Fused (φ hG (Multiplicative.ofAdd (vec3 k))))
    {s : ℕ × ℕ × ℕ} (hs : stepOK (kDag ext) gRows cov s = true) :
    s.1 < 125 ∧ Fused (φ hG (Multiplicative.ofAdd (vec3 s.1))) := by
  unfold stepOK at hs
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, beq_iff_eq,
    and_assoc] at hs
  obtain ⟨hp, hk, hl, heq⟩ := hs
  have rn := rep_nd (ext := ext) hD (88 + s.2.2)
  have rnI := rep_ndI (ext := ext) hD (88 + s.2.2)
  have rp := rep_a0Row hG (hcov s.2.1 hp).1
  have rk := rep_a0Row hG hk
  have key := step_core (n := ⟨kG ext (88 + s.2.2), kG_mem ext (88 + s.2.2)⟩) rn rnI rp rk heq
  refine ⟨hk, ?_⟩
  rw [key]
  exact (hcov _ hp).2.conj _

theorem chain_sound (hG : GOK) (hD : (kDag ext).2.2 = true) :
    ∀ (st : List (ℕ × ℕ × ℕ)) (cov : List ℕ),
      (∀ k ∈ cov, k < 125 ∧ Fused (φ hG (Multiplicative.ofAdd (vec3 k)))) →
      chainOK (kDag ext) gRows cov st = true →
      ∀ k ∈ st.map (·.1) ++ cov, k < 125 ∧ Fused (φ hG (Multiplicative.ofAdd (vec3 k))) := by
  intro st
  induction st with
  | nil =>
    intro cov hcov _ k hk
    exact hcov k (by simpa using hk)
  | cons s rest ih =>
    intro cov hcov hch k hk
    simp only [chainOK, Bool.and_eq_true] at hch
    obtain ⟨hs, hrest⟩ := hch
    have h1 := step_sound hG hD hcov hs
    have := ih (s.1 :: cov) (by
      intro j hj
      rcases List.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact hcov j hj) hrest
    apply this
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
    tauto

end Step

section Census


theorem census_all (hG : GOK) {k : ℕ} (hk : k < 125) (hk0 : k ≠ 0) :
    Fused (φ hG (Multiplicative.ofAdd (vec3 k))) := by
  have h := (Certificates.certificate17327 : censusCheck () = true)
  simp only [censusCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hD, -, hr1, hr5, hr6, hchain, hcover⟩ := h
  have roots : ∀ j ∈ [1, 5, 6], j < 125 ∧ Fused (φ hG (Multiplicative.ofAdd (vec3 j))) := by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · refine ⟨by norm_num, fused_of_rep (Or.inl ?_)⟩
      rw [← hr1]
      exact rep_a0Row hG (by norm_num)
    · refine ⟨by norm_num, fused_of_rep (Or.inr (Or.inl ?_))⟩
      rw [← hr5]
      exact rep_a0Row hG (by norm_num)
    · refine ⟨by norm_num, fused_of_rep (Or.inr (Or.inr ?_))⟩
      rw [← hr6]
      exact rep_a0Row hG (by norm_num)
  have hall := chain_sound hG hD steps [1, 5, 6] roots hchain
  have hk' := hcover k hk
  rcases hk' with (((h0 | h1) | h5) | h6) | ⟨s, hs, hsk⟩
  · exact absurd h0 hk0
  · exact (roots k (by simp [h1])).2
  · exact (roots k (by simp [h5])).2
  · exact (roots k (by simp [h6])).2
  · exact (hall k (by
      simp only [List.mem_append, List.mem_map]
      exact Or.inl ⟨s, hs, hsk⟩)).2

theorem tabCo1_census (hG : GOK) (s : ↥GA) (hs : orderOf s = 5) : Fused s := by
  obtain ⟨c, a, hca⟩ := fusion_exists hG s hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h1 : c * s * c⁻¹ = 1 := by
      rw [hca]
      exact map_one (φ hG)
    have hs1 : s = 1 := mul_eq_left.1 (mul_inv_eq_one.1 h1)
    rw [hs1, orderOf_one] at hs
    omega
  have hF : Fused (φ hG (Multiplicative.ofAdd a)) := by
    have := census_all hG (idx3_lt a) (fun h => ha0 (idx3_eq_zero h))
    rwa [vec3_idx3] at this
  have e : s = c⁻¹ * (φ hG (Multiplicative.ofAdd a)) * c⁻¹⁻¹ := by
    rw [← hca]
    group
  rw [e]
  exact hF.conj c⁻¹

end Census

end CFSG.HardMathSupport.Dickson.I271.TabCo1
