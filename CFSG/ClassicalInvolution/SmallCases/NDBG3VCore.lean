module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinU
import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExcl
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.SmallCases.NDBG3TwinT

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]


theorem twinFrameHyp51tCore_of (hres : TwinSmallInner p) : TwinFrameHyp51tCore p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have main : ∀ c : G, (c = t ∨ c = t * z) →
      Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro c hc
    have hp : p ≠ 2 := hs.odd
    have hq : 5 ≤ p ^ f := hs.five
    have hΩ := hs.hyp
    have hd := hs.frame
    have hK : K ∈ Ω := hd.mem
    have hK'Ω : K' ∈ Ω := hd.hK'.1
    have hz := hd.hz
    have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hd.hK'
    have hcK : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hK hz
    have hcK' : IsClassicalMember p f K' z := isClassicalMember_of_twin hΩ hK'Ω hzK'
    have hBab := twinFrame_isElemAbelian hp hΩ hd
    have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
    have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := mem_closure_of_eq_or_eq_mul hc
    have hc2 := hs.isPGroup_zpowers_c hc
    have hc1 := hs.c_ne_one hc
    have hzc : z ≠ c := hs.z_ne_c hc
    have hMK : K ∈ tqMembers Ω c := ⟨hK, hs.tq_c_K hc⟩
    have hMK' : K' ∈ tqMembers Ω c := ⟨hK'Ω, hs.tq_c_K' hc⟩
    have hne : K' ≠ K := hd.hne
    refine hs.hyp51At_t_of hc fun D j hMj hM'j hmov => ?_
    by_cases hD4 : D.tag j = .trialityD4
    · exact (false_of_trialityD4_sec hp hq hΩ hc2 D j hD4 hMK hMK' hcK hcK' hne hMj hM'j).elim
    have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
    have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
    by_cases hG2 : D.tag j = .G2
    · obtain ⟨hzC, R, R', x, x', hpair, hRM, hR'M, hψx⟩ := vertexTwin_g2 hp hq hΩ hc2 hBab hcB
        hc1 hzB hz.ne_one hzc hMK hMK' hcK hcK' hne D j hMj hmov hG2
      have hr : D.rank j = 0 := by
        have h := D.admissible j
        rw [hG2] at h
        exact h.2.2.1
      have hTI : TwinInnerAlpha p (D.exp j) (D.tag j) (D.rank j) := by
        rw [hG2, hr]
        exact twinInnerAlpha_g2 hp hq'
      exact ⟨hzC, R, R', x, x', hpair, hRM, hR'M, hψx, hTI⟩
    · obtain ⟨hzC, R, R', x, x', hpair, hshape, hRM, hR'M, hψx⟩ := vertexTwin hp hq hΩ hc2 hBab
        hcB hc1 hzB hz.ne_one hzc hMK hMK' hcK hcK' hne D j hMj hmov hG2 hD4
      exact ⟨hzC, R, R', x, x', hpair, hRM, hR'M, hψx,
        twinInnerAlpha_of_shape hres hp hq' (D.admissible j) hshape⟩
  exact ⟨main t (Or.inl rfl), main (t * z) (Or.inr rfl)⟩

theorem twinFrameHyp51uCore_of (hres : TwinSmallOuter p) (hp3 : p = 3) :
    TwinFrameHyp51uCore p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have main : ∀ c : G, UCoset z u t c → Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
    intro c hc
    have hp : p ≠ 2 := hs.odd
    have hq : 5 ≤ p ^ f := hs.five
    have hΩ := hs.hyp
    have hd := hs.frame
    have hBab := twinFrame_isElemAbelian hp hΩ hd
    have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
    have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := hc.mem_closure
    have hc1 : c ≠ 1 := hs.uc_ne_one hc
    have htc : t ≠ c := hs.t_ne_uc hc
    have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hBab hcB
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) := isPGroup_zpowers_of_sq_eq_one hcc
    have hJΩ : J ∈ Ω := hd.hJ.1
    have hJt : IsUniqueInvolution J t := hd.ht
    have hcJ : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hJΩ hJt
    have hMJ : J ∈ tqMembers Ω c := ⟨hJΩ, hs.tq_uc hc hJΩ hJt⟩
    refine hs.hyp51At_u_of hc fun J' hMJ' hcJ' hJ'ne D j hMj hM'j hmov => ?_
    have ht1 : t ≠ 1 := hJt.ne_one
    by_cases hD4 : D.tag j = .trialityD4
    · exact (false_of_trialityD4_sec hp hq hΩ hc2 D j hD4 hMJ hMJ' hcJ hcJ' hJ'ne hMj hM'j).elim
    have hexp : D.exp j = f := (D.exp_eq j).resolve_right fun h => hD4 h.1
    have hq' : 5 ≤ p ^ D.exp j := by rw [hexp]; exact hq
    by_cases hG2 : D.tag j = .G2
    · obtain ⟨htC, R, R', x₁, x₁', hpair, hRM, hR'M, hψx₁⟩ := vertexTwin_g2 hp hq hΩ hc2 hBab
        hcB hc1 htB ht1 htc hMJ hMJ' hcJ hcJ' hJ'ne D j hMj hmov hG2
      have hr : D.rank j = 0 := by
        have h := D.admissible j
        rw [hG2] at h
        exact h.2.2.1
      have hnA1 : ¬ (D.tag j = .PSL ∧ D.rank j = 2) := fun h => by
        rw [hG2] at h
        exact absurd h.1 (by decide)
      have he : 2 ≤ D.exp j := by
        rw [hexp]
        by_contra h
        push Not at h
        interval_cases f <;> simp [hp3] at hq
      have hTO : TwinOuterAlpha p (D.exp j) (D.tag j) (D.rank j) := by
        rw [hG2, hr]
        subst hp3
        exact twinOuterAlpha_g2_three he
      exact ⟨htC, R, R', x₁, x₁', hpair, hRM, hR'M, hψx₁, hnA1, hexp, hTO⟩
    · obtain ⟨htC, R, R', x₁, x₁', hpair, hshape, hRM, hR'M, hψx₁⟩ := vertexTwin hp hq hΩ hc2
        hBab hcB hc1 htB ht1 htc hMJ hMJ' hcJ hcJ' hJ'ne D j hMj hmov hG2 hD4
      exact ⟨htC, R, R', x₁, x₁', hpair, hRM, hR'M, hψx₁, hshape.not_A1, hexp,
        twinOuterAlpha_of_shape hres hp hq' (D.admissible j) hshape⟩
  exact ⟨main u (Or.inl rfl), main (u * z) (Or.inr (Or.inl rfl)),
    main (u * t) (Or.inr (Or.inr (Or.inl rfl))), main (u * t * z) (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem twinFrameHyp51Core_of_cases (hz : TwinFrameHyp51zCore p f) (ht : TwinFrameHyp51tCore p f)
    (hu : TwinFrameHyp51uCore p f) : TwinFrameHyp51Core p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have hfr := hs.frame
  have hcg := hfr.comm_gen hs.odd hs.hyp
  have hzu : Commute z u := hcg z (by simp) u (by simp)
  have hzt : Commute z t := hcg z (by simp) t (by simp)
  have hut : Commute u t := hcg u (by simp) t (by simp)
  have hz2 : z * z = 1 := hfr.hz.sq
  have hu2 : u * u = 1 := hfr.hu2
  have ht2 : t * t = 1 := hfr.ht.sq
  refine ⟨twinFrame_isElemAbelian hs.odd hs.hyp hfr,
    twinFrame_natCard_eight hs.odd hs.five hs.hyp hfr, ?_⟩
  intro c hc hc1
  obtain ⟨a, b, d, rfl⟩ := T7A.mem_closure_words hz2 hu2 ht2 hzu hzt hut hc
  have hz' := hz G Ω K K' J z u t hs
  have ht' := ht G Ω K K' J z u t hs
  have hu' := hu G Ω K K' J z u t hs
  rw [T7A.pow_eq_pow_mod_two hz2 a, T7A.pow_eq_pow_mod_two hu2 b,
    T7A.pow_eq_pow_mod_two ht2 d] at hc1 ⊢
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;> rw [ha, hb, hd] at hc1 ⊢
  · exact absurd (by simp) hc1
  · simpa using ht'.1
  · simpa using hu'.1
  · simpa [hut.eq] using hu'.2.2.1
  · simpa using hz'
  · simpa [hzt.eq] using ht'.2
  · simpa [hzu.eq] using hu'.2.1
  · have e : z * u * t = u * t * z := by
      calc z * u * t = u * z * t := by rw [hzu.eq]
        _ = u * (z * t) := by rw [mul_assoc]
        _ = u * (t * z) := by rw [hzt.eq]
        _ = u * t * z := by rw [mul_assoc]
    simpa [e] using hu'.2.2.2

theorem twinFrameHyp51Core_of (hin : TwinSmallInner p) (hout : TwinSmallOuter p) (hp3 : p = 3) :
    TwinFrameHyp51Core p f :=
  twinFrameHyp51Core_of_cases (twinFrameHyp51zCore p f) (twinFrameHyp51tCore_of hin)
    (twinFrameHyp51uCore_of hout hp3)

end CFSG.ClassicalInvolution.NDB.NDBG3
