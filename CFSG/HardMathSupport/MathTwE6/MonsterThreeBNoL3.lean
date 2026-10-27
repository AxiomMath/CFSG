module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBComponents
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMCenter
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def L3AutDvd : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X], IsL3Kind p X →
    ∃ (r : ℕ) (ε : Bool) (f e : ℕ), (e = 1 ∨ e = 3) ∧ L3Cond r ε ∧ Nat.card X * e = L3Ord r ε ∧
      r = p ^ f ∧ Nat.card (MulAut X) ∣ 2 * f * L3Ord r ε

theorem nine_dvd_index_center_of_isL3Kind {p : ℕ} {X : Type} [Group X] [Finite X]
    (h : IsL3Kind p X) : 9 ∣ (Subgroup.center X).index := by
  have hidx := Subgroup.card_mul_index (Subgroup.center X)
  rcases h with hSL | ⟨W, hW, hWSL, ⟨f⟩⟩
  · obtain ⟨r, ε, hc, hcard⟩ := sl3Eps_card_forms hSL
    obtain ⟨hZ3, -⟩ := sl3Eps_facts hSL
    obtain ⟨m, hm⟩ := L3Ord_dvd hc
    rw [hZ3, hcard, hm] at hidx
    exact ⟨m, by omega⟩
  · haveI := CFSG.HardMathSupport.Dickson.Sec6.BM.isPerfect_of_sl3EpsOfChar hWSL
    have hc : Nat.card ↥(Subgroup.center X) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr f).toEquiv,
        Group.IsPerfect.center_quotient_center_eq_bot W, Subgroup.card_bot]
    have h9 := isL3Kind_ninth (Or.inr ⟨W, hW, hWSL, ⟨f⟩⟩ : IsL3Kind p X)
    rw [hc, one_mul] at hidx
    rwa [hidx]

theorem not_three_pow_twelve_dvd {r : ℕ} {ε : Bool} {e p f : ℕ} (he : e = 1 ∨ e = 3)
    (hc : L3Cond r ε) (hd : L3Ord r ε ∣ monsterOrder * e) (hr : r = p ^ f) :
    ¬ 3 ^ 12 ∣ 2 * f * L3Ord r ε := by
  have hnum := CFSG.HardMathSupport.Dickson.Sec6.BM.l3_forall_of_check_M (fun r ε _ => ¬ 3 ^ 10 ∣ L3Ord r ε ∧ r < 2 ^ 27)
    (by decide +kernel) r ε e he hc (by simpa [monsterOrder] using hd)
  obtain ⟨h10, hr27⟩ := hnum
  have hr4 : 4 ≤ r := by
    cases ε
    · exact le_trans (by norm_num) (hc.2 rfl).1
    · exact (hc.1 rfl).1
  have hp2 : 2 ≤ p := by
    by_contra hp
    have hp' : p = 0 ∨ p = 1 := by omega
    rcases hp' with rfl | rfl
    · rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at hr; omega
      · rw [zero_pow hf.ne'] at hr; omega
    · rw [one_pow] at hr; omega
  have hf27 : f < 27 := by
    by_contra hf
    have : 2 ^ 27 ≤ p ^ f :=
      (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_le_pow_left hp2 f)
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hr
    omega
  intro h12
  apply h10
  have hL0 : L3Ord r ε ≠ 0 := by
    have := L3Ord_dvd hc
    rintro h0
    rw [h0] at hd
    exact absurd (zero_dvd_iff.1 hd) (by rcases he with rfl | rfl <;> norm_num [monsterOrder])
  have h2f0 : 2 * f ≠ 0 := by omega
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (mul_ne_zero h2f0 hL0),
    Nat.factorization_mul h2f0 hL0, Finsupp.add_apply] at h12
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hL0]
  have h2f : (2 * f).factorization 3 ≤ 2 := by
    by_contra h3
    have h27 : 3 ^ 3 ∣ 2 * f :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three h2f0).2 (by omega)
    have : 27 ∣ f := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h27)
    omega
  omega

theorem noL3Comp_centralizer_tbw
    (hB2 : L3AutDvd)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({tbw} : Set Gmat)) = ⊥) :
    NoL3Comp (Subgroup.centralizer ({tbw} : Set Gmat)) := by
  haveI : Finite Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  intro J hJ p hL3
  have hcore := glaPPrimeCore_eq_bot_of_glaPComponent hO hJ
  have eJ : barOf 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hJL3 : IsL3Kind p ↥J := isL3Kind_of_mulEquiv eJ hL3
  have hcomp := isComponentOf_of_glaPComponent' hO hJ
  have hC : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
      Subgroup.centralizer ({tbw} : Set Gmat) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_closure {tbw}
  rw [← hC] at hcomp
  have h12 := components_dvd_card_mulAut_of_certificates J hcomp
    (nine_dvd_index_center_of_isL3Kind hJL3)
  obtain ⟨r, ε, f, e, he, hc, hcard, hr, haut⟩ := hB2 p ↥J hJL3
  have hd : L3Ord r ε ∣ monsterOrder * e := by
    rw [← hcard, ← CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    exact Nat.mul_dvd_mul_right (Subgroup.card_subgroup_dvd_card J) e
  exact not_three_pow_twelve_dvd he hc hd hr (h12.trans haut)

@[expose] def M3BCensusA : Prop :=
  ∀ s : Gmat, orderOf s = 3 →
    ¬ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA s →
      IsConj s tbw ∨ IsConj s tbw⁻¹

theorem sporL3DownInner_M_of_census
    (hM : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group))
    (hI : ∀ s : Gmat, orderOf s = 3 →
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA s →
        NoL3Comp (Subgroup.centralizer ({s} : Set Gmat)))
    (hOu : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.UninvertedOPrimeTrivial 3 Gmat)
    (hB2 : L3AutDvd) (hA : M3BCensusA) : SporL3DownInner .M := by
  haveI : Finite Gmat := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.finite_Gmat
  refine sporL3DownInner_of_comp (s := .M) Gmat hM ?_ ?_
  · rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder,
      CFSG.HardMathSupport.Dickson.Sec6.BM.monsterOrder_eq_numeral]
    exact CFSG.HardMathSupport.Dickson.Sec6.BM.noL3Eq_M
  intro x hx
  by_cases hinv : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA x
  · exact hI x hx hinv
  have hconj : ∃ y, (y = tbw ∨ y = tbw⁻¹) ∧ IsConj x y := by
    rcases hA x hx hinv with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  obtain ⟨y, hy, hxy⟩ := hconj
  have hwinv : ¬ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA tbw := by
    intro hw
    apply hinv
    obtain ⟨c, hc⟩ := isConj_iff.1 hxy.symm
    have hy' : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.InvertedByTwoA y := by
      rcases hy with rfl | rfl
      · exact hw
      · obtain ⟨α, hα, hcα, hi⟩ := hw
        refine ⟨α, hα, hcα, ?_⟩
        rw [inv_inv, show α * tbw⁻¹ * α⁻¹ = (α * tbw * α⁻¹)⁻¹ by group, hi, inv_inv]
    have := hy'.map (MulAut.conj c)
    rwa [MulAut.conj_apply, hc] at this
  have hw := noL3Comp_centralizer_tbw hB2
    (hOu tbw CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.orderOf_tbw hwinv)
  have hwy : NoL3Comp (Subgroup.centralizer ({y} : Set Gmat)) := by
    rcases hy with rfl | rfl
    · exact hw
    · have e : Subgroup.centralizer ({tbw⁻¹} : Set Gmat) = Subgroup.centralizer ({tbw} : Set Gmat) := by
        ext g
        simp only [Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h
          calc g * tbw = tbw * (tbw⁻¹ * g) * tbw := by group
            _ = tbw * (g * tbw⁻¹) * tbw := by rw [h]
            _ = tbw * g := by group
        · intro h
          calc g * tbw⁻¹ = tbw⁻¹ * (tbw * g) * tbw⁻¹ := by group
            _ = tbw⁻¹ * (g * tbw) * tbw⁻¹ := by rw [h]
            _ = tbw⁻¹ * g := by group
      rw [e]
      exact hw
  exact noL3Comp_centralizer_of_isConj hxy.symm hwy

end CFSG.HardMathSupport.MathTwE6.M3BIrr
