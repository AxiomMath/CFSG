module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace Up34Exc

section Arith

theorem two_suN_pow_le_six {k z : ℕ} (hz : Odd z) (h : 2 ^ k ∣ 20160 * z) : k ≤ 6 := by
  have hodd : Odd (315 * z) := Odd.mul (by decide) hz
  have hcop : Nat.Coprime (2 ^ k) (315 * z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h' : 2 ^ k ∣ 2 ^ 6 * (315 * z) := by
    have e : 20160 * z = 2 ^ 6 * (315 * z) := by ring
    rwa [e] at h
  have h6 : 2 ^ k ∣ 2 ^ 6 := hcop.dvd_of_dvd_mul_right h'
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h6

theorem two_suN_prod_three (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 3, (Q ^ i - (-1) ^ i) = (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  have e : Finset.Icc 2 3 = {2, 3} := by decide
  rw [e]
  simp

theorem two_suN_prod_four (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 4, (Q ^ i - (-1) ^ i) = (Q ^ 2 - 1) * ((Q ^ 3 + 1) * (Q ^ 4 - 1)) := by
  have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e]
  simp

theorem two_suN_arith {ν t z : ℕ} (hν : 3 ≤ ν) (ht : 1 ≤ t) (hne : ¬ (ν = 3 ∧ t = 1))
    (hz : Odd z)
    (hcard : ((2 : ℤ) ^ t) ^ (ν * (ν - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 ν, (((2 : ℤ) ^ t) ^ i - (-1) ^ i) = ((20160 * z : ℕ) : ℤ)) :
    False := by
  have hdvdZ : ((2 : ℤ) ^ (t * (ν * (ν - 1) / 2))) ∣ ((20160 * z : ℕ) : ℤ) := by
    rw [pow_mul]
    exact ⟨_, hcard.symm⟩
  have hdvd : 2 ^ (t * (ν * (ν - 1) / 2)) ∣ 20160 * z := by
    have : (((2 ^ (t * (ν * (ν - 1) / 2)) : ℕ)) : ℤ) ∣ ((20160 * z : ℕ) : ℤ) := by
      push_cast
      exact hdvdZ
    exact Int.natCast_dvd_natCast.mp this
  have h6 := two_suN_pow_le_six hz hdvd
  have hν4 : ν ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have hm : 10 ≤ ν * (ν - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      have h4 : 4 ≤ ν - 1 := by omega
      calc 10 * 2 = 5 * 4 := by norm_num
        _ ≤ ν * (ν - 1) := Nat.mul_le_mul hcon h4
    have : 1 * 10 ≤ t * (ν * (ν - 1) / 2) := Nat.mul_le_mul ht hm
    omega
  interval_cases ν
  · have ht2 : t ≤ 2 := by
      have : t * 3 ≤ 6 := by simpa using h6
      omega
    interval_cases t
    · exact hne ⟨rfl, rfl⟩
    · rw [two_suN_prod_three] at hcard
      norm_num at hcard
      omega
  · have ht1 : t ≤ 1 := by
      have : t * 6 ≤ 6 := by simpa using h6
      omega
    interval_cases t
    rw [two_suN_prod_four] at hcard
    norm_num at hcard
    omega

end Arith

section Center

theorem two_suN_center_odd {ν q : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hν : 1 ≤ ν)
    (hZ : Subgroup.center ↥(StatedSU ν q F) =
      (StatedScalars (Fin ν) F).subgroupOf (StatedSU ν q F)) :
    Odd (Nat.card ↥(Subgroup.center ↥(StatedSU ν q F))) := by
  classical
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(StatedSU ν q F)) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center ↥(StatedSU ν q F))) 2 h2
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hxmem : ((x : ↥(StatedSU ν q F)) : GL (Fin ν) F) ∈ StatedScalars (Fin ν) F :=
    Subgroup.mem_subgroupOf.1 ((SetLike.ext_iff.mp hZ (x : ↥(StatedSU ν q F))).1 x.2)
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin ν) c =
      ((x : ↥(StatedSU ν q F)) : GL (Fin ν) F) := hxmem
  have hne : Nonempty (Fin ν) := ⟨⟨0, hν⟩⟩
  have hc2 : c ^ 2 = 1 := by
    have h1 : (((x : ↥(StatedSU ν q F)) : GL (Fin ν) F)) ^ 2 = 1 := by
      have := congrArg (fun y : ↥(Subgroup.center ↥(StatedSU ν q F)) =>
        ((y : ↥(StatedSU ν q F)) : GL (Fin ν) F)) hx2
      simpa using this
    rw [← hc, ← map_pow] at h1
    have h3 := congrArg (fun g : GL (Fin ν) F => (g : Matrix (Fin ν) (Fin ν) F)) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] at h3
    have h4 : Matrix.scalar (Fin ν) ((c ^ 2 : Fˣ) : F) = Matrix.scalar (Fin ν) (1 : F) := by
      rw [map_one]
      exact h3
    exact Units.ext (Matrix.scalar_inj.1 h4)
  have hc1 : c = 1 := by
    have h2F : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    have hsq : (c : F) ^ 2 = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) hc2
      simpa using this
    have h3 : ((c : F) - 1) ^ 2 = 0 := by
      linear_combination hsq + (1 - (c : F)) * h2F
    have h4 : (c : F) = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
    exact Units.ext h4
  apply hx1
  apply Subtype.ext
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

end Center

section Transfer

theorem two_isLThreeFour_of_surjective_central {C R : Type*} [Group C] [Group R]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) (h : IsLThreeFour (R ⧸ Subgroup.center R)) :
    IsLThreeFour (C ⧸ Subgroup.center C) := by
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hC f hf hker
  obtain ⟨F, _, _, hc, ⟨g⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, ⟨e.trans g⟩⟩

end Transfer

section Main

set_option linter.unusedSectionVars false


theorem char2Hrat_suN {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hs : RDSize τ) :
    Char2Hrat τ .suN := by
  classical
  have _hτ := hτ
  have _hs := hs
  intro L _ _ _ p₀ S a hT hap _ i hk _ hL34
  exfalso
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨hs0, hsorb, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  obtain ⟨h2', hn⟩ := suN_rank_ncard hk
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have : (3 : ℕ) = 2 + 1 := rfl
      rw [this, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2' hn
  obtain ⟨π, hπ⟩ := two_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar (by assumption)
  subst hr2
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
    two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨hfin, hqsC, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  haveI := hfin
  have hR20160 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160 :=
    card_eq_of_isLThreeFour hL34
  by_cases h32 : (ν, 2 ^ (e * s)) = (3, 2)
  ·
    have h216 := hc216 h32
    haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Finite.of_injective (Subgroup.inclusion hf1) (Subgroup.inclusion_injective hf1)
    have h1 : 20160 ≤ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
      rw [← hR20160]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥f.range :=
      Subgroup.card_le_of_le hf1
    have h3 : Nat.card ↥f.range ≤ 216 := by
      rw [← h216]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd f)
    omega
  · have hCperf : Group.IsPerfect ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) :=
      (hqsC h32).1
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      le_antisymm (hf2 hCperf) hf1
    let g : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      exact ⟨c, Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hCL := two_isLThreeFour_of_surjective_central hCperf g hgsurj hgker hL34
    have hcardCL : Nat.card (↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ⧸
        Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))) = 20160 :=
      card_eq_of_isLThreeFour hCL
    have hcardC : Nat.card ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) =
        20160 * Nat.card ↥(Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))), hcardCL]
    obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos Nat.two_pos _) 2).ne')
    haveI : CharP ↥F 2 := inferInstance
    have hU : UnitaryFieldData 2 (e * s) ↥F :=
      ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := ν) (by omega)
    have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
      (f := e * s) hFcard hν h32).2
    have hodd : Odd (Nat.card ↥(Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)))) := by
      rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
      exact two_suN_center_odd (by omega) hZ
    refine two_suN_arith (ν := ν) (t := e * s) hν hes (fun h => h32 ?_) hodd ?_
    · obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
      norm_num
    · rw [Nat.card_congr eC.toEquiv, hcardC] at hint
      push_cast at hint
      exact hint.symm

end Main

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
