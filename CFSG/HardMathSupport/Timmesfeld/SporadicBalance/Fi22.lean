module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Reps
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiTransp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterPow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi22FinalK
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Witness
public import CFSG.Sporadic.FischerOddCore.Fi23NoComp

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.Fi22S0
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three CFSG.Open CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer in
theorem fi22_card_centralizer_of_not_mem_D'
    {f : CFSG.Sporadic.Fi22.J} (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hfD : f ∉ CFSG.Sporadic.Fi22.D) :
    Nat.card ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)) = 1769472 ∨
      Nat.card ↥(Subgroup.centralizer ({f} : Set CFSG.Sporadic.Fi22.J)) = 53084160 := by
  set τ : fi22P := fi22PJ.symm f
  have hτP : (τ : Equiv.Perm (Fin 3510)) ∈ fi22P := τ.2
  have hτ : orderOf (τ : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj (fi22P_le_R hτP) hτ
  have hrn := fi22R_le_normalizer hr
  have hkP : fi22ExtRep k ∈ fi22P := by
    rw [← hrτ]
    exact (Subgroup.mem_normalizer_iff.1 hrn _).1 hτP
  have hk3 : k < 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CTUC_Fi22_all_extension_involutions_covered.2.1 j (by omega)).2 hkP
  have e1 := @centralizerMulEquiv CFSG.Sporadic.Fi22.J fi22P inferInstance inferInstance
    fi22PJ.symm f
  have e2 : ↥(Subgroup.centralizer ({fi22PJ.symm f} : Set fi22P)) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {(τ : Equiv.Perm (Fin 3510))}) :=
    (infCentralizerEquiv fi22P hτP).symm
  have e3 : ↥(fi22P ⊓ Subgroup.centralizer {(τ : Equiv.Perm (Fin 3510))}) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k}) :=
    (fi22CP_conj_equiv hrn _).trans (MulEquiv.subgroupCongr (by rw [hrτ]))
  rw [Nat.card_congr ((e1.trans e2).trans e3).toEquiv]
  obtain ⟨h0, h1, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · left
    rw [h0, card_fi22H_zero]
  · right
    rw [h1, card_fi22H_one]
  · exfalso
    apply hfD
    have hrin : r⁻¹ ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) :=
      Subgroup.inv_mem _ hrn
    have hα : normalizerConj hrin fi22OuterZP = τ := by
      apply Subtype.ext
      rw [normalizerConj_apply, fi22OuterZP_eq]
      change r⁻¹ * fi22OuterZ * r⁻¹⁻¹ = (τ : Equiv.Perm (Fin 3510))
      rw [← fi22ExtRep_two, ← hrτ]
      group
    have hzτ := (fi22P_aut_class (normalizerConj hrin)).1
    rw [hα] at hzτ
    have hyτ : IsConj fi22Ya τ := isConj_fi22OuterZP_fi22Ya.symm.trans hzτ
    have := MonoidHom.map_isConj
      (@MulEquiv.toMonoidHom fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ) hyτ
    rw [MulEquiv.coe_toMonoidHom, fi22Ya, MulEquiv.apply_symm_apply,
      show fi22PJ τ = f from MulEquiv.apply_symm_apply fi22PJ f] at this
    exact this

section Reps


theorem D_mul_self {e : CFSG.Sporadic.Fi22.J} (he : e ∈ D) : e * e = 1 := by
  have h := pow_orderOf_eq_one e
  rw [orderOf_of_mem_D he, sq] at h
  exact h

theorem D_conj {e : CFSG.Sporadic.Fi22.J} (he : e ∈ D) (g : CFSG.Sporadic.Fi22.J) : g * e * g⁻¹ ∈ D :=
  IsConj.trans he (isConj_iff.2 ⟨g, rfl⟩)

theorem D_cube {e f : CFSG.Sporadic.Fi22.J} (he : e ∈ D) (hf : f ∈ D) (hne : e * f ≠ f * e) :
    e * f * (e * f) * (e * f) = 1 := by
  rcases orderOf_mul_mem_D he hf with h | h | h
  · exfalso
    exact hne (by
      have h1 : e * f = 1 := orderOf_eq_one_iff.1 h
      have h2 : f = e⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2, mul_inv_cancel, inv_mul_cancel])
  · exfalso
    apply hne
    have h3 := pow_orderOf_eq_one (e * f)
    rw [h, sq] at h3
    have h4 : e * f = (e * f)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have he2 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (D_mul_self he)
    have hf2 : f⁻¹ = f := inv_eq_of_mul_eq_one_right (D_mul_self hf)
    rw [h4, mul_inv_rev, he2, hf2]
  · have h3 := pow_orderOf_eq_one (e * f)
    rw [h, pow_succ, pow_succ, pow_one] at h3
    exact h3

theorem orderOf_xRep {k : ℕ} (hk : k < 4) : orderOf (xRep k) = 3 := by
  obtain ⟨-, -, -, -, -, -, -, hg, -⟩ := classify_parts
  obtain ⟨h0, hcube, -⟩ := hg k hk
  have hT := tabData
  have hρ := globRep_lt k hk
  obtain ⟨hl1, e1⟩ := hT.mul _ hρ _ hρ
  obtain ⟨-, e2⟩ := hT.mul _ hρ _ hl1
  have h3 : xRep k ^ 3 = 1 := by
    rw [xRep_def, pow_three, e1, e2, hcube, tabElt_zero]
  have h1 : xRep k ≠ 1 := by
    intro h
    rw [xRep_def, ← tabElt_zero gJ par] at h
    exact h0 (hT.inj _ hρ 0 (by unfold nS; omega) h)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 h1

theorem gLAPPrimeCoreOf_xRep_sep {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) = ⊥ := by
  have := finite_J
  have hk4 : k < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have hE2 : ∀ e ∈ CFSG.Sporadic.Fi22.D, e * e = 1 := fun e he => D_mul_self he
  have hE3 : ∀ e ∈ CFSG.Sporadic.Fi22.D, ∀ f ∈ CFSG.Sporadic.Fi22.D, e * f ≠ f * e →
      e * f * (e * f) * (e * f) = 1 := fun e he f hf hne => D_cube he hf hne
  have hEc : ∀ e ∈ CFSG.Sporadic.Fi22.D, ∀ g : CFSG.Sporadic.Fi22.J, g * e * g⁻¹ ∈ CFSG.Sporadic.Fi22.D :=
    fun e he g => D_conj he g
  refine @gLAPPrimeCoreOf_eq_bot_of_separated CFSG.Sporadic.Fi22.J (inferInstance : Group CFSG.Sporadic.Fi22.J) finite_J
    CFSG.Sporadic.Fi22.D hE2 hE3 hEc
    (xRep k) (sep_xRep hk) ?_
  intro y hy hD
  set H := Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J) ⊓ fixStab (xRep k) with hHdef
  have hyH : y ∈ H := by
    refine ⟨(Subgroup.mem_centralizer_singleton_iff (g := xRep k)).2 hy, ?_⟩
    show ∀ v : Fin 3510, xRep k • v = v → y • v = v
    intro v hv
    have hc : conjPt v * xRep k = xRep k * conjPt v :=
      conj_eq_self_iff.1 ((smul_eq_iff _ v v).1 hv)
    have := hD (conjPt v) (mem_D_iff.2 ⟨v, v.2, rfl⟩) hc
    exact (smul_eq_iff y v v).2 (conj_eq_self_iff.2 this.symm)
  have hxH : xRep k ∈ H := by
    refine ⟨(Subgroup.mem_centralizer_singleton_iff (g := xRep k)).2 rfl, ?_⟩
    show ∀ v : Fin 3510, xRep k • v = v → xRep k • v = v
    exact fun v hv => hv
  have hcard : Nat.card H = 3 := by
    have h3 := card_centralizer_fix_le hk
    have hdvd : orderOf (xRep k) ∣ Nat.card H := Subgroup.orderOf_dvd_natCard H hxH
    rw [orderOf_xRep hk4] at hdvd
    have hpos : 0 < Nat.card H := Nat.card_pos
    obtain ⟨c, hc⟩ := hdvd
    rw [hc] at h3 hpos ⊢
    have : c = 1 := by omega
    rw [this]
  have hpow := pow_card_eq_one' (G := H) (x := ⟨y, hyH⟩)
  rw [hcard, pow_succ, pow_succ, pow_one] at hpow
  have h := congrArg (fun z : H => (z : CFSG.Sporadic.Fi22.J)) hpow
  simp only [Subgroup.coe_mul, Subgroup.coe_one] at h
  exact h

theorem card_P_inf_centralizer (k : ℕ) (hk : k < 4) {T : Subgroup CFSG.Sporadic.Fi22.J}
    (hT : ∀ x, x ∈ T ↔ ∃ i < nS, tabElt gJ par i = x) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) = tabComm par L nS globRep[k]! := by
  rw [xRep_def]
  exact tabData.card_inf_centralizer hT (globRep_lt k hk)

theorem three_pow_seven_dvd_card_centralizer_xRep {k : ℕ} (hk : k < 4) :
    2187 ∣ Nat.card (Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) := by
  have := finite_J
  obtain ⟨-, -, -, -, -, -, -, hg, -⟩ := classify_parts
  obtain ⟨-, -, hc⟩ := hg k hk
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  have hcard := card_P_inf_centralizer k hk hT
  have hTcard := tabData.card_subgroup hT
  have hdvd : Nat.card ↥(T ⊓ Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) ∣ 3 ^ 9 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : T ⊓ Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J) ≤ T)
    rw [hTcard] at this
    exact this
  obtain ⟨a, -, haeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have h7 : 7 ≤ a := by
    by_contra hlt
    have : 3 ^ a ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hcard] at haeq
    omega
  have h1 : 2187 ∣ Nat.card ↥(T ⊓ Subgroup.centralizer ({xRep k} : Set CFSG.Sporadic.Fi22.J)) := by
    rw [haeq]
    exact (show (2187 : ℕ) = 3 ^ 7 by norm_num) ▸ pow_dvd_pow 3 h7
  exact h1.trans (Subgroup.card_dvd_of_le inf_le_right)

end Reps

theorem gLAPPrimeCoreOf_xRep_zero :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({xRep 0} : Set CFSG.Sporadic.Fi22.J)) = ⊥ := by
  have := finite_J
  obtain ⟨-, -, -, -, -, -, -, -, h2187⟩ := classify_parts
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  set C := Subgroup.centralizer ({xRep 0} : Set CFSG.Sporadic.Fi22.J) with hCdef
  set P := T ⊓ C with hPdef
  have hPcard : Nat.card P = 2187 := by
    rw [hPdef, hCdef, card_P_inf_centralizer 0 (by norm_num) hT, h2187]
  have hTp : IsPGroup 3 T := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPGroup.of_card (n := 9) (by rw [tabData.card_subgroup hT]; rfl)
  have hPp : IsPGroup 3 P := hTp.to_le inf_le_left
  have hPC : P ≤ C := inf_le_right
  have hCle : Nat.card C ≤ 34992 := card_centralizer_xRep_zero_le
  obtain ⟨t, ht4, htc⟩ := exists_orderOf_four_comm
  have h4 : 4 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C
      ((Subgroup.mem_centralizer_singleton_iff (g := xRep 0)).2 htc)
    rwa [ht4] at this
  have h2187' : 2187 ∣ Nat.card C := hPcard ▸ Subgroup.card_dvd_of_le hPC
  have hC : Nat.card C ∣ 3 ^ 8 * 16 := by
    have h8748 : 2187 * 4 ∣ Nat.card C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2187' h4
    obtain ⟨j, hj⟩ := h8748
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hj4 : j ≤ 4 := by omega
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, mul_zero] at hj; omega
      · exact h
    rw [hj]
    interval_cases j <;> norm_num
  set L := GLAPPrimeCoreOf 3 C with hLdef
  have hcop := coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  have hL16 : Nat.card L ∣ 16 := by
    have hLC : Nat.card L ∣ Nat.card C := Subgroup.card_dvd_of_le (GLAPPrimeCoreOf_le C)
    have h1 := hLC.trans hC
    exact (Nat.Coprime.pow_left 8 hcop).symm.dvd_of_dvd_mul_left h1
  refine @gLAPPrimeCoreOf_eq_bot_of_card_le CFSG.Sporadic.Fi22.J (inferInstance : Group CFSG.Sporadic.Fi22.J) finite_J 3
    Nat.prime_three C P hPC hPp 16 81 (Nat.le_of_dvd (by norm_num) hL16)
    (by rw [hPcard]; norm_num) (fun q hq hqL => (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
      (hq.dvd_of_dvd_pow (show q ∣ 2 ^ 4 from hqL.trans hL16))) ?_
  intro w hwL hww hw1 Q hQ hQw
  have hwC : w ∈ C := GLAPPrimeCoreOf_le C hwL
  have hwD : w ∉ D := by
    intro hD
    obtain ⟨i, hi, hwi⟩ := mem_D_iff.1 hD
    have hc : conjPt i * xRep 0 = xRep 0 * conjPt i := by
      rw [← hwi]
      exact (Subgroup.mem_centralizer_singleton_iff (g := xRep 0)).1 hwC
    exact xRep_zero_smul_ne ⟨i, hi⟩ ((smul_eq_iff _ _ _).2 (conj_eq_self_iff.2 hc))
  have hQd := Subgroup.card_dvd_of_le hQw
  rcases fi22_card_centralizer_of_not_mem_D' hww hw1 hwD with h | h <;> rw [h] at hQd
  · exact card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 4) (by norm_num) hQd
  · exact card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 4) (by norm_num) hQd

theorem oPrimeCoreTrivialAt_Fi22J :
    OPrimeCoreTrivialAt 3 CFSG.Sporadic.Fi22.J := by
  intro s hs
  obtain ⟨k, hk, hc⟩ := fi22_classify s hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  refine (gLAPPrimeCoreOf_centralizer_conj c s).1 ?_
  rw [hc]
  interval_cases k
  · exact gLAPPrimeCoreOf_xRep_zero
  · exact gLAPPrimeCoreOf_xRep_sep (by decide)
  · exact gLAPPrimeCoreOf_xRep_sep (by decide)
  · exact gLAPPrimeCoreOf_xRep_sep (by decide)

theorem sporadicOPrimeHolds_Fi22_three :
    SporadicOPrimeHolds .Fi22 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Fi22 := e
  exact @OPrimeCoreTrivialAt.of_mulEquiv 3 S _ ↥CFSG.Sporadic.Fi22.J inferInstance (e0.trans fi22EquivJ)
    oPrimeCoreTrivialAt_Fi22J

open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer CFSG.EvenSporadicStandard.Solomon78 in
theorem sporadicOuterHolds_Fi22_three :
    SporadicOuterHolds .Fi22 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.Fi22 := e
  refine noOuterFixesCentralizer_of_pow_dvd 2187 ?_ ?_
  · intro σ hσ2 hσ H hH h2187
    set θ : S ≃* fi22P := e0.trans fi22PermEquiv with hθ
    set σ' := MulAut.congr θ σ with hσ'
    have hσσ : σ * σ = 1 := by rw [← sq]; exact hσ2
    have h1 : σ' * σ' = 1 := congr_mul_self θ σ hσσ
    have h2 : σ' ≠ 1 := by
      intro h
      apply hσ
      have hσ1 : σ = 1 := (MulAut.congr θ).injective (by rw [← hσ', h, map_one])
      rw [hσ1]
      exact (innerAut S).one_mem
    have hle : H.map θ.toMonoidHom ≤ fixSubgroup σ' := by
      rintro _ ⟨h, hh, rfl⟩
      show σ' (θ h) = θ h
      rw [hσ', congr_apply_apply, MulEquiv.symm_apply_apply, hH h hh]
    have hdvd : Nat.card H ∣ Nat.card (fixSubgroup σ') := by
      rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective]
      exact Subgroup.card_dvd_of_le hle
    have hd := h2187.trans hdvd
    rcases fi22_card_fix_involutive σ' h1 h2 with h | h | h | h | h | h <;> rw [h] at hd <;>
      norm_num at hd
  · intro s hs
    set ψ : S ≃* CFSG.Sporadic.Fi22.J := e0.trans fi22EquivJ with hψ
    have hcard := @card_centralizer_mulEquiv S _ ↥CFSG.Sporadic.Fi22.J inferInstance ψ s
    rw [← hcard]
    have hs' : orderOf (ψ s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
    obtain ⟨k, hk, hc⟩ := fi22_classify _ hs'
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    rw [← card_centralizer_conj c (ψ s), hc]
    exact three_pow_seven_dvd_card_centralizer_xRep hk

theorem sporadicOnePairHolds_Fi22_three :
    SporadicOnePairHolds .Fi22 3 :=
  ⟨sporadicOPrimeHolds_Fi22_three, sporadicOuterHolds_Fi22_three⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
