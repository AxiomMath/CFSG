module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResExcTri
public import CFSG.RankThree.PartOne.K128.F4Syl
public import CFSG.RankThree.PartOne.S11c.Sec66F4ReeK1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti
open CFSG.LieType.Ree CFSG.RankThree.Chevalley SteinbergBT CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.LargeReeOrder
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.HardMathSupport.Timmesfeld.CrossChar (rankLE1_of_pRank)


section


theorem hasIndepPair_reeGamma_phi2 {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ (2 * b + 1) + 1) :
    HasIndepPair p (ReeTag.F4.reeGamma k b) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma k b) := Subtype.finite
  obtain ⟨D⟩ := reeFrameData_nonempty (K := k) (L := AlgebraicClosure k) hk
  have : CharP (AlgebraicClosure k) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective 2
  have hodd : Odd (p ^ 1) := (hp.odd_of_ne_two hp2).pow
  have hmM : ((p ^ 1 : ℕ) : ℤ) ∣ 2 ^ (2 * b + 1) + 1 := by
    rw [pow_one]
    exact_mod_cast hpq
  obtain ⟨Φ, hΦ, -, hΦF⟩ := torus_hom_m_phi2 (L := AlgebraicClosure k) D.isFrob hodd hmM
  obtain ⟨Ψ, hΨ⟩ := exists_hom_reeGamma D wPhi2 Φ hΦ hΦF
  obtain ⟨Ψ', hΨ'⟩ := exists_injective_pi_of_rootsOfUnity_hom hp
    (natCast_ne_zero_algebraicClosure hp hp2) Ψ hΨ
  exact hasIndepPair_of_injective_pi hp le_rfl Ψ' hΨ'

theorem fixesPair_reeGamma {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {α : MulAut (ReeTag.F4.reeGamma K a)} (hαp : α ^ p = 1)
    (hα : α ∉ inner (ReeTag.F4.reeGamma K a))
    (hpair : ∀ (b : ℕ) (k : Type) [Field k] [Finite k] [CharP k ReeTag.F4.prime],
      (2 * b + 1) * p = 2 * a + 1 → Nat.card k = 2 ^ (2 * b + 1) →
        HasIndepPair p (ReeTag.F4.reeGamma k b)) :
    FixesIndepPair p α := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α
  have hΨα : Ψ ⟨x, β⟩ = α := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α = β := by
    show SemidirectProduct.rightHom (Ψ.symm α) = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hαp, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 := by
    rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α hαp ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hchar, ⟨eC⟩⟩ := reeF4_fixed_data_odd hK hp hp2 hβord
  haveI := hchar
  haveI : Finite (fixSubfield β) := Subtype.finite
  have hpairb := hpair b (fixSubfield β) hbp hbcard
  have hfp : FixesIndepPair p (ReeTag.F4.reeGammaFieldAut K a β) :=
    fixesPair_of_injective_fixed
      ((fixSub (ReeTag.F4.reeGammaFieldAut K a β)).subtype.comp eC.symm.toMonoidHom)
      (Subtype.val_injective.comp eC.symm.injective) (fun y => (eC.symm y).2) hpairb
  rw [hg]
  exact hfp.map (MulAut.conj g)

theorem three_dvd_two_pow_odd_add_one (b : ℕ) : 3 ∣ 2 ^ (2 * b + 1) + 1 := by
  have h : (4 : ℕ) ^ b ≡ 1 ^ b [MOD 3] := Nat.ModEq.pow b (by decide)
  rw [one_pow] at h
  have h2 : 2 ^ (2 * b + 1) + 1 = 2 * 4 ^ b + 1 := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  have h3 : 2 * 4 ^ b + 1 ≡ 2 * 1 + 1 [MOD 3] := Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 2 h)
  exact (Nat.modEq_zero_iff_dvd).1 (h3.trans (by decide))

theorem hasIndepPair_reeGamma_geFive {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hrk1 : ¬ RankLE1 p (ReeTag.F4.reeGamma K a)) (b : ℕ) (k : Type) [Field k]
    [Finite k] [CharP k ReeTag.F4.prime] (hbp : (2 * b + 1) * p = 2 * a + 1)
    (hk : Nat.card k = 2 ^ (2 * b + 1)) : HasIndepPair p (ReeTag.F4.reeGamma k b) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hpr : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
    by_contra hlt
    exact hrk1 (rankLE1_of_pRank hp (fun _ => by omega))
  obtain ⟨d, hd, hpd⟩ := ree_class hK hp hp5 hpr
  have hq1' : 1 ≤ 2 ^ (2 * b + 1) := Nat.one_le_two_pow
  have hq2' : 2 ≤ 2 ^ (2 * b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ : 2 ^ (2 * a + 1) = (2 ^ (2 * b + 1)) ^ p := by rw [← hbp, pow_mul]
  have hpdq : p ∣ phiF4 d (2 ^ (2 * b + 1)) :=
    dvd_phiF4_of_dvd_pow hp hq1' hd (by rw [← hQ]; exact hpd)
  have hne : phiF4 d (2 ^ (2 * b + 1)) ≠ 0 := phiF4_ne_zero hd hq2'
  have hone : 1 ≤ (phiF4 d (2 ^ (2 * b + 1))).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hpdq
  have : Finite (ModGL ReeTag.F4.tag k) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma k b) := Subtype.finite
  exact hasIndepPair_of_sylowShape hp hone (sylowShape_ree hk hd hp hp5 hpdq)

theorem chevTwoOuterFixesPair_reeF4 : ChevTwoOuterFixesPair LieIndexReeF4 := by
  intro p hp hp2 L _ _ hrk ⟨d, hchar, hF, ⟨e⟩⟩ hne α hα hαp
  obtain ⟨d, hv⟩ := d
  cases d with
  | reeF4 m =>
    have hR0 := (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46).reeF4 m hv
    have hR : ReeTitsModel L .twistedF4 2 (2 * m + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv e hR0
    obtain ⟨a, K, _, _, _, ha, hfa, hKcard, ⟨eK⟩⟩ := reeF4_model_data hR
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hfa]
    have hα' : MulAut.congr eK α ∉ inner (ReeTag.F4.reeGamma K a) :=
      (congr_mem_inner_iff eK α).not.2 hα
    have hαp' : (MulAut.congr eK α) ^ p = 1 := by rw [← map_pow, hαp, map_one]
    apply FixesIndepPair.of_mulEquiv eK
    by_cases hp3 : p = 3
    · subst hp3
      exact fixesPair_reeGamma ha hK hp hp2 hαp' hα'
        (fun b k _ _ _ _ hk => hasIndepPair_reeGamma_phi2 hk hp hp2
          (three_dvd_two_pow_odd_add_one b))
    · have hp5 := five_le_of_prime_ne hp hp2 hp3
      obtain ⟨hrk2, E, hE, hEc⟩ := rank_data_of_pRank hp hrk eK
      exact fixesPair_reeGamma ha hK hp hp2 hαp' hα'
        (fun b k _ _ _ hbp hk => hasIndepPair_reeGamma_geFive hK hp hp5
          (not_rankLE1_of_sq hp hE hEc) b k hbp hk)
  | A _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | twistedA _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | B _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | C _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | D _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | twistedD _ _ => exact absurd hF (by simp [LieIndexReeF4])
  | E6 _ => exact absurd hF (by simp [LieIndexReeF4])
  | E7 _ => exact absurd hF (by simp [LieIndexReeF4])
  | E8 _ => exact absurd hF (by simp [LieIndexReeF4])
  | F4 _ => exact absurd hF (by simp [LieIndexReeF4])
  | G2 _ => exact absurd hF (by simp [LieIndexReeF4])
  | twistedE6 _ => exact absurd hF (by simp [LieIndexReeF4])
  | trialityD4 _ => exact absurd hF (by simp [LieIndexReeF4])
  | suzuki _ => exact absurd hF (by simp [LieIndexReeF4])
  | reeG2 _ => exact absurd hF (by simp [LieIndexReeF4])
  | tits => exact absurd hF (by simp [LieIndexReeF4])

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
