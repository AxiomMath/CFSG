module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33d
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.RecipeExcLang
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33 (isLpType_of_mulEquiv centerQuotCongr
  card_of_isLpType_three_three isComponentOf_map_congr isLpType_center_map congr_self_eq)

set_option linter.unusedSectionVars false

section Orders

theorem three_pow_four_dvd_div {M g : ℕ} (hM : 3 ^ 4 ∣ M) (hg : g ∣ M) (hcop : Nat.Coprime 3 g) :
    3 ^ 4 ∣ M / g := by
  rw [← Nat.mul_div_cancel' hg] at hM
  exact (Nat.Coprime.pow_left 4 hcop).dvd_of_dvd_mul_left hM

theorem add_one_dvd_sq_sub_one' {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  refine ⟨r, ?_⟩
  have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
  omega

theorem three_pow_four_dvd_pow {q N : ℕ} (hq : 3 ∣ q) (hN : 4 ≤ N) : 3 ^ 4 ∣ q ^ N :=
  (pow_dvd_pow 3 hN).trans (pow_dvd_pow_of_dvd hq N)

theorem three_pow_four_dvd_lieOrderFormula {d : TauCeti.LieTypeIndex}
    (hd : CFSG.Yardstones.Md42047359a2a.lieFamily d = .exceptional) (hc : d.characteristic = 3) :
    3 ^ 4 ∣ lieOrderFormula d := by
  cases d with
  | E6 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have hq1 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.2 (by
      rw [TauCeti.PrimePower.card_def]
      exact pow_ne_zero _ q.prime_p.ne_zero)
    simp only [lieOrderFormula, CFSG.Open.orderE6]
    refine three_pow_four_dvd_div (((((((three_pow_four_dvd_pow h3 (by norm_num)).mul_right
      _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _) ?_ ?_
    · exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)) _
    · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => by omega)
  | E7 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderE7]
    refine three_pow_four_dvd_div ((((((((three_pow_four_dvd_pow h3 (by norm_num)).mul_right
      _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _) ?_ ?_
    · exact Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one _ 2)) _
    · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
  | E8 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderE8]
    exact ((((((((three_pow_four_dvd_pow h3 (by norm_num)).mul_right _).mul_right _).mul_right
      _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _
  | F4 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderF4]
    exact ((((three_pow_four_dvd_pow h3 (by norm_num)).mul_right _).mul_right _).mul_right
      _).mul_right _
  | G2 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderG2]
    exact ((three_pow_four_dvd_pow h3 (by norm_num)).mul_right _).mul_right _
  | twistedE6 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderTwistedE6]
    refine three_pow_four_dvd_div (((((((three_pow_four_dvd_pow h3 (by norm_num)).mul_right
      _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _) ?_ ?_
    · refine Dvd.dvd.mul_left ((Nat.gcd_dvd_right _ _).trans ?_) _
      exact add_one_dvd_sq_sub_one'
        (Nat.one_le_iff_ne_zero.2 (by
          rw [TauCeti.PrimePower.card_def]
          exact pow_ne_zero _ q.prime_p.ne_zero))
    · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => by omega)
  | trialityD4 q =>
    have h3 : 3 ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, show q.p = 3 by simpa using hc]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    simp only [lieOrderFormula, CFSG.Open.orderTrialityD4]
    exact (((three_pow_four_dvd_pow h3 (by norm_num)).mul_right _).mul_right _).mul_right _
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hd

theorem lieOrderFormula_exc_ne {d : TauCeti.LieTypeIndex}
    (hd : CFSG.Yardstones.Md42047359a2a.lieFamily d = .exceptional) (hc : d.characteristic = 3) :
    lieOrderFormula d ≠ 5616 := fun h => by
  have := three_pow_four_dvd_lieOrderFormula hd hc
  rw [h] at this
  omega

theorem not_isLpType_of_center_eq_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (hX : Nat.card X ≠ 5616) : ¬ IsLpType 3 3 (X ⧸ Subgroup.center X) := fun hL => by
  have h := card_of_isLpType_three_three hL
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv] at h
  exact hX h

end Orders

section Untw

theorem noL33_entrywise_field {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hexc : ∀ q, CFSG.Yardstones.Md42047359a2a.lieFamily (c q) = .exceptional)
    {K : Type} [Field K] [Finite K] (hK3 : ringChar K = 3) (σ : K ≃+* K)
    {J : Subgroup ↥(adjointGroup τ K)}
    (hJ : IsComponentOf J (fixSubgroup (entrywiseAdjointAut τ σ))) :
    ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  obtain ⟨q, hqp, hqcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_primePower_card_subfield hK3
      (fixSubfield σ)
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hk3 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := fun _ => by
    rw [hqcard, TauCeti.PrimePower.card_def, hqp]
    exact Nat.le_self_pow q.exponent_pos.ne' 3
  have hperf := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup τ
    (fixSubfield σ) hk3
  obtain ⟨hs, hnc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ
      (fixSubfield σ) hperf
  have hv : (c q).Valid := hvalid q (fun h => by rw [← hqcard]; exact hk3 h)
  obtain ⟨eq⟩ := hB q hv (fixSubfield σ) hqcard
  have hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  let eX : ↥(adjointGroup τ (fixSubfield σ)) ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eq
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ι, hι, hJC, hJn, hsol⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_fixed_structure τ σ
  let e : ↥(adjointGroup τ (fixSubfield σ)) ≃* ι.range := MonoidHom.ofInjective hι
  haveI := hs
  have hJs : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hJnc : ∃ x y : ι.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  have hJq : CFSG.IsQuasisimple ↥ι.range := isQuasisimple_of_isSimpleGroup hJs hJnc
  haveI := hJn
  have hJc : IsComponentOf ι.range (fixSubgroup (entrywiseAdjointAut τ σ)) :=
    ⟨hJC, CFSG.Open.IsSubnormal.step hJC inferInstance (CFSG.Open.IsSubnormal.refl _),
      open_isQuasisimple hJq⟩
  have hJeq : J = ι.range :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eq_of_isComponentOf_of_perfect_le hJc
      (fun P hPC hP => perfect_le_of_solvable_quotient hJC hsol hPC hP) hJ
  subst hJeq
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(adjointGroup τ (fixSubfield σ)) := Subtype.finite
  have hcard : Nat.card ↥ι.range = lieOrderFormula (c q) := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨c q, hv⟩ _ ⟨eX⟩
  haveI := hJs
  have hZJ : Subgroup.center ↥ι.range = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hJnc
  exact not_isLpType_of_center_eq_bot hZJ
    (by rw [hcard]; exact lieOrderFormula_exc_ne (hexc q) (by rw [hchar, hqp]))

theorem noL33_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hG2 : ∀ (q : TauCeti.PrimePower), (c q).Valid → τ = .G2 → 3 ≤ q.card)
    (hexc : ∀ q, CFSG.Yardstones.Md42047359a2a.lieFamily (c q) = .exceptional)
    (q : TauCeti.PrimePower) (hv : (c q).Valid) (hq3 : q.p = 3) (hq9 : q.card ≠ 3)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) (α : MulAut S)
    (hα : α ^ 13 = 1) (hα1 : α ≠ 1) {J : Subgroup S} (hJ : IsComponentOf J (fixSubgroup α)) :
    ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hp13 : (13 : ℕ).Prime := by norm_num
  obtain ⟨K, _, hKfin, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' : S ≃* ↥(adjointGroup τ K) := e.trans eK
  have hℓ : ringChar K = 3 := by rw [ringChar.eq K q.p, hq3]
  have hβ : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hβ1 : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hJ' := isComponentOf_map_congr e' hJ
  intro hL
  have hL' := isLpType_center_map e' hL
  have hG2K : τ = .G2 → 3 ≤ Nat.card K := fun h => hK ▸ hG2 q hv h
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e' α * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
        ((MulAut.congr e' α) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 13 = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inr h)
        hG2K hp13 (by norm_num) _ hβ hβ1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl h)
        hG2K hp13 (by norm_num) _ hβ hβ1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inl h)
        hp13 (by norm_num) _ hβ hβ1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E
        (Or.inr (Or.inl h)) hp13 (by norm_num) _ hβ hβ1
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E
        (Or.inr (Or.inr h)) hp13 (by norm_num) _ hβ hβ1
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  ·
    have hJ'' := isComponentOf_map_congr (ψ : ↥(adjointGroup τ K) ≃* ↥(adjointGroup τ K)) hJ'
    rw [congr_self_eq, hψ] at hJ''
    exact noL33_entrywise_field hB hchar hvalid hexc hℓ σ hJ'' (isLpType_center_map _ hL')
  ·
    have hpK : ¬ 13 ∣ Nat.card K := by
      rw [hK]
      exact CFSG.LieType.SeitzGeneration.not_dvd_card_of_ne hp13 (by omega)
    have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
      rcases hτ with h | h | h | h | h
      · subst h
        exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
          (hG2K rfl)).commutator_eq_top
      all_goals exact single_edge_perfect τ K (by simp [h])
    have hmon : MonomialToralAt τ 13 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
        (by rcases hτ with h | h | h | h | h <;> simp [h]) hp13 (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw hτ hp13 hpK (Or.inl (by norm_num)) hmon hperf _ h
        (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
    obtain ⟨i, hqs, hKR⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S' hp13 ι hinj
        hrange _ hconj hT hap h1 (langSetup_hTame S' hT hap h1) hJ'
    have hAC : ringChar (AlgebraicClosure K) = 3 := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, hℓ]
    have hq9' : 9 ≤ S'.D.q := by
      rw [hSq, hK, TauCeti.PrimePower.card_def, hq3]
      have he1 : q.exponent ≠ 1 := fun h' =>
        hq9 (by rw [TauCeti.PrimePower.card_def, hq3, h', pow_one])
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by have := q.exponent_pos; omega)
    let eKR : ↥(J.map (e' : S →* ↥(adjointGroup τ K))) ≃*
        ↥(rationalComponent S'.ρ S'.Γ (rootCharHom a) i) :=
      ((J.map (e' : S →* ↥(adjointGroup τ K))).equivMapOfInjective ι hinj).trans
        (MulEquiv.subgroupCongr hKR)
    exact noL33_rationalComponent S' hAC hq9' hp13 (by norm_num) hT hap h1 i hqs
      (isLpType_of_mulEquiv (centerQuotCongr eKR).symm hL')

end Untw

theorem eq_of_isComponentOf_of_derived_eq_simple {G : Type*} [Group G] [Finite G]
    {C J K : Subgroup G} (hder : ⁅C, C⁆ = J) (hs : IsSimpleGroup J)
    (hnc : ∃ a b : J, a * b ≠ b * a) (hK : IsComponentOf K C) : K = J := by
  have hJC : J ≤ C := by
    rw [← hder]
    exact Subgroup.commutator_le_self C
  haveI hJnorm : (J.subgroupOf C).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup C C
    rwa [sup_idem] at h
  have hJq : CFSG.IsQuasisimple J := isQuasisimple_of_isSimpleGroup hs hnc
  have hJc : IsComponentOf J C :=
    ⟨hJC, CFSG.Open.IsSubnormal.step hJC inferInstance (CFSG.Open.IsSubnormal.refl _),
      open_isQuasisimple hJq⟩
  refine CFSG.HardMathSupport.Solomon.Coordinator.LieComp.eq_of_isComponentOf_of_perfect_le hJc
    (fun P hPC hP => ?_) hK
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hPC hPC
    _ = J := hder

section TwE6

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (fixSubgroup_pow_eq_of_pow_pow')
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer subfieldRootGroupImage)

theorem noL33_twE6_field {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * f)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1)
    {J : Subgroup (twistedE6RootGroup K σ)} (hJ : IsComponentOf J (fixSubgroup β)) :
    ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 3 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = 3 ^ (2 * d * p) := by rw [hK, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ 3 ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 3 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, hcardk, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set Jf := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ) with hJdef
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδdef
  haveI : Finite (fixSubfield κ) := Subtype.finite
  haveI : Finite C := Subtype.finite
  have eJC : Jf.subgroupOf C ≃* Jf := Subgroup.subgroupOfEquivOfLe hJC
  haveI := hsimpleJ
  have hJs : IsSimpleGroup (Jf.subgroupOf C) := eJC.isSimpleGroup
  have hJn : ∃ x y : Jf.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  let q' : TauCeti.PrimePower := ⟨3, d, hℓ, hd1⟩
  have hv' : (TauCeti.LieTypeIndex.twistedE6 q').Valid := TauCeti.LieTypeIndex.valid_twistedE6 q'
  have hcardk' : Nat.card (fixSubfield κ) = q'.card ^ 2 := by
    rw [hcardk, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
  have hσ₀k : ∀ c, (fixSubfieldRestrict T κ) c = c ^ q'.card := fun c =>
    Subtype.ext (by rw [hσ₀ c, TauCeti.PrimePower.card_def]; rfl)
  obtain ⟨eCat⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_twistedE6_of_field q' hv'
      (fixSubfield κ) hcardk' (fixSubfieldRestrict T κ) hσ₀k
  let eXJ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) ≃* ↥Jf :=
    (graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom).equivMapOfInjective
      (baseChangeGL (fixSubfield κ).subtype) (baseChangeGL_injective _)
  let eX : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) ≃* ↥(Jf.subgroupOf C) := eXJ.trans eJC.symm
  have hfixr : fixSubgroup (β ^ r) = fixSubgroup β := fixSubgroup_pow_eq_of_pow_pow' hrs
  have hJr : IsComponentOf J (fixSubgroup (β ^ r)) := by rw [hfixr]; exact hJ
  have hJψ := isComponentOf_map_congr (ψ : C ≃* C) hJr
  rw [congr_self_eq, hψ] at hJψ
  have hJeq := eq_of_isComponentOf_of_derived_eq_simple hder hJs hJn hJψ
  intro hL
  have hL' := isLpType_center_map (ψ : C ≃* C) hL
  rw [hJeq] at hL'
  have hZ : Subgroup.center ↥(Jf.subgroupOf C) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hJn
  refine not_isLpType_of_center_eq_bot hZ ?_ hL'
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ).toRingHom) := Finite.of_equiv _ eX.toEquiv.symm
  rw [← Nat.card_congr eX.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedE6 q', hv'⟩ _
      ⟨eCat.symm⟩]
  exact lieOrderFormula_exc_ne (by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) (by simp [q'])

theorem noL33_twE6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq3 : q.p = 3) (hq9 : q.card ≠ 3)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group)
    (α : MulAut S) (hα : α ^ 13 = 1) (hα1 : α ≠ 1) {J : Subgroup S}
    (hJ : IsComponentOf J (fixSubgroup α)) : ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hp13 : (13 : ℕ).Prime := by norm_num
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  let e' : S ≃* ↥(twistedE6RootGroup K σ) := e.trans eK
  have hβ' : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hβ1' : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hJ' := isComponentOf_map_congr e' hJ
  intro hL
  have hL' := isLpType_center_map e' hL
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e' α) = 1
  ·
    have hmem : MulAut.congr e' α ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, hh⟩ := hmem
    have hp1 : h ^ 13 = 1 :=
      twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
        (by rw [map_pow, hh, hβ', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1' (by rw [← hh, h', map_one])
    have hpℓ : (13 : ℕ) ≠ q.p := by omega
    have hmon : MonomialToralAt Tag.E6 13 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp13
        (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime q.prime_p q.exponent_pos hK σ hσ hp13 hpℓ hp13 hpℓ
        (Or.inl (by norm_num)) hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
        (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
        (fun h' => hh1 (Subtype.ext h'))
    rw [← hh] at hJ'
    have hpL := natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp13 hK hpℓ
    obtain ⟨i, hqs, hKR⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S' hp13 ι hinj
        hrange _ hconj hT hap h1
        (langSetup_hTame_of_prime S' hp13 hpL (fun h => absurd h (by decide)) hT hap h1) hJ'
    have hAC : ringChar (AlgebraicClosure K) = 3 := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, ← hq3]
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
        (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
    have hq9' : 9 ≤ S'.D.q := by
      rw [hSq, hq3]
      have he1 : q.exponent ≠ 1 := fun h' =>
        hq9 (by rw [TauCeti.PrimePower.card_def, hq3, h', pow_one])
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by have := q.exponent_pos; omega)
    let eKR : ↥(J.map (e' : S →* ↥(twistedE6RootGroup K σ))) ≃*
        ↥(rationalComponent S'.ρ S'.Γ (rootCharHom a) i) :=
      ((J.map (e' : S →* ↥(twistedE6RootGroup K σ))).equivMapOfInjective ι hinj).trans
        (MulEquiv.subgroupCongr hKR)
    exact noL33_rationalComponent S' hAC hq9' hp13 (by norm_num) hT hap h1 i hqs
      (isLpType_of_mulEquiv (centerQuotCongr eKR).symm hL')
  ·
    exact noL33_twE6_field q.exponent_pos (by rw [hK, hq3, ← pow_mul, mul_comm]) σ
      (by rw [← hq3]; exact hσ) hp13 (by norm_num) Θ hΘ _ hβ' hΘβ hJ' hL'

end TwE6

section TriD4

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (exists_cubic_exponent_exc)
open CFSG.RankThree.Chevalley

theorem card_graphFixedRootGroup_cubic {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      lieOrderFormula (.trialityD4 ⟨ℓ, f', hℓ, hf'⟩) := by
  classical
  let q' : TauCeti.PrimePower := ⟨ℓ, f', hℓ, hf'⟩
  have hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid := TauCeti.LieTypeIndex.valid_trialityD4 q'
  have hKq : Nat.card K = q'.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ q'.card) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one, TauCeti.PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ q'.card := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, TauCeti.PrimePower.card_def, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          K σ σ.symm (fun c => σ.apply_symm_apply c)⟩
  obtain ⟨eCat⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.catEquiv_trialityD4_of_field q' hv' K hKq σ₁
      hσ₁
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := Subtype.finite
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.trialityD4 q', hv'⟩ _
    ⟨eCat.symm⟩

theorem noL33_triD4_field {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (3 ^ f)) (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφp : φ ^ p = 1)
    (hφout : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    {J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hJ : IsComponentOf J (fixSubgroup φ)) : ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hℓ : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hφ1 : φ ≠ 1 := fun h => hφout (h ▸ one_mem _)
  have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ1
  obtain ⟨-, -, Θ, hΘ, -⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨φ, Subgroup.mem_top _⟩ hφout
      (by rw [Subgroup.orderOf_mk]; exact hφord)
  have hh₀' : MulAut.conj h₀ * φ * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ φ) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  have hK3 : Nat.card K = 3 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ', hφ', hφord', -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ' ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ 3 ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ' _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord', hff']; exact ⟨p, by ring⟩), hφord', hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ φ) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 3 * f) hK3
      hηord hδcord
  have hfix_eq : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ φ)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = 3 ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ 3 ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, hk, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ
      hσ' δc hδc
  haveI := hsimpJ
  set δ₀ := fieldActor (t := TwistTag.D4) σ δc with hδ₀
  have e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hsimE : IsSimpleGroup ↥(fixSubgroup δ₀) := e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup δ₀), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  haveI : Finite (fixSubfield δc) := Subtype.finite
  have hk3 : Nat.card (fixSubfield δc) = (3 ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  obtain ⟨r, hr, hσr⟩ := exists_cubic_exponent_exc hp (by omega) (fixSubfield δc) hk σ hσ'
  have eJ : graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δc).subtype)
      (baseChangeGL_injective _)
  have eM : ↥(fixSubgroup δ₀) ≃* graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom := e3.trans eJ.symm
  have hperf : commutator ↥(fixSubgroup δ₀) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hncE).1
  have hder : ⁅fixSubgroup δ₀, fixSubgroup δ₀⁆ = fixSubgroup δ₀ :=
    Subgroup.isPerfect_iff.1 ⟨hperf⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hJ1 := isComponentOf_map_congr (MulAut.conj h₀ :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) hJ
  rw [congr_self_eq, hh₀', hfix_eq] at hJ1
  have hJeq := eq_of_isComponentOf_of_derived_eq_simple hder hsimE hncE hJ1
  intro hL
  have hL' := isLpType_center_map (MulAut.conj h₀ :
    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)) hL
  rw [hJeq] at hL'
  have hZ : Subgroup.center ↥(fixSubgroup δ₀) = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncE
  refine not_isLpType_of_center_eq_bot hZ ?_ hL'
  rw [Nat.card_congr eM.toEquiv,
    card_graphFixedRootGroup_cubic hℓ hd (fixSubfield δc) hk3 (fixSubfieldRestrict σ δc) hr
      fun c => Subtype.ext (hσr c)]
  exact lieOrderFormula_exc_ne (by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) (by simp)

theorem noL33_triD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq3 : q.p = 3) (hq9 : q.card ≠ 3)
    {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
    (α : MulAut S) (hα : α ^ 13 = 1) (hα1 : α ≠ 1) {J : Subgroup S}
    (hJ : IsComponentOf J (fixSubgroup α)) : ¬ IsLpType 3 3 (↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hp13 : (13 : ℕ).Prime := by norm_num
  obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘker⟩, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  have hβ' : MulAut.congr e' α ^ 13 = 1 := by rw [← map_pow, hα, map_one]
  have hβ1' : MulAut.congr e' α ≠ 1 := fun h =>
    hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
  have hJ' := isComponentOf_map_congr e' hJ
  intro hL
  have hL' := isLpType_center_map e' hL
  have hpℓ : (13 : ℕ) ≠ q.p := by omega
  by_cases hΘβ : Θ (MulAut.congr e' α) = 1
  ·
    have hmem : MulAut.congr e' α ∈
        (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hΘker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, hx⟩ := hmem
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    have hxp : x ^ 13 = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hx, hβ', map_one])
    have hx1 : x ≠ 1 := fun h' => hβ1' (by rw [← hx, h', map_one])
    have hmon : MonomialToralAt Tag.D4 13 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp13
        (by norm_num)
    obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ hp13 hpℓ hp13 hpℓ
        (Or.inl (by norm_num)) hmon x hxp hx1
    rw [← hx] at hJ'
    have hpL := natCast_ne_zero_algebraicClosure_of_ne q.prime_p hp13 hK hpℓ
    obtain ⟨i, hqs, hKR⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S' hp13 ι hinj
        hrange _ hconj hT hap h1
        (langSetup_hTame_of_prime S' hp13 hpL (fun h => absurd h (by decide)) hT hap h1) hJ'
    have hAC : ringChar (AlgebraicClosure K) = 3 := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure, ← hq3]
      exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
        (n := q.exponent * 3) q.prime_p (by have := q.exponent_pos; omega) (by rw [hK, ← pow_mul])
    have hq9' : 9 ≤ S'.D.q := by
      rw [hSq, hq3]
      have he1 : q.exponent ≠ 1 := fun h' =>
        hq9 (by rw [TauCeti.PrimePower.card_def, hq3, h', pow_one])
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) (by have := q.exponent_pos; omega)
    let eKR : ↥(J.map (e' : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ≃*
        ↥(rationalComponent S'.ρ S'.Γ (rootCharHom a) i) :=
      ((J.map (e' : S →* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).equivMapOfInjective ι
        hinj).trans (MulEquiv.subgroupCongr hKR)
    exact noL33_rationalComponent S' hAC hq9' hp13 (by norm_num) hT hap h1 i hqs
      (isLpType_of_mulEquiv (centerQuotCongr eKR).symm hL')
  ·
    have hout' : MulAut.congr e' α ∉
        (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hΘker]; exact hmem)
    exact noL33_triD4_field hp13 (by norm_num) q.exponent_pos K (by rw [hK, hq3]) σ
      (by rw [← hq3]; exact hσ) _ hβ' hout' hJ' hL'

end TriD4

section Final

theorem noL33CompExc_holds : InputsL33.NoL33CompExc := by
  intro S _ _ hs hna idx hP hc3 hfo he α hα hα1 K hK
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | E6 q =>
    exact noL33_untw (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q) (fun q _ h => absurd h (by decide))
      (fun q => by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) q hv (by simpa using hc3)
      (by simpa using hfo) e α hα hα1 hK
  | E7 q =>
    exact noL33_untw (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q => by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) q hv (by simpa using hc3)
      (by simpa using hfo) e α hα hα1 hK
  | E8 q =>
    exact noL33_untw (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q => by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) q hv (by simpa using hc3)
      (by simpa using hfo) e α hα hα1 hK
  | F4 q =>
    exact noL33_untw (τ := .F4) (Or.inr (Or.inl rfl))
      (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q => by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) q hv (by simpa using hc3)
      (by simpa using hfo) e α hα hα1 hK
  | G2 q =>
    exact noL33_untw (τ := .G2) (Or.inl rfl)
      (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
      (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
      (fun q => by simp [CFSG.Yardstones.Md42047359a2a.lieFamily]) q hv (by simpa using hc3)
      (by simpa using hfo) e α hα hα1 hK
  | twistedE6 q =>
    exact noL33_twE6 q hv (by simpa using hc3) (by simpa using hfo) e α hα hα1 hK
  | trialityD4 q =>
    exact noL33_triD4 q hv (by simpa using hc3) (by simpa using hfo) e α hα hα1 hK
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hP

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
