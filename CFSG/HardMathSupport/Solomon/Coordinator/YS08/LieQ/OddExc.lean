module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Inner
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreE
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreF4G2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreTwistedE6
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.GH74.GLS.Stage2.OddAut CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.LieType.Ree (ReeTag)

theorem radRigid_of_pCharData {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hBT : Holds Y p) (hd : PCharData Y p ⊤) : RadRigid p Y := by
  intro R hR α hfix hord
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  obtain ⟨-, -, -, -, -, S₀, hS₀⟩ := canonical_parabolic hBT h0 hp
  rw [radInf_eq_of_pCoreOf hc] at hS₀
  obtain ⟨Q, hQP, hQn, hQp, hQr⟩ := hd S₀ (Subgroup.normalizer (R : Set Y)) hS₀ hnt
  have hQR : Q ≤ R := by
    rw [← hc]
    exact le_pCoreOf p hQP hQn hQp
  obtain ⟨z, hz, hzα⟩ := hQr α (Subgroup.mem_top α) (fun x hx => hfix x (hQR hx))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQp) ⟨z, hz⟩
  have hk' : orderOf z = p ^ k := by
    rw [← Subgroup.orderOf_coe (⟨z, hz⟩ : Q)] at hk
    exact hk
  have hdvd : orderOf α ∣ p ^ k := by
    rw [← hzα, ← hk']
    exact orderOf_map_dvd (MulAut.conj : Y →* MulAut Y) z
  have hcop : Nat.Coprime (orderOf α) (p ^ k) := Nat.Coprime.pow_right k hord
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem radRigid_of_pCharData_model {S Y : Type} [Group S] [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (e : S ≃* Y) (hBT : Holds Y p) (hd : PCharData Y p ⊤) : RadRigid p S :=
  (radRigid_of_pCharData hBT hd).of_mulEquiv e.symm

theorem center_eq_bot_of_simple_nonabelian {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

theorem radRigidInner_of_radRigid {q : ℕ} [Fact q.Prime] {S : Type} [Group S]
    (hcen : Subgroup.center S = ⊥) (h : RadRigid q S) : RadRigidInner q S := by
  intro R hR x hx hxo
  have h1 : (MulAut.conj x : MulAut S) = 1 := by
    refine h R hR _ ?_ ?_
    · intro r hr
      simp only [MulAut.conj_apply]
      rw [hx r hr]
      group
    · exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd (MulAut.conj : S →* MulAut S) x) hxo
  have hxc : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun β : MulAut S => β g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = (x * g * x⁻¹) * x := by rw [this]
      _ = x * g := by group
  rw [hcen, Subgroup.mem_bot] at hxc
  exact hxc

set_option linter.unusedSectionVars false

section Exc


theorem radRigid_of_untwistedModel_odd {S : Type} [Group S] {τ : Tag} {q f : ℕ} [Fact q.Prime]
    (hd : ∀ (K : Type) [Field K] [Finite K] [CharP K q], Nat.card K = q ^ f →
      PCharData (adjointGroup τ K) q ⊤)
    (h : UntwistedChevalleyModel S τ (q ^ f)) : RadRigid q S := by
  obtain ⟨K, _, hfin, hcard, ⟨e⟩⟩ := h
  haveI : CharP K q := charP_of_natCard_eq hcard
  have e' : S ≃* ↥(adjointGroup τ K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := τ) (K := K))).trans QuotientGroup.quotientBot)
  exact radRigid_of_pCharData_model e' (holds_adjointGroup_tag τ K q) (hd K hcard)

theorem radRigid_of_twistedE6Model {S : Type} [Group S] {q f : ℕ} [Fact q.Prime] (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .E6 (q ^ f)) : RadRigid q S := by
  obtain ⟨K, _, hfin, hK, σ', hσ', ⟨e⟩⟩ := h
  have hK2 : Nat.card K = (q ^ f) ^ 2 := hK
  haveI : CharP K q := charP_of_natCard_eq (p := q) (f := f * 2) (by rw [hK2, pow_mul])
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 (Fact.out : q.Prime) hf K hK
  have hσeq : σ' = σ.toRingHom := RingHom.ext fun c => (hσ' c).trans (hσ c).symm
  subst hσeq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcen, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (Fact.out : q.Prime) hf K hK2 σ hσ
  have e' : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom := e.trans eC
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    have h2 : TwistTag.E6.order = 2 := rfl
    rw [h2]
    ext c
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = (q ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card, hK2]
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, ← sq, ← hcard, FiniteField.pow_card]
  have hBT : Holds (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) q :=
    holds_of_twistedChevalleyModel (t := TwistTag.E6) hf
      ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := fixedDiagonalFieldActors_E6_eq_top_all (Fact.out : q.Prime) hf hK2 σ hσ
  have hd := pCharData_fixed TwistTag.E6 K σ hσ2 q
  rw [hAtop] at hd
  exact radRigid_of_pCharData_model e' hBT hd

theorem radRigid_of_trialityD4Model {S : Type} [Group S] {q f : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S .D4 (q ^ f)) : RadRigid q S := by
  obtain ⟨K, _, hfin, hK, σ', hσ', ⟨e⟩⟩ := h
  have hK3 : Nat.card K = (q ^ f) ^ 3 := hK
  haveI : CharP K q := charP_of_natCard_eq (p := q) (f := f * 3) (by rw [hK3, pow_mul])
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 (Fact.out : q.Prime) hf K hK
  have hσeq : σ' = σ.toRingHom := RingHom.ext fun c => (hσ' c).trans (hσ c).symm
  subst hσeq
  obtain ⟨-, -, -, -, -, -, hcen, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form (Fact.out : q.Prime) hq2 hf K hK3 σ hσ
  have e' : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.trans eC
  have hσ3 : σ ^ TwistTag.D4.order = 1 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_sigma_pow_order K hK3 σ hσ
  have hBT : Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) q :=
    holds_of_twistedChevalleyModel (t := TwistTag.D4) hf
      ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := CFSG.GH74.GLS.Stage2.Bender.Thm1.par_fixedDiagonalFieldActors_D4_eq_top_odd
    (Fact.out : q.Prime) hq2 hf K hK3 σ hσ
  have hd := CFSG.GH74.GLS.Stage2.Bender.Thm1.pCharData_fixed TwistTag.D4 K σ hσ3 q
  rw [hAtop] at hd
  exact radRigid_of_pCharData_model e' hBT hd

theorem radRigid_of_reeG2Model {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .twistedG2 3 f) : RadRigid 3 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hadm, a, hfa, K, _, hfin, hK, ⟨e⟩⟩ := h
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha1 : 1 ≤ a := by omega
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  haveI : CharP K 3 := charP_of_natCard_eq hK
  haveI : CharP K ReeTag.G2.prime := inferInstanceAs (CharP K 3)
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma K a) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 (K := K) ha1 hK'
  have e' : S ≃* ReeTag.G2.reeGamma K a := (e.trans e1).trans E
  haveI : Finite (ReeTag.G2.reeGamma K a) := finite_reeGamma
  exact radRigid_of_pCharData_model e' ree_holds (ree_pCharData ha1 hK')

theorem radRigid_exceptional_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S : Type} [Group S]
    {t : StatedLieTag} {f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel S t q f) : RadRigid q S := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hadm, hmodel⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    change UntwistedChevalleyModel S .G2 (q ^ f) at hmodel
    refine radRigid_of_untwistedModel_odd (τ := .G2) ?_ hmodel
    intro K _ _ _ hK
    by_cases h3 : q = 3
    · subst h3
      haveI : CharP K ReeTag.G2.prime := inferInstanceAs (CharP K 3)
      exact pCharData_adjoint_top_of_outer ReeTag.G2.tag K 3 (g2_three_sq_mem hf hK)
        (fun J hJ α hfix hsq => g2_three_hOut hf hK hJ α hfix hsq)
    · have htop := diagonalFieldActors_eq_top_F4_G2 hq hq2 hf K hK .G2 (Or.inr ⟨rfl, h3⟩)
      have := pCharData_adjoint .G2 K q
      rwa [htop] at this
  ·
    change UntwistedChevalleyModel S .F4 (q ^ f) at hmodel
    refine radRigid_of_untwistedModel_odd (τ := .F4) ?_ hmodel
    intro K _ _ _ hK
    have htop := diagonalFieldActors_eq_top_F4_G2 hq hq2 hf K hK .F4 (Or.inl rfl)
    have := pCharData_adjoint .F4 K q
    rwa [htop] at this
  ·
    change UntwistedChevalleyModel S .E6 (q ^ f) at hmodel
    refine radRigid_of_untwistedModel_odd (τ := .E6) ?_ hmodel
    intro K _ _ _ _
    exact pCharData_adjoint_top .E6 K q
      (fun hJ α hα => mem_diagonalFieldActors_E6_of_fixes_radical hJ hα)
  ·
    change UntwistedChevalleyModel S .E7 (q ^ f) at hmodel
    refine radRigid_of_untwistedModel_odd (τ := .E7) ?_ hmodel
    intro K _ _ _ _
    exact pCharData_adjoint_top .E7 K q
      (fun hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inl rfl) α)
  ·
    change UntwistedChevalleyModel S .E8 (q ^ f) at hmodel
    refine radRigid_of_untwistedModel_odd (τ := .E8) ?_ hmodel
    intro K _ _ _ _
    exact pCharData_adjoint_top .E8 K q
      (fun hJ α hα => mem_diagonalFieldActors_of_E7_E8 (Or.inr rfl) α)
  ·
    change TwistedChevalleyModel S .E6 (q ^ f) at hmodel
    exact radRigid_of_twistedE6Model hf hmodel
  ·
    change TwistedChevalleyModel S .D4 (q ^ f) at hmodel
    exact radRigid_of_trialityD4Model hq2 hf hmodel

theorem radRigid_ree_odd {q : ℕ} {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .twistedG2 q f) : RadRigid q S := by
  have hq3 : q = 3 := h.1.2.2.2.1
  subst hq3
  exact radRigid_of_reeG2Model h

end Exc

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
