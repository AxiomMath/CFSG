module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32PSL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Lift
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFL2

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv
open CatalogueSchreierLinearTwo (semilinearEquivAut)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem false_of_psl2_pump
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (h13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hJcM : Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hJcMpc : IsPComponent 2 (Jc.subgroupOf ((M ⊔ M.map (MulAut.conj t).toMonoidHom) ⊓
      centralizer ({t} : Set X))))
    (hfix : M.map (MulAut.conj t).toMonoidHom = M)
    (hcov : ¬ Jc ⊔ (pPrimeCore 2 ↥M).map M.subtype = M)
    (hL : Blueprint.LieModel (↥M ⧸ pPrimeCore 2 ↥M) .PSL 2 5 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    AutL2Facts.isOddPrimePower_of Nat.prime_five (by norm_num) (by norm_num) hF
  have h25 : Nat.card F = 25 := by rw [hF]; norm_num
  have hF4 : 4 ≤ Nat.card F := by omega
  have : IsSimpleGroup (GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  have : IsSimpleGroup (↥M ⧸ pPrimeCore 2 ↥M) := e.isSimpleGroup
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
  have hJcM' : Jc ≤ M := by
    have h1 := hJcM
    rwa [hfix, sup_idem] at h1
  have hJcMpc' : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
    have h1 := hJcMpc
    rwa [hfix, sup_idem] at h1
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcY : Jc ≤ M ⊓ centralizer ({t} : Set X) := le_inf hJcM' (hJcJ'.trans hJC)
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) (hJcJ.trans inf_le_right)
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hD5 : Nat.card ((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  have : Nontrivial ((coreImage θ he₀).supportᶜ : Finset (Fin 9)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD5]
    norm_num
  have : IsSimpleGroup (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 9))) :=
    alternatingGroup.isSimpleGroup (by rw [hD5])
  have hA60 : Nat.card (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = 60 := by
    rw [nat_card_alternatingGroup, hD5]
    rfl
  set st := TBLit.oddQuotAction M ⟨t, htN⟩ with hstdef
  have hst : st * st = 1 := by
    rw [hstdef, ← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (M : Set X)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [h1, map_one]
  have hst1 : st ≠ 1 := fun h1 =>
    hcov (FiveFL2.sup_pPrimeCore_eq_of_oddQuotAction_eq_one htN ht2 h1 hJcY hJcMpc' χ)
  have hS := FiveFHe.hasOddA_fixedSubgroup_oddQuotAction htN ht2 hJcY hJcMpc' χ
  set αt := MulAut.congr e st with hαtdef
  have hαt2 : αt * αt = 1 := by rw [hαtdef, ← map_mul, hst, map_one]
  have hαt1 : αt ≠ 1 := fun h1 =>
    hst1 ((MulAut.congr e).injective (by rw [← hαtdef, h1, map_one]))
  have hS' := hS.of_mulEquiv (((fixedSubgroup st).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr (FiveFHe.map_fixedSubgroup_congr e st)))
  obtain ⟨-, hrt⟩ := FiveFL2.card_eq_25_of_hasOddA hpp hαt2 hαt1 hA60 hS'
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  have hCtN : centralizer ({t} : Set X) ≤ normalizer (J : Set X) := by
    have hCt : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) :=
      UnbalancedLayer.centralizer_zpowers_eq t
    have ht := hpair.1.1
    have hT1 : zpowers t ≠ ⊥ := by
      intro h1
      rw [zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at ht
      exact absurd ht (by decide)
    have hT2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hJT : FooteLit.IsTwoComponentIn J (centralizer ((zpowers t : Subgroup X) : Set X)) := by
      rw [hCt]
      exact ⟨hpair.1.2.1, hpair.1.2.2.1⟩
    have hN := Sol78H.normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt h13 hML hSch
      hnab hKP hunb hnU hpair.2.1 hpair.2.2.1 ⟨t, J, hpair.1⟩ hpair.2.2.2.1 hT1 hT2 hJT
      hpair.1.2.2.2
    intro g hg
    apply hN
    rw [← hCt] at hg
    exact Subgroup.centralizer_le_normalizer _ hg
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hπdef
  set Jt := (Jc.subgroupOf M).map π with hJtdef
  have hJtF : Jt ≤ fixedSubgroup st := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt : t * (x : X) * t⁻¹ = x := by
      have h1 := mem_centralizer_singleton_iff.1 (hJcJ'.trans hJC (mem_subgroupOf.1 hx))
      rw [← h1, mul_inv_cancel_right]
    change st (π x) = π x
    rw [hπdef, QuotientGroup.mk'_apply, hstdef, TBLit.oddQuotAction_mk]
    congr 1
    exact Subtype.ext hxt
  have hJcsub : ⁅Jc.subgroupOf M, Jc.subgroupOf M⁆ = Jc.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJcM', hJcperf]
  have hJtp : ⁅Jt, Jt⁆ = Jt := by rw [hJtdef, ← map_commutator, hJcsub]
  have hcardJc : Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc) = 60 := by
    rw [Nat.card_congr χ.toEquiv, hA60]
  have hJtdvd : Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc) ∣ Nat.card Jt := by
    rw [hJtdef, hπdef, card_map_mk_eq_index]
    have hle : (pPrimeCore 2 ↥M).subgroupOf (Jc.subgroupOf M) ≤
        pPrimeCore 2 ↥(Jc.subgroupOf M) := by
      have : (pPrimeCore 2 ↥M).Normal := pPrimeCore_normal
      refine le_sSup ⟨inferInstance, ?_⟩
      have h1 : Nat.card ↥((pPrimeCore 2 ↥M).subgroupOf (Jc.subgroupOf M)) ∣
          Nat.card ↥(pPrimeCore 2 ↥M) := by
        rw [← card_map_of_injective (Jc.subgroupOf M).subtype_injective, subgroupOf_map_subtype]
        exact card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    refine dvd_trans ?_ (Subgroup.index_dvd_of_le hle)
    exact dvd_of_eq (Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJcM')).toEquiv).symm
  have h60 : 60 ≤ Nat.card Jt := by
    rw [hcardJc] at hJtdvd
    exact Nat.le_of_dvd Nat.card_pos hJtdvd
  obtain ⟨hJt60, hfixφ, hcentg, hbig⟩ := mbar_facts_psl2 hpp h25 e hst hrt hJtF hJtp h60
  have hOJc : (pPrimeCore 2 ↥Jc).map Jc.subtype ≤ (pPrimeCore 2 ↥M).map M.subtype :=
    map_pPrimeCore_le_of_card hJcM' (by rw [← hπdef, ← hJtdef, hJt60, hcardJc])
  have hfixJt : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)),
      y ∈ UnbalancedLayer.coreActionKernel Jc → ∀ q ∈ Jt, TBLit.oddQuotAction M ⟨y, hy⟩ q = q := by
    intro y hy hyK
    rintro _ ⟨x, hx, rfl⟩
    have hxJc : (x : X) ∈ Jc := mem_subgroupOf.1 hx
    have hyK' : y⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc := inv_mem hyK
    have h1 := hyK'.2 (x : X) hxJc
    rw [inv_inv] at h1
    have h2 : (x : X)⁻¹ * (y * x * y⁻¹) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      have h3 : (x : X)⁻¹ * (y * x * y⁻¹) = (x : X)⁻¹ * y * x * y⁻¹ := by group
      rw [h3]
      exact hOJc h1
    obtain ⟨o, ho, hoeq⟩ := h2
    rw [hπdef, QuotientGroup.mk'_apply, TBLit.oddQuotAction_mk]
    apply QuotientGroup.eq.mpr
    have h4 : (⟨y * x * y⁻¹, (mem_normalizer_iff.mp hy x).mp x.2⟩ : ↥M)⁻¹ * x = o⁻¹ :=
      Subtype.ext (by
        change (y * (x : X) * y⁻¹)⁻¹ * x = ((o : X))⁻¹
        rw [show (o : X) = (x : X)⁻¹ * (y * x * y⁻¹) from hoeq]
        group)
    rw [h4]
    exact inv_mem ho
  have hW1 : ∀ w ∈ M, w ∈ UnbalancedLayer.coreActionKernel Jc →
      ∃ hwM : w ∈ M, ((⟨w, hwM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
    intro w hwM hwK
    refine ⟨hwM, hcentg _ fun q hq => ?_⟩
    have h1 := hfixJt w (le_normalizer hwM) hwK q hq
    obtain ⟨x, -, rfl⟩ := hq
    have h2 : ((⟨w, hwM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) * π x *
        ((⟨w, hwM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M)⁻¹ =
          TBLit.oddQuotAction M ⟨w, le_normalizer hwM⟩ (π x) := by
      rw [hπdef, QuotientGroup.mk'_apply, TBLit.oddQuotAction_mk, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rw [h2, h1]
  have hE1 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf w) := by
    intro w hwM _ hwK
    obtain ⟨hwM', hw1⟩ := hW1 w hwM hwK
    rw [QuotientGroup.eq_one_iff] at hw1
    have h2 : orderOf (⟨⟨w, hwM'⟩, hw1⟩ : ↥(pPrimeCore 2 ↥M)) ∣ Nat.card (pPrimeCore 2 ↥M) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h2
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
  have hE2 : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)), y * t = t * y →
      y ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf (TBLit.oddQuotAction M ⟨y, hy⟩)) ∨
        Odd (orderOf (TBLit.oddQuotAction M ⟨y * t, mul_mem hy htN⟩)) := by
    intro y hy _ hyK
    rcases hfixφ _ (hfixJt y hy hyK) with h | h
    · left
      rw [h, orderOf_one]
      exact odd_one
    · right
      have h1 : (⟨y * t, mul_mem hy htN⟩ : ↥(normalizer (M : Set X))) = ⟨y, hy⟩ * ⟨t, htN⟩ := rfl
      rw [h1, map_mul, h, ← hstdef, hst, orderOf_one]
      exact odd_one
  have hE3 : ∃ h ∈ M, h * t = t * h ∧ ∃ (hhJ : h ∈ normalizer (J : Set X))
      (σD σF : Perm (Fin 9)), ρJ ⟨h, hhJ⟩ = σD * σF ∧
        (∀ v ∉ (coreImage θ he₀).support, σD v = v) ∧
        (∀ v ∈ (coreImage θ he₀).support, σF v = v) ∧ Perm.sign σF = -1 := by
    obtain ⟨q, hqF, hqJt⟩ : ∃ q ∈ fixedSubgroup st, q ∉ Jt := by
      by_contra hne
      push Not at hne
      have h1 : Nat.card (fixedSubgroup st) ≤ Nat.card Jt :=
        Subgroup.card_le_of_le (fun q hq => hne q hq)
      omega
    obtain ⟨h, hhM, hht, hhq⟩ := exists_lift_of_mem_fixedSubgroup htN ht2 hqF
    have hhJ : h ∈ normalizer (J : Set X) := hCtN (mem_centralizer_singleton_iff.mpr hht)
    have hhc : h * c = c * h := mem_centralizer_singleton_iff.mp (hMC hhM)
    have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
      hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
    have hπc : ρJ ⟨h, hhJ⟩ * coreImage θ he₀ = coreImage θ he₀ * ρJ ⟨h, hhJ⟩ := by
      rw [← hρJc, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hhc
    obtain ⟨σD, σF, hsplit, hσD, hσF, -, hσFπ⟩ :=
      exists_split (coreImage θ he₀).support (apply_mem_support_iff_of_commute hπc)
    refine ⟨h, hhM, hht, hhJ, σD, σF, hsplit, hσD, hσF, ?_⟩
    rcases Int.units_eq_one_or (Perm.sign σF) with hs | hs
    · exfalso
      have hmem : σF ∈ (Perm.ofSubtype :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) →* Perm (Fin 9)).range := by
        rw [Perm.mem_range_ofSubtype_iff]
        intro v hv
        change v ∈ (coreImage θ he₀).supportᶜ
        rw [Finset.mem_compl]
        intro hvD
        exact (Perm.mem_support.mp hv) (hσF v hvD)
      obtain ⟨b, hb⟩ := hmem
      have hbA : b ∈ alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) := by
        rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hb, hs]
      obtain ⟨xq, hxq⟩ := χ.surjective ⟨b, hbA⟩
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective xq
      have hjJ : (j : X) ∈ J := hJcJ' j.2
      have hρj : coreImage θ hjJ = σF := by
        rw [← hχ j hjJ, hxq]
        exact hb
      have hwM : h * (j : X)⁻¹ ∈ M := mul_mem hhM (inv_mem (hJcM' j.2))
      have hwJ : h * (j : X)⁻¹ ∈ normalizer (J : Set X) :=
        mul_mem hhJ (inv_mem (le_normalizer hjJ))
      have hjc : (j : X) * c = c * j :=
        mem_centralizer_singleton_iff.mp (hJcJ.trans inf_le_right j.2)
      have hwc : h * (j : X)⁻¹ * c = c * (h * (j : X)⁻¹) := by
        have c1 : Commute h c := hhc
        have c2 : Commute (j : X) c := hjc
        exact (c1.mul_left c2.inv_left).eq
      have hρw : ρJ ⟨h * (j : X)⁻¹, hwJ⟩ = σD := by
        have h1 : (⟨h * (j : X)⁻¹, hwJ⟩ : ↥(normalizer (J : Set X))) =
            ⟨h, hhJ⟩ * (⟨(j : X), le_normalizer hjJ⟩)⁻¹ := rfl
        have hρj' : ρJ ⟨(j : X), le_normalizer hjJ⟩ = coreImage θ hjJ :=
          hρJ.apply_of_mem (by norm_num) ⟨(j : X), hjJ⟩
        rw [h1, map_mul, map_inv, hρj', hρj, hsplit, mul_inv_cancel_right]
      have hwD : (ρJ ⟨h * (j : X)⁻¹, hwJ⟩).support ⊆ (coreImage θ he₀).support := by
        rw [hρw]
        intro v hv
        by_contra hvD
        exact (Perm.mem_support.mp hv) (hσD v hvD)
      obtain ⟨-, hwK⟩ := mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ
        hχ hwJ hwc hwD
      obtain ⟨hwM', hw1⟩ := hW1 _ hwM hwK
      apply hqJt
      rw [← hhq]
      have h2 : (⟨h, hhM⟩ : ↥M) = ⟨h * (j : X)⁻¹, hwM'⟩ * ⟨(j : X), hJcM' j.2⟩ :=
        Subtype.ext (by simp)
      rw [h2, QuotientGroup.mk_mul, hw1, one_mul]
      exact ⟨⟨(j : X), hJcM' j.2⟩, mem_subgroupOf.2 j.2, rfl⟩
    · exact hs
  have hpM : 13 ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F hpp, h25]
    norm_num
  have hpHe : 9 = 9 → ¬ 13 ∣ Nat.card Blueprint.NativeSporadic.He := fun _ => by
    rw [CFSG.Sporadic.He.card_He]
    norm_num
  exact false_of_exceptional_pump (p := 13) hPump hN1 hnab hKP hunb hnU hpair hρJ he₀ hc htc hcN
    hce hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM' htN (by norm_num) (by norm_num) hpM hpHe hE1
    hE2 hE3

end CFSG.ComponentClassification.SolMax.L32

namespace CFSG.ComponentClassification.SolMax

theorem signalizerFivePumpLTwoInnerInput_holds
    (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    SignalizerFivePumpLTwoInnerInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc _ hfix hcov _ _ _ _ _ _ _ hP
  exact (L32.false_of_psl2_pump hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair θ he₀ hc htc hcN
    hce hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM hJcMpc hfix hcov hP.1).elim

theorem signalizerFivePumpLTwoInput_holds
    (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    SignalizerFivePumpLTwoInput :=
  signalizerFivePumpLTwoInput_of_inner
    (signalizerFivePumpLTwoInnerInput_holds hPump hN1 h13 hML hSch)

end CFSG.ComponentClassification.SolMax
