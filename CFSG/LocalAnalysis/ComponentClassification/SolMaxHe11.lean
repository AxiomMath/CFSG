module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11Y
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11Jc
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveFHeM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHe11Rec

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup Equiv CFSG.Sporadic.HeldB
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem false_of_held_pump
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (h13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hMult : TBLit.HeldTrivialMultiplier)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 11) (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 11))
    {c e₀ : X} (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc M : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hJc7 : Nonempty (↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 7)))
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hfix : M.map (MulAut.conj t).toMonoidHom = M) (hJcM : Jc ≤ M)
    (hJcMpc : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))))
    (ψ : ↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.He) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.2 hfix
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcY : Jc ≤ M ⊓ centralizer ({t} : Set X) := le_inf hJcM (hJcJ'.trans hJC)
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) (hJcJ.trans inf_le_right)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
  have hfc := exists_fixed_component_of_perm hJC hpair.1.2.2.1 hρJ hcN hc2
    (by rw [hρJc, hs4]; norm_num)
  rw [hρJc] at hfc
  obtain ⟨Jb, hJbJ, hJbpc, hinv, hsubP, χ, hχ⟩ := hfc
  have hcard7 : Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc) = 2520 := by
    obtain ⟨e7⟩ := hJc7
    rw [Nat.card_congr e7.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  have hJbC : Jb ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf ((hJbJ.trans inf_le_left).trans hJC) (hJbJ.trans inf_le_right)
  have hJeq : Jc = Jb := eq_of_isPComponent_of_card he₀ hs4 (by norm_num) hJcJ'
    (hJbJ.trans inf_le_left) hJcC hJbC hJcpc hJbpc χ hχ (by rw [hcard7]; norm_num)
  subst Jb
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hMC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hMpc)
  have hZO : Open.fusionZStar ↥M = pPrimeCore 2 ↥M := (Sol78.fusionZStar_eq_iff M).mpr
    (hMult (↥M ⧸ pPrimeCore 2 ↥M) hq ⟨(Sol78.coreQuotientCenterEquiv M).trans ψ⟩)
  let eY : ↥M ⧸ pPrimeCore 2 ↥M ≃* heP :=
    ((QuotientGroup.quotientMulEquivOfEq hZO.symm).trans ψ).trans heEquivP
  set st := TBLit.oddQuotAction M ⟨t, htN⟩ with hstdef
  have hst : st * st = 1 := by
    rw [hstdef, ← map_mul]
    have h1 : (⟨t, htN⟩ : normalizer (M : Set X)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [h1, map_one]
  have hD7 : Nat.card ((coreImage θ he₀).supportᶜ : Finset (Fin 11)) = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  have : Nontrivial ((coreImage θ he₀).supportᶜ : Finset (Fin 11)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD7]
    norm_num
  have : IsSimpleGroup (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 11))) :=
    alternatingGroup.isSimpleGroup (by rw [hD7]; norm_num)
  have hA7 : Nat.card (alternatingGroup ((coreImage θ he₀).supportᶜ : Finset (Fin 11))) =
      2520 := by
    rw [nat_card_alternatingGroup, hD7]
    rfl
  have hS := FiveFHe.hasOddA_fixedSubgroup_oddQuotAction htN ht2 hJcY hJcMpc χ
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_heAutU hA7 (alt_nonabelian_of_card (by rw [hD7]; norm_num))
    eY st hst hS
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
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJcM,
      UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc]
  have hJtp : ⁅Jt, Jt⁆ = Jt := by rw [hJtdef, ← map_commutator, hJcsub]
  have hJtdvd : Nat.card (↥Jc ⧸ pPrimeCore 2 ↥Jc) ∣ Nat.card Jt := by
    rw [hJtdef, hπdef, L32.card_map_mk_eq_index]
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
    exact dvd_of_eq (Nat.card_congr (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJcM)).toEquiv).symm
  set NY := (((pPrimeCore 2 ↥Jc).map Jc.subtype).subgroupOf M).map π with hNYdef
  have hNL : NY ≤ Jt := map_mono fun x hx => map_subtype_le (pPrimeCore 2 ↥Jc) hx
  have hNn : ∀ l ∈ Jt, ∀ n ∈ NY, l * n * l⁻¹ ∈ NY := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine ⟨x * y * x⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    obtain ⟨o, ho, hoy⟩ := hy
    have hxJc : (x : X) ∈ Jc := hx
    refine ⟨⟨(x : X), hxJc⟩ * o * ⟨(x : X), hxJc⟩⁻¹,
      pPrimeCore_normal.conj_mem o ho _, ?_⟩
    change (x : X) * (o : X) * (x : X)⁻¹ = (x : X) * (y : X) * (x : X)⁻¹
    rw [show (o : X) = (y : X) from hoy]
  have hNodd : Odd (Nat.card NY) := by
    have h1 : Nat.card NY ∣ Nat.card (pPrimeCore 2 ↥Jc) := by
      refine (card_map_dvd _ _).trans ?_
      rw [← card_map_of_injective M.subtype_injective, subgroupOf_map_subtype,
        ← card_map_of_injective Jc.subtype_injective]
      exact card_dvd_of_le inf_le_left
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  obtain ⟨hH2, hH1, hH3⟩ := he_local Φ hΦ hJtF hJtp (hcard7 ▸ hJtdvd) hNL hNn hNodd
  have hmove : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)),
      y ∈ UnbalancedLayer.coreActionKernel Jc →
        ∀ q ∈ Jt, q⁻¹ * TBLit.oddQuotAction M ⟨y, hy⟩ q ∈ NY := by
    intro y hy hyK
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (inv_mem hyK : y⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc).2 (x : X)
      (mem_subgroupOf.1 hx)
    rw [inv_inv] at h1
    rw [hπdef, QuotientGroup.mk'_apply, TBLit.oddQuotAction_mk]
    refine ⟨x⁻¹ * ⟨y * x * y⁻¹, (mem_normalizer_iff.mp hy x).mp x.2⟩, ?_, ?_⟩
    · change (x : X)⁻¹ * (y * x * y⁻¹) ∈ (pPrimeCore 2 ↥Jc).map Jc.subtype
      rw [show (x : X)⁻¹ * (y * x * y⁻¹) = (x : X)⁻¹ * y * x * y⁻¹ by group]
      exact h1
    · rw [map_mul, map_inv]
      rfl
  have hM2 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc →
      ∃ hwM : w ∈ M, π ⟨w, hwM⟩ ∈ Jt ∧ π ⟨w, hwM⟩ ^ 3 = 1 := by
    intro w hwM hwt hwK
    refine ⟨hwM, hH2 _ ?_ fun q hq => ?_⟩
    · rw [hstdef, hπdef, QuotientGroup.mk'_apply, TBLit.oddQuotAction_mk]
      congr 1
      apply Subtype.ext
      change t * w * t⁻¹ = w
      rw [← hwt, mul_inv_cancel_right]
    · have h1 := hmove w (le_normalizer hwM) hwK q hq
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      have h2 : TBLit.oddQuotAction M ⟨w, le_normalizer hwM⟩ (m : ↥M ⧸ pPrimeCore 2 ↥M) =
          π ⟨w, hwM⟩ * m * (π ⟨w, hwM⟩)⁻¹ := by
        rw [hπdef, QuotientGroup.mk'_apply, TBLit.oddQuotAction_mk, ← QuotientGroup.mk_inv,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [h2] at h1
      exact h1
  have hodd3 : ∀ φ : MulAut (↥M ⧸ pPrimeCore 2 ↥M), φ ^ 3 = 1 → Odd (orderOf φ) := fun φ h =>
    (show Odd 3 from ⟨1, rfl⟩).of_dvd_nat (orderOf_dvd_of_pow_eq_one h)
  have hE1 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf w) := by
    intro w hwM hwt hwK
    obtain ⟨hwM', -, hw3⟩ := hM2 w hwM hwt hwK
    have h3 : (((⟨w, hwM'⟩ : ↥M) ^ 3 : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hw3
    rw [QuotientGroup.eq_one_iff] at h3
    have h4 : Odd (orderOf ((⟨w, hwM'⟩ : ↥M) ^ 3)) := by
      have h5 := orderOf_dvd_natCard (⟨_, h3⟩ : ↥(pPrimeCore 2 ↥M))
      rw [Subgroup.orderOf_mk] at h5
      exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h5
    have h6 : orderOf (⟨w, hwM'⟩ : ↥M) ∣ 3 * orderOf ((⟨w, hwM'⟩ : ↥M) ^ 3) :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_mul, pow_orderOf_eq_one])
    rw [Subgroup.orderOf_mk] at h6
    exact (Nat.odd_mul.mpr ⟨⟨1, rfl⟩, h4⟩).of_dvd_nat h6
  have hE2 : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)), y * t = t * y →
      y ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf (TBLit.oddQuotAction M ⟨y, hy⟩)) ∨
        Odd (orderOf (TBLit.oddQuotAction M ⟨y * t, mul_mem hy htN⟩)) := by
    intro y hy hyt hyK
    have hcomm : TBLit.oddQuotAction M ⟨y, hy⟩ * st = st * TBLit.oddQuotAction M ⟨y, hy⟩ := by
      rw [hstdef, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyt
    rcases hH1 _ hcomm (hmove y hy hyK) with h | h
    · exact Or.inl (hodd3 _ h)
    · right
      have h1 : TBLit.oddQuotAction M ⟨y * t, mul_mem hy htN⟩ =
          TBLit.oddQuotAction M ⟨y, hy⟩ * st := by
        rw [hstdef, ← map_mul]
        rfl
      rw [h1]
      exact hodd3 _ h
  have hpM : 17 ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [Nat.card_congr eY.toEquiv, card_heP]
    norm_num
  exact false_of_held_pump_core hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair hρJ he₀ hc htc
    hcN hce hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM htN hres hpM hE1 hE2 (L := Jt)
    (fun j hjM hj => ⟨⟨j, hjM⟩, mem_subgroupOf.2 hj, rfl⟩)
    (fun w hwM hwt hwK => (hM2 w hwM hwt hwK).imp fun _ h => h.1) hH3

end CFSG.ComponentClassification.SolMax.He11

namespace CFSG.ComponentClassification.SolMax

theorem signalizerHeldPumpExclusionInput_holds
    (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hMult : TBLit.HeldTrivialMultiplier) : SignalizerHeldPumpExclusionInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc M hJcJ hJcpc hJc7
    hMC hMpc hfix hJcM hJcMpc _ _ _ _ _
  exact ⟨fun ψ => He11.false_of_held_pump hPump hN1 h13 hML hSch hMult hnab hKP hunb hnU hpair θ
    he₀ hc htc hcN hce hs4 hJcJ hJcpc hJc7 hMC hMpc hfix hJcM hJcMpc ψ⟩

end CFSG.ComponentClassification.SolMax
