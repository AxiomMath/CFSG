module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveA
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem core_inf_centralizer_le_of_nine (hbal : Sol78.BalanceTwoComponentInput)
    (hFP : SignalizerFivePumpBalanceInput) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9)
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9))
    {e f : X} (he : e ∈ J) (hf : f ∈ J) (he2 : e * e = 1) (hf2 : f * f = 1) (he1 : e ≠ 1)
    (hf1 : f ≠ 1) (hef : e * f = f * e) (hse : (coreImage θ he).support.card ≤ 4)
    (hsf : (coreImage θ hf).support.card ≤ 4)
    (hdisj : Disjoint (coreImage θ he).support (coreImage θ hf).support) :
    (pPrimeCore 2 (centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ⊓
        centralizer ({e} : Set X) ≤
      (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, hJC, hJpc, -⟩ := hpair.1
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  set Ce : Subgroup X := centralizer ({e} : Set X) with hCedef
  set Cf : Subgroup X := centralizer ({f} : Set X) with hCfdef
  set Oe := (pPrimeCore 2 ↥Ce).map Ce.subtype with hOedef
  set Of := (pPrimeCore 2 ↥Cf).map Cf.subtype with hOfdef
  have hte : t ∈ Ce := by
    rw [hCedef, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hJC he)).symm
  by_contra hX₀
  have he2' : e ^ 2 = 1 := by rw [sq]; exact he2
  have hf2' : f ^ 2 = 1 := by rw [sq]; exact hf2
  have hS : zpowers f ≠ ⊥ := fun h => hf1 (zpowers_eq_bot.mp h)
  have hT : zpowers e ≠ ⊥ := fun h => he1 (zpowers_eq_bot.mp h)
  have hST : zpowers f ≤ centralizer ((zpowers e : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hef.symm
  obtain ⟨-, hbc, hd⟩ := hbal X (zpowers f) (zpowers e) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one hf2')
    (IsElementaryAbelian.zpowers_of_pow_eq_one he2') hST
  have hCe' : centralizer ((zpowers e : Subgroup X) : Set X) = Ce := centralizer_zpowers_eq' e
  have hCf' : centralizer ((zpowers f : Subgroup X) : Set X) = Cf := centralizer_zpowers_eq' f
  rw [hCe', hCf'] at hbc hd
  obtain ⟨M, ⟨hMCe, hMpc⟩, hMX⟩ := hd hX₀
  obtain ⟨-, hc⟩ := hbc M ⟨hMCe, hMpc⟩
  obtain ⟨-, -, hOM⟩ := hc hMX
  have hOMCe : (pPrimeCore 2 ↥M).map M.subtype ≤ Oe := pPrimeCore_le_of_isPComponent hMCe hMpc
  have hfK : f ∉ UnbalancedLayer.coreActionKernel M := by
    intro hfK
    have h1 : ⁅M, zpowers f ⊓ normalizer (M : Set X)⁆ ≤ Oe :=
      (commutator_le_of_le_coreActionKernel (inf_le_left.trans (zpowers_le.mpr hfK))).trans
        hOMCe
    have h2 : Oe ⊔ M ≤ Oe := by
      have h3 : GH74.GLS.pPrimeCoreOf 2 Ce ⊔ M = GH74.GLS.pPrimeCoreOf 2 Ce ⊔
          ⁅M, zpowers f ⊓ normalizer (M : Set X)⁆ := hOM
      change GH74.GLS.pPrimeCoreOf 2 Ce ⊔ M ≤ GH74.GLS.pPrimeCoreOf 2 Ce
      rw [h3]
      exact sup_le le_rfl h1
    exact not_le_pPrimeCore_of_isPComponent hMCe hMpc (le_sup_right.trans h2)
  have hθe1 := coreImage_ne_one_of_involution θ he he2 he1
  have hθe2 : coreImage θ he * coreImage θ he = 1 := by
    have h1 : (⟨e, he⟩ : ↥J) * ⟨e, he⟩ = 1 := Subtype.ext he2
    have h2 : θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  have hse4 : 4 ≤ (coreImage θ he).support.card :=
    four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ he) hθe2 hθe1
  have hse4' : (coreImage θ he).support.card = 4 := by omega
  have heN : e ∈ normalizer (J : Set X) := le_normalizer he
  have hee : e * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨Je, hJeJC, hJepc, hinv, hsubP, χ, hχ⟩ :=
    exists_fixed_component_of_acts hJC hJpc θ heN he2 he hee (by omega)
  have hJeCe : Je ≤ Ce := hJeJC.trans inf_le_right
  have hJeJ : Je ≤ J := hJeJC.trans inf_le_left
  have hfJe : f ∈ Je := by
    refine hinv f hf hef.symm ⟨1, by rw [pow_one, sq]; exact hf2⟩ ?_
    intro x hx
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hdisj hx
  have hJeTC : Je ≤ Ce ⊓ centralizer ({t} : Set X) := le_inf hJeCe (hJeJ.trans hJC)
  have hJepc' : IsPComponent 2 (Je.subgroupOf (Ce ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJepc
  obtain ⟨M', hM'Ce, hM'pc, hJeM', hJeM'pc⟩ := exists_pump_in hte ht2 hJeTC hJepc'
  set M't := M'.map (MulAut.conj t).toMonoidHom with hM'tdef
  obtain ⟨hM'tCe, hM'tpc⟩ := isPComponent_conj hM'Ce hM'pc hte
  have hMM' : M = M' ∨ M = M't := by
    by_contra h
    push Not at h
    have h1 : M' ≤ UnbalancedLayer.coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMCe hM'Ce hMpc hM'pc h.1
    have h2 : M't ≤ UnbalancedLayer.coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMCe hM'tCe hMpc hM'tpc h.2
    exact hfK ((sup_le h1 h2) (hJeM' hfJe))
  have hpump : Je ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
      IsPComponent 2 (Je.subgroupOf ((M ⊔ M.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set X))) := by
    rcases hMM' with h | h
    · rw [h]
      exact ⟨hJeM', hJeM'pc⟩
    · rw [h, hM'tdef, map_conj_map_conj_of_mul_self htt, sup_comm]
      exact ⟨hJeM', hJeM'pc⟩
  have heo : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact he2) he1
  have hfo : orderOf f = 2 := orderOf_eq_prime (by rw [sq]; exact hf2) hf1
  have hft : f * t = t * f := mem_centralizer_singleton_iff.mp (hJC hf)
  have hff : f * f⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
    rw [mul_inv_cancel]
    exact one_mem _
  have hffe : f * f⁻¹ ∈ UnbalancedLayer.coreActionKernel Je := by
    rw [mul_inv_cancel]
    exact one_mem _
  have hχf : ((χ ((⟨f, hfJe⟩ : ↥Je) : ↥Je ⧸ pPrimeCore 2 ↥Je) : alternatingGroup _) :
      Perm ↥((coreImage θ he).supportᶜ : Finset (Fin 9))).support.card ≤ 4 := by
    rw [← card_support_ofSubtype, hχ ⟨f, hfJe⟩ hf]
    exact hsf
  exact hMX (hFP X hnab hKP hunb hnU t J hpair θ e e he heo
    (mem_centralizer_singleton_iff.mp (hJC he)).symm heN hee hse4' Je hJeJC hJepc hinv hsubP χ
    hχ M hMCe hMpc hpump.1 hpump.2 (fun hK => hfK (hK hfJe)) f hfo hef.symm hft
    (le_normalizer hf) ⟨f, hf, hff, hsf⟩ ⟨f, hfJe, hffe, hχf⟩)

theorem signalizerLemma35Nine (hbal : Sol78.BalanceTwoComponentInput)
    (hFP : SignalizerFivePumpBalanceInput) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 9) (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9))
    {E F : Subgroup X} (hEJ : E ≤ J) (hFJ : F ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hF : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hEF : E ≤ centralizer (F : Set X)) {D DF : Finset (Fin 9)} (hD : D.card = 4)
    (hDF : DF.card = 4) (hdisj : Disjoint D DF)
    (hsE : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) ω = ω)
    (hsF : ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) ω = ω)
    {f : X} (hf : f ∈ F) (hf1 : f ≠ 1) {b : X} (hb : b ∈ E) (hb1 : b ≠ 1) :
    SolAltLit.thetaFunctor F f ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  rw [thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hF) (ne_bot_of_klein hF) hf
    hf1, thetaFunctor_eq_of_balance hbal (isElementaryAbelian_of_klein hE) (ne_bot_of_klein hE)
    hb hb1]
  have hb2 : b * b = 1 := by rw [← sq]; exact (card_sq_of_klein hE).2 b hb
  have hf2 : f * f = 1 := by rw [← sq]; exact (card_sq_of_klein hF).2 f hf
  have hbf : b * f = f * b := (mem_centralizer_iff.mp (hEF hb) f hf).symm
  have hsb := support_coreImage_subset θ hsE (hEJ hb) hb
  have hsf := support_coreImage_subset θ hsF (hFJ hf) hf
  exact core_inf_centralizer_le_of_nine hbal hFP hnab hKP hunb hnU hpair θ (hEJ hb)
    (hFJ hf) hb2 hf2 hb1 hf1 hbf ((Finset.card_le_card hsb).trans hD.le)
    ((Finset.card_le_card hsf).trans hDF.le)
    (Finset.disjoint_of_subset_left hsb (Finset.disjoint_of_subset_right hsf hdisj))

theorem signalizerSmallDegreeNineInput_of_fivePump (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hFP : SignalizerFivePumpBalanceInput) : SignalizerSmallDegreeNineInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair e E hEJ hE D hD hsupp
  exact ⟨fun y hy hyE hyK hyJ a ha ha1 b hb hb1 =>
      balanceLemma_of_nine hbal hPump hN1 hFP hnab hKP hunb hnU hpair e hEJ hE hD hsupp hy hyE
        hyK hyJ ha ha1 hb hb1,
    fun F hFJ hF hEF DF hDF hdisj hsF f hf hf1 b hb hb1 =>
      signalizerLemma35Nine hbal hFP hnab hKP hunb hnU hpair e hEJ hFJ hE hF hEF hD hDF
        hdisj hsupp hsF hf hf1 hb hb1⟩

end CFSG.ComponentClassification.SolMax
