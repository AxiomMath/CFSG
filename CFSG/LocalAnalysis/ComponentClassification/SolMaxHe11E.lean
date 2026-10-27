module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32Lift

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {X : Type} [Group X]

theorem false_of_held_pump_core (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 11) {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 11)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 11)} (hρJ : IsPermAction θ ρJ) {c e₀ : X}
    (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 11)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 11))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (htM : t ∈ normalizer (M : Set X)) (hres : CatalogueBPrimeJoin.primeResidual 2 ↥Jc = ⊤)
    (hpM : 17 ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M))
    (hE1 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc → Odd (orderOf w))
    (hE2 : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)), y * t = t * y →
      y ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf (TBLit.oddQuotAction M ⟨y, hy⟩)) ∨
        Odd (orderOf (TBLit.oddQuotAction M ⟨y * t, mul_mem hy htM⟩)))
    {L : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)}
    (hJcL : ∀ (j : X) (hjM : j ∈ M), j ∈ Jc → ((⟨j, hjM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ∈ L)
    (hM2 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc →
      ∃ hwM : w ∈ M, ((⟨w, hwM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ∈ L)
    (hL : Nat.card L < Nat.card (fixedSubgroup (TBLit.oddQuotAction M ⟨t, htM⟩))) : False := by
  classical
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
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
  have hE3 : ∃ h ∈ M, h * t = t * h ∧ ∃ (hhJ : h ∈ normalizer (J : Set X))
      (σD σF : Perm (Fin 11)), ρJ ⟨h, hhJ⟩ = σD * σF ∧
        (∀ v ∉ (coreImage θ he₀).support, σD v = v) ∧
        (∀ v ∈ (coreImage θ he₀).support, σF v = v) ∧ Perm.sign σF = -1 := by
    obtain ⟨q, hqF, hqL⟩ : ∃ q ∈ fixedSubgroup (TBLit.oddQuotAction M ⟨t, htM⟩), q ∉ L := by
      by_contra hne
      push Not at hne
      have h1 : Nat.card (fixedSubgroup (TBLit.oddQuotAction M ⟨t, htM⟩)) ≤ Nat.card L :=
        Subgroup.card_le_of_le (fun q hq => hne q hq)
      omega
    obtain ⟨h, hhM, hht, hhq⟩ := L32.exists_lift_of_mem_fixedSubgroup htM ht2 hqF
    have hhJ : h ∈ normalizer (J : Set X) := hCtN (mem_centralizer_singleton_iff.mpr hht)
    have hhc : h * c = c * h := mem_centralizer_singleton_iff.mp (hMC hhM)
    have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
      hρJ.apply_eq_coreImage_of_acts (by norm_num) hcN he₀ hce
    have hπc : ρJ ⟨h, hhJ⟩ * coreImage θ he₀ = coreImage θ he₀ * ρJ ⟨h, hhJ⟩ := by
      rw [← hρJc, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hhc
    obtain ⟨σD, σF, hsplit, hσD, hσF, -, -⟩ :=
      exists_split (coreImage θ he₀).support (apply_mem_support_iff_of_commute hπc)
    refine ⟨h, hhM, hht, hhJ, σD, σF, hsplit, hσD, hσF, ?_⟩
    rcases Int.units_eq_one_or (Perm.sign σF) with hs | hs
    · exfalso
      have hmem : σF ∈ (Perm.ofSubtype :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 11)) →* Perm (Fin 11)).range := by
        rw [Perm.mem_range_ofSubtype_iff]
        intro v hv
        change v ∈ (coreImage θ he₀).supportᶜ
        rw [Finset.mem_compl]
        intro hvD
        exact (Perm.mem_support.mp hv) (hσF v hvD)
      obtain ⟨b, hb⟩ := hmem
      have hbA : b ∈ alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 11)) := by
        rw [Perm.mem_alternatingGroup, ← Perm.sign_ofSubtype, hb, hs]
      obtain ⟨xq, hxq⟩ := χ.surjective ⟨b, hbA⟩
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective xq
      have hjJ : (j : X) ∈ J := hJcJ' j.2
      have hρj : coreImage θ hjJ = σF := by
        rw [← hχ j hjJ, hxq]
        exact hb
      have hwM : h * (j : X)⁻¹ ∈ M := mul_mem hhM (inv_mem (hJcM j.2))
      have hwJ : h * (j : X)⁻¹ ∈ normalizer (J : Set X) :=
        mul_mem hhJ (inv_mem (le_normalizer hjJ))
      have hjc : (j : X) * c = c * j :=
        mem_centralizer_singleton_iff.mp (hJcJ.trans inf_le_right j.2)
      have hwc : h * (j : X)⁻¹ * c = c * (h * (j : X)⁻¹) :=
        ((show Commute h c from hhc).mul_left (show Commute (j : X) c from hjc).inv_left).eq
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
      obtain ⟨-, hwK⟩ := L32.mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv
        hsubP χ hχ hwJ hwc hwD
      have hjt : (j : X) * t = t * j := mem_centralizer_singleton_iff.mp (hJcJ'.trans hJC j.2)
      have hwt : h * (j : X)⁻¹ * t = t * (h * (j : X)⁻¹) :=
        ((show Commute h t from hht).mul_left (show Commute (j : X) t from hjt).inv_left).eq
      obtain ⟨hwM', hwL⟩ := hM2 _ hwM hwt hwK
      apply hqL
      rw [← hhq]
      have h2 : (⟨h, hhM⟩ : ↥M) = ⟨h * (j : X)⁻¹, hwM'⟩ * ⟨(j : X), hJcM j.2⟩ :=
        Subtype.ext (by simp)
      rw [h2, QuotientGroup.mk_mul]
      exact mul_mem hwL (hJcL _ _ j.2)
    · exact hs
  have hpHe : 11 = 9 → ¬ 17 ∣ Nat.card Blueprint.NativeSporadic.He := fun h =>
    absurd h (by norm_num)
  exact L32.false_of_exceptional_pump (p := 17) hPump hN1 hnab hKP hunb hnU hpair hρJ he₀ hc htc
    hcN hce hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM htM (by norm_num) (by norm_num) hpM hpHe
    hE1 hE2 hE3

end CFSG.ComponentClassification.SolMax.He11
