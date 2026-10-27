module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.GroupTheory.MulAutCongr

public section
namespace CFSG
universe u

theorem common_pPrimeCore_quotient_transport :
∀ {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    {D B H : Subgroup G} (hDB : D ≤ B) (hDH : D ≤ H)
    (_hB : Function.Surjective
      ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥B)).comp (Subgroup.inclusion hDB)))
    (_hH : Function.Surjective
      ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hDH))),
  let fB : ↥D →* (↥B ⧸ CFSG.pPrimeCore p ↥B) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥B)).comp (Subgroup.inclusion hDB)
  let fH : ↥D →* (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hDH)
  fB.ker = CFSG.pPrimeCore p ↥D ∧
  fH.ker = CFSG.pPrimeCore p ↥D ∧
  ∃ e : (↥B ⧸ CFSG.pPrimeCore p ↥B) ≃* (↥H ⧸ CFSG.pPrimeCore p ↥H),
    (∀ d : ↥D, e (fB d) = fH d) ∧
    (∀ e' : (↥B ⧸ CFSG.pPrimeCore p ↥B) ≃* (↥H ⧸ CFSG.pPrimeCore p ↥H),
      (∀ d : ↥D, e' (fB d) = fH d) → e' = e) ∧
    (∀ (a : G)
      (_haD : a ∈ Subgroup.normalizer (D : Set G))
      (haB : a ∈ Subgroup.normalizer (B : Set G))
      (haH : a ∈ Subgroup.normalizer (H : Set G)),
      let αB : MulAut (↥B ⧸ CFSG.pPrimeCore p ↥B) :=
        MulAut.mapQuotient (CFSG.pPrimeCore p ↥B) (B.normalizerMonoidHom ⟨a, haB⟩)
      let αH : MulAut (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
        MulAut.mapQuotient (CFSG.pPrimeCore p ↥H) (H.normalizerMonoidHom ⟨a, haH⟩)
      (∀ q : (↥B ⧸ CFSG.pPrimeCore p ↥B), e (αB q) = αH (e q)) ∧
      MulAut.congr e αB = αH ∧
      (αB = 1 ↔ αH = 1) ∧
      (αB ≠ 1 ↔ αH ≠ 1) ∧
      (αB ∈ (MulAut.conj :
          (↥B ⧸ CFSG.pPrimeCore p ↥B) →* MulAut (↥B ⧸ CFSG.pPrimeCore p ↥B)).range ↔
       αH ∈ (MulAut.conj :
          (↥H ⧸ CFSG.pPrimeCore p ↥H) →* MulAut (↥H ⧸ CFSG.pPrimeCore p ↥H)).range)) := by
  classical
  intro G _ _ p _ D B H hDB hDH hB hH
  let fB : ↥D →* (↥B ⧸ CFSG.pPrimeCore p ↥B) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥B)).comp (Subgroup.inclusion hDB)
  let fH : ↥D →* (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hDH)
  have hkerB_dvd : ¬ p ∣ Nat.card fB.ker := by
    have hker_eq : fB.ker = (CFSG.pPrimeCore p ↥B).comap (Subgroup.inclusion hDB) := by
      simp only [fB]
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hcop : Nat.Coprime p (Nat.card fB.ker) := by
      rw [hker_eq]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective (CFSG.pPrimeCore p ↥B)
          (Subgroup.inclusion hDB) (Subgroup.inclusion_injective hDB))
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥B))
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.1 hcop
  have hkerH_dvd : ¬ p ∣ Nat.card fH.ker := by
    have hker_eq : fH.ker = (CFSG.pPrimeCore p ↥H).comap (Subgroup.inclusion hDH) := by
      simp only [fH]
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hcop : Nat.Coprime p (Nat.card fH.ker) := by
      rw [hker_eq]
      exact Nat.Coprime.coprime_dvd_right
        (Subgroup.card_comap_dvd_of_injective (CFSG.pPrimeCore p ↥H)
          (Subgroup.inclusion hDH) (Subgroup.inclusion_injective hDH))
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H))
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.1 hcop
  have hkerB : fB.ker = CFSG.pPrimeCore p ↥D := by
    have h := (CFSG.prime_complement_kernel_core_preimage fB hB hkerB_dvd).1
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥B) p] at h
    simpa [MonoidHom.comap_bot] using h
  have hkerH : fH.ker = CFSG.pPrimeCore p ↥D := by
    have h := (CFSG.prime_complement_kernel_core_preimage fH hH hkerH_dvd).1
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) p] at h
    simpa [MonoidHom.comap_bot] using h
  let eB : (↥D ⧸ CFSG.pPrimeCore p ↥D) ≃* (↥B ⧸ CFSG.pPrimeCore p ↥B) :=
    (QuotientGroup.quotientMulEquivOfEq hkerB).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective fB hB)
  let eH : (↥D ⧸ CFSG.pPrimeCore p ↥D) ≃* (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    (QuotientGroup.quotientMulEquivOfEq hkerH).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective fH hH)
  let e : (↥B ⧸ CFSG.pPrimeCore p ↥B) ≃* (↥H ⧸ CFSG.pPrimeCore p ↥H) := eB.symm.trans eH
  have eB_mk : ∀ d : ↥D, eB (QuotientGroup.mk d) = fB d := by
    intro d
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkerB).symm (QuotientGroup.mk d) =
        QuotientGroup.mk d := by
      rw [← QuotientGroup.quotientMulEquivOfEq_mk hkerB d, MulEquiv.symm_apply_apply]
    simp only [eB, MulEquiv.trans_apply, h1]
    exact QuotientGroup.kerLift_mk fB d
  have eH_mk : ∀ d : ↥D, eH (QuotientGroup.mk d) = fH d := by
    intro d
    have h1 : (QuotientGroup.quotientMulEquivOfEq hkerH).symm (QuotientGroup.mk d) =
        QuotientGroup.mk d := by
      rw [← QuotientGroup.quotientMulEquivOfEq_mk hkerH d, MulEquiv.symm_apply_apply]
    simp only [eH, MulEquiv.trans_apply, h1]
    exact QuotientGroup.kerLift_mk fH d
  have hformula : ∀ d : ↥D, e (fB d) = fH d := by
    intro d
    have hsymm : eB.symm (fB d) = QuotientGroup.mk d := by
      rw [← eB_mk d, MulEquiv.symm_apply_apply]
    simp only [e, MulEquiv.trans_apply, hsymm]
    exact eH_mk d
  have huniq : ∀ e' : (↥B ⧸ CFSG.pPrimeCore p ↥B) ≃*
      (↥H ⧸ CFSG.pPrimeCore p ↥H),
      (∀ d : ↥D, e' (fB d) = fH d) → e' = e := by
    intro e' he'
    ext q
    obtain ⟨d, rfl⟩ := hB q
    rw [he' d, hformula d]
  refine ⟨hkerB, hkerH, e, hformula, huniq, ?_⟩
  intro a haD haB haH
  let γ : MulAut ↥D := D.normalizerMonoidHom ⟨a, haD⟩
  let αB : MulAut (↥B ⧸ CFSG.pPrimeCore p ↥B) :=
    MulAut.mapQuotient (CFSG.pPrimeCore p ↥B) (B.normalizerMonoidHom ⟨a, haB⟩)
  let αH : MulAut (↥H ⧸ CFSG.pPrimeCore p ↥H) :=
    MulAut.mapQuotient (CFSG.pPrimeCore p ↥H) (H.normalizerMonoidHom ⟨a, haH⟩)
  change (∀ q : (↥B ⧸ CFSG.pPrimeCore p ↥B), e (αB q) = αH (e q)) ∧
    MulAut.congr e αB = αH ∧
    (αB = 1 ↔ αH = 1) ∧
    (αB ≠ 1 ↔ αH ≠ 1) ∧
    (αB ∈ (MulAut.conj :
        (↥B ⧸ CFSG.pPrimeCore p ↥B) →* MulAut (↥B ⧸ CFSG.pPrimeCore p ↥B)).range ↔
     αH ∈ (MulAut.conj :
        (↥H ⧸ CFSG.pPrimeCore p ↥H) →* MulAut (↥H ⧸ CFSG.pPrimeCore p ↥H)).range)
  have hαB : ∀ d : ↥D, αB (fB d) = fB (γ d) := by
    intro d
    have hconj : (B.normalizerMonoidHom ⟨a, haB⟩) (Subgroup.inclusion hDB d) =
        Subgroup.inclusion hDB (γ d) := by
      ext
      simp [γ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc αB (fB d) = (((B.normalizerMonoidHom ⟨a, haB⟩)
          (Subgroup.inclusion hDB d) : ↥B) : ↥B ⧸ CFSG.pPrimeCore p ↥B) := by
          simp only [αB, fB, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
          exact MulAut.mapQuotient_mk _ _ _
      _ = (((Subgroup.inclusion hDB (γ d) : ↥B) : ↥B ⧸ CFSG.pPrimeCore p ↥B)) := by
          rw [hconj]
      _ = fB (γ d) := rfl
  have hαH : ∀ d : ↥D, αH (fH d) = fH (γ d) := by
    intro d
    have hconj : (H.normalizerMonoidHom ⟨a, haH⟩) (Subgroup.inclusion hDH d) =
        Subgroup.inclusion hDH (γ d) := by
      ext
      simp [γ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    calc αH (fH d) = (((H.normalizerMonoidHom ⟨a, haH⟩)
          (Subgroup.inclusion hDH d) : ↥H) : ↥H ⧸ CFSG.pPrimeCore p ↥H) := by
          simp only [αH, fH, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
          exact MulAut.mapQuotient_mk _ _ _
      _ = (((Subgroup.inclusion hDH (γ d) : ↥H) : ↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
          rw [hconj]
      _ = fH (γ d) := rfl
  have hequiv : ∀ q : (↥B ⧸ CFSG.pPrimeCore p ↥B), e (αB q) = αH (e q) := by
    intro q
    obtain ⟨d, rfl⟩ := hB q
    calc e (αB (fB d)) = e (fB (γ d)) := by rw [hαB d]
      _ = fH (γ d) := hformula (γ d)
      _ = αH (fH d) := by rw [hαH d]
      _ = αH (e (fB d)) := by rw [hformula d]
  have hcongr : MulAut.congr e αB = αH := by
    ext x
    obtain ⟨q, rfl⟩ := e.surjective x
    calc MulAut.congr e αB (e q) = e (αB q) := by
          simp [MulAut.congr_apply]
      _ = αH (e q) := hequiv q
  have htriv : (αB = 1 ↔ αH = 1) := by
    constructor
    · intro h
      have h' := congrArg (MulAut.congr e) h
      rw [hcongr, map_one] at h'
      exact h'
    · intro h
      apply (MulAut.congr e).injective
      rw [hcongr, h, map_one]
  have hne : (αB ≠ 1 ↔ αH ≠ 1) := not_congr htriv
  have hinner : (αB ∈ (MulAut.conj :
        (↥B ⧸ CFSG.pPrimeCore p ↥B) →* MulAut (↥B ⧸ CFSG.pPrimeCore p ↥B)).range ↔
      αH ∈ (MulAut.conj :
        (↥H ⧸ CFSG.pPrimeCore p ↥H) →* MulAut (↥H ⧸ CFSG.pPrimeCore p ↥H)).range) := by
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨e b, ?_⟩
      calc MulAut.conj (e b) = MulAut.congr e (MulAut.conj b) :=
            (CFSG.mulAut_congr_conj e b).symm
        _ = MulAut.congr e αB := by rw [hb]
        _ = αH := hcongr
    · rintro ⟨c, hc⟩
      refine ⟨e.symm c, ?_⟩
      apply (MulAut.congr e).injective
      calc MulAut.congr e (MulAut.conj (e.symm c))
          = MulAut.conj (e (e.symm c)) := CFSG.mulAut_congr_conj e (e.symm c)
        _ = MulAut.conj c := by simp
        _ = αH := hc
        _ = MulAut.congr e αB := hcongr.symm
  exact ⟨hequiv, hcongr, htriv, hne, hinner⟩

end CFSG
