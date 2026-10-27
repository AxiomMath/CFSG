module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieHalf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36EvenOddCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem even_hat_lieModel (h : Config G p w v L K) :
    ∃ k : ℕ, 1 ≤ k ∧ 5 ≤ p ^ k ∧ IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) ∧
      Blueprint.LieModel (↥(hatOf K L) ⧸ Open.fusionZStar ↥(hatOf K L)) .PSL 2 p k := by
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  have hc := h.isTwoComponentIn_hat h.compLK
  have hBq : IsQuasisimple (↥(hatOf K L) ⧸ pPrimeCore 2 ↥(hatOf K L)) := hc.2.2.2
  have : Nontrivial (↥(hatOf K L) ⧸ pPrimeCore 2 ↥(hatOf K L)) :=
    LocalCores.isQuasisimple_nontrivial hBq
  let f : ↥L →* ↥(hatOf K L) ⧸ pPrimeCore 2 ↥(hatOf K L) :=
    (QuotientGroup.mk' _).comp (hatHom h.L_le)
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (hatHom_surjective h.L_le)
  obtain ⟨e₁⟩ := h.nonempty_centralQuot_of_surjective f hf
    (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨e₂⟩ := nonempty_fusionZStar_quotient_equiv ↥(hatOf K L)
  exact ⟨k, hk, hs5, hLsl, GSThmB.OddQuot.lieModel_of_equiv (e₁.trans e₂.symm) hQm⟩

theorem orderOf_quotAut_tau (h : Config G p w v L K) : orderOf (quotAut h.tau) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ h.quotAut_tau_ne_one
  rw [pow_two]
  ext y
  exact h.quotAut_tau_sq y

theorem even_not_inner
    (h : Config G p w v L K) {t : StatedLieTag} {n f : ℕ}
    (hm : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) t n 2 f) :
    quotAut h.tau ∉ innAut ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
  rintro ⟨y, hy⟩
  have hq := h.quasisimple_quot
  have : IsSimpleGroup ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := hq.2.1
  have hZ := CatLeaf.center_eq_bot_of_simple hq.2.2
  have hfix : fixedPoints (quotAut h.tau) = centralizer {y} := by
    ext z
    rw [mem_fixedPoints, ← hy, MulAut.conj_apply, mem_centralizer_singleton_iff]
    constructor
    · intro hz
      calc z * y = y * z * y⁻¹ * y := by rw [hz]
        _ = y * z := by group
    · intro hz
      rw [← hz]
      group
  have hyy : y * y = 1 := by
    have hc : y * y ∈ center ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
      rw [mem_center_iff]
      intro z
      have h1 := h.quotAut_tau_sq z
      rw [← hy] at h1
      simp only [MulAut.conj_apply] at h1
      calc z * (y * y) = y * (y * z * y⁻¹) * y⁻¹ * (y * y) := by rw [h1]
        _ = y * y * z := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have hy1 : y ≠ 1 := fun h1 => h.quotAut_tau_ne_one (by rw [← hy, h1, map_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
  have hO : pPrimeCore 2 ↥(fixedPoints (quotAut h.tau)) = ⊥ := by
    rw [hfix]
    exact N36.EvenOddCore.evenLieInvolutionOddCoreFact_holds _ t n f hm y hy2
  obtain ⟨hcomp, -⟩ := h.isComponent_hat hO
  exact CatLeaf.involutionCentralizersComponentFree_of_evenLieType
    ⟨t, n, f, N36.admissible_of_lieModel' hm, hm⟩ y hy2 _
    (CatLeaf.isComponent_map_mulEquiv (MulEquiv.subgroupCongr hfix) hcomp)

theorem even_false_of_noOddPSL2 (h : Config G p w v L K)
    (hY : EvenCover.NoOddPSL2 ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)))
    (hout : quotAut h.tau ∉ innAut ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) :
    False := by
  obtain ⟨k, -, -, -, hLm⟩ := h.even_hat_lieModel
  have hc := h.isTwoComponentIn_hat h.compLK
  have hP := (isTwoComponentIn_iff hc.1).mp hc
  obtain ⟨e⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hc.1)
  exact hY (quotAut h.tau) h.orderOf_quotAut_tau hout _ hP p k h.ne_two
    (GSThmB.OddQuot.lieModel_of_equiv e.symm hLm)

theorem even_false_of_oddModel
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h : Config G p w v L K) {t : StatedLieTag}
    {n r f : ℕ} (hr2 : r ≠ 2) (hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n r f) :
    False := by
  obtain ⟨n', k, hn, hm, hne⟩ := h.partialCover_of_oddLie hGLS hGA hr2 hL
  obtain ⟨rfl, -⟩ := h.four_of_partialCover hn hm
  rcases hm with hm | hm
  · exact h.false_of_psl4 hGA hm hne
  · exact h.false_of_psu4 hGA hm hne

end Config

end CFSG.ComponentClassification.HarrisLit.L35
