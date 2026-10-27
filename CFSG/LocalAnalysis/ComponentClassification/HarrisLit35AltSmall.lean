module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneTools
public import CFSG.LocalAnalysis.SteinbergCEAltEvenCenterQuaternionCover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

@[expose] def wbar (h : Config G p w v L K) : ↥K ⧸ pPrimeCore 2 ↥K :=
  QuotientGroup.mk (⟨w, h.w_mem_K⟩ : ↥K)

theorem wbar_mem_center (h : Config G p w v L K) :
    h.wbar ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
  rw [mem_center_iff]
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hk : (k : G) * w = w * k := mem_centralizer_singleton_iff.mp (h.compK.1 k.2)
  have hk' : k * (⟨w, h.w_mem_K⟩ : ↥K) = ⟨w, h.w_mem_K⟩ * k := Subtype.ext hk
  unfold wbar
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hk']

theorem orderOf_wbar (h : Config G p w v L K) : orderOf h.wbar = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw2 : (⟨w, h.w_mem_K⟩ : ↥K) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    have h1 := pow_orderOf_eq_one w
    rwa [h.orderOf_w] at h1
  refine orderOf_eq_prime ?_ ?_
  · unfold wbar
    rw [← QuotientGroup.mk_pow, hw2, QuotientGroup.mk_one]
  · intro h1
    unfold wbar at h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_mk, h.orderOf_w] at hdvd
    exact absurd hdvd (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)

theorem even_card_center (h : Config G p w v L K) :
    Even (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) := by
  have h2 : orderOf (⟨h.wbar, h.wbar_mem_center⟩ : ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.orderOf_wbar
  have hd := orderOf_dvd_natCard (⟨h.wbar, h.wbar_mem_center⟩ :
    ↥(center (↥K ⧸ pPrimeCore 2 ↥K)))
  rw [h2] at hd
  exact even_iff_two_dvd.mpr hd

theorem false_of_pRank_le_one
    (hCI : GSLit.ClassicalInvolutionInput) (h : Config G p w v L K)
    (hr : CFSG.pRank 2 ↥K ≤ 1) : False := by
  have := h.simple
  obtain ⟨t, n, q, f, -, -, -, hm⟩ := FooteLit.oddLieType_of_classical_twoComponent hCI
    h.nonabelian h.orderOf_w h.compK.1 ((isTwoComponentIn_iff h.compK.1).mp h.compK) h.w_mem_K hr
  exact h.not_catalog (Blueprint.lieModel_catalog G t n q f hm)

theorem false_of_alt_small
    (hCI : GSLit.ClassicalInvolutionInput) (h : Config G p w v L K) {m : ℕ} (hm5 : 5 ≤ m)
    (hm7 : m ≤ 7) (e : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin m)) : False := by
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  obtain ⟨-, z, hz2, huniq, -⟩ := LocalAnalysis.small_alternating_even_center_exact_quaternion_cover
    hm5 hm7 h.quasisimple_quot h.even_card_center (eZ.symm.trans e)
  have hrY : CFSG.pRank 2 (↥K ⧸ pPrimeCore 2 ↥K) ≤ 1 :=
    UnbalancedAltSeven.pRank_le_one_of_unique hz2 huniq
  rw [FooteLit.pRank_quotient_pPrimeCore] at hrY
  exact h.false_of_pRank_le_one hCI hrY

end Config

end CFSG.ComponentClassification.HarrisLit.L35
