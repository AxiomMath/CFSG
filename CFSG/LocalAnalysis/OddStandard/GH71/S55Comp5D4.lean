module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5ECom
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Tr
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Pair
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5D4C
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Gen
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityCommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 C5

theorem prime_dvd_ordTrialityD4_cases {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q)
    (h : p ∣ CFSG.Open.ordTrialityD4 q) :
    p ∣ q ^ 2 - 1 ∨ p ∣ q ^ 2 + q + 1 ∨ p ∣ q ^ 2 - q + 1 ∨ p ∣ q ^ 4 - q ^ 2 + 1 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have e8 : q ^ 8 + q ^ 4 + 1 = (q ^ 2 + q + 1) * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) := by
    zify [h2, h3]
    ring
  have e6 : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) := by
    zify [h1, h2, h6]
    ring
  rw [CFSG.Open.ordTrialityD4, e8, e6] at h
  simp only [Nat.Prime.dvd_mul hp] at h
  rcases h with (((h | (h | h) | h) | (h | h) | h) | h)
  · exact absurd (hp.dvd_of_dvd_pow h) hpq
  all_goals tauto

theorem not_dvd_d4_index {p q k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ q)
    (h1 : p ∣ q ^ 2 - 1) (hq : 1 ≤ q) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    ¬ p ∣ q ^ 8 * (q ^ 8 + q ^ 4 + 1) * k := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpq (hp.dvd_of_dvd_pow h)
    · have he : q ^ 8 + q ^ 4 + 1 = (q ^ 2 - 1) * (q ^ 6 + q ^ 4 + 2 * q ^ 2 + 2) + 3 := by
        have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
        zify [this]
        ring
      rw [he] at h
      have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem d4_card_fixSubfield {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (fixSubfield σ) = ℓ ^ f := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  have hσfr : σ = fr ^ f := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr f c]
  have hσo : orderOf σ = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 3 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ
    (by omega : 1 ≤ 3 * f) hK3 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard


variable {r : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4_comp5_block {p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrp : r ≠ p) (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (r ^ f))
    (h1 : p ∣ (r ^ f) ^ 2 - 1) {y : 𝒞} (hy : orderOf y = p) (hyr : RFree r y) :
    Comp5Concl r y := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hpq : ¬ p ∣ r ^ f := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1
    (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨ι, η, hι, hη, hc⟩ :=
    CFSG.RankThree.Chevalley.triality_D4_commuting_faithful_extension_and_fixed_SL2 K σ hσ3
  have : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨k, hk1, hk2, hidx⟩ := index_mul_of_commute ι η hι hη hc
  have hk2' : k ≤ 2 := hk2.trans card_center_SL2_le
  rw [CFSG.ClassicalInvolution.card_graphFixedRootGroup_D4_of_ne_two hr hr2 hf hK σ.toRingHom hσ,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK,
    d4_card_fixSubfield hr hf hK σ hσ] at hidx
  set q := r ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hr.pos
  have hq2 : 2 ≤ q := by have := three_le_pow hr hr2 hf; omega
  have hind : (ι.range ⊔ η.range).index = q ^ 8 * (q ^ 8 + q ^ 4 + 1) * k := by
    have hq2' : 0 < q ^ 2 - 1 := by
      have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
    have hq6 : 0 < (q ^ 3) ^ 2 - 1 := by
      have : 1 < (q ^ 3) ^ 2 :=
        Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by norm_num) (by omega))
      omega
    have hpos : 0 < q ^ 3 * ((q ^ 3) ^ 2 - 1) * (q * (q ^ 2 - 1)) :=
      Nat.mul_pos (Nat.mul_pos (by positivity) hq6) (Nat.mul_pos (by omega) hq2')
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hidx, CFSG.Open.ordTrialityD4]
    have h1' : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
    have h6' : 1 ≤ (q ^ 3) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hq1)
    zify [h1', h6, h6']
    ring
  have hM : ¬ p ∣ (ι.range ⊔ η.range).index := by
    rw [hind]
    exact not_dvd_d4_index hp hp5 hpq h1 hq1 hk1 hk2'
  have hK' : Nat.card K = r ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hq27 : r ^ (3 * f) ≠ 3 := by
    rw [← hK', hK]
    intro h
    have h3 : 3 ≤ q := three_le_pow hr hr2 hf
    have : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left h3 3
    omega
  obtain ⟨hQ, hC, hrL⟩ := typ_sl hr hr2 (by omega : 1 ≤ 3 * f) (Or.inl rfl) hK' (Or.inr hq27)
    (MonoidHom.ofInjective hι)
  refine comp5Concl_of_block hM (le_normalizer_of_commute ι η hc) ?_ hQ hC hrL hy hyr
  intro htop
  have h1M : (ι.range ⊔ η.range).index = 1 := by
    rw [htop, top_sup_eq, index_top]
  rw [hind] at h1M
  have h4 : q ^ 8 ∣ 1 := Dvd.intro _ (by rw [← mul_assoc]; exact h1M)
  have h5 : 1 < q ^ 8 := Nat.one_lt_pow (by norm_num) (by omega)
  have := Nat.le_of_dvd one_pos h4
  omega

theorem d4_no_two_p {p f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (r ^ f)) (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ (r ^ f) ^ 4 - (r ^ f) ^ 2 + 1) (w : 𝒞) : orderOf w ≠ 2 * p := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨T, -, -, hT⟩ :=
    CFSG.RankThree.Chevalley.triality_cyclotomic_twelve_torus_and_prime_centralizers hr hf K hK σ
      hσ
  obtain ⟨-, -, hx⟩ := hT p hp hp3 hpd
  refine no_two_p_of_odd_centralizer hp (fun x hxp => ?_) w
  obtain ⟨-, -, -, -, hodd⟩ := hx x hxp
  exact hodd

theorem d4_comp5 {p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrp : r ≠ p) (hf : 1 ≤ f) (hK : Nat.card K = (r ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (r ^ f))
    (hR : NoR 2 𝒞) {y : 𝒞} (g : 𝒞) (hy : orderOf y = p) (hyr : RFree r y)
    (hJ : PairSL2 p y g) : Comp5Concl r y := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hpq : ¬ p ∣ r ^ f := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1
    (hp.dvd_of_dvd_pow h)).symm
  have hpC : p ∣ Nat.card 𝒞 := hy ▸ orderOf_dvd_natCard y
  rw [CFSG.ClassicalInvolution.card_graphFixedRootGroup_D4_of_ne_two hr hr2 hf hK σ.toRingHom hσ]
    at hpC
  have hq1 : 1 ≤ r ^ f := Nat.one_le_pow _ _ hr.pos
  rcases prime_dvd_ordTrialityD4_cases hp hq1 hpq hpC with h1 | h2 | h3 | h4
  · exact d4_comp5_block σ hr hr2 hp hp5 hrp hf hK hσ h1 hy hyr
  · exact d4C_comp5 hr hr2 hp hp5 hf hK σ hσ (Or.inl rfl) (d := (r ^ f) ^ 2 + r ^ f + 1)
      (by push_cast; ring) h2 hy hyr
  · have h2' : r ^ f ≤ (r ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact d4C_comp5 hr hr2 hp hp5 hf hK σ hσ (Or.inr rfl) (d := (r ^ f) ^ 2 - r ^ f + 1)
      (by push_cast [h2']; ring) h3 hy hyr
  · exact absurd hJ (not_pairSL2_of_no_two_p hp (by omega)
      (d4_no_two_p σ hr hf hK hσ hp (by omega) h4) hR y g)


theorem comp5_fd4d : Comp5 FD4d := by
  refine comp5_of fun r p Y _ _ hr hr2 hp hp5 hrp hY y g hy hyr hJ => ?_
  obtain ⟨f, hf, hm⟩ := hY
  have hR := noR_two_of_lieModel_D4 hr hr2 hf hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 hr hf (twistedChevalleyModel_of_lieModel hm)
  exact comp5Concl_of_mulEquiv e (fun hy' hyr' hJ' =>
    d4_comp5 σ hr hr2 hp hp5 hrp hf hK hσ ((noR_congr e).1 hR) (e g) hy' hyr' hJ') hy hyr hJ

end CFSG.OddStandard.GH71.S55
