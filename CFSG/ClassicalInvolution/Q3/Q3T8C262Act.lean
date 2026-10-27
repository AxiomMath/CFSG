module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Type
public import CFSG.ClassicalInvolution.Q3.Q3T8Dich
public import CFSG.ClassicalInvolution.Q3.Q3T8C262A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

section Act


theorem s26Act_of_sec (h3 : C26_3_S4) : S26Act := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hS4 P hPD M hMΩ hPM hMK hMJ u hu
  obtain ⟨b, c, n, hn, hbo, hco, hbu, hct, hbW, hcW, hcT, hbK, hbJ, hbc, huW, htW, hfac⟩ :=
    s26_setup hs hPD hMΩ hPM hMK hMJ hu
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hTJ : T ≤ J := hs.hT.2.1
  have hbX : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := s26_conjSub_omegaNbrGen hΩ hbK
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hbN : b ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbX
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have hcJ : c ∈ J := hTJ hcT
  have hcX : c ∈ X := hJX hcJ
  have htX : t ∈ X := hJX hs.ht.mem
  have huN : u ∈ Subgroup.normalizer (X : Set G) :=
    hbu ▸ (Subgroup.normalizer (X : Set G)).pow_mem hbN _
  have htN : t ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer htX
  let β : MulAut (↥X ⧸ classicalInvolutionOddCore ↥X) := s26Act X ⟨b, hbN⟩
  let ū : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  let tbar : ↥X ⧸ classicalInvolutionOddCore ↥X :=
    ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
  have hβū : β ū = ū := by
    refine s26Act_mk X ⟨b, hbN⟩ ⟨c, hcX⟩ ⟨c, hcX⟩ ?_
    show c = b * c * b⁻¹
    rw [hbc]
    group
  have hb2 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 ^ (n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hbo]
    exact pow_orderOf_eq_one b
  have hβ2 : β ^ 2 ^ (n + 1) = 1 := by
    rw [← map_pow, hb2, map_one]
  have hβu : β ^ 2 ^ n = s26Act X ⟨u, huN⟩ := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hbu
  have hūt : ū ^ 2 ^ n = tbar := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ n =
      ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X)
    rw [← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hct
  have ht1 : tbar ≠ 1 := by
    intro h1
    have h2 : (⟨t, htX⟩ : ↥X) ∈ classicalInvolutionOddCore ↥X := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : t ∈ oddCoreOf X := mem_oddCoreOf_iff.mpr ⟨htX, h2⟩
    exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) h3
      (isPGroup_zpowers_of_mul_self_eq_one hs.ht.sq hs.ht.ne_one))
  have hū2 : ū ^ 2 ^ (n + 1) = 1 := by
    show ((⟨c, hcX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ (n + 1) = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcX⟩ : ↥X) ^ 2 ^ (n + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hco]
      exact pow_orderOf_eq_one c
    rw [this]
    rfl
  have hord : orderOf ū = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hūt]; exact ht1) hū2
  have hJ' : (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      oddQuotientFamily (restrictFamily Ω X) := ⟨J.subgroupOf X, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩
  have hūJ' : ū ∈ (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) :=
    ⟨⟨c, hcX⟩, hcJ, rfl⟩
  have hdich : β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj tbar := by
    rcases h3 G Ω K J S R T W z t hs hdisc hS4 with ⟨D, hD⟩ | ⟨D, hD⟩
    · have := s26_dich_of_sysDataU D (Or.inl hD) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
    · have := s26_dich_of_sysDataU D (Or.inr hD) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
  have hact : s26Act X ⟨t, htN⟩ = MulAut.conj tbar := s26Act_eq_conj X ⟨t, htX⟩
  rw [hβu] at hdich
  rcases hdich with h | h
  · refine ⟨0, by norm_num, fun x hx => ?_⟩
    have := s26_comm_mem_oddCore_of_act_eq_one X ⟨u, huN⟩ h hx
    simpa using this
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have h1 : s26Act X (⟨u, huN⟩ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, h, hact, ← map_mul]
      have : tbar * tbar = 1 := by
        show ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) *
          ((⟨t, htX⟩ : ↥X) : ↥X ⧸ classicalInvolutionOddCore ↥X) = 1
        rw [← QuotientGroup.mk_mul]
        have : (⟨t, htX⟩ : ↥X) * ⟨t, htX⟩ = 1 := Subtype.ext hs.ht.sq
        rw [this]
        rfl
      rw [this, map_one]
    have := s26_comm_mem_oddCore_of_act_eq_one X
      ⟨u * t, (Subgroup.normalizer (X : Set G)).mul_mem huN htN⟩ h1 hx
    simpa using this

theorem c26_2_u_of_sec (h3 : C26_3_S4) : C26_2_u :=
  c26_2_u_of_act (s26Act_of_sec h3)

theorem c26_2_of_x (hB : S26XProper) (hE : S26XEdgeless) (hT : S26XTop) (hZ : S26XMuZ2) :
    C26_2 :=
  c26_2_of_u (c26_2_u_of_sec (c26_3_S4_of_x hB hE hT hZ))

end Act

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
