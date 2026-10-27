module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4P01
public import CFSG.ClassicalInvolution.Q3.Q3AMLY4P02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
open scoped commutatorElement MatrixGroups

section Act


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_act_of_layerL3M11 (hs : Std8 Ω K J S R T W z t)
    (hshape : LayerL3 Ω K z ∨ LayerM11 Ω K z) {P M : Subgroup G} (hPD : P ∈ DSet Ω W)
    (hMΩ : M ∈ Ω) (hPM : P ≤ M) (hMK : M ≠ K) (hMJ : M ≠ J) {u : G}
    (hu : IsUniqueInvolution M u) :
    ∃ ε : ℕ, ε ≤ 1 ∧
      ∀ x ∈ nbrLayer Ω K z, ⁅u * t ^ ε, x⁆ ∈ oddCoreOf (nbrLayer Ω K z) := by
  obtain ⟨b, c, n, hn, hbo, hco, hbu, hct, hbW, hcW, hcT, hbK, hbJ, hbc, huW, htW, hfac⟩ :=
    s26_setup hs hPD hMΩ hPM hMK hMJ hu
  have hbN : b ∈ Subgroup.normalizer ((nbrLayer Ω K z : Subgroup G) : Set G) :=
    centralizer_le_normalizer_nbrLayer_of_std8 hs hs.stand.mem hs.hz
      (mem_centralizer_of_conjSub_eq hs.hz hbK)
  have hcJ : c ∈ exactCore3 z J := layerT_le_exactCore hs hcT
  set Y : Subgroup G := nbrLayer Ω K z with hYdef
  have hcY : c ∈ Y := exactCore3_le_nbrLayer hs.hJ hcJ
  have htY : t ∈ Y := by
    rw [← hct]
    exact Y.pow_mem hcY _
  have huN : u ∈ Subgroup.normalizer (Y : Set G) :=
    hbu ▸ (Subgroup.normalizer (Y : Set G)).pow_mem hbN _
  have htN : t ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer htY
  let β : MulAut (↥Y ⧸ classicalInvolutionOddCore ↥Y) := s26Act Y ⟨b, hbN⟩
  let ū : ↥Y ⧸ classicalInvolutionOddCore ↥Y :=
    ((⟨c, hcY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y)
  let tbar : ↥Y ⧸ classicalInvolutionOddCore ↥Y :=
    ((⟨t, htY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y)
  have hβū : β ū = ū := by
    refine s26Act_mk Y ⟨b, hbN⟩ ⟨c, hcY⟩ ⟨c, hcY⟩ ?_
    show c = b * c * b⁻¹
    rw [hbc]
    group
  have hb2 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 2 ^ (n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hbo]
    exact pow_orderOf_eq_one b
  have hβ2 : β ^ 2 ^ (n + 1) = 1 := by
    rw [← map_pow, hb2, map_one]
  have hβu : β ^ 2 ^ n = s26Act Y ⟨u, huN⟩ := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hbu
  have hūt : ū ^ 2 ^ n = tbar := by
    show ((⟨c, hcY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ^ 2 ^ n =
      ((⟨t, htY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y)
    rw [← QuotientGroup.mk_pow]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hct
  have ht1 : tbar ≠ 1 := by
    intro h1
    have h2 : (⟨t, htY⟩ : ↥Y) ∈ classicalInvolutionOddCore ↥Y := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : t ∈ oddCoreOf Y := mem_oddCoreOf_iff.mpr ⟨htY, h2⟩
    exact hs.ht.ne_one (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h3
      (isPGroup_zpowers_of_mul_self_eq_one hs.ht.sq hs.ht.ne_one))
  have hū2 : ū ^ 2 ^ (n + 1) = 1 := by
    show ((⟨c, hcY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) ^ 2 ^ (n + 1) = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨c, hcY⟩ : ↥Y) ^ 2 ^ (n + 1) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hco]
      exact pow_orderOf_eq_one c
    rw [this]
    rfl
  have hord : orderOf ū = 2 ^ (n + 1) :=
    orderOf_eq_prime_pow (by rw [hūt]; exact ht1) hū2
  have hJ' : modOddIn Y (exactCore3 z J) ∈ layerFam Ω K z := exactCore3_mem_layerFam hs.hJ
  have hūJ' : ū ∈ modOddIn Y (exactCore3 z J) :=
    ⟨⟨c, hcY⟩, Subgroup.mem_subgroupOf.mpr hcJ, rfl⟩
  have hdich : β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj tbar := by
    rcases hshape with ⟨ι, -, D, i₀, hone, hk⟩ | ⟨ι, -, D, i₀, hone, hk⟩
    · have := dich_of_lieSystemData3 D hone (Or.inl hk) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
    · have := dich_of_lieSystemData3 D hone (Or.inr hk) hJ' hūJ' hn hord hfac β hβū hβ2
      rwa [hūt] at this
  have hact : s26Act Y ⟨t, htN⟩ = MulAut.conj tbar := s26Act_eq_conj Y ⟨t, htY⟩
  rw [hβu] at hdich
  rcases hdich with h | h
  · refine ⟨0, by norm_num, fun x hx => ?_⟩
    have := s26_comm_mem_oddCore_of_act_eq_one Y ⟨u, huN⟩ h hx
    simpa using this
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have h1 : s26Act Y (⟨u, huN⟩ * ⟨t, htN⟩) = 1 := by
      rw [map_mul, h, hact, ← map_mul]
      have : tbar * tbar = 1 := by
        show ((⟨t, htY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) *
          ((⟨t, htY⟩ : ↥Y) : ↥Y ⧸ classicalInvolutionOddCore ↥Y) = 1
        rw [← QuotientGroup.mk_mul]
        have : (⟨t, htY⟩ : ↥Y) * ⟨t, htY⟩ = 1 := Subtype.ext hs.ht.sq
        rw [this]
        rfl
      rw [this, map_one]
    have := s26_comm_mem_oddCore_of_act_eq_one Y
      ⟨u * t, (Subgroup.normalizer (Y : Set G)).mul_mem huN htN⟩ h1 hx
    simpa using this

end Act

end CFSG.ClassicalInvolution.Q3.Q3AM
