module

public import CFSG.ClassicalInvolution.Q3.Q3KBPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3KB
open scoped MatrixGroups

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_le_of_card_modOddIn {Y K : Subgroup G} (hKY : K ≤ Y)
    (h : Nat.card (modOddIn Y K) = Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K)) :
    oddCoreIn K ≤ oddCoreIn Y := by
  set f : ↥K →* ↥Y ⧸ classicalInvolutionOddCore ↥Y := toOddQuot hKY with hf
  have hrange : f.range = modOddIn Y K := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKY k, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
  have hker : f.ker = (classicalInvolutionOddCore ↥Y).comap (Subgroup.inclusion hKY) :=
    ker_toOddQuot hKY
  have hkerodd : Odd (Nat.card f.ker) := by
    rw [hker]
    exact (CFSG.ComponentClassification.OddCore.odd_card Y).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKY))
  have hkerle : f.ker ≤ classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.maximal K f.ker inferInstance hkerodd
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore ↥K)
  have hpos : 0 < Nat.card (↥K ⧸ classicalInvolutionOddCore ↥K) := Nat.card_pos
  rw [h] at h1
  have hcard : Nat.card (classicalInvolutionOddCore ↥K) ≤ Nat.card f.ker := by
    have := Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
    omega
  have heq : f.ker = classicalInvolutionOddCore ↥K := Subgroup.eq_of_le_of_card_ge hkerle hcard
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k ∈ f.ker := by
    rw [heq]
    exact hk
  rw [hker] at hk'
  exact mem_oddCoreIn_of_mem_classicalInvolutionOddCore (J := Y) (y := Subgroup.inclusion hKY k) hk'

end OddCore

section Section

variable {G : Type} [Group G] [Finite G]

theorem mul_mem_oddCoreIn_of_modOddIn_eq3_in {X K K' : Subgroup G} {z z' : G}
    (hK : IsClassicalMember3In X K z) (hK' : IsClassicalMember3In X K' z')
    (h : modOddIn X K = modOddIn X K') : z * z' ∈ oddCoreIn X := by
  obtain ⟨hzX, hK0⟩ := hK
  obtain ⟨hz'X, hK0'⟩ := hK'
  have h1 := hK0.map_oddQuotient
  have h2 := hK0'.map_oddQuotient
  unfold modOddIn at h
  rw [← h] at h2
  have h3 := involution_unique3 h1 h2
  have h4 := QuotientGroup.eq.mp h3
  refine ⟨_, h4, ?_⟩
  have hsq : (⟨z, hzX⟩ : ↥X) * ⟨z, hzX⟩ = 1 := hK0.isCentralInvolution.sq
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (congrArg Subtype.val hsq)
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hz]

end Section

section M11

open CFSG.Blueprint

variable {R R' : Subgroup ↥NativeSporadic.M11} {z z' : ↥NativeSporadic.M11}

theorem m11_eq_of_le_centralizer (h : IsClassicalMember3 R z) (h' : IsClassicalMember3 R' z')
    (hR'C : R' ≤ Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11)) : R = R' := by
  have hRC : R ≤ Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11) :=
    isSubnormal_le h.subnormal
  have hC : Nat.card (Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11)) ≤ 48 :=
    card_centralizer_le_of_orderOf_eq_two h.orderOf_eq_two
  have hR : Nat.card R = 24 := h.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  have hR' : Nat.card R' = 24 := h'.card_eq_of_mulEquiv_m11 (MulEquiv.refl _)
  obtain ⟨eR⟩ := Uniform.m11_member_equiv h
  set C := Subgroup.centralizer ({z} : Set ↥NativeSporadic.M11) with hCdef
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hiR : R.relIndex C * 24 = Nat.card C := by
    have := Subgroup.relIndex_mul_card R C
    rwa [inf_eq_left.mpr hRC, hR] at this
  have hiR' : R'.relIndex C * 24 = Nat.card C := by
    have := Subgroup.relIndex_mul_card R' C
    rwa [inf_eq_left.mpr hR'C, hR'] at this
  have hiI : (R ⊓ R').relIndex C * Nat.card ↥(R ⊓ R') = Nat.card C := by
    have := Subgroup.relIndex_mul_card (R ⊓ R') C
    rwa [inf_eq_left.mpr (inf_le_left.trans hRC)] at this
  have hle : (R ⊓ R').relIndex C ≤ R.relIndex C * R'.relIndex C := Subgroup.relIndex_inf_le
  have hdvd : Nat.card ↥(R ⊓ R') ∣ 24 := hR ▸ Subgroup.card_dvd_of_le inf_le_left
  have hcases : Nat.card ↥(R ⊓ R') = 12 ∨ Nat.card ↥(R ⊓ R') = 24 := by
    set a := R.relIndex C
    set r := (R ⊓ R').relIndex C
    set n := Nat.card ↥(R ⊓ R')
    have ha : R'.relIndex C = a := by omega
    rw [ha] at hle
    have ha2 : a ≤ 2 := by omega
    have ha0 : 0 < a := by omega
    have hr4 : r ≤ 4 := by nlinarith
    have hn0 : 0 < n := Nat.card_pos
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, zero_mul] at hiI
        omega
      · exact h0
    have hn24 : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
    have hn12 : 12 ≤ n := by
      interval_cases a <;> interval_cases r <;> omega
    interval_cases n <;> omega
  rcases hcases with h12 | h24
  · exfalso
    have hle' : R ⊓ R' ≤ R := inf_le_left
    have hc1 : Nat.card ((R ⊓ R').subgroupOf R) = 12 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv]
      exact h12
    have hc2 : Nat.card (((R ⊓ R').subgroupOf R).map eR.toMonoidHom) = 12 := by
      rw [Subgroup.card_map_of_injective eR.injective]
      exact hc1
    exact Uniform.sl2Three_no_card_twelve _ hc2
  · have h1 : R ⊓ R' = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h24, hR])
    have hRR' : R ≤ R' := h1 ▸ inf_le_right
    exact Subgroup.eq_of_le_of_card_ge hRR' (by rw [hR, hR'])

theorem false_of_pair_m11_weak {X : Type} [Group X] {c : CompData} (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) (hc : c = CompData.m11) {R₁ R₂ : Subgroup c.G}
    (hR₁ : R₁ ∈ c.fund) (hR₂ : R₂ ∈ c.fund) {ζ ξ : X} (hζ : ζ ∈ R₁.map ψ) (hξ : ξ ∈ R₂.map ψ)
    (hζ2 : ζ * ζ = 1) (hξ2 : ξ * ξ = 1) (hζ1 : ζ ≠ 1) (hξ1 : ξ ≠ 1) (hζξ : ζ ≠ ξ)
    (hζR₁ : ∀ y ∈ R₁.map ψ, ζ * y = y * ζ) (hξR₂ : ∀ y ∈ R₂.map ψ, ξ * y = y * ξ)
    (hζR₂ : ∀ y ∈ R₂.map ψ, ζ * y = y * ζ) : False := by
  subst hc
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_m11_eq_bot m11Facts).le
  obtain ⟨u, huR, hu⟩ := hζ
  obtain ⟨v, hvR, hv⟩ := hξ
  have hu2 : u * u = 1 := hinj (by rw [map_mul, hu, map_one, hζ2])
  have hv2 : v * v = 1 := hinj (by rw [map_mul, hv, map_one, hξ2])
  have hu1 : u ≠ 1 := fun h => hζ1 (by rw [← hu, h, map_one])
  have hv1 : v ≠ 1 := fun h => hξ1 (by rw [← hv, h, map_one])
  have huv : u ≠ v := fun h => hζξ (by rw [← hu, ← hv, h])
  have huc : ∀ y ∈ R₁, u * y = y * u := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu]; exact hζR₁ _ (Subgroup.mem_map_of_mem ψ hy))
  have hvc : ∀ y ∈ R₂, v * y = y * v := fun y hy =>
    hinj (by rw [map_mul, map_mul, hv]; exact hξR₂ _ (Subgroup.mem_map_of_mem ψ hy))
  have hu₂ : ∀ y ∈ R₂, u * y = y * u := fun y hy =>
    hinj (by rw [map_mul, map_mul, hu]; exact hζR₂ _ (Subgroup.mem_map_of_mem ψ hy))
  obtain ⟨w₁, hw₁⟩ := hR₁
  obtain ⟨w₂, hw₂⟩ := hR₂
  obtain ⟨φ₁, hφ₁⟩ := hw₁.exists_chart
  obtain ⟨φ₂, hφ₂⟩ := hw₂.exists_chart
  have hcu : IsCentralInvolution R₁ u := ⟨huR, hu1, hu2, huc⟩
  have hcv : IsCentralInvolution R₂ v := ⟨hvR, hv1, hv2, hvc⟩
  have e₁ : w₁ = u := hφ₁.eq_of_central hw₁.isCentralInvolution hcu
  have e₂ : w₂ = v := hφ₂.eq_of_central hw₂.isCentralInvolution hcv
  subst e₁ e₂
  have hR₂C : R₂ ≤ Subgroup.centralizer ({w₁} : Set ↥CFSG.Blueprint.NativeSporadic.M11) :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hu₂ y hy).symm
  have hRR : R₁ = R₂ := m11_eq_of_le_centralizer hw₁ hw₂ hR₂C
  subst hRR
  exact huv (hφ₁.eq_of_central hcu hcv)

end M11

section Pair


variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem range_le_of_pair_weak (D : LieSystemData3 ι X Φ) {k : ι} (hk : D.kind k ≠ CompData.sl23)
    {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ) {ζ ξ : X} (hζK : ζ ∈ K) (hξJ : ξ ∈ J)
    (hζ2 : ζ * ζ = 1) (hξ2 : ξ * ξ = 1) (hζ1 : ζ ≠ 1) (hξ1 : ξ ≠ 1) (hζξ : ζ ≠ ξ)
    (hζK' : ∀ y ∈ K, ζ * y = y * ζ) (hξJ' : ∀ y ∈ J, ξ * y = y * ξ)
    (hζJ : ∀ y ∈ J, ζ * y = y * ζ) (hξK : ∀ y ∈ K, ξ * y = y * ξ)
    (hζnc : ¬ ∀ q ∈ (D.hom k).range, ζ * q = q * ζ)
    (hξnc : ¬ ∀ q ∈ (D.hom k).range, ξ * q = q * ξ) :
    (D.hom k).range ≤ (Subgroup.centralizer ({ζ} : Set X) ⊓ (D.hom k).range) ⊔
      (Subgroup.centralizer ({ξ} : Set X) ⊓ (D.hom k).range) ⊔
      (Subgroup.centralizer ({ζ * ξ} : Set X) ⊓ (D.hom k).range) := by
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, R', hR', hJR⟩ := D.fundamental J hJ
  have hcommc : ∀ {c d : ι}, c ≠ d → ∀ {a b : X}, a ∈ (D.hom c).range → b ∈ (D.hom d).range →
      a * b = b * a := by
    rintro c d h _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact D.commute c d h x y
  have hik : i = k := by
    by_contra h
    refine hζnc fun q hq => hcommc h ?_ hq
    rw [hKR] at hζK
    exact Subgroup.map_le_range _ _ hζK
  have hjk : j = k := by
    by_contra h
    refine hξnc fun q hq => hcommc h ?_ hq
    rw [hJR] at hξJ
    exact Subgroup.map_le_range _ _ hξJ
  subst hik
  subst hjk
  subst hKR
  subst hJR
  rcases D.valid j with ⟨t, n, hfund, hadm, hc⟩ | hc | hc
  · exact range_le_of_pair_model (D.hom j) (D.ker_le_center j) hfund hadm hc hR hR' hζK hξJ hζ2
      hξ2 hζ1 hξ1 hζξ hζK' hξJ' hζJ hξK
  · exact absurd hc hk
  · exact (false_of_pair_m11_weak (D.hom j) (D.ker_le_center j) hc hR hR' hζK hξJ hζ2 hξ2 hζ1
      hξ1 hζξ hζK' hξJ' hζJ).elim

end Pair

end CFSG.ClassicalInvolution.Q3.Q3NF
