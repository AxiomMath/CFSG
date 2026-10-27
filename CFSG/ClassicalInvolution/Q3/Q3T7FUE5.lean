module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE2
public import CFSG.ClassicalInvolution.Asc77.AscE187P3
public import CFSG.ClassicalInvolution.Asc77.AscE187Delta
public import CFSG.ClassicalInvolution.Asc77.AscE187P1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section GoodFour
variable [Finite G]

theorem commute_of_mem_of_twin (hΩ : HM MT Ω) {K K' : Subgroup G} {z : G}
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω) (hKK' : K ≠ K')
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) {u u' : G} (huK : u ∈ K)
    (huW : u ∈ W) (hu'K : u' ∈ K') (hu'W : u' ∈ W) : u * u' = u' * u :=
  hΩ.commutes_of_twin_of_isPGroup hK hK'Ω hKK' hz hz' (A := Subgroup.zpowers u)
    (B := Subgroup.zpowers u') (Subgroup.zpowers_le.mpr huK) (Subgroup.zpowers_le.mpr hu'K)
    (hW2.to_le (sup_le (Subgroup.zpowers_le.mpr huW) (Subgroup.zpowers_le.mpr hu'W))) u
    (Subgroup.mem_zpowers u) u' (Subgroup.mem_zpowers u')

theorem goodFour_of_swap (hΩ : HM MT Ω) {K : Subgroup G} {z t : G} {H R : Subgroup G}
    (hR2 : IsPGroup 2 ↥(R ⊔ conjSub t R)) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (htz : t * z = z * t) (hnK : conjSub t K ≠ K) {u : G} (huK : u ∈ K)
    (huR : u ∈ R) (hu4 : orderOf u = 4) (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R ⊔ conjSub t R, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_of_swap_gen hΩ.conjInvariant (fun hW hK hK' hKK' hz hz' huK huW hu'K hu'W =>
      commute_of_mem_of_twin hΩ hW hK hK' hKK' hz hz' huK huW hu'K hu'W)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    hR2 hK hz ht2 htz hnK huK huR hu4 hzcent h2

theorem goodFour_of_fixed (hΩ : HM MT Ω) {K K' : Subgroup G} {z t : G}
    {H W R₁ R₂ : Subgroup G} (hR2 : IsPGroup 2 ↥(R₁ ⊔ R₂)) (hK : K ∈ Ω) (hK'Ω : K' ∈ Ω)
    (hKK' : K ≠ K') (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (htz : t * z = z * t) (htK : conjSub t K = K) (htK' : conjSub t K' = K')
    (htW : conjSub t W = W) (hUK : IsCyclic ↥(K ⊓ W)) (hUK' : IsCyclic ↥(K' ⊓ W)) {u u' : G}
    (huK : u ∈ K) (huW : u ∈ W) (huR : u ∈ R₁) (hu4 : orderOf u = 4) (hu'K : u' ∈ K')
    (hu'W : u' ∈ W) (hu'R : u' ∈ R₂) (hu'4 : orderOf u' = 4)
    (hC : ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 → t * x ≠ x * t)
    (hzcent : Subgroup.centralizer ({z} : Set G) ≤ H)
    (h2 : ∀ a ∈ R₁ ⊔ R₂, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H) :
    GoodFour H t :=
  E187C.goodFour_of_fixed_gen (fun hW hK hK' hKK' hz hz' huK huW hu'K hu'W =>
      commute_of_mem_of_twin hΩ hW hK hK' hKK' hz hz' huK huW hu'K hu'W)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    hR2 hK hK'Ω hKK' hz hz' htz htK htK' htW hUK hUK' huK huW huR hu4 hu'K hu'W hu'R hu'4 hC hzcent
    h2

end GoodFour
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_z (c : MinCex MT Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz, hzW⟩ := e18_zW G Ω K S R W H c
  exact ⟨z, hz, hzW, c.centralizer_le hz⟩

theorem inf_S_eq_of_mem_RSet (hΩ : HM MT Ω) {S : Sylow 2 G}
    {M R' : Subgroup G} (hM : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' := by
  have hsyl : IsSylow2In R' M := hΩ.isSylow2In_of_mem_RSet_of_le hM hR' hR'M
  exact hsyl.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'M hR'S)

theorem MinCex.inf_W_mem_USet (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ W ∈ USet Ω := by
  obtain ⟨η, hη, hWη, hηU, -, -⟩ := c.exists_eta hA
  have h2 : 2 < Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have h8 := c.stand.hyp.eight_le_of_mem_RSet hR'
    have := Subgroup.card_le_of_le (le_inf hR'M hR'S)
    omega
  have hmem := hM S η hη (fun V hV => (hηU V hV).2) M hMΩ h2
  rw [← hWη] at hmem
  exact (hηU _ hmem).1

theorem MinCex.exists_order_four_of_inf_W (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {M R' : Subgroup G} (hMΩ : M ∈ Ω) (hR' : R' ∈ RSet Ω) (hR'M : R' ≤ M)
    (hR'S : R' ≤ (S : Subgroup G)) :
    IsCyclic ↥(M ⊓ W) ∧ ∃ u ∈ M ⊓ W, orderOf u = 4 := by
  have hU := c.inf_W_mem_USet hA hM hMΩ hR' hR'M hR'S
  obtain ⟨R'', -, J, -, hRJ, hUR, hcyc, -, h4⟩ :=
    c.stand.hyp.exists_data_of_mem_USet hU
  refine ⟨hcyc, ?_⟩
  obtain ⟨u, hu, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic
    (c.stand.hyp.isPGroup_of_mem_USet hU) hcyc h4
  exact ⟨u, hu, hu4⟩

theorem MinCex.hbad_of_conj (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {z g : G} (hz : IsUniqueInvolution K z) (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M (g * z * g⁻¹) → ∀ u ∈ M, orderOf u = 4 → u ∉ H := by
  exact E187C.hbad_of_conj_of c.stand.hyp.conjInvariant (fun hM => mem_dstarComp_of_twin c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hA hM hMS hu hu4 hx) hz hg

theorem MinCex.hC_of_conj (c : MinCex MT Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {z g : G} (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hg : g ∉ H) :
    ∀ M ∈ Ω, IsUniqueInvolution M z → ∀ x ∈ M, orderOf x = 4 →
      (g * z * g⁻¹) * x ≠ x * (g * z * g⁻¹) := by
  exact E187C.hC_of_conj_of (fun hM => mem_dstarComp_of_twin c.stand.hyp c.stand.mem hM)
    (fun hMS hu hu4 hx => c.mem_of_conj_mem_dstar hA hM hMS hu hu4 hx) hz hzH hg

theorem MinCex.goodFour_of_commute (h : E187Hyps) (c : MinCex MT Ω K S R W H) {z g t : G}
    (hz : IsUniqueInvolution K z) (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hg : g ∉ H)
    (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hcomm : t * z = z * t) :
    GoodFour H t := by
  have hΩ : HM MT Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  have hM : EtaMeet Ω := h.etaMeet hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨-, hWS, hWn⟩ := c.stand.hW
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  exact E187C.goodFour_of_commute_of (z := z) (g := g) (t := t) (K' := K') (R' := R') (Q := GoodFour H t) (Wp := fun _ => True) hΩ.conjInvariant
    (fun hK₁ hK₂ hz₁ hz₂ => CFSG.ClassicalInvolution.Q3.Q3T7M.mem_kPerp_of_twin hΩ hK₁ hK₂ hz₁ hz₂)
    (fun hM' hR₀ hR₀M hR₀S => inf_S_eq_of_mem_RSet hΩ hM' hR₀ hR₀M hR₀S)
    (fun hM' hR₀ hR₀M hR₀S => c.exists_order_four_of_inf_W hA hM hM' hR₀ hR₀M hR₀S)
    (fun hK₁ hJ hKJ hz₁ hz₂ hA₁ hB₁ hAB => hΩ.commutes_of_twin_of_isPGroup hK₁ hJ hKJ hz₁ hz₂ hA₁ hB₁ hAB)
    (by have := c.hC_of_conj hA hM hz hzH hg; rwa [← ht] at this)
    (fun hR2 hK₁ hK'Ω hKK' hz₁ hz₂ htz htK htK' htW hUK hUK' u u' huK huW huR hu4 hu'K hu'W hu'R
        hu'4 hC' hzcent h2 =>
      goodFour_of_fixed hΩ hR2 hK₁ hK'Ω hKK' hz₁ hz₂ htz htK htK' htW hUK hUK' huK huW huR hu4
        hu'K hu'W hu'R hu'4 hC' hzcent (fun a ha ha1 ha2 => h2 a ha trivial ha1 ha2))
    (fun hR2 hK₁ hz₁ ht2 htz hnK huK huR hu4 huW hWt hzcent h2 =>
      goodFour_of_swap hΩ hR2 hK₁ hz₁ ht2 htz hnK huK huR hu4 hzcent
        (fun a ha ha1 ha2 => h2 a ha trivial ha1 ha2))
    (fun hK₀tw hJ hR₀ hR₀K₀ _ hR₂ hR₂J hcm a ha _ ha1 ha2 =>
      c.hyp.cent _ hK₀tw _ hJ _ _ hR₀ hR₀K₀ hR₂ hR₂J (Or.inl hcm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS hWS hWn hK'tw hne hR' hR'K' hR'S hz hzH ht htS hcomm

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_delta (h : E187Hyps) (c : MinCex MT Ω K S R W H) {z t : G}
    (hz : IsUniqueInvolution K z) (hzW : z ∈ W) (ht2 : t * t = 1)
    (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
      IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
      Subgroup.centralizer ({b} : Set G) ≤ H := by
  have hΩ : HM MT Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.exists_delta_of hΩ.conjInvariant (fun hR => hΩ.eight_le_of_mem_RSet hR)
    (fun hK hJ hKJ hA hAK hAJ => hΩ.card_le_two_of_le_inf hK hJ hKJ hA hAK hAJ)
    (fun hK hR hRK => hΩ.isSylow2In_of_mem_RSet_of_le hK hR hRK)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      hΩ.le_normalizer_of_le_centralizer hK hJ hKJ hz hAJ hA2 hA3 hAc)
    (fun hR' hR'S hne => h.l67 G Ω hΩ S R hRR _ hR' hRS hR'S hne)
    (fun hJ hR₂ hR₂J hcomm a ha _ ha1 ha2 =>
      c.hyp.cent K ⟨c.stand.mem, z, hz, hz⟩ _ hJ R _ hRR hRK hR₂ hR₂J (Or.inl hcomm) a ha ha1 ha2)
    c.stand.mem hRR hRK hRS c.stand.hW.2.2 hz hzW ht2 htS hnc

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem centralizes_conj_of_mem_RSet (h : E187Hyps) (hΩ : HM MT Ω) {S₁ : Sylow 2 G} {K₁ R₁ T :
    Subgroup G} {z₁ β : G}
    (hz₁ : IsUniqueInvolution K₁ z₁) (hR₁ : R₁ ∈ RSet Ω) (hR₁K₁ : R₁ ≤ K₁)
    (hR₁S : R₁ ≤ (S₁ : Subgroup G)) (hβ : β ∈ (S₁ : Subgroup G)) (hT : T ∈ RSet Ω)
    (hTS : T ≤ (S₁ : Subgroup G)) : ∀ y ∈ T, y * (β * z₁ * β⁻¹) = (β * z₁ * β⁻¹) * y := by
  exact E187C.centralizes_conj_of_mem_RSet_of hΩ.conjInvariant
    (fun hQ => hΩ.eight_le_of_mem_RSet hQ)
    (fun S₁ X hX Y hY hXS hYS hXY => h.l67 G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS

end Asc77
end
end CFSG.ClassicalInvolution.T7FU
