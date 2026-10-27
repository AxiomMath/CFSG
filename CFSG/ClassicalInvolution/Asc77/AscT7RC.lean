module

public import CFSG.ClassicalInvolution.Asc77.AscE184SecB
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer

section OddCore

namespace T7R

variable {G : Type} [Group G]

theorem conj_mem_oddCoreOf {Y : Subgroup G} {y o : G} (hy : y ∈ Y) (ho : o ∈ oddCoreOf Y) :
    y * o * y⁻¹ ∈ oddCoreOf Y := by
  obtain ⟨hoY, ho'⟩ := mem_oddCoreOf_iff.mp ho
  have hyoy : y * o * y⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy hoY) (Y.inv_mem hy)
  refine mem_oddCoreOf_iff.mpr ⟨hyoy, ?_⟩
  have hmem := Subgroup.Normal.conj_mem (inferInstance : (classicalInvolutionOddCore ↥Y).Normal)
    _ ho' ⟨y, hy⟩
  have e : (⟨y * o * y⁻¹, hyoy⟩ : ↥Y) = (⟨y, hy⟩ : ↥Y) * ⟨o, hoY⟩ * (⟨y, hy⟩ : ↥Y)⁻¹ := rfl
  rw [e]
  exact hmem

variable [Finite G]

theorem exists_conj_le_centralizer_of_comm_mem_oddCore {Y R : Subgroup G} {c : G}
    (hc2 : c * c = 1) (hcY : conjSub c Y = Y) (hR2 : IsPGroup 2 ↥R) (hRY : R ≤ Y)
    (h : ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ oddCoreOf Y) :
    ∃ n ∈ oddCoreOf Y, conjSub n R ≤ Subgroup.centralizer ({c} : Set G) := by
  set O := oddCoreOf Y with hO
  have hOY : O ≤ Y := oddCoreOf_le_self Y
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcO : ∀ o ∈ O, c * o * c⁻¹ ∈ O := by
    intro o ho
    have h1 : oddCoreOf (conjSub c Y) = conjSub c (oddCoreOf Y) := oddCoreOf_conjSub c Y
    rw [hcY] at h1
    have : c * o * c⁻¹ ∈ conjSub c (oddCoreOf Y) := conj_mem_conjSub ho
    rwa [← h1] at this
  have hYN : Y ≤ Subgroup.normalizer (O : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => conj_mem_oddCoreOf hg hx
    · intro hx
      have := conj_mem_oddCoreOf (Y.inv_mem hg) hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rwa [e] at this
  have hRN : R ≤ Subgroup.normalizer (O : Set G) := hRY.trans hYN
  set Q : Subgroup G := R ⊔ O with hQ
  have hQY : Q ≤ Y := sup_le hRY hOY
  have hcQ : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro q hq
    have hq' : q ∈ ((R ⊔ O : Subgroup G) : Set G) := hq
    rw [Subgroup.coe_mul_of_left_le_normalizer_right R O hRN] at hq'
    obtain ⟨ρ, hρ, n, hn, rfl⟩ := hq'
    have e : c * (ρ * n) * c⁻¹ = (c * ρ * c⁻¹ * ρ⁻¹) * ρ * (c * n * c⁻¹) := by group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (Subgroup.mem_sup_right (h ρ (hRY hρ)))
      (Subgroup.mem_sup_left hρ)) (Subgroup.mem_sup_right (hcO n hn))
  have hcNQ : c ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hcQ x, fun hx => ?_⟩
    have := hcQ _ hx
    have e : c * (c * x * c⁻¹) * c⁻¹ = x := by
      rw [hcinv]
      calc c * (c * x * c) * c = (c * c) * x * (c * c) := by group
        _ = x := by rw [hc2]; group
    rwa [e] at this
  obtain ⟨R₀, hR₀, hRR₀⟩ := IsSylow2In.exists_ge hR2 (le_sup_left : R ≤ Q)
  obtain ⟨R₁, hR₁, hfix⟩ := T3.exists_sylow_normalized (K := Q) (W := Subgroup.zpowers c)
    (isPGroup_zpowers_of_sq_eq_one hc2) (Subgroup.zpowers_le.mpr hcNQ)
  have hR₁c : R₁ ≤ Subgroup.centralizer ({c} : Set G) := by
    intro r hr
    have hcR₁ : conjSub c R₁ = R₁ := hfix c (Subgroup.mem_zpowers c)
    have h1 : c * r * c⁻¹ ∈ R₁ := by
      have : c * r * c⁻¹ ∈ conjSub c R₁ := conj_mem_conjSub hr
      rwa [hcR₁] at this
    have h2 : c * r * c⁻¹ * r⁻¹ ∈ R₁ := R₁.mul_mem h1 (R₁.inv_mem hr)
    have h3 : c * r * c⁻¹ * r⁻¹ ∈ O := h r (hQY (hR₁.1 hr))
    have h4 : IsPGroup 2 (Subgroup.zpowers (c * r * c⁻¹ * r⁻¹)) :=
      hR₁.2.1.to_le (Subgroup.zpowers_le.mpr h2)
    have h5 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h3 h4
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h6 : c * r * c⁻¹ = r := by
      have := congrArg (fun y => y * r) h5
      simpa [mul_assoc] using this
    calc r * c = (c * r * c⁻¹) * c := by rw [h6]
      _ = c * r := by group
  obtain ⟨q, hq, hqR⟩ := Thompson.exists_conj_of_isSylow2In hR₀ hR₁
  have hQsup : Q = O ⊔ R₀ := by
    apply le_antisymm
    · exact sup_le (le_trans hRR₀ le_sup_right) le_sup_left
    · exact sup_le (le_sup_right) hR₀.1
  have hR₀N : R₀ ≤ Subgroup.normalizer (O : Set G) := hR₀.1.trans (hQY.trans hYN)
  have hq' : q ∈ ((O ⊔ R₀ : Subgroup G) : Set G) := by
    rw [← hQsup]
    exact hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O R₀ hR₀N] at hq'
  obtain ⟨n, hn, ρ, hρ, rfl⟩ := hq'
  refine ⟨n, hn, ?_⟩
  have e : conjSub (n * ρ) R₀ = conjSub n R₀ := by
    rw [conjSub_mul, conjSub_eq_self_of_mem hρ]
  rw [e] at hqR
  exact (conjSub_mono hRR₀).trans (hqR ▸ hR₁c)

end T7R

end OddCore

end CFSG.ClassicalInvolution.Asc77
