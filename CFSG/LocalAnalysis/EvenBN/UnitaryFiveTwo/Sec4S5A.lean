module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSTen
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3D
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3F

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem exists_mem_normalizer_not_mem {G : Type*} [Group G] [Finite G] {Q H : Subgroup G}
    (hQ : IsPGroup 2 Q) (hHQ : H ≤ Q) (hne : H ≠ Q) :
    ∃ q ∈ Q, q ∈ normalizer (H : Set G) ∧ q ∉ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : H.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne ?_
    apply le_antisymm hHQ
    intro q hq
    have : (⟨q, hq⟩ : Q) ∈ H.subgroupOf Q := by rw [htop]; trivial
    exact this
  have hnorm := Group.normalizerCondition_of_isNilpotent (H.subgroupOf Q) hlt
  obtain ⟨⟨q, hqQ⟩, hqN, hqH⟩ := SetLike.exists_of_lt hnorm
  refine ⟨q, hqQ, mem_normalizer_fintype fun x hx => ?_, fun hqH' => hqH hqH'⟩
  have hxQ : x ∈ Q := hHQ hx
  have hmem : (⟨x, hxQ⟩ : Q) ∈ H.subgroupOf Q := hx
  exact (mem_normalizer_iff.1 hqN ⟨x, hxQ⟩).1 hmem

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem e₁_mem_NHS (h : d.Hyp) : d.e₁ ∈ normalizer (d.S : Set G) ⊓ d.H :=
  Subgroup.mem_inf.2 ⟨ι_mem_normalizer_pull e₁SU_mem_normalizer_Ssub, h.L_le_H (d.ι_mem _)⟩

theorem xi_conj_e₁ (h : d.Hyp) {k : G} (hk : k ∈ d.AW) :
    d.xi (d.e₁ * k * d.e₁⁻¹) = F4.ω * d.xi k := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hk
  obtain ⟨α, hα, rfl⟩ := ha
  have hα' : e₁SU * α * e₁SU⁻¹ ∈ A₁sub :=
    (mem_normalizer_iff.1 (normalizer_Ssub_le_normalizer_A₁sub e₁SU_mem_normalizer_Ssub) α).1 hα
  have hw' : d.e₁ * w * d.e₁⁻¹ ∈ d.W :=
    (mem_normalizer_iff.1 (h.NHS_le_normalizer_W h.e₁_mem_NHS) w).1 hw
  have e : d.e₁ * (d.ι α * w) * d.e₁⁻¹ =
      d.ι (e₁SU * α * e₁SU⁻¹) * (d.e₁ * w * d.e₁⁻¹) := by
    simp only [Data.e₁, map_mul, map_inv]
    group
  rw [e, h.xi_ι_mul hα' hw', h.xi_ι_mul hα hw, mat_conj_e₁_one_zero α]

theorem eq_D₃_or_eq_D₁_of_conj_e₁ (h : d.Hyp) {T : Subgroup G} (h₃ : d.D₃ ≤ T) (hT : T ≤ d.D₁)
    (he : ∀ r ∈ T, d.e₁ * r * d.e₁⁻¹ ∈ T) : T = d.D₃ ∨ T = d.D₁ := by
  by_cases hTD : T ≤ d.D₃
  · exact Or.inl (le_antisymm hTD h₃)
  right
  refine le_antisymm hT fun x hx => ?_
  obtain ⟨r, hrT, hr3⟩ := SetLike.not_le_iff_exists.1 hTD
  have hrD₁ : r ∈ d.D₁ := hT hrT
  have hr0 : d.xi (r * d.t * r⁻¹ * d.t) ≠ 0 := fun h0 => hr3 ((h.mem_D₃_iff_xi hrD₁).2 h0)
  have hconj : ∀ y ∈ d.D₁, d.xi ((d.e₁ * y * d.e₁⁻¹) * d.t * (d.e₁ * y * d.e₁⁻¹)⁻¹ * d.t) =
      F4.ω * d.xi (y * d.t * y⁻¹ * d.t) := fun y hy => by
    rw [crossed_conj_of_mem_H (Subgroup.mem_inf.1 h.e₁_mem_NHS).2]
    exact h.xi_conj_e₁ (h.theta_mem_AW hy)
  have hmem : ∀ y ∈ T, ∀ z ∈ d.D₁,
      d.xi (y * d.t * y⁻¹ * d.t) = d.xi (z * d.t * z⁻¹ * d.t) → z ∈ T := fun y hy z hz hyz => by
    have hyD : y ∈ d.D₁ := hT hy
    have h1 := h.xi_theta_mul (inv_mem hyD) hz
    rw [h.xi_theta_inv hyD, hyz, neg_add_cancel] at h1
    have h2 : y⁻¹ * z ∈ d.D₃ := (h.mem_D₃_iff_xi (mul_mem (inv_mem hyD) hz)).2 h1
    have := mul_mem hy (h₃ h2)
    rwa [mul_inv_cancel_left] at this
  have hr₁T : d.e₁ * r * d.e₁⁻¹ ∈ T := he r hrT
  have hr₁D : d.e₁ * r * d.e₁⁻¹ ∈ d.D₁ := hT hr₁T
  have hr₂T : d.e₁ * (d.e₁ * r * d.e₁⁻¹) * d.e₁⁻¹ ∈ T := he _ hr₁T
  rcases F4_eq_of_ne_zero _ (d.xi (x * d.t * x⁻¹ * d.t)) hr0 with h0 | h0 | h0 | h0
  · exact h₃ ((h.mem_D₃_iff_xi hx).2 h0)
  · exact hmem r hrT x hx h0.symm
  · exact hmem _ hr₁T x hx ((hconj r hrD₁).trans h0.symm)
  · exact hmem _ hr₂T x hx (((hconj _ hr₁D).trans (by rw [hconj r hrD₁])).trans h0.symm)

theorem D₁_le_normalizer_R_sup_D₃ (h : d.Hyp) :
    d.D₁ ≤ normalizer ((d.R ⊔ d.D₃ : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRN : d.R ≤ normalizer (d.D₁ : Set G) := h.R_le_normalizer_D₁
  have hRD₃ : d.R ≤ normalizer (d.D₃ : Set G) := h.R_le_normalizer_D₃
  have hQ : IsPGroup 2 (d.R ⊔ d.D₁ : Subgroup G) :=
    (IsPGroup.of_card h.card_R).to_sup_of_normal_right' (IsPGroup.of_card h.card_D₁) hRN
  have hH₀Q : d.R ⊔ d.D₃ ≤ d.R ⊔ d.D₁ := sup_le_sup_left D₃_le_D₁' _
  obtain ⟨x, hxD₁, hxD₃⟩ : ∃ x ∈ d.D₁, x ∉ d.D₃ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (hcon : d.D₁ ≤ d.D₃)
    rw [h.card_D₁, h.card_D₃] at this
    omega
  have hne : d.R ⊔ d.D₃ ≠ d.R ⊔ d.D₁ := by
    intro heq
    apply hxD₃
    have hset := coe_mul_of_left_le_normalizer_right d.R d.D₃ hRD₃
    obtain ⟨r, hr, u, hu, hru⟩ : x ∈ (d.R : Set G) * (d.D₃ : Set G) := by
      rw [← hset, heq]
      exact mem_sup_right hxD₁
    have hxu : x = r * u := hru.symm
    have hrD₁ : r ∈ d.D₁ := by
      have := mul_mem hxD₁ (inv_mem (D₃_le_D₁' hu))
      rwa [hxu, mul_inv_cancel_right] at this
    have hrA₁ : r ∈ d.A₁ := by
      have : r ∈ d.D₁ ⊓ d.H := Subgroup.mem_inf.2 ⟨hrD₁, h.R_le_H hr⟩
      rwa [h.D₁_inf_H] at this
    rw [hxu]
    exact mul_mem (h.A₁_le_D₃ hrA₁) hu
  obtain ⟨q, hqQ, hqN, hqH⟩ := exists_mem_normalizer_not_mem hQ hH₀Q hne
  have hset := coe_mul_of_left_le_normalizer_right d.R d.D₁ hRN
  obtain ⟨r, hr, y, hy, hry⟩ : q ∈ (d.R : Set G) * (d.D₁ : Set G) := by
    rw [← hset]
    exact hqQ
  have hqy : q = r * y := hry.symm
  have hrH : r ∈ d.R ⊔ d.D₃ := mem_sup_left hr
  have hyN : y ∈ normalizer ((d.R ⊔ d.D₃ : Subgroup G) : Set G) := by
    have := mul_mem (inv_mem ((d.R ⊔ d.D₃).le_normalizer hrH)) hqN
    rwa [hqy, inv_mul_cancel_left] at this
  have hyD₃ : y ∉ d.D₃ := fun hyD => hqH (by
    rw [hqy]
    exact mul_mem hrH (mem_sup_right hyD))
  have he₁D₁ : ∀ r ∈ d.D₁, d.e₁ * r * d.e₁⁻¹ ∈ d.D₁ := fun r hr =>
    h.conj_mem_D₁ (h.NHS_le_XW h.e₁_mem_NHS) hr
  have he₁N : d.e₁ ∈ normalizer ((d.R ⊔ d.D₃ : Subgroup G) : Set G) :=
    mem_normalizer_sup (NHS_le_normalizer_R h.e₁_mem_NHS)
      (mem_normalizer_fintype fun u hu => h.conj_mem_D₃ h.e₁_mem_NHS hu)
  let T : Subgroup G := d.D₁ ⊓ normalizer ((d.R ⊔ d.D₃ : Subgroup G) : Set G)
  have hT : T = d.D₃ ∨ T = d.D₁ := by
    refine h.eq_D₃_or_eq_D₁_of_conj_e₁ (T := T) (fun u hu => Subgroup.mem_inf.2
      ⟨D₃_le_D₁' hu, (d.R ⊔ d.D₃).le_normalizer (mem_sup_right hu)⟩) inf_le_left
      fun r hr => Subgroup.mem_inf.2 ⟨he₁D₁ r (Subgroup.mem_inf.1 hr).1, ?_⟩
    have := mul_mem (mul_mem he₁N (Subgroup.mem_inf.1 hr).2) (inv_mem he₁N)
    exact this
  rcases hT with hT | hT
  · exfalso
    have : y ∈ T := Subgroup.mem_inf.2 ⟨hy, hyN⟩
    rw [hT] at this
    exact hyD₃ this
  · intro u hu
    have : u ∈ T := by rw [hT]; exact hu
    exact (Subgroup.mem_inf.1 this).2

theorem D₁_le_normalizer_R₃ (h : d.Hyp) (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.D₁ ≤ normalizer (d.R₃ : Set G) := fun x hx => by
  have h1 := mem_normalizer_sup (h.D₁_le_normalizer_R_sup_D₃ hx) (h.D₁_le_normalizer_Y hKY hx)
  have e : d.R₃ = (d.R ⊔ d.D₃) ⊔ d.Y := by
    rw [h.R₃_eq]
    exact sup_right_comm _ _ _
  rw [e]
  exact h1

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
