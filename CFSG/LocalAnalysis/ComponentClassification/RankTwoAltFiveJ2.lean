module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveTau
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveJ2Gens

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5
open scoped commutatorElement

namespace CFSG.ComponentClassification.RankTwoAltFive

open CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace Setting310

variable {G : Type} [Group G] [Finite G]
variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem exists_not_commute_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA)
    (hGs : IsSimpleGroup G) (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hxP : x ∉ P) : ∃ w ∈ V₀, x * w ≠ w * x := by
  obtain ⟨-, hS128, -, -, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hrelPS : P.relIndex S = 2 := by
    have h1 := Subgroup.relIndex_mul_card P S
    rw [inf_eq_left.mpr hPS, hS128, hP64] at h1
    omega
  by_contra hno
  push Not at hno
  refine h.false_of_tauType hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv
    S hPS fun s hs w hw => ?_
  by_cases hsP : s ∈ P
  · exact P_comm_V₀ hP hw hsP
  · have hk := CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hrelPS hxS hs hxP hsP
    calc s * w = x * ((x⁻¹ * s) * w) := by group
      _ = x * (w * (x⁻¹ * s)) := by rw [P_comm_V₀ hP hw hk]
      _ = (x * w) * (x⁻¹ * s) := by group
      _ = (w * x) * (x⁻¹ * s) := by rw [hno w hw]
      _ = w * s := by group

theorem exists_j2Gens_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {x : G} (hxS : x ∈ (S : Subgroup G)) (hxP : x ∉ P) (hx2 : x * x = 1) :
    ∃ J : J2Gens G, J.x = x ∧ J.P = P ∧ J.Z .z1 ≠ 1 := by
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  obtain ⟨hVx, hV'x⟩ := hswap x hxS hxP
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hx2, mul_one]
      _ = x := by group
  have hxx : ∀ y, x * (x * y * x⁻¹) * x⁻¹ = y := fun y => by
    rw [hxinv, show x * (x * y * x) * x = (x * x) * y * (x * x) by group, hx2, one_mul, mul_one]
  have hxV : ∀ y ∈ R ⊔ T, x * y * x⁻¹ ∈ V' := fun y hy => by
    rw [← hV'x] at hy
    exact (mem_rightConjugate_iff _ _ _).mp hy
  have hxV' : ∀ y ∈ V', x * y * x⁻¹ ∈ R ⊔ T := fun y hy => by
    rw [← hVx] at hy
    exact (mem_rightConjugate_iff _ _ _).mp hy
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hxV₀ : ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ := fun v hv =>
    hinf ▸ mem_inf.mpr ⟨hxV' v (hV₀V' hv), hxV v (h.V₀_le hv)⟩
  have hR2 : ∀ y ∈ R, y * y = 1 := fun y hy => h.mul_self (mem_sup_left hy)
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  obtain ⟨p, hp, hp1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  obtain ⟨q, hq, hq1, hqp⟩ := exists_ne_one_ne h.cardR hR2 hp
  have hRV₀ : ∀ r ∈ R, r ∈ V₀ → r = 1 := fun r hr hr0 => by
    have h1 := mem_inf.mpr ⟨hr, hr0⟩
    rw [h.inf_R_V₀] at h1
    exact (mem_bot.mp h1)
  have hRP : ∀ r ∈ R, r ∈ P := fun r hr => hVP (mem_sup_left hr)
  have hxRP : ∀ r ∈ R, x * r * x⁻¹ ∈ P := fun r hr => hV'P (hxV r (mem_sup_left hr))
  have hδV₀ : ∀ r ∈ R, ∀ r' ∈ R, ⁅x * r * x⁻¹, r'⁆ ∈ V₀ := fun r hr r' hr' =>
    h.P_comm_mem_V₀ hP hPC hIIa (hxRP r hr) (hRP r' hr')
  have hnd : ∀ r ∈ R, ∀ r' ∈ R, r ≠ 1 → r' ≠ 1 → ⁅x * r * x⁻¹, r'⁆ ≠ 1 := by
    intro r hr r' hr' hr1 hr'1 he
    have hrV : x * r * x⁻¹ ∉ R ⊔ T := by
      intro hrV
      have h0 : x * r * x⁻¹ ∈ V₀ := hinf ▸ mem_inf.mpr ⟨hrV, hxV r (mem_sup_left hr)⟩
      have h1 := hxV₀ _ h0
      rw [hxx] at h1
      exact hr1 (hRV₀ r hr h1)
    have hfix : x * r * x⁻¹ * r' * (x * r * x⁻¹)⁻¹ = r' := by
      rw [commutatorElement_eq_one_iff_mul_comm.mp he]
      group
    exact hr'1 (hRV₀ r' hr' (h.P_fixed hP hPC (hxRP r hr) hrV (mem_sup_left hr') hfix))
  have hsym : ∀ r ∈ R, ∀ r' ∈ R, x * ⁅x * r * x⁻¹, r'⁆ * x⁻¹ = ⁅x * r' * x⁻¹, r⁆ := by
    intro r hr r' hr'
    rw [conjugate_commutatorElement, hxx, ← commutatorElement_inv]
    exact inv_eq_of_mul_eq_one_right (hV₀2 _ (hδV₀ r' hr' r hr))
  obtain ⟨w₀, hw₀, hw₀x⟩ := h.exists_not_commute_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε
    hV'P hV'e hV'16 hinf hsup hV'inv S hPS hxS hxP
  have hc : ∀ y, x * y * x⁻¹ = y → x * y = y * x := fun y hy => by
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hy]
  have hfix : ∀ v ∈ V₀, ∀ v' ∈ V₀, v ≠ 1 → v' ≠ 1 → x * v * x⁻¹ = v → x * v' * x⁻¹ = v' →
      v = v' := by
    intro v hv v' hv' hv1 hv'1 hxv hxv'
    by_contra hne
    apply hw₀x
    rcases mem_four h.card_V₀ hV₀2 hv hv' hv1 hv'1 hne hw₀ with rfl | rfl | rfl | rfl
    · group
    · exact hc _ hxv
    · exact hc _ hxv'
    · refine hc _ ?_
      rw [show x * (v * v') * x⁻¹ = (x * v * x⁻¹) * (x * v' * x⁻¹) by group, hxv, hxv']
  have hpp1 := hnd p hp p hp hp1 hp1
  have hpp_fix := hsym p hp p hp
  have hqq : ⁅x * q * x⁻¹, q⁆ = ⁅x * p * x⁻¹, p⁆ :=
    hfix _ (hδV₀ q hq q hq) _ (hδV₀ p hp p hp) (hnd q hq q hq hq1 hq1) hpp1 (hsym q hq q hq)
      hpp_fix
  have hpq_ne : ⁅x * p * x⁻¹, q⁆ ≠ ⁅x * p * x⁻¹, p⁆ := by
    intro he
    have hpq1 : p * q ≠ 1 := fun h1 => hqp (by
      calc q = p * (p * q) := by rw [← mul_assoc, hR2 p hp, one_mul]
        _ = p := by rw [h1, mul_one])
    apply hnd p hp (p * q) (mul_mem hp hq) hp1 hpq1
    rw [commutatorElement_mul_right' (P_comm_V₀ hP (hδV₀ p hp q hq) (hRP p hp)).symm, he,
      hV₀2 _ (hδV₀ p hp p hp)]
  have hqp_eq : ⁅x * q * x⁻¹, p⁆ = ⁅x * p * x⁻¹, p⁆ * ⁅x * p * x⁻¹, q⁆ := by
    have hu := hsym p hp q hq
    rcases mem_four h.card_V₀ hV₀2 (hδV₀ p hp p hp) (hδV₀ p hp q hq) hpp1
      (hnd p hp q hq hp1 hq1) hpq_ne.symm (hδV₀ q hq p hp) with h1 | h1 | h1 | h1
    · exact absurd h1 (hnd q hq p hp hq1 hp1)
    · refine absurd ?_ hpq_ne
      rw [h1] at hu
      calc ⁅x * p * x⁻¹, q⁆ = x * (x * ⁅x * p * x⁻¹, q⁆ * x⁻¹) * x⁻¹ := (hxx _).symm
        _ = ⁅x * p * x⁻¹, p⁆ := by rw [hu, hpp_fix]
    · exact absurd (hfix _ (hδV₀ p hp q hq) _ (hδV₀ p hp p hp) (hnd p hp q hq hp1 hq1) hpp1
        (hu.trans h1) hpp_fix) hpq_ne
    · exact h1
  exact ⟨⟨x, p, q, P, V₀, hx2, hR2 p hp, hR2 q hq, h.comm (mem_sup_left hp) (mem_sup_left hq),
    hRP p hp, hRP q hq, hxRP p hp, hxRP q hq, h.V₀_le.trans hVP,
    fun c hc y hy => (P_comm_V₀ hP hc hy).symm, hV₀2, hδV₀ p hp p hp, hδV₀ p hp q hq, hqq,
    hqp_eq⟩, rfl, rfl, hpp1⟩

theorem j2Emb_of_eps_one (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) :
    ∃ x : G, IsConj z x ∧ J2Emb (S : Subgroup G) P x := by
  obtain ⟨-, hS128, -, -, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  obtain ⟨c, hcS, hcP⟩ := h.exists_conj_not_mem hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
    hV'16 hinf hsup hV'inv S hPS hz hz1
  obtain ⟨x, hx⟩ : ∃ x : G, c⁻¹ * z * c = x := ⟨_, rfl⟩
  rw [hx] at hcS hcP
  have hx2 : x * x = 1 := by
    rw [← hx]
    calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
      _ = 1 := by rw [h.mul_self (h.V₀_le hz)]; group
  obtain ⟨J, rfl, rfl, hJd⟩ := h.exists_j2Gens_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS hcS hcP hx2
  exact ⟨J.x, isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]; exact hx⟩,
    J.j2Emb hJd hS128 hPS hcS hP64⟩

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
