module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordSz
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5CoordField
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Six
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G} {u v : G → BinaryGaloisField (2 * a + 1)}
  {κ : BinaryGaloisField (2 * a + 1)}

section A₁

variable (hS : SzR G L T R a y d) (hc : RootCoords (T ⊓ L) a d u v κ)
include hS hc

theorem u_eq_zero_of_mem_gmsA {b : G} (hb : b ∈ gmsA L T) : u b = 0 :=
  (hc.mem_center_iff hS.one_le (mem_inf.mp hb).1).mp hb

theorem v_mul_gmsA {b b' : G} (hb : b ∈ gmsA L T) (hb' : b' ∈ gmsA L T) :
    v (b * b') = v b + v b' := by
  rw [(hc.mul b (mem_inf.mp hb).1 b' (mem_inf.mp hb').1).2, hS.u_eq_zero_of_mem_gmsA hc hb,
    zero_mul, add_zero]

theorem v_inv_gmsA {b : G} (hb : b ∈ gmsA L T) : v b⁻¹ = v b := by
  have h := hS.v_mul_gmsA hc hb (inv_mem hb)
  rw [mul_inv_cancel, hc.v_one] at h
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  linear_combination -h - v b * h2

theorem eq_one_of_v_eq_zero {b : G} (hb : b ∈ gmsA L T) (h : v b = 0) : b = 1 :=
  hc.inj b (mem_inf.mp hb).1 1 (one_mem _) (by rw [hS.u_eq_zero_of_mem_gmsA hc hb, hc.u_one])
    (by rw [h, hc.v_one])

theorem exists_v_eq (w : BinaryGaloisField (2 * a + 1)) : ∃ b ∈ gmsA L T, v b = w := by
  obtain ⟨b, hb, hu, hv⟩ := hc.surj 0 w
  exact ⟨b, (hc.mem_center_iff hS.one_le hb).mpr hu, hv⟩

theorem v_conj_gmsA {b : G} (hb : b ∈ gmsA L T) :
    v (d⁻¹ * b * d) = κ ^ (2 ^ (a + 1) + 1) * v b :=
  hc.conj_v b (mem_inf.mp hb).1 (hS.u_eq_zero_of_mem_gmsA hc hb)

end A₁

section Calculus

variable (hS : SzR G L T R a y d)
  (h34 : NoStronglyClosedAbelian G)
include hS h34

theorem commutator_mul_left {x x' z : G} (hx : x ∈ R) (hx' : x' ∈ R) (hz : z ∈ R) :
    x * x' * z * (x * x')⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ * (x' * z * x'⁻¹ * z⁻¹) := by
  have hc' := hS.commutator_mem_gmsA h34 hx' hz
  have h1 := hS.commute_gmsA hx hc'
  have h2 := hS.commute_gmsA (hS.T_le (gmsA_le_T hc')) (hS.commutator_mem_gmsA h34 hx hz)
  calc x * x' * z * (x * x')⁻¹ * z⁻¹ =
        x * (x' * z * x'⁻¹ * z⁻¹) * x⁻¹ * (x * z * x⁻¹ * z⁻¹) := by group
    _ = (x' * z * x'⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by rw [h1]; group
    _ = _ := h2

theorem commutator_mul_right {x z z' : G} (hx : x ∈ R) (hz : z ∈ R) (hz' : z' ∈ R) :
    x * (z * z') * x⁻¹ * (z * z')⁻¹ = x * z * x⁻¹ * z⁻¹ * (x * z' * x⁻¹ * z'⁻¹) := by
  have h1 := hS.commute_gmsA hz (hS.commutator_mem_gmsA h34 hx hz')
  calc x * (z * z') * x⁻¹ * (z * z')⁻¹ =
        (x * z * x⁻¹ * z⁻¹) * (z * (x * z' * x⁻¹ * z'⁻¹) * z⁻¹) := by group
    _ = _ := by rw [h1]; group

theorem sq_mul {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) :
    (x * x') ^ 2 = x * x' * x⁻¹ * x'⁻¹ * x ^ 2 * x' ^ 2 := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  have h1 := hS.commute_gmsA hx' (hS.sq_mem_gmsA_of_mem_R h34 hX hx)
  calc (x * x') ^ 2 = x * x' * x⁻¹ * x'⁻¹ * (x' * x ^ 2) * x' := by simp only [sq]; group
    _ = _ := by rw [h1]; simp only [sq]; group

theorem commutator_mul_gmsA_left {x z b : G} (hx : x ∈ R) (hz : z ∈ R) (hb : b ∈ gmsA L T) :
    x * b * z * (x * b)⁻¹ * z⁻¹ = x * z * x⁻¹ * z⁻¹ := by
  rw [hS.commutator_mul_left h34 hx (hS.T_le (gmsA_le_T hb)) hz]
  have h1 := hS.commute_gmsA hz hb
  have e : b * z * b⁻¹ * z⁻¹ = 1 := by rw [← h1]; group
  rw [e, mul_one]

theorem commutator_mul_gmsA_right {x z b : G} (hx : x ∈ R) (hz : z ∈ R) (hb : b ∈ gmsA L T) :
    x * (z * b) * x⁻¹ * (z * b)⁻¹ = x * z * x⁻¹ * z⁻¹ := by
  rw [hS.commutator_mul_right h34 hx hz (hS.T_le (gmsA_le_T hb))]
  have h1 := hS.commute_gmsA hx hb
  have e : x * b * x⁻¹ * b⁻¹ = 1 := by rw [h1]; group
  rw [e, mul_one]

omit h34 in
theorem sq_mul_gmsA {x b : G} (hx : x ∈ R) (hb : b ∈ gmsA L T) : (x * b) ^ 2 = x ^ 2 := by
  obtain ⟨-, hA₁sq, -⟩ := hS.facts.sylow hS.sec3
  have h1 := hS.commute_gmsA hx hb
  calc (x * b) ^ 2 = x * (b * x) * b := by simp only [sq]; group
    _ = x * x * b ^ 2 := by rw [← h1]; simp only [sq]; group
    _ = x ^ 2 := by rw [hA₁sq b hb, mul_one, sq]

end Calculus

section Rho

variable (hS : SzR G L T R a y d)
  (hc : RootCoords (T ⊓ L) a d u v κ) {s₀ : G} (hs₀ : s₀ ∈ T ⊓ centralizer (L : Set G))
include hS hc hs₀

omit hc in
theorem comm_mem_gmsA_of_T₀ {x : G} (hx : x ∈ R) : x * s₀ * x⁻¹ * s₀⁻¹ ∈ gmsA L T :=
  conj_mul_inv_mem (hS.isR.le_gmsTrans hx) (mem_sup_right hs₀)

theorem rho_mul {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) :
    v (x * x' * s₀ * (x * x')⁻¹ * s₀⁻¹) = v (x * s₀ * x⁻¹ * s₀⁻¹) + v (x' * s₀ * x'⁻¹ * s₀⁻¹) := by
  rw [hS.commutator_mul hs₀ hx hx', hS.v_mul_gmsA hc (hS.comm_mem_gmsA_of_T₀ hs₀ hx)
    (hS.comm_mem_gmsA_of_T₀ hs₀ hx')]

theorem rho_conj {x : G} (hx : x ∈ R) :
    v (d⁻¹ * x * d * s₀ * (d⁻¹ * x * d)⁻¹ * s₀⁻¹) =
      κ ^ (2 ^ (a + 1) + 1) * v (x * s₀ * x⁻¹ * s₀⁻¹) := by
  have h := hS.commutator_conj_pow hs₀ 1 x
  simp only [pow_one] at h
  rw [h, hS.v_conj_gmsA hc (hS.comm_mem_gmsA_of_T₀ hs₀ hx)]

theorem rho_eq_zero_of_mem_T {x : G} (hx : x ∈ T) : v (x * s₀ * x⁻¹ * s₀⁻¹) = 0 := by
  obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hcomm : x * s₀ = s₀ * x :=
    mem_centralizer_iff.mp (hVC (mem_sup_right hs₀)) x (by rw [hS.eq_gmsW] at hx; exact hx)
  have e : x * s₀ * x⁻¹ * s₀⁻¹ = 1 := by rw [hcomm]; group
  rw [e, hc.v_one]

theorem rho_eq_zero_iff (hR₂ : IsR₂ L T R R₂ d) (hs₀1 : s₀ ≠ 1) {r : G} (hr : r ∈ R₂) :
    v (r * s₀ * r⁻¹ * s₀⁻¹) = 0 ↔ r ∈ gmsA L T := by
  rw [← hS.commutator_eq_one_iff hR₂ hs₀ hs₀1 hr]
  refine ⟨hS.eq_one_of_v_eq_zero hc (hS.comm_mem_gmsA_of_T₀ hs₀ (hR₂.le_R hr)), fun h => ?_⟩
  rw [h, hc.v_one]

theorem exists_rho_eq (hR₂ : IsR₂ L T R R₂ d) (hs₀1 : s₀ ≠ 1) (w : BinaryGaloisField (2 * a + 1)) :
    ∃ r ∈ R₂, v (r * s₀ * r⁻¹ * s₀⁻¹) = w := by
  obtain ⟨b, hb, hbw⟩ := hS.exists_v_eq hc w
  obtain ⟨r, hr, hrb⟩ := hS.exists_commutator_eq hR₂ hs₀ hs₀1 hb
  exact ⟨r, hr, by rw [hrb, hbw]⟩

theorem inv_mul_mem_of_rho_eq (hR₂ : IsR₂ L T R R₂ d) (hs₀1 : s₀ ≠ 1) {r r' : G} (hr : r ∈ R₂)
    (hr' : r' ∈ R₂) (h : v (r * s₀ * r⁻¹ * s₀⁻¹) = v (r' * s₀ * r'⁻¹ * s₀⁻¹)) :
    r⁻¹ * r' ∈ gmsA L T := by
  rw [← hS.rho_eq_zero_iff hc hs₀ hR₂ hs₀1 (mul_mem (inv_mem hr) hr'),
    hS.rho_mul hc hs₀ (hR₂.le_R (inv_mem hr)) (hR₂.le_R hr')]
  have h0 := hS.rho_mul hc hs₀ (hR₂.le_R (inv_mem hr)) (hR₂.le_R hr)
  have e : r⁻¹ * r * s₀ * (r⁻¹ * r)⁻¹ * s₀⁻¹ = 1 := by group
  rw [e, hc.v_one] at h0
  linear_combination -h0 - h

end Rho

section Constants

variable (hS : SzR G L T R a y d)
  (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d) (hc : RootCoords (T ⊓ L) a d u v κ)
  {s₀ : G} (hs₀ : s₀ ∈ T ⊓ centralizer (L : Set G)) (hs₀1 : s₀ ≠ 1)
  (hμ : ∀ w, w ≠ 0 → ∃ m : ℕ, (κ ^ (2 ^ (a + 1) + 1)) ^ m = w)
include hS h34 hR₂ hc hs₀ hs₀1 hμ

omit h34 hμ in
theorem commutator_T₀_eq_of_rho_eq {s : G} (hs : s ∈ T ⊓ centralizer (L : Set G)) {r r' : G}
    (hr : r ∈ R₂) (hr' : r' ∈ R₂) (h : v (r * s₀ * r⁻¹ * s₀⁻¹) = v (r' * s₀ * r'⁻¹ * s₀⁻¹)) :
    r' * s * r'⁻¹ * s⁻¹ = r * s * r⁻¹ * s⁻¹ := by
  have hb := hS.inv_mul_mem_of_rho_eq hc hs₀ hR₂ hs₀1 hr hr' h
  have e : r' = r * (r⁻¹ * r') := by group
  rw [e, hS.commutator_mul hs (hR₂.le_R hr) (hS.T_le (gmsA_le_T hb))]
  have h1 : r⁻¹ * r' * s = s * (r⁻¹ * r') :=
    (mem_centralizer_iff.mp (mem_inf.mp hs).2 _ (mem_inf.mp (mem_inf.mp hb).1).2)
  have e2 : r⁻¹ * r' * s * (r⁻¹ * r')⁻¹ * s⁻¹ = 1 := by rw [h1]; group
  rw [e2, mul_one]

omit h34 in
theorem exists_lam : ∃ lam : G → BinaryGaloisField (2 * a + 1),
    ∀ s ∈ T ⊓ centralizer (L : Set G), ∀ r ∈ R₂,
      v (r * s * r⁻¹ * s⁻¹) = lam s * v (r * s₀ * r⁻¹ * s₀⁻¹) := by
  choose! ρ hρ hρw using hS.exists_rho_eq hc hs₀ hR₂ hs₀1
  refine ⟨fun s => v (ρ 1 * s * (ρ 1)⁻¹ * s⁻¹), fun s hs r hr => ?_⟩
  have hf : ∀ w, v (ρ (κ ^ (2 ^ (a + 1) + 1) * w) * s * (ρ (κ ^ (2 ^ (a + 1) + 1) * w))⁻¹ * s⁻¹) =
      κ ^ (2 ^ (a + 1) + 1) * v (ρ w * s * (ρ w)⁻¹ * s⁻¹) := by
    intro w
    have hdr : d⁻¹ * ρ w * d ∈ R₂ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hR₂.mem_normalizer) (ρ w)).mp (hρ w)
    rw [hS.commutator_T₀_eq_of_rho_eq hR₂ hc hs₀ hs₀1 hs hdr (hρ _)
      (by rw [hS.rho_conj hc hs₀ (hR₂.le_R (hρ w)), hρw, hρw])]
    have h := hS.commutator_conj_pow hs 1 (ρ w)
    simp only [pow_one] at h
    rw [h, hS.v_conj_gmsA hc (conj_mul_inv_mem (hS.isR.le_gmsTrans (hR₂.le_R (hρ w)))
      (mem_sup_right hs))]
  have h0 : v (ρ 0 * s * (ρ 0)⁻¹ * s⁻¹) = 0 := by
    rw [hS.commutator_T₀_eq_of_rho_eq hR₂ hc hs₀ hs₀1 hs (one_mem _) (hρ 0)
      (by rw [hρw, hS.rho_eq_zero_of_mem_T hc hs₀ (one_mem _)])]
    have e : (1 : G) * s * 1⁻¹ * s⁻¹ = 1 := by group
    rw [e, hc.v_one]
  have hlin := VLike.linear_of_equivariant (f := fun w => v (ρ w * s * (ρ w)⁻¹ * s⁻¹)) hf h0 hμ
    (v (r * s₀ * r⁻¹ * s₀⁻¹))
  rw [← hS.commutator_T₀_eq_of_rho_eq hR₂ hc hs₀ hs₀1 hs (hρ _) hr (hρw _)] at hlin
  exact hlin

omit h34 hμ in
theorem sq_eq_of_rho_eq {r r' : G} (hr : r ∈ R₂) (hr' : r' ∈ R₂)
    (h : v (r * s₀ * r⁻¹ * s₀⁻¹) = v (r' * s₀ * r'⁻¹ * s₀⁻¹)) : r' ^ 2 = r ^ 2 := by
  have hb := hS.inv_mul_mem_of_rho_eq hc hs₀ hR₂ hs₀1 hr hr' h
  have e : r' = r * (r⁻¹ * r') := by group
  rw [e, hS.sq_mul_gmsA (hR₂.le_R hr) hb]

theorem exists_e : ∃ e : BinaryGaloisField (2 * a + 1), ∀ r ∈ R₂,
    v (r ^ 2) = e * v (r * s₀ * r⁻¹ * s₀⁻¹) := by
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨-, hA₁sq, -⟩ := hS.facts.sylow hS.sec3
  choose! ρ hρ hρw using hS.exists_rho_eq hc hs₀ hR₂ hs₀1
  refine ⟨v (ρ 1 ^ 2), fun r hr => ?_⟩
  have hf : ∀ w, v (ρ (κ ^ (2 ^ (a + 1) + 1) * w) ^ 2) = κ ^ (2 ^ (a + 1) + 1) * v (ρ w ^ 2) := by
    intro w
    have hdr : d⁻¹ * ρ w * d ∈ R₂ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hR₂.mem_normalizer) (ρ w)).mp (hρ w)
    rw [hS.sq_eq_of_rho_eq hR₂ hc hs₀ hs₀1 hdr (hρ _)
      (by rw [hS.rho_conj hc hs₀ (hR₂.le_R (hρ w)), hρw, hρw])]
    have e : (d⁻¹ * ρ w * d) ^ 2 = d⁻¹ * ρ w ^ 2 * d := by simp only [sq]; group
    rw [e, hS.v_conj_gmsA hc (hS.sq_mem_gmsA_of_mem_R h34 hX (hR₂.le_R (hρ w)))]
  have h0 : v (ρ 0 ^ 2) = 0 := by
    have hA : ρ 0 ∈ gmsA L T := (hS.rho_eq_zero_iff hc hs₀ hR₂ hs₀1 (hρ 0)).mp (hρw 0)
    rw [hA₁sq _ hA, hc.v_one]
  have hlin := VLike.linear_of_equivariant (f := fun w => v (ρ w ^ 2)) hf h0 hμ
    (v (r * s₀ * r⁻¹ * s₀⁻¹))
  rw [← hS.sq_eq_of_rho_eq hR₂ hc hs₀ hs₀1 (hρ _) hr (hρw _)] at hlin
  exact hlin

omit hμ in
theorem commutator_eq_of_coord_eq {t t' r r' : G} (ht : t ∈ T ⊓ L) (ht' : t' ∈ T ⊓ L)
    (hr : r ∈ R₂) (hr' : r' ∈ R₂) (hu : u t = u t')
    (h : v (r * s₀ * r⁻¹ * s₀⁻¹) = v (r' * s₀ * r'⁻¹ * s₀⁻¹)) :
    t' * r' * t'⁻¹ * r'⁻¹ = t * r * t⁻¹ * r⁻¹ := by
  have hb := hS.inv_mul_mem_of_rho_eq hc hs₀ hR₂ hs₀1 hr hr' h
  have h2 : (2 : BinaryGaloisField (2 * a + 1)) = 0 := CharTwo.two_eq_zero
  have hb' : t⁻¹ * t' ∈ gmsA L T := by
    refine (hc.mem_center_iff hS.one_le (mul_mem (inv_mem ht) ht')).mpr ?_
    rw [(hc.mul _ (inv_mem ht) _ ht').1, (hc.inv ht).1, hu]
    linear_combination u t' * h2
  have e1 : t' = t * (t⁻¹ * t') := by group
  have e2 : r' = r * (r⁻¹ * r') := by group
  have htR := hS.T_le (mem_inf.mp ht).1
  rw [e1, hS.commutator_mul_gmsA_left h34 htR (hR₂.le_R hr') hb', e2,
    hS.commutator_mul_gmsA_right h34 htR (hR₂.le_R hr) hb]

theorem exists_c : ∃ c : BinaryGaloisField (2 * a + 1), ∀ t ∈ T ⊓ L, ∀ r ∈ R₂,
    v (t * r * t⁻¹ * r⁻¹) = c * (u t * v (r * s₀ * r⁻¹ * s₀⁻¹)) ^ 2 ^ a := by
  classical
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  choose! ρ hρ hρw using hS.exists_rho_eq hc hs₀ hR₂ hs₀1
  choose! τ hτ hτu using fun α => (hc.surj α 0)
  have hτu' : ∀ α, u (τ α) = α := fun α => (hτu α).1
  have hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z * x⁻¹ * z⁻¹ ∈ gmsA L T := fun x hx z hz =>
    hS.commutator_mem_gmsA h34 hx hz
  have hτR : ∀ α, τ α ∈ R := fun α => hS.T_le (mem_inf.mp (hτ α)).1
  have hρR : ∀ w, ρ w ∈ R := fun w => hR₂.le_R (hρ w)
  obtain ⟨β, hβ⟩ : ∃ β : BinaryGaloisField (2 * a + 1) → BinaryGaloisField (2 * a + 1) →
      BinaryGaloisField (2 * a + 1), ∀ α w, β α w = v (τ α * ρ w * (τ α)⁻¹ * (ρ w)⁻¹) :=
    ⟨_, fun _ _ => rfl⟩
  have hwd : ∀ t ∈ T ⊓ L, ∀ r ∈ R₂, v (t * r * t⁻¹ * r⁻¹) = β (u t) (v (r * s₀ * r⁻¹ * s₀⁻¹)) :=
    fun t ht r hr => by
      rw [hβ, hS.commutator_eq_of_coord_eq h34 hR₂ hc hs₀ hs₀1 ht (hτ (u t)) hr (hρ _)
        (hτu' _).symm (hρw _).symm]
  have h1 : ∀ α α' w, β (α + α') w = β α w + β α' w := by
    intro α α' w
    have hm := (hc.mul _ (hτ α) _ (hτ α')).1
    rw [hβ, hβ, hβ, hS.commutator_eq_of_coord_eq h34 hR₂ hc hs₀ hs₀1 (mul_mem (hτ α) (hτ α'))
      (hτ (α + α')) (hρ w) (hρ w) (by rw [hm, hτu', hτu', hτu']) rfl,
      hS.commutator_mul_left h34 (hτR α) (hτR α') (hρR w),
      hS.v_mul_gmsA hc (hcomm _ (hτR α) _ (hρR w)) (hcomm _ (hτR α') _ (hρR w))]
  have h2' : ∀ α w w', β α (w + w') = β α w + β α w' := by
    intro α w w'
    rw [hβ, hβ, hβ, hS.commutator_eq_of_coord_eq h34 hR₂ hc hs₀ hs₀1 (hτ α) (hτ α)
      (mul_mem (hρ w) (hρ w')) (hρ (w + w')) rfl
      (by rw [hS.rho_mul hc hs₀ (hρR w) (hρR w'), hρw, hρw, hρw]),
      hS.commutator_mul_right h34 (hτR α) (hρR w) (hρR w'),
      hS.v_mul_gmsA hc (hcomm _ (hτR α) _ (hρR w)) (hcomm _ (hτR α) _ (hρR w'))]
  have hκ : ∀ w, w ≠ 0 → ∃ m : ℕ, κ ^ m = w := fun w hw => by
    obtain ⟨m, hm⟩ := hμ w hw
    exact ⟨(2 ^ (a + 1) + 1) * m, by rw [pow_mul]; exact hm⟩
  have heq : ∀ α w, β (κ * α) (κ ^ (2 ^ (a + 1) + 1) * w) = κ ^ (2 ^ (a + 1) + 1) * β α w := by
    intro α w
    have hdt : d⁻¹ * τ α * d ∈ T ⊓ L := hc.conj_mem _ (hτ α)
    have hdr : d⁻¹ * ρ w * d ∈ R₂ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hR₂.mem_normalizer) (ρ w)).mp (hρ w)
    have e : d⁻¹ * τ α * d * (d⁻¹ * ρ w * d) * (d⁻¹ * τ α * d)⁻¹ * (d⁻¹ * ρ w * d)⁻¹ =
        d⁻¹ * (τ α * ρ w * (τ α)⁻¹ * (ρ w)⁻¹) * d := by group
    rw [hβ, hβ, hS.commutator_eq_of_coord_eq h34 hR₂ hc hs₀ hs₀1 hdt (hτ _) hdr (hρ _)
      (by rw [hc.conj_u _ (hτ α), hτu', hτu']) (by rw [hS.rho_conj hc hs₀ (hρR w), hρw, hρw]), e,
      hS.v_conj_gmsA hc (hcomm _ (hτR α) _ (hρR w))]
  obtain ⟨c, hc'⟩ := VLike.bilinear_of_equivariant' hS.one_le hK β h1 h2' hκ heq
  exact ⟨c, fun t ht r hr => by rw [hwd t ht r hr, hc']⟩

end Constants

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
