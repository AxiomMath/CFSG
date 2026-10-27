module

public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.ClassicalInvolution.Asc77.AscSCH02

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

theorem alt_full_eq_zero {K : Type*} [Field K] {A : Type*} [AddCommGroup A] (b : K → K → A)
    (h2 : ∀ x y, 2 • b x y = 0 → b x y = 0)
    (hadd₁ : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y + b x y') (halt : ∀ x, b x x = 0)
    (hinv : ∀ a : K, a ≠ 0 → ∀ x y, b (a * x) (a * y) = b x y) (x y : K) : b x y = 0 := by
  have hz₁ : ∀ y, b 0 y = 0 := fun y => by
    have := hadd₁ 0 0 y
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hz₂ : ∀ x, b x 0 = 0 := fun x => by
    have := hadd₂ x 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hneg₂ : ∀ x y, b x (-y) = -b x y := fun x y => by
    have := hadd₂ x y (-y)
    rw [add_neg_cancel, hz₂] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have halt' : ∀ x y, b x y = - b y x := fun x y => by
    have h := halt (x + y)
    rw [hadd₁, hadd₂, hadd₂, halt, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  set c : K → A := fun u => b 1 u with hc
  have hcadd : ∀ u u', c (u + u') = c u + c u' := fun u u' => hadd₂ 1 u u'
  have hc1 : c 1 = 0 := halt 1
  have hcneg : ∀ u, c (-u) = - c u := fun u => hneg₂ 1 u
  have hbc : ∀ s w, s ≠ 0 → b s w = c (w / s) := by
    intro s w hs
    have := hinv s⁻¹ (inv_ne_zero hs) s w
    rw [inv_mul_cancel₀ hs] at this
    rw [hc]
    show b s w = b 1 (w / s)
    rw [← this]
    congr 1
    field_simp
  have hI : ∀ t : K, t ≠ 0 → 1 + t ≠ 0 → c (t ^ 2) = - c t := by
    intro t ht h1t
    have h := hadd₁ 1 t (t * (1 + t))
    rw [hbc 1 _ one_ne_zero, hbc t _ ht, hbc (1 + t) _ h1t] at h
    have e1 : t * (1 + t) / 1 = t + t ^ 2 := by ring
    have e2 : t * (1 + t) / t = 1 + t := by field_simp
    have e3 : t * (1 + t) / (1 + t) = t := by field_simp
    rw [e1, e2, e3, hcadd, hcadd, hc1, zero_add] at h
    rw [add_assoc] at h
    exact eq_neg_of_add_eq_zero_left (left_eq_add.mp h)
  have hc0 : c 0 = 0 := by
    have := hcadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hcz : ∀ u, c u = 0 := by
    intro u
    by_cases hu0 : u = 0
    · rw [hu0]; exact hc0
    by_cases hu1 : u = 1
    · rw [hu1]; exact hc1
    by_cases hum : u = -1
    · rw [hum, hcneg, hc1, neg_zero]
    have h1 := hI u hu0 (fun h => hum (by linear_combination h))
    have h2' := hI (-u) (neg_ne_zero.2 hu0) (fun h => hu1 (by linear_combination -h))
    rw [neg_sq, hcneg, neg_neg] at h2'
    have h3 : c u = - c u := h2'.symm.trans h1
    exact h2 1 u (by rw [two_nsmul]; exact add_eq_zero_iff_eq_neg.2 h3)
  by_cases hx : x = 0
  · rw [hx]; exact hz₁ y
  · rw [hbc x y hx]; exact hcz _

section Pairing

open CFSG.RankThree.Classical

variable {Y X : Type*} [Group Y] [Group X] {φ : Y →* X} (hφ : Function.Surjective φ)
  {V : Type*} [AddCommGroup V] (ρ : Multiplicative V →* X) (hZ : φ.ker ≤ Subgroup.center Y)
include hZ

theorem liftPair_eq_one_of_scale_right {K : Type*} [Field K] (e₁ e₂ : K →+ V) (g : X) (μ : K)
    (hμ : μ ≠ 1)
    (hg₁ : ∀ s, g * ρ (Multiplicative.ofAdd (e₁ s)) * g⁻¹ = ρ (Multiplicative.ofAdd (e₁ s)))
    (hg₂ : ∀ t, g * ρ (Multiplicative.ofAdd (e₂ t)) * g⁻¹ =
      ρ (Multiplicative.ofAdd (e₂ (μ * t)))) (s t : K) :
    liftPair hφ ρ (e₁ s) (e₂ t) = 1 := by
  have h1 : ∀ s t, liftPair hφ ρ (e₁ s) (e₂ (μ * t)) = liftPair hφ ρ (e₁ s) (e₂ t) :=
    fun s t => liftPair_conj' hφ ρ hZ g (hg₁ s) (hg₂ t)
  have hμ' : μ - 1 ≠ 0 := sub_ne_zero.2 hμ
  set t₀ := t / (μ - 1) with ht₀
  have hmu : μ * t₀ = t₀ + t := by rw [ht₀]; field_simp; ring
  have h2 := h1 s t₀
  rw [hmu, map_add, liftPair_add_right hφ ρ hZ] at h2
  exact left_eq_mul.mp h2.symm

theorem liftPair_eq_one_of_scale_left {K : Type*} [Field K] (e₁ e₂ : K →+ V) (g : X) (μ : K)
    (hμ : μ ≠ 1)
    (hg₁ : ∀ s, g * ρ (Multiplicative.ofAdd (e₁ s)) * g⁻¹ =
      ρ (Multiplicative.ofAdd (e₁ (μ * s))))
    (hg₂ : ∀ t, g * ρ (Multiplicative.ofAdd (e₂ t)) * g⁻¹ = ρ (Multiplicative.ofAdd (e₂ t)))
    (s t : K) : liftPair hφ ρ (e₁ s) (e₂ t) = 1 := by
  have h1 : ∀ s t, liftPair hφ ρ (e₁ (μ * s)) (e₂ t) = liftPair hφ ρ (e₁ s) (e₂ t) :=
    fun s t => liftPair_conj' hφ ρ hZ g (hg₁ s) (hg₂ t)
  have hμ' : μ - 1 ≠ 0 := sub_ne_zero.2 hμ
  set s₀ := s / (μ - 1) with hs₀
  have hmu : μ * s₀ = s₀ + s := by rw [hs₀]; field_simp; ring
  have h2 := h1 s₀ t
  rw [hmu, map_add, liftPair_add_left hφ ρ hZ] at h2
  exact left_eq_mul.mp h2.symm

variable {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hCp : IsPGroup p φ.ker)

theorem liftPair_mem_ker (v w : V) : liftPair hφ ρ v w ∈ φ.ker := by
  rw [← commutatorElement_eq_liftPair hφ ρ hZ (map_lift hφ (ρ (Multiplicative.ofAdd v)))
    (map_lift hφ (ρ (Multiplicative.ofAdd w))), MonoidHom.mem_ker, map_commutatorElement,
    map_lift, map_lift, commutatorElement_eq_one_iff_mul_comm]
  exact commute_rho ρ v w

include hp2 hCp in
theorem liftPair_eq_one_of_mul_self (v w : V)
    (h : liftPair hφ ρ v w * liftPair hφ ρ v w = 1) : liftPair hφ ρ v w = 1 :=
  eq_one_of_central_inv hp2 φ hCp (liftPair_mem_ker hφ ρ hZ v w) (eq_inv_of_mul_eq_one_left h)

theorem liftPairAdd_two_nsmul_eq_zero (v w : V) (h : 2 • liftPairAdd hφ ρ hZ v w = 0) :
    liftPair hφ ρ v w * liftPair hφ ρ v w = 1 := by
  let _ := centerCommGroup Y
  rw [two_nsmul, liftPairAdd] at h
  have := congrArg (fun x : Additive (Subgroup.center Y) => ((Additive.toMul x : _) : Y)) h
  simpa using this

include hp2 hCp in
theorem liftPair_self_eq_one_of_full {K : Type*} [Field K] (e : K →+ V)
    (hfull : ∀ c : K, c ≠ 0 → ∃ g : X, ∀ s, g * ρ (Multiplicative.ofAdd (e s)) * g⁻¹ =
      ρ (Multiplicative.ofAdd (e (c * s)))) (s t : K) :
    liftPair hφ ρ (e s) (e t) = 1 := by
  let _ := centerCommGroup Y
  have hb := alt_full_eq_zero (K := K) (fun s t => liftPairAdd hφ ρ hZ (e s) (e t))
    (fun x y h => by
      rw [liftPairAdd_eq_zero_iff hφ ρ hZ]
      exact liftPair_eq_one_of_mul_self hφ ρ hZ hp2 hCp _ _
        (liftPairAdd_two_nsmul_eq_zero hφ ρ hZ _ _ h))
    (fun x x' y => by simp only [map_add]; exact liftPairAdd_add_left hφ ρ hZ _ _ _)
    (fun x y y' => by simp only [map_add]; exact liftPairAdd_add_right hφ ρ hZ _ _ _)
    (fun x => liftPairAdd_self hφ ρ hZ _)
    (fun a ha x y => by
      obtain ⟨g, hg⟩ := hfull a ha
      exact liftPairAdd_congr hφ ρ hZ (liftPair_conj' hφ ρ hZ g (hg x) (hg y))) s t
  exact (liftPairAdd_eq_zero_iff hφ ρ hZ _ _).1 hb

theorem liftPair_self_eq_one_of_sq {K : Type*} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (hK : Nat.card K = ℓ ^ f) (h9 : ℓ ^ f ≠ 9) (e : K →+ V)
    (hsq : ∀ c : K, c ≠ 0 → ∃ g : X, ∀ s, g * ρ (Multiplicative.ofAdd (e s)) * g⁻¹ =
      ρ (Multiplicative.ofAdd (e (c ^ 2 * s)))) (s t : K) :
    liftPair hφ ρ (e s) (e t) = 1 := by
  let _ := centerCommGroup Y
  have hb := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero (K := K) hℓ2 hK
    (fun s t => liftPairAdd hφ ρ hZ (e s) (e t))
    (fun x x' y => by simp only [map_add]; exact liftPairAdd_add_left hφ ρ hZ _ _ _)
    (fun x y y' => by simp only [map_add]; exact liftPairAdd_add_right hφ ρ hZ _ _ _)
    (fun x => liftPairAdd_self hφ ρ hZ _)
    (fun a ha x y => by
      obtain ⟨g, hg⟩ := hsq a ha
      exact liftPairAdd_congr hφ ρ hZ (liftPair_conj' hφ ρ hZ g (hg x) (hg y))) h9 s t
  exact (liftPairAdd_eq_zero_iff hφ ρ hZ _ _).1 hb

end Pairing

end CFSG.ClassicalInvolution.Asc77.SCH
