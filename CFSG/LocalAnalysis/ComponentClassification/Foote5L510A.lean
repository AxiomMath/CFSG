module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53F
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L58C

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_of_cover {P S : Subgroup G} {h : G}
    (hcov : ∀ x ∈ P, x ∈ S ∨ h⁻¹ * x ∈ S) : Nat.card P ≤ 2 * Nat.card S := by
  classical
  let f : P → S ⊕ S := fun x =>
    if hx : (x : G) ∈ S then Sum.inl ⟨x, hx⟩
    else Sum.inr ⟨h⁻¹ * x, (hcov x x.2).resolve_left hx⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) ∈ S <;> by_cases hy : (y : G) ∈ S <;>
      simp only [f, hx, hy, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq] at hxy
    · have h1 := congrArg (fun u : S => (u : G)) hxy
      exact Subtype.ext h1
    · have h1 := congrArg (fun u : S => (u : G)) hxy
      simp only at h1
      exact Subtype.ext (mul_left_cancel h1)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at h1
  omega

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem mem_S_of_mem_normalizer_Q {x : G} (hxT : x ∈ T) (hxN : x ∈ normalizer (Q : Set G)) :
    x ∈ S := by
  by_contra hxS
  exact h.not_mem_normalizer_Q hxT hxS hxN

theorem commute_conjugate_R_of_le (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S) {H : Subgroup G} (hRH : S ⊓ L ≤ H) (hHS : H ≤ S)
    {a : G} (haT : a ∈ T) (haS : a ∉ S) (haN : a ∈ normalizer (H : Set G)) :
    ∀ r ∈ S ⊓ L, ∀ b ∈ conjugate (S ⊓ L) a, r * b = b * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := S ⊓ L with hR
  have hRaH : conjugate R a ≤ H := fun x hx => by
    have h1 := hRH (mem_conjugate_iff.mp hx)
    have h2 := (mem_normalizer_iff.mp (inv_mem haN) (a * x * a⁻¹)).mp h1
    rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at h2
  have hRnorm : ∀ r ∈ R, ∀ b ∈ conjugate R a, r * b * r⁻¹ ∈ conjugate R a := by
    intro r hr b hb
    have hrH : a * r * a⁻¹ ∈ S := hHS ((mem_normalizer_iff.mp haN r).mp (hRH hr))
    rw [mem_conjugate_iff, show a * (r * b * r⁻¹) * a⁻¹ =
      (a * r * a⁻¹) * (a * b * a⁻¹) * (a * r * a⁻¹)⁻¹ by group]
    exact h.conj_mem_R hrH (mem_conjugate_iff.mp hb)
  have hRaR : ∀ b ∈ conjugate R a, ∀ r ∈ R, b * r * b⁻¹ ∈ R := fun b hb r hr =>
    h.conj_mem_R (hHS (hRaH hb)) hr
  have hbot : R ⊓ conjugate R a = ⊥ := by
    by_contra hne
    have hP : IsPGroup 2 ↥(R ⊔ conjugate R a) :=
      h.isPGroup_S.to_le (sup_le inf_le_left (hRaH.trans hHS))
    have hN : R ⊔ conjugate R a ≤ normalizer ((R ⊓ conjugate R a : Subgroup G) : Set G) := by
      refine sup_le (le_normalizer_of_conj_mem fun r hr y hy =>
        mem_inf.mpr ⟨h.conj_mem_R (mem_inf.mp hr).1 (mem_inf.mp hy).1,
          hRnorm r hr y (mem_inf.mp hy).2⟩)
        (le_normalizer_of_conj_mem fun b hb y hy =>
          mem_inf.mpr ⟨hRaR b hb y (mem_inf.mp hy).1, mul_mem (mul_mem hb (mem_inf.mp hy).2)
            (inv_mem hb)⟩)
    obtain ⟨u, huN, hu2, huZ⟩ := exists_involution_center hP (inf_le_left.trans le_sup_left) hN hne
    have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu2; omega
    have hut : u = t := by
      rcases h.center_R hna (mem_inf.mp huN).1 (fun r hr => (huZ r (mem_sup_left hr)).symm)
        with h1 | h1
      · exact absurd h1 hu1
      · exact h1
    have hauR : a * u * a⁻¹ ∈ R := mem_conjugate_iff.mp (mem_inf.mp huN).2
    have hauZ : ∀ r ∈ R, a * u * a⁻¹ * r = r * (a * u * a⁻¹) := by
      intro r hr
      have hb : a⁻¹ * r * a ∈ conjugate R a := by
        rw [mem_conjugate_iff, show a * (a⁻¹ * r * a) * a⁻¹ = r by group]
        exact hr
      have h1 := huZ _ (mem_sup_right hb)
      calc a * u * a⁻¹ * r = a * (u * (a⁻¹ * r * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * r * a) * u) * a⁻¹ := by rw [h1]
        _ = r * (a * u * a⁻¹) := by group
    rcases h.center_R hna hauR hauZ with h1 | h1
    · apply hu1
      calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
        _ = 1 := by rw [h1]; group
    · apply haS
      refine hCt a haT ?_
      calc a * t = (a * u * a⁻¹) * a := by rw [hut]; group
        _ = t * a := by rw [h1]
  intro r hr b hb
  have h1 : b * r * b⁻¹ * r⁻¹ ∈ R ⊓ conjugate R a := by
    refine mem_inf.mpr ⟨mul_mem (hRaR b hb r hr) (inv_mem hr), ?_⟩
    rw [show b * r * b⁻¹ * r⁻¹ = b * (r * b⁻¹ * r⁻¹) by group]
    exact mul_mem hb (hRnorm r hr _ (inv_mem hb))
  rw [hbot, mem_bot] at h1
  calc r * b = (b * r * b⁻¹ * r⁻¹)⁻¹ * (b * r) := by group
    _ = b * r := by rw [h1, inv_one, one_mul]

include ε in
theorem card_normalizer_le_of_R_le (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ : 4 < Nat.card Q)
    (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S) {H : Subgroup G} (hRH : S ⊓ L ≤ H) (hHS : H ≤ S) :
    Nat.card ↥(T ⊓ normalizer (H : Set G)) ≤ 2 * Nat.card S := by
  set P := T ⊓ normalizer (H : Set G) with hP
  have hta : ∀ a ∈ P, a ∉ S → t ∈ conjugate Q a⁻¹ := by
    intro a haP haS
    have haT := (mem_inf.mp haP).1
    have haN := (mem_inf.mp haP).2
    have hcomm := h.commute_conjugate_R_of_le hna hCt hRH hHS haT haS haN
    have hRaS : conjugate (S ⊓ L) a ≤ S := fun x hx => by
      have h1 := hRH (mem_conjugate_iff.mp hx)
      have h2 := (mem_normalizer_iff.mp (inv_mem haN) (a * x * a⁻¹)).mp h1
      rw [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at h2
      exact hHS h2
    have hle : ⁅conjugate (S ⊓ L) a, conjugate (S ⊓ L) a⁆ ≤ Q := by
      rw [commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact h.commutator_mem_Q_of_centralizes ε hD hRaS
        (fun b hb r hr => (hcomm r hr b hb).symm) hx hy
    have h1 := conj_mem_commutator_conjugate (a := a⁻¹) (h.t_mem_commutator_R ε hD hna)
    rw [inv_inv] at h1
    rw [mem_conjugate_iff, inv_inv]
    exact hle h1
  by_contra hcard
  push Not at hcard
  obtain ⟨h₁, hh₁P, hh₁S⟩ : ∃ x ∈ P, x ∉ S := by
    by_contra hno
    push Not at hno
    have h1 := card_le_two_mul_of_cover (P := P) (S := S) (h := 1) fun x hx => Or.inl (hno x hx)
    omega
  obtain ⟨k, hkP, hkS, hkh⟩ : ∃ x ∈ P, x ∉ S ∧ h₁⁻¹ * x ∉ S := by
    by_contra hno
    push Not at hno
    have h1 := card_le_two_mul_of_cover (P := P) (S := S) (h := h₁) fun x hx => by
      by_cases hxS : x ∈ S
      · exact Or.inl hxS
      · exact Or.inr (hno x hx hxS)
    omega
  have hcc : ∀ x y : G, conjugate (conjugate Q x) y = conjugate Q (x * y) := fun x y => by
    ext a
    rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
      show x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ by group]
  have hc1 : conjugate Q 1 = Q := by
    ext a
    rw [mem_conjugate_iff, one_mul, inv_one, mul_one]
  have hh₁T := (mem_inf.mp hh₁P).1
  have hkT := (mem_inf.mp hkP).1
  have hne : conjugate Q h₁⁻¹ ≠ conjugate Q k⁻¹ := by
    intro h1
    apply hkh
    refine h.mem_S_of_mem_normalizer_Q (mul_mem (inv_mem hh₁T) hkT)
      (mem_normalizer_of_conjugate_eq ?_)
    rw [← hcc, h1, hcc, inv_mul_cancel, hc1]
  have h1 := (h.lemma58 hQ (inv_mem hh₁T) (inv_mem hkT) hne).1
  have h2 : t ∈ conjugate Q h₁⁻¹ ⊓ conjugate Q k⁻¹ :=
    mem_inf.mpr ⟨hta h₁ hh₁P hh₁S, hta k hkP hkS⟩
  rw [h1, mem_bot] at h2
  exact h.t_ne_one h2

end Sec5

end CFSG.ComponentClassification.Foote5
