module

public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQuot
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {t : X}

@[expose] def e8Word (b₁ b₂ b₃ : Bool) : QuaternionGroup 2 × QuaternionGroup 2 :=
  (if b₁ then (a 2, 1) else 1) * ((if b₂ then (a 1, a 1) else 1) * (if b₃ then (xa 0, xa 0) else 1))

theorem e8Word_eq : ∀ b₁ b₂ b₃ : Bool, (e8Word b₁ b₂ b₃ = 1 ∨ e8Word b₁ b₂ b₃ = (a 2, a 2)) →
    b₁ = false ∧ b₂ = false ∧ b₃ = false := by
  unfold e8Word
  decide

theorem zmodHom_two_apply {Q : Type*} [Group Q] (c : Q) (hc : c ^ 2 = 1)
    (m : Multiplicative (ZMod 2)) :
    LocalAnalysis.ComponentInitial.zmodHom 2 c hc m =
      if m = Multiplicative.ofAdd 1 then c else 1 := by
  have hm : m = 1 ∨ m = Multiplicative.ofAdd 1 := by revert m; decide
  rcases hm with rfl | rfl
  · split_ifs with h
    · exact absurd h (by decide)
    · exact map_one _
  · split_ifs with h
    · exact LocalAnalysis.ComponentInitial.zmodHom_ofAdd_one 2 c hc
    · exact absurd rfl h

section Quot

variable (hD : TightDatum R S t)
include hD

theorem datum_three_le_twoRank {H : Subgroup X}
    (hHC : H ≤ Subgroup.centralizer ({t} : Set X)) [Group.IsPerfect H]
    (φ : QuaternionGroup 2 →* X) (hi : Function.Injective φ) (hr : ∀ x, φ x ∈ H)
    (ht : φ (a 1) ^ 2 = t) : 3 ≤ CFSG.Open.twoRank X := by
  have := datum_oddCore_normal hD
  set C := Subgroup.centralizer ({t} : Set X) with hCdef
  set N := (oddCoreImg R).subgroupOf C with hNdef
  obtain ⟨φ₀, hi₀, hr₀, ht₀⟩ := datum_exists_q8 hD
  have hC₀ : ∀ x, φ₀ x ∈ C := fun x => hD.cent (hr₀ x)
  have hC : ∀ x, φ x ∈ C := fun x => hHC (hr x)
  set α := (QuotientGroup.mk' N).comp (φ₀.codRestrict C hC₀) with hαdef
  set β := (QuotientGroup.mk' N).comp (φ.codRestrict C hC) with hβdef
  have hα : Function.Injective α := datum_lift_injective hD φ₀ hC₀ hi₀
  have hβ : Function.Injective β := datum_lift_injective hD φ hC hi
  have hab : ∀ x y, Commute (α x) (β y) := fun x y =>
    (datum_commute_mk hD (hC y) (hC₀ x) (datum_commutator_mem hD hHC _ (hr y) _ (hr₀ x))).symm
  have hz : α (a 2) = β (a 2) := by
    have e₀ : (φ₀.codRestrict C hC₀) (a 2) = (φ.codRestrict C hC) (a 2) := by
      apply Subtype.ext
      simp only [MonoidHom.codRestrict_apply]
      rw [← q8_a_one_sq, map_pow, map_pow, ht, ht₀]
    simp only [hαdef, hβdef, MonoidHom.comp_apply, e₀]
  let Φ := α.noncommCoprod β hab
  have hΦ : ∀ x y, Φ (x, y) = α x * β y := fun _ _ => rfl
  have hcen : ∀ (γ : QuaternionGroup 2 →* C ⧸ N), Function.Injective γ →
      ∀ x, (∀ z, γ x * γ z = γ z * γ x) → x = 1 ∨ x = a 2 := fun γ hγ x h =>
    q8_central x (fun z => hγ (by rw [map_mul, map_mul, h z]))
  have ha2 : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have hw1 : α (a 2) ≠ 1 := fun h => ha2 (hα (h.trans (map_one α).symm))
  have hk : Φ (a 2, a 2) = 1 := by
    rw [hΦ, ← hz, ← map_mul, show (a 2 : QuaternionGroup 2) * a 2 = 1 by decide, map_one]
  have hker : ∀ x y, Φ (x, y) = 1 → (x = 1 ∧ y = 1) ∨ (x = a 2 ∧ y = a 2) := by
    intro x y h
    rw [hΦ] at h
    have hxy : α x = β y⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
    have hx := hcen α hα x (fun z => by rw [hxy]; exact (hab z y⁻¹).eq.symm)
    have hy := hcen β hβ y⁻¹ (fun z => by rw [← hxy]; exact (hab x z).eq)
    have hy' : y = 1 ∨ y = a 2 := by
      rcases hy with h1 | h1
      · exact Or.inl (inv_eq_one.mp h1)
      · exact Or.inr (by rw [← inv_inv y, h1]; decide)
    rcases hx with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (by simpa [hz] using h) hw1
    · exact absurd (by simpa using h) hw1
    · exact Or.inr ⟨rfl, rfl⟩
  set w := Φ (a 2, 1) with hwdef
  set u := Φ (a 1, a 1) with hudef
  set v := Φ (xa 0, xa 0) with hvdef
  have hcommΦ : ∀ p q : QuaternionGroup 2 × QuaternionGroup 2,
      (p * q = q * p ∨ p * q = q * p * (a 2, a 2)) → Commute (Φ p) (Φ q) := by
    intro p q h
    show Φ p * Φ q = Φ q * Φ p
    rcases h with h | h
    · rw [← map_mul, h, map_mul]
    · rw [← map_mul, h, map_mul, map_mul, hk, mul_one]
  have hsq : ∀ p : QuaternionGroup 2 × QuaternionGroup 2,
      (p * p = 1 ∨ p * p = (a 2, a 2)) → Φ p ^ 2 = 1 := by
    intro p h
    rw [sq, ← map_mul]
    rcases h with h | h
    · rw [h, map_one]
    · rw [h, hk]
  have hw2 : w ^ 2 = 1 := hsq _ (by decide)
  have hu2 : u ^ 2 = 1 := hsq _ (by decide)
  have hv2 : v ^ 2 = 1 := hsq _ (by decide)
  have huv : Commute u v := hcommΦ _ _ (by decide)
  have hwu : Commute w u := hcommΦ _ _ (by decide)
  have hwv : Commute w v := hcommΦ _ _ (by decide)
  have h₁ := zmodHom_two_apply w hw2
  have h₂ := zmodHom_two_apply u hu2
  have h₃ := zmodHom_two_apply v hv2
  set f₁ := LocalAnalysis.ComponentInitial.zmodHom 2 w hw2
  set f₂ := LocalAnalysis.ComponentInitial.zmodHom 2 u hu2
  set f₃ := LocalAnalysis.ComponentInitial.zmodHom 2 v hv2
  have hc23 : ∀ m n, Commute (f₂ m) (f₃ n) := by
    intro m n
    rw [h₂, h₃]
    split_ifs
    · exact huv
    · exact Commute.one_right _
    · exact Commute.one_left _
    · exact Commute.one_left _
  set f₂₃ := f₂.noncommCoprod f₃ hc23
  have hc1 : ∀ m n, Commute (f₁ m) (f₂₃ n) := by
    intro m n
    show Commute (f₁ m) (f₂ n.1 * f₃ n.2)
    rw [h₁, h₂, h₃]
    split_ifs
    · exact hwu.mul_right hwv
    · simpa using hwu
    · simpa using hwv
    · simp
    all_goals simp
  set f := f₁.noncommCoprod f₂₃ hc1
  have key : ∀ b₁ b₂ b₃ : Bool, Φ (e8Word b₁ b₂ b₃) =
      (if b₁ then w else 1) * ((if b₂ then u else 1) * (if b₃ then v else 1)) := by
    intro b₁ b₂ b₃
    unfold e8Word
    rw [map_mul, map_mul]
    cases b₁ <;> cases b₂ <;> cases b₃ <;> simp [hwdef, hudef, hvdef]
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m₁, m₂, m₃⟩ hm
    have hm' : Φ (e8Word (decide (m₁ = Multiplicative.ofAdd 1))
        (decide (m₂ = Multiplicative.ofAdd 1)) (decide (m₃ = Multiplicative.ofAdd 1))) = 1 := by
      rw [key]
      have e : f (m₁, m₂, m₃) = f₁ m₁ * (f₂ m₂ * f₃ m₃) := rfl
      rw [e, h₁, h₂, h₃] at hm
      simpa using hm
    have hk' := hker _ _ (show Φ ((e8Word _ _ _).1, (e8Word _ _ _).2) = 1 from hm')
    have hw : e8Word (decide (m₁ = Multiplicative.ofAdd 1)) (decide (m₂ = Multiplicative.ofAdd 1))
        (decide (m₃ = Multiplicative.ofAdd 1)) = 1 ∨
      e8Word (decide (m₁ = Multiplicative.ofAdd 1)) (decide (m₂ = Multiplicative.ofAdd 1))
        (decide (m₃ = Multiplicative.ofAdd 1)) = (a 2, a 2) := by
      rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h1 h2)
    obtain ⟨e₁, e₂, e₃⟩ := e8Word_eq _ _ _ hw
    have hz : ∀ m : Multiplicative (ZMod 2),
        decide (m = Multiplicative.ofAdd 1) = false → m = 1 := by
      decide
    rw [hz m₁ e₁, hz m₂ e₂, hz m₃ e₃]
    rfl
  have hcard : Nat.card (Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2))) = 2 ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]
    norm_num
  have hpow : ∀ m : Multiplicative (ZMod 2) × (Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2)), m ^ 2 = 1 := by decide
  have h3 := SectionRank.le_pRank_of_injective (G := C ⧸ N) (by norm_num) (fun a b => mul_comm a b)
    hpow hcard f hf (H := ⊤) le_top
  have hN2 : ¬ 2 ∣ Nat.card N := by
    intro h2
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have hmem : ((n : C) : X) ∈ oddCoreImg R := Subgroup.mem_subgroupOf.mp n.2
    have h8 : orderOf ((n : C) : X) ∣ 8 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hn]; norm_num
    have h1 := eq_one_of_mem_oddCoreImg hmem h8
    have : n = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hn
    exact absurd hn (by norm_num)
  have hq := SectionRank.pRank_quotient_eq (G := C) (p := 2) (hp := ⟨Nat.prime_two⟩) N hN2
  have hle := SectionRank.pRank_top_le_of_injective (p := 2) (by norm_num) C.subtype
    C.subtype_injective
  show 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X)
  omega

end Quot

end CFSG.ClassicalInvolution.Q3.TA3
