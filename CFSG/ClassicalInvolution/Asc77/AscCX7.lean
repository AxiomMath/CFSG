module

public import CFSG.ClassicalInvolution.Asc77.AscCX6
public import CFSG.ClassicalInvolution.Asc77.AscC25W17
import CFSG.ClassicalInvolution.Asc77.AscCX7Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

section Complement

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem mem_zpowers_of_sq {z x : G} (hz2 : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
  · left
    rw [hk, zpow_mul, zpow_two, hz2, one_zpow]
  · right
    rw [hk, zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul]

theorem four_le_card_of_three {D : Subgroup G} (hD2 : IsPGroup 2 D) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 4 ≤ Nat.card D := by
  classical
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have h3 : 3 ≤ Nat.card D := by
    let v : Fin 3 → D := ![⟨1, D.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩]
    have hinj : Function.Injective v := by
      intro i j hij
      have hij' := congrArg Subtype.val hij
      fin_cases i <;> fin_cases j <;> simp_all [v, eq_comm]
    have := Nat.card_le_card_of_injective v hinj
    rwa [Nat.card_fin] at this
  rw [hk] at h3 ⊢
  rcases k with _ | _ | k
  · norm_num at h3
  · norm_num at h3
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_bad_complement_of_ext (h6 : Layer6Twin p f)
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))) {y : G}
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hya : y * a = a * y) (hy2 : C25W.InFour a z (y * y)) (hyV : ¬ C25W.InFour a z y) :
    ∃ D : Subgroup G, D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      a ∈ D ∧ z ∉ zStarOf (Subgroup.centralizer (D : Set G)) ∧
      (∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
        g ∈ D ∨ g * z ∈ D) ∧ 4 ≤ Nat.card D := by
  exact CFSG.ClassicalInvolution.Asc77.CX7Eng.exists_bad_complement_of_ext_gen
    hyp.std.setting.hz.sq hyp.std.setting.hz.ne_one hyp.hzS (exists_bad_complement h6 hyp)
    mem_zpowers_of_sq four_le_card_of_three haA ha2 ha1 haz hbad hyA hya hy2 hyV

theorem not_mem_of_badSub (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hDbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G))) : z ∉ D := by
  exact CFSG.ClassicalInvolution.Asc77.CX7Eng.not_mem_of_badSub_gen hyp.hzS hDA hDbad

theorem sq_comm_mem_of_complement {A D' : Subgroup G} {z : G} (hz2 : z * z = 1) (hzA : z ∈ A)
    (hzc : ∀ g ∈ A, g * z = z * g) (hcov : ∀ g ∈ A, g ∈ D' ∨ g * z ∈ D')
    {d e : G} (hd : d ∈ A) (he : e ∈ A) : d * d ∈ D' ∧ d * e * d⁻¹ * e⁻¹ ∈ D' := by
  have hzi : z⁻¹ = z := by
    calc z⁻¹ = z⁻¹ * (z * z) := by rw [hz2, mul_one]
      _ = z := by group
  have hsq : ∀ g ∈ A, g * g = (g * z) * (g * z) := by
    intro g hg
    calc g * g = g * (z * z) * g := by rw [hz2, mul_one]
      _ = (g * z) * (z * g) := by group
      _ = (g * z) * (g * z) := by rw [hzc g hg]
  have hcomm : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ = (g * z) * h * (g * z)⁻¹ * h⁻¹ := by
    intro g hg h hh
    have : (g * z) * h * (g * z)⁻¹ * h⁻¹ = g * (z * h * z⁻¹) * g⁻¹ * h⁻¹ := by group
    rw [this, ← hzc h hh, mul_inv_cancel_right]
  have hcomm' : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ = g * (h * z) * g⁻¹ * (h * z)⁻¹ := by
    intro g hg h hh
    have : g * (h * z) * g⁻¹ * (h * z)⁻¹ = g * h * (z * g⁻¹ * z⁻¹) * h⁻¹ := by group
    rw [this, show z * g⁻¹ * z⁻¹ = g⁻¹ by
      rw [← hzc g⁻¹ (A.inv_mem hg), mul_inv_cancel_right]]
  refine ⟨?_, ?_⟩
  · rcases hcov d hd with h | h
    · exact D'.mul_mem h h
    · rw [hsq d hd]
      exact D'.mul_mem h h
  · rcases hcov d hd with h₁ | h₁ <;> rcases hcov e he with h₂ | h₂
    · exact D'.mul_mem (D'.mul_mem (D'.mul_mem h₁ h₂) (D'.inv_mem h₁)) (D'.inv_mem h₂)
    · rw [hcomm' d hd e he]
      exact D'.mul_mem (D'.mul_mem (D'.mul_mem h₁ h₂) (D'.inv_mem h₁)) (D'.inv_mem h₂)
    · rw [hcomm d hd e he]
      exact D'.mul_mem (D'.mul_mem (D'.mul_mem h₁ h₂) (D'.inv_mem h₁)) (D'.inv_mem h₂)
    · rw [hcomm d hd e he, hcomm' (d * z) (A.mul_mem hd hzA) e he]
      exact D'.mul_mem (D'.mul_mem (D'.mul_mem h₁ h₂) (D'.inv_mem h₁)) (D'.inv_mem h₂)

theorem elemAbelian_of_noMix (h6 : Layer6Twin p f) (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂)
    {D : Subgroup G}
    (hDA : D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hDbad : z ∉ zStarOf (Subgroup.centralizer (D : Set G))) (h4 : 4 ≤ Nat.card D)
    (hnomix : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x ∉ Subgroup.zpowers z → z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) →
        z ∉ zStarOf (Subgroup.centralizer ({x * z} : Set G))) :
    (∀ d ∈ D, d * d = 1) ∧ ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := by
  exact CFSG.ClassicalInvolution.Asc77.CX7Eng.elemAbelian_of_noMix_gen hyp.std.setting.hz.sq
    hyp.std.setting.hz.ne_one hyp.hzS (T7T.z_mem_centralizer_of_hyp hyp)
    (exists_bad_complement h6 hyp) mem_zpowers_of_sq four_le_card_of_three
    sq_comm_mem_of_complement exists_mem_normalizer_sq_mem hDA hDbad h4 hnomix

end Complement

section Residual

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NoMixParity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      ∀ D : Subgroup G,
        D ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
        z ∉ zStarOf (Subgroup.centralizer (D : Set G)) →
        (∀ g ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
          g ∈ D ∨ g * z ∈ D) →
        4 ≤ Nat.card D → (∀ d ∈ D, d * d = 1) → (∀ d ∈ D, ∀ e ∈ D, d * e = e * d) →
        (∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
          x ∉ Subgroup.zpowers z → z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) →
            z ∉ zStarOf (Subgroup.centralizer ({x * z} : Set G))) →
        (∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
          b * b = 1 → b ≠ 1 → z ∉ zStarOf (Subgroup.centralizer ({b} : Set G)) →
            LayerOrthType p f Ω b 5 true ∨ LayerOrthType p f Ω b 6 (!piSign p f)) →
        False

end Residual

section Assembly

variable {p f : ℕ} [Fact p.Prime]


theorem centExtNoMix_of (h6 : Layer6Twin p f) (h : NoMixParity p f) : C25W.CentExtNoMix p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz _ hbad y hyA hya hy2 _ hnomix
  by_contra hyV
  obtain ⟨D, hDA, -, hDbad, hcov, h4⟩ :=
    exists_bad_complement_of_ext h6 hyp haA ha2 ha1 haz hbad hyA hya hy2 hyV
  have hnomix' : ∀ x ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      x ∉ Subgroup.zpowers z → z ∉ zStarOf (Subgroup.centralizer ({x} : Set G)) →
        z ∉ zStarOf (Subgroup.centralizer ({x * z} : Set G)) :=
    fun x hx hxz hxbad hgood => hnomix ⟨x, hx, hxz, hxbad, hgood⟩
  obtain ⟨hsq, hcomm⟩ := elemAbelian_of_noMix h6 hyp hDA hDbad h4 hnomix'
  refine h G Ω K K' W S R R' z t u₁ u₂ hyp D hDA hDbad hcov h4 hsq hcomm hnomix'
    fun b hbA hb2 hb1 hbbad => ?_
  have hcent := Subgroup.mem_centralizer_iff.mp hbA.2
  have haR : ∀ x ∈ R, b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', b * x = x * b := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  exact (C25X.layer_a_typed_proved hyp hb2 hb1 haR haR').resolve_left hbbad

theorem centExt_of (h6 : Layer6Twin p f) (hmix : C25W.CentExtMix p f) (h : NoMixParity p f) :
    C25W.CentExt p f :=
  C25W.centExt_of_parts p f hmix (centExtNoMix_of h6 h)

end Assembly

end CFSG.ClassicalInvolution.Asc77.CX
