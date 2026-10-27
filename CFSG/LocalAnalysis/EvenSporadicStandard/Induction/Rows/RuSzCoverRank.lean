module

public import CFSG.RankThree.PartTwo.Census.TransitiveLift
public import CFSG.LieType.Ree.SuzukiBorelStructure

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartTwo.Sec4.Census
open scoped commutatorElement

section Suzuki

variable {a : ℕ} {F : Type} [Field F] [Finite F]

theorem suzukiZ0_sq_card (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    (∀ x ∈ suzukiZ0 a F, x ^ 2 = 1) ∧ Nat.card (suzukiZ0 a F) = 2 ^ (2 * a + 1) := by
  have h2 : (2 : F) = 0 := (suzuki_frob_data a hF).1
  obtain ⟨-, -, hcoe, -⟩ := suzuki_unipotent_structure hF
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hF).1 hx
    rw [pow_two, suzukiSElt_mul hF, add_zero, zero_pow (by positivity), zero_mul, add_zero,
      ← two_mul, h2, zero_mul, suzukiSElt_zero_zero hF]
  · rw [← SetLike.coe_sort_coe, hcoe,
      Nat.card_range_of_injective (fun v w h => (suzukiSElt_inj.1 h).2), hF]

theorem commutator_suzukiSElt_zero (hF : Nat.card F = 2 ^ (2 * a + 1)) (u u' : F) :
    ⁅suzukiSElt a F u 0, suzukiSElt a F u' 0⁆ =
      suzukiSElt a F 0 (u ^ 2 ^ (a + 1) * u' + u' ^ 2 ^ (a + 1) * u) := by
  obtain ⟨h2, hθ, -⟩ := suzuki_frob_data a hF
  have e1 : u + u' + u = u' := by linear_combination u * h2
  rw [commutatorElement_def, suzukiSElt_inv hF, suzukiSElt_inv hF, suzukiSElt_mul hF,
    suzukiSElt_mul hF, suzukiSElt_mul hF, e1]
  refine congrArg₂ (suzukiSElt a F) ?_ ?_
  · linear_combination 1 * h2 * u'
  · rw [hθ u u']
    linear_combination (u ^ (2 ^ (a + 1) + 1) + u' ^ (2 ^ (a + 1) + 1)) * h2

theorem coprime_theta_succ (a : ℕ) : Nat.Coprime (2 ^ (2 * a + 1) - 1) (2 ^ (a + 1) + 1) := by
  have hq : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hθ : 2 ^ (a + 1) * 2 ^ (a + 1) = 2 * 2 ^ (2 * a + 1) := by
    rw [← pow_add, show a + 1 + (a + 1) = (2 * a + 1) + 1 by ring, pow_succ']
  have hθ1 : 1 ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
  rw [Nat.coprime_comm]
  set θ := 2 ^ (a + 1) with hθdef
  set q := 2 ^ (2 * a + 1) with hqdef
  refine Nat.Coprime.symm ?_
  rw [Nat.coprime_comm]
  have key : (θ + 1) * (θ - 1) = 2 * (q - 1) + 1 := by
    zify [hq, hθ1]
    have : (θ : ℤ) * θ = 2 * q := by exact_mod_cast hθ
    linear_combination this
  have hd1 : Nat.gcd (θ + 1) (q - 1) ∣ (θ + 1) * (θ - 1) :=
    (Nat.gcd_dvd_left _ _).trans (dvd_mul_right _ _)
  have hd2 : Nat.gcd (θ + 1) (q - 1) ∣ 2 * (q - 1) :=
    (Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _)
  rw [key] at hd1
  have : Nat.gcd (θ + 1) (q - 1) ∣ 1 := (Nat.dvd_add_right hd2).1 hd1
  exact Nat.dvd_one.1 this

theorem exists_pow_theta_eq (hF : Nat.card F = 2 ^ (2 * a + 1)) (v : F) (hv : v ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ c ^ (2 ^ (a + 1) + 1) = v := by
  have hc : (Nat.card Fˣ).Coprime (2 ^ (a + 1) + 1) := by
    rw [Nat.card_units, hF]
    exact coprime_theta_succ a
  obtain ⟨c, hc'⟩ := (powCoprime hc).surjective (Units.mk0 v hv)
  refine ⟨c, c.ne_zero, ?_⟩
  have := congrArg (fun x : Fˣ => (x : F)) hc'
  simpa using this

theorem exists_ne_zero_one' (h8 : 8 ≤ Nat.card F) : ∃ u : F, u ≠ 0 ∧ u ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro u _
    by_cases h0 : u = 0
    · simp [h0]
    · simp [hcon u h0]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
  have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

theorem exists_pow_theta_ne (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    ∃ w : F, w ^ 2 ^ (a + 1) ≠ w := by
  by_contra hcon
  push Not at hcon
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu0, hu1⟩ := exists_ne_zero_one' h8
  have h := (suzuki_frob_data a hF).2.2 u
  rw [hcon u, hcon u] at h
  have h2 : u * (u - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.1 h2 with h | h
  · exact hu0 h
  · exact hu1 (sub_eq_zero.1 h)

theorem exists_commutator_eq (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1)) (v : F) :
    ∃ u u' : F, suzukiSElt a F 0 v = ⁅suzukiSElt a F u 0, suzukiSElt a F u' 0⁆ := by
  by_cases hv : v = 0
  · refine ⟨0, 0, ?_⟩
    rw [hv, suzukiSElt_zero_zero hF]
    simp
  · obtain ⟨w, hw⟩ := exists_pow_theta_ne ha hF
    have h2 : (2 : F) = 0 := (suzuki_frob_data a hF).1
    have hω : w ^ 2 ^ (a + 1) + w ≠ 0 := by
      intro h
      apply hw
      linear_combination h - w * h2
    obtain ⟨c, hc0, hc⟩ := exists_pow_theta_eq hF (v / (w ^ 2 ^ (a + 1) + w)) (div_ne_zero hv hω)
    refine ⟨c * w, c, ?_⟩
    rw [commutator_suzukiSElt_zero hF]
    congr 1
    have : c ^ (2 ^ (a + 1) + 1) * (w ^ 2 ^ (a + 1) + w) = v := by
      rw [hc]
      field_simp
    rw [← this, mul_pow]
    ring

theorem exists_conj_eq (hF : Nat.card F = 2 ^ (2 * a + 1)) (v : F) (hv : v ≠ 0) :
    ∃ g : suzukiGroup a F, g * suzukiSElt a F 0 1 * g⁻¹ = suzukiSElt a F 0 v := by
  obtain ⟨c, hc0, hc⟩ := exists_pow_theta_eq hF v hv
  refine ⟨suzukiDElt a F (Units.mk0 c hc0)⁻¹, ?_⟩
  rw [suzukiDElt_conj' hF, mul_zero, inv_inv]
  simp [hc]

theorem three_le_pRank_of_suzuki_cover (ha : 1 ≤ a) (hF : Nat.card F = 2 ^ (2 * a + 1))
    {J : Type} [Group J] [Finite J] {φ : J →* suzukiGroup a F} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center J) : 3 ≤ CFSG.pRank 2 J := by
  obtain ⟨hsq, hcard⟩ := suzukiZ0_sq_card hF
  have h8 : 8 ≤ Nat.card (suzukiZ0 a F) := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW : ∀ y y' : J, φ y ∈ suzukiZ0 a F → φ y' ∈ suzukiZ0 a F → y * y' = y' * y := by
    intro y y' hy hy'
    obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hF).1 hy'
    obtain ⟨u, u', huu⟩ := exists_commutator_eq ha hF v
    obtain ⟨p, hp⟩ := hφ (suzukiSElt a F u 0)
    obtain ⟨q, hq⟩ := hφ (suzukiSElt a F u' 0)
    refine TransitiveLift.commute_of_map_eq_commutatorElement hker (p := p) (q := q) ?_ ?_ ?_
    · obtain ⟨v₁, hv₁⟩ := (mem_suzukiZ0_iff hF).1 hy
      rw [hp, ← hv₁]
      exact suzukiSElt_zero_commute hF v₁ u 0
    · obtain ⟨v₁, hv₁⟩ := (mem_suzukiZ0_iff hF).1 hy
      rw [hq, ← hv₁]
      exact suzukiSElt_zero_commute hF v₁ u' 0
    · rw [map_commutatorElement, hp, hq, ← huu, hv]
  have htr : ∀ x ∈ suzukiZ0 a F, x ≠ 1 → ∃ g : suzukiGroup a F,
      g * suzukiSElt a F 0 1 * g⁻¹ = x := by
    intro x hx hx1
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hF).1 hx
    exact exists_conj_eq hF v (fun h => hx1 (by rw [h, suzukiSElt_zero_zero hF]))
  have hsq' : ∀ y : J, φ y ∈ suzukiZ0 a F → ∃ c : J, φ c = 1 ∧ y ^ 2 = c ^ 2 := fun y hy =>
    TransitiveLift.exists_sq_eq_sq hφ hker hsq h8 htr hy
  obtain ⟨A, hA, hAcard⟩ :=
    TransitiveLift.exists_isElementaryAbelian_card hφ hker hW hsq'
  refine TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hAcard]
  have : Nonempty {c : J // φ c = 1 ∧ c ^ 2 = 1} := ⟨⟨1, map_one φ, one_pow 2⟩⟩
  have hpos : 0 < Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := Nat.card_pos
  calc 2 ^ 3 = 8 := by norm_num
    _ ≤ Nat.card (suzukiZ0 a F) := h8
    _ = Nat.card (suzukiZ0 a F) * 1 := (mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ hpos

end Suzuki

theorem three_le_pRank_of_suzukiModel_cover {X : Type} [Group X]
    [Finite X] {n : ℕ} (hn : 1 ≤ n) (h : SuzukiModel (X ⧸ center X) 2 (2 * n + 1)) :
    3 ≤ CFSG.pRank 2 X := by
  obtain ⟨-, a, ha, F, _, _, hf, hcard, ⟨e⟩⟩ := h
  obtain rfl : a = n := by omega
  let φ : X →* suzukiGroup a F := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ center X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  exact three_le_pRank_of_suzuki_cover ha hcard hφ hker

end CFSG.EvenSporadicStandard.Induction
