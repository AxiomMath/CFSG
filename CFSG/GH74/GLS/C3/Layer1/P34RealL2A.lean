module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.NotationTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

section L2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem innDiagSub_eq (e e' : K ≃* L2 F) : innDiagSub e' = innDiagSub e := by
  have h : e' = twistEquiv e (e'.trans e.symm) := by
    ext k
    simp [twistEquiv]
  rw [h]
  exact innDiagSub_twist e _

theorem L2Field_of_fieldAut (hodd : Odd (Nat.card F)) (e : K ≃* L2 F) {α : MulAut K}
    (hα : α ∈ fieldAutSub e) (hα1 : α ≠ 1) : L2Field F := by
  refine ⟨hodd, ?_⟩
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  by_contra hle
  push Not at hle
  obtain ⟨m, hm⟩ := hodd
  have h3 : Nat.card F = 3 := by omega
  obtain ⟨τ, rfl⟩ := hα
  have hτ : τ = 1 := by
    have hc := card_ringAut (F := F) 3 1 Nat.prime_three (by rw [h3]; norm_num)
    have hone : Nat.card (F ≃+* F) = 1 := hc
    have : Subsingleton (F ≃+* F) := Nat.card_eq_one_iff_unique.1 hone |>.1
    exact Subsingleton.elim _ _
  exact hα1 (by rw [hτ, map_one])

theorem factorization_two_mul_odd' {a b : ℕ} (ha : a ≠ 0) (hb : Odd b) :
    (a * b).factorization 2 = a.factorization 2 := by
  have hb0 : b ≠ 0 := hb.pos.ne'
  have hb2 : b.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hb)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply, hb2, add_zero]

variable [Finite K]

theorem fix_two_part_L2 (hF : L2Field F) (e : K ≃* L2 F) {α : MulAut K} (hα : α ∈ fieldAutSub e)
    (hα2 : orderOf α = 2) :
    (Nat.card ↥(fixedSubgroup K α)).factorization 2 = (Nat.card K).factorization 2 := by
  obtain ⟨τ, rfl⟩ := hα
  have hinj : Function.Injective (fieldAutHom e) := fieldAutHom_injective e
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hα2
  obtain ⟨F₀, hF₀, hFin₀, hcard, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF K e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard
  have hCcard : Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) =
      Nat.card F₀ * (Nat.card F₀ ^ 2 - 1) := by
    rw [Nat.card_congr eqv.toEquiv, pgl2_card_formula F₀]
  have hKcard : Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := ivk_1_2b F hF K e
  set r := Nat.card F₀ with hr
  have hrodd : Odd r := by
    have : Odd (r ^ 2) := by rw [hcard]; exact hF.1
    exact (Nat.odd_mul.mp (by simpa [pow_two] using this)).1
  have hr3 : 3 ≤ r := by
    obtain ⟨k, hk⟩ := hrodd
    by_contra hlt
    have hk0 : k = 0 := by omega
    have hr1 : r = 1 := by omega
    have : Nat.card F = 1 := by rw [← hcard, hr1]; norm_num
    have h4 := hF.2
    omega
  obtain ⟨k, hk⟩ := hrodd
  obtain ⟨c, hc⟩ := Nat.even_mul_succ_self k
  have hr2 : r ^ 2 = 8 * c + 1 := by
    calc r ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
      _ = 8 * c + 1 := by rw [hc]; ring
  have hc1 : 1 ≤ c := by
    by_contra hlt
    have : c = 0 := by omega
    rw [this] at hr2
    have : r = 1 := by nlinarith
    omega
  have hq : Nat.card F = 8 * c + 1 := by rw [← hcard]; exact hr2
  have hCc : Nat.card ↥(fixedSubgroup K (fieldAutHom e τ)) = (8 * c) * r := by
    rw [hCcard, hr2]
    simp only [Nat.add_sub_cancel]
    ring
  have hKc : Nat.card K = (8 * c) * ((8 * c + 1) * (4 * c + 1)) := by
    rw [hKcard, hq]
    have h1 : (8 * c + 1) * ((8 * c + 1) ^ 2 - 1) = 2 * ((8 * c) * ((8 * c + 1) * (4 * c + 1))) := by
      have h2 : (8 * c + 1) ^ 2 - 1 = 8 * c * (8 * c + 2) := by
        have : (8 * c + 1) ^ 2 = 8 * c * (8 * c + 2) + 1 := by ring
        omega
      rw [h2]
      ring
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num)]
  have hc0 : 8 * c ≠ 0 := by omega
  rw [hCc, hKc, factorization_two_mul_odd' hc0 (hk ▸ ⟨k, rfl⟩),
    factorization_two_mul_odd' hc0 ?_]
  refine Odd.mul ?_ ?_
  · exact ⟨4 * c, by ring⟩
  · exact ⟨2 * c, by ring⟩

theorem pgl2_data (hF : L2Field F) (e : K ≃* L2 F) {α : MulAut K} (hα : α ∈ fieldAutSub e)
    (hα2 : orderOf α = 2) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Odd (Nat.card F₀) ∧ 3 ≤ Nat.card F₀ ∧
      Nat.card F₀ ^ 2 = Nat.card F ∧ Nonempty (↥(fixedSubgroup K α) ≃* PGL2 F₀) := by
  obtain ⟨τ, rfl⟩ := hα
  have hinj : Function.Injective (fieldAutHom e) := fieldAutHom_injective e
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hα2
  obtain ⟨F₀, hF₀, hFin₀, hcard, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF K e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard
  have hrodd : Odd (Nat.card F₀) := by
    have : Odd (Nat.card F₀ ^ 2) := by rw [hcard]; exact hF.1
    exact (Nat.odd_mul.mp (by simpa [pow_two] using this)).1
  have hr3 : 3 ≤ Nat.card F₀ := by
    obtain ⟨k, hk⟩ := hrodd
    by_contra hlt
    have hr1 : Nat.card F₀ = 1 := by omega
    have : Nat.card F = 1 := by rw [← hcard, hr1]; norm_num
    have h4 := hF.2
    omega
  exact ⟨F₀, hF₀, hFin₀, hrodd, hr3, hcard, ⟨eqv⟩⟩

end L2

end CFSG.GH74.GLS.C3.Layer1.P34Real

