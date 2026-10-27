module

public import CFSG.LargeExtraspecial.S9RACaseC
public import CFSG.LargeExtraspecial.S9ThreeMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem typeII_of_caseA (H : Hyp4 S g) {t : S.O}
    (hA : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ = t) {x : S.O} (hxM : x ∈ S.Mbar)
    (hne : x * t * x⁻¹ ≠ t) :
    ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
  intro k hk hkA
  have hkt := commute_of_mem_Rbar H.conj_mem hk
  have h1 := (mem_Lbar_mul_iff S k g).mp hkA.1
  have e : (S.ρ k)⁻¹ * (x * t * x⁻¹) * S.ρ k = ((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹ := by
    group
  rw [e] at h1
  have h2 := hA _ (S.Mbar.mul_mem (inv_mem (Rbar_le_Mbar hk)) hxM) h1
  apply hne
  calc x * t * x⁻¹ = S.ρ k * (((S.ρ k)⁻¹ * x) * t * ((S.ρ k)⁻¹ * x)⁻¹) * (S.ρ k)⁻¹ := by group
    _ = S.ρ k * t * (S.ρ k)⁻¹ := by rw [h2]
    _ = t := by rw [hkt, mul_inv_cancel_right]

section Main

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem conj_eq_t_of_typeII (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    ∀ y ∈ S.Mbar, y * t * y⁻¹ ∈ S.Lbar g → y * t * y⁻¹ = t := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hcase := finrank_nqSub_Fbar hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL
  rcases hcase with h0 | h2
  · intro y hyM hyL
    have hmem : y * t * y⁻¹ ∈ Fbar S g t := subset_closure ⟨hyL, y, hyM, rfl⟩
    have hN : y * t * y⁻¹ ∈ Nbar S g t := hL y hyM hyL
    have hz : nqMk (⟨_, hN⟩ : Nbar S g t) = 0 := by
      have hm : nqMk (⟨_, hN⟩ : Nbar S g t) ∈ nqSub S g t (Fbar S g t) := ⟨_, hmem, rfl⟩
      rw [Submodule.finrank_eq_zero.mp h0] at hm
      exact hm
    rw [nqMk_eq_zero_iff] at hz
    have hz' : y * t * y⁻¹ ∈ zpowers t := hz
    rcases S8.eq_one_or_eq_of_mem_zpowers htt hz' with h1 | h1
    · exfalso
      apply ht1
      calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  · exact (false_of_caseB hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL h2 hxM hτt hβ).elim

theorem false_of_typeII_sp_four (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hL : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x : S.O} (hxM : x ∈ S.Mbar) (hτt : x * t * x⁻¹ * t = t * (x * t * x⁻¹))
    (hβ : ∀ k : S.M, S.ρ k ∈ Rbar S g t → x * t * x⁻¹ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t) :
    False := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hA := conj_eq_t_of_typeII hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hτt hβ
  have hτM : x * t * x⁻¹ ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  obtain ⟨k₀, hk₀⟩ := MonoidHom.mem_range.mp hτM
  have hττ : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  have hback : ∀ n ∈ Nbar S g t, x⁻¹ * n * x ∈ S.Mbar ∧
      (x⁻¹ * n * x) * t * (x⁻¹ * n * x)⁻¹ = x⁻¹ * (n * (x * t * x⁻¹) * n⁻¹) * x := fun n hn =>
    ⟨S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem hxM) (Rbar_le_Mbar (Nbar_le_Rbar hn))) hxM,
      by group⟩
  have hconjx : ∀ a b : S.O, a * b = b * a → x⁻¹ * a * x * (x⁻¹ * b * x) =
      x⁻¹ * b * x * (x⁻¹ * a * x) := fun a b hab => by
    calc x⁻¹ * a * x * (x⁻¹ * b * x) = x⁻¹ * (a * b) * x := by group
      _ = x⁻¹ * (b * a) * x := by rw [hab]
      _ = x⁻¹ * b * x * (x⁻¹ * a * x) := by group
  have ht' : x⁻¹ * (x * t * x⁻¹) * x = t := by group
  have hβconj : ∀ n ∈ Nbar S g t, n * (x * t * x⁻¹) * n⁻¹ ≠ x * t * x⁻¹ →
      ∀ k : S.M, S.ρ k ∈ Rbar S g t → (x⁻¹ * n * x) * t * (x⁻¹ * n * x)⁻¹ ∉
        S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
    intro n hn hne
    refine typeII_of_caseA H hA (hback n hn).1 ?_
    rw [(hback n hn).2]
    intro he
    apply hne
    calc n * (x * t * x⁻¹) * n⁻¹ = x * (x⁻¹ * (n * (x * t * x⁻¹) * n⁻¹) * x) * x⁻¹ := by group
      _ = x * t * x⁻¹ := by rw [he]
  have hcomt : ∀ n ∈ Nbar S g t, Commute (x * t * x⁻¹) (n * (x * t * x⁻¹) * n⁻¹) →
      (x⁻¹ * n * x) * t * (x⁻¹ * n * x)⁻¹ * t = t * ((x⁻¹ * n * x) * t * (x⁻¹ * n * x)⁻¹) := by
    intro n hn hc
    rw [(hback n hn).2]
    have := hconjx _ _ hc.eq.symm
    rwa [ht'] at this
  refine false_of_lambda (t := t) (τ := x * t * x⁻¹) (N := Nbar S g t) htt hττ hτt.symm
    (fun n hn => commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)) hNQ.comm hNQ.sq ?_ ?_ ?_ ?_
  · intro n hn
    rw [← hk₀]
    exact conj_mem_Nbar haQ (k := k₀) (by rw [hk₀]; exact hτt) hn
  · intro n hn he
    refine conj_ne_mul_t_of_typeII H C ht ht1 hVQ hSp.transitive hL hxM hτt hβ (n * x) ?_
    rw [← he]
    group
  · rintro ρ₁ ⟨n₁, hn₁, hρ₁⟩ ρ₂ ⟨n₂, hn₂, hρ₂⟩ c₁ c₂ c₁₂ ne₁ ne₂ ne₁₂ ⟨n₃, hn₃, h₃⟩
    subst hρ₁ hρ₂
    have hρ₂sq : n₂ * (x * t * x⁻¹) * n₂⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹) = 1 := by
      calc n₂ * (x * t * x⁻¹) * n₂⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹) =
          n₂ * (x * t * x⁻¹ * (x * t * x⁻¹)) * n₂⁻¹ := by group
        _ = 1 := by rw [hττ, mul_one, mul_inv_cancel]
    have ne₃ : n₃ * (x * t * x⁻¹) * n₃⁻¹ ≠ x * t * x⁻¹ := by
      rw [h₃]
      intro he
      apply ne₁₂
      have h1 : n₁ * (x * t * x⁻¹) * n₁⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹) = 1 := by
        have := congrArg (fun a => (x * t * x⁻¹)⁻¹ * a) he
        simp only [inv_mul_cancel] at this
        rw [← this]
        group
      calc n₁ * (x * t * x⁻¹) * n₁⁻¹ = n₁ * (x * t * x⁻¹) * n₁⁻¹ *
            (n₂ * (x * t * x⁻¹) * n₂⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹)) := by rw [hρ₂sq, mul_one]
        _ = (n₁ * (x * t * x⁻¹) * n₁⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹)) *
            (n₂ * (x * t * x⁻¹) * n₂⁻¹) := by group
        _ = n₂ * (x * t * x⁻¹) * n₂⁻¹ := by rw [h1, one_mul]
    have c₃ : Commute (x * t * x⁻¹) (n₃ * (x * t * x⁻¹) * n₃⁻¹) := by
      rw [h₃]
      exact ((Commute.refl _).mul_right c₁).mul_right c₂
    refine false_of_triangle hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL (hback n₁ hn₁).1
      (hback n₂ hn₂).1 (hback n₃ hn₃).1 (hcomt n₁ hn₁ c₁) (hcomt n₂ hn₂ c₂) (hcomt n₃ hn₃ c₃)
      (hβconj n₁ hn₁ ne₁) (hβconj n₂ hn₂ ne₂) (hβconj n₃ hn₃ ne₃) ?_ ?_
    · rw [(hback n₁ hn₁).2, (hback n₂ hn₂).2]
      exact hconjx _ _ c₁₂.eq
    · rw [(hback n₁ hn₁).2, (hback n₂ hn₂).2, (hback n₃ hn₃).2, h₃]
      calc x⁻¹ * (x * t * x⁻¹ * (n₁ * (x * t * x⁻¹) * n₁⁻¹) * (n₂ * (x * t * x⁻¹) * n₂⁻¹)) * x =
          x⁻¹ * (x * t * x⁻¹) * x * (x⁻¹ * (n₁ * (x * t * x⁻¹) * n₁⁻¹) * x) *
            (x⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹) * x) := by group
        _ = t * (x⁻¹ * (n₁ * (x * t * x⁻¹) * n₁⁻¹) * x) *
            (x⁻¹ * (n₂ * (x * t * x⁻¹) * n₂⁻¹) * x) := by rw [ht']
  · exact lt_of_lt_of_le (by norm_num)
      (sixteen_le_card_nOrbit hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hτt hβ)


end Main

theorem timmesfeld93Residual : Timmesfeld93Residual.{u} := by
  intro G _ _ S g hCE _ H hNo C t ht ht1 hVQ hSp h4 _ hL h hh hb x hxM hτt hβ w _
  exact (false_of_typeII_sp_four hCE H hNo C ht ht1 hVQ hSp hh hb h4 hL hxM hτt hβ).elim

end CFSG.LargeExtraspecial.S9
