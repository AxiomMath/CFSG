module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3ProdAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.M24Std

theorem eq_one_of_pow_seven {A : Type*} [Group A]
    (hs : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hc : ∀ a : A, (∀ c, a * c = c * a) → a = 1) (hnt : ∃ s : A, s ≠ 1)
    (h7 : ¬ 7 ∣ Nat.card (MulAut A)) {α : MulAut (A × A)} (hα : α ^ 7 = 1) : α = 1 := by
  have h7' : Nat.Prime 7 := by norm_num
  have hord : ∀ f : MulAut A, f ^ 7 = 1 → f = 1 := by
    intro f hf
    have h1 : orderOf f ∣ 7 := orderOf_dvd_of_pow_eq_one hf
    rcases (Nat.dvd_prime h7').1 h1 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard f) h7
  have hprod : ∀ (f₁ f₂ : MulAut A), ((f₁ ^ 7 = 1) → (f₂ ^ 7 = 1) → (f₁ = 1 ∧ f₂ = 1)) :=
    fun f₁ f₂ h₁ h₂ => ⟨hord f₁ h₁, hord f₂ h₂⟩
  rcases ProdAut.mulAut_prod_cases hs hc hnt α with ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩
  · obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_preserve α hp1 hp2
    have e₁ : f₁ ^ 7 = 1 := MulEquiv.ext fun a => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (a, 1)).1) hα
      simpa [pow_apply_pres hf] using this
    have e₂ : f₂ ^ 7 = 1 := MulEquiv.ext fun b => by
      have := congrArg (fun γ : MulAut (A × A) => (γ (1, b)).2) hα
      simpa [pow_apply_pres hf] using this
    obtain ⟨r₁, r₂⟩ := hprod f₁ f₂ e₁ e₂
    exact mulAut_prod_eq_one fun a b => by simp [hf, r₁, r₂]
  · exfalso
    obtain ⟨f₁, f₂, hf⟩ := ProdAut.exists_prod_swap α hs1 hs2
    obtain ⟨s, hs1'⟩ := hnt
    have h8 : α ^ (2 * 4) = α := by
      have : α ^ (2 * 4) = α ^ 7 * α := by rw [← pow_succ]
      rw [this, hα, one_mul]
    have e := pow_two_mul_apply_swap hf 4 1 s
    rw [h8, hf] at e
    have e1 := congrArg Prod.fst e
    simp only [map_one] at e1
    exact hs1' (f₁.injective (by rw [e1]; exact (map_one f₁).symm))

theorem not_seven_dvd_card_of_prod {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    [N.Normal] (hC : centralizer (N : Set Γ) = ⊥)
    (e : N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) : ¬ 7 ∣ Nat.card Γ := by
  intro h7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_orderOf_of_dvd_card h7
  have hρ := conjEmb_injective N e hC
  have hα : (conjEmb N e g) ^ 7 = 1 := by
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hnt : ∃ s : alternatingGroup (Fin 6), s ≠ 1 := by
    have : Nontrivial (alternatingGroup (Fin 6)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [DRes.card_alt6]; norm_num)
    exact exists_ne 1
  have h1 := eq_one_of_pow_seven (A := alternatingGroup (Fin 6))
    (fun N hN => DRes.alt6_hsimple N hN) (fun _ h => DRes.alt6_central h) hnt (by
      rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]; norm_num) hα
  have : g = 1 := hρ (by rw [h1, map_one])
  rw [this, orderOf_one] at hg
  omega

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
