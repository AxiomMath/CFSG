module

public import CFSG.GH74.GLS.C3.Layer1.Thm1AutModel
public import CFSG.GH74.GLS.C3.Layer1.Th2Tstar
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Fix

theorem hasL2Model_of_l2 {H : Type} [Group H] {F : Type} [Field F] [Finite F] (hF : L2Field F)
    (e : H ≃* L2 F) : HasL2Model H (fun q => q = Nat.card F) := by
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_odd F hF.1
  have h3 : 3 < p ^ n := hq ▸ hF.2
  refine ⟨p, n, hp, hn, hq.symm, ?_⟩
  refine Or.inl ⟨by simp [Blueprint.classicalTags], ?_, F, inferInstance, inferInstance, hq, ⟨e⟩⟩
  refine ⟨hp, hn, le_refl 2, ?_, ?_⟩
  · intro h
    have : p ^ n = 2 := congrArg Prod.snd h
    omega
  · intro h
    have : p ^ n = 3 := congrArg Prod.snd h
    omega

theorem fixedPGL_of_isFAut {Kb : Type} [Group Kb] [Finite Kb] (hL2 : HasL2Model Kb Odd)
    (h9 : ¬ HasL2Model Kb (fun q => q = 9)) {σ : MulAut Kb} (hσ : P34.IsFAutL2A7 Kb σ)
    (hσ2 : σ * σ = 1) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Odd (Nat.card F₀) ∧ 3 < Nat.card F₀ ∧
      Nonempty (↥(fixedSubgroup Kb σ) ≃* GorensteinWalter.PGL2 F₀) := by
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩⟩ := exists_l2_model_of_hasL2Model hL2
  obtain ⟨hσ1, hcases⟩ := hσ
  rcases hcases with ⟨F, _, _, e, hFodd, hσF⟩ | ⟨⟨hA7⟩, -⟩
  swap
  · exact (Th2Tstar.not_hasL2Model_alt7 (fun q hq => hq) hA7 hL2).elim
  have hcard1 : Nat.card Kb = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) / 2 := card_eq_of_L2Field e₁ hF₁
  have h60 : 60 ≤ Nat.card Kb := by
    rw [hcard1]
    obtain ⟨⟨t, ht⟩, h3⟩ := hF₁
    have h5 : 5 ≤ Nat.card F₁ := by omega
    have h25 : 25 ≤ Nat.card F₁ ^ 2 := by nlinarith
    have h24 : 24 ≤ Nat.card F₁ ^ 2 - 1 := by omega
    have : 5 * 24 ≤ Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := Nat.mul_le_mul h5 h24
    omega
  have hodd := isOddPrimePower_of_odd F hFodd
  have hcard : Nat.card Kb = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (toPSL e).toEquiv]
    exact GorensteinWalter.psl2_card_formula F hodd
  have hF3 : 3 < Nat.card F := by
    by_contra hle
    push Not at hle
    obtain ⟨m, hm⟩ := hFodd
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h3 : Nat.card F = 3 := by omega
    rw [hcard, h3] at h60
    norm_num at h60
  have hF : L2Field F := ⟨hFodd, hF3⟩
  have hF9 : Nat.card F ≠ 9 := fun h' => h9 (hasL2Model_nine h' e)
  obtain ⟨τ, rfl⟩ := hσF
  have hinj : Function.Injective (fieldAutHom e) := fun a b hab => by
    have := congrArg (fieldProj e) hab
    rwa [fieldProj_fieldAutHom, fieldProj_fieldAutHom] at this
  have hσord : orderOf (fieldAutHom e τ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hσord
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF Kb e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard₀
  have hodd₀ : Odd (Nat.card F₀) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have : Even (Nat.card F) := by
      rw [← hcard₀]
      exact Nat.even_pow.2 ⟨hne, by norm_num⟩
    exact (Nat.not_even_iff_odd.2 hF.1) this
  have h3₀ : 3 < Nat.card F₀ := by
    by_contra hle
    push Not at hle
    have hq3 : 3 < Nat.card F := hF.2
    obtain ⟨m, hm⟩ := hodd₀
    interval_cases hq : Nat.card F₀
    · omega
    · have : Nat.card F = 1 := by rw [← hcard₀]; norm_num
      omega
    · omega
    · have : Nat.card F = 9 := by rw [← hcard₀]; norm_num
      exact hF9 this
  exact ⟨F₀, hF₀, hFin₀, hodd₀, h3₀, ⟨eqv⟩⟩

end Fix

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
