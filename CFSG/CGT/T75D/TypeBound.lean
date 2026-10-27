module

public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.GoldType CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem typeBound
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : goldschmidtSimpleType S)
    {V : Subgroup S} (hV : IsElemAbelian 2 V)
    {Γ : Type*} [Group Γ] [Finite Γ] {N : Type*} [Group N] [Finite N] {d : ℕ}
    (hN : Nat.card N = 2 ^ d) (ρ : Γ →* MulAut N) (hρ : Function.Injective ρ)
    (θ : Γ →* S) (hθ : Function.Surjective θ) :
    Nat.card V ≤ 8 ∨ Nat.card V ^ 2 ≤ 2 ^ d := by
  have hdvd : Nat.card S ∣ Nat.card Γ := Subgroup.card_dvd_of_surjective hθ
  obtain ⟨T, hVT⟩ := (isPGroup_two_of_isElemAbelian hV).exists_le_sylow
  have hVle : Nat.card V ≤ Nat.card (T : Subgroup S) := Subgroup.card_le_of_le hVT
  have hVΩ : ∀ v ∈ V, v ∈ Omega1 (T : Subgroup S) := fun v hv =>
    mem_omega1 (hVT hv) (hV.2 v hv)
  rcases hS with ⟨f, hf, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨p, f, hp, hpo, hf, -, h8, ⟨e⟩⟩ |
      hRee | hJ1
  ·
    right
    have hB : fusionIsBenderGroup S := Or.inl ⟨f, by omega, ⟨e⟩⟩
    obtain ⟨D, hD⟩ := G3a.exists_borelSetup hB T
    obtain ⟨-, -, hZc⟩ := hD.orders_psl2 (by omega) e
    have hΩ := omega1_eq_sylowCenter_of_bender hB T
    have hVZ : V ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (T : Subgroup S) := fun v hv => hΩ ▸ hVΩ v hv
    have hVcard : Nat.card V ≤ 2 ^ f := hZc ▸ Subgroup.card_le_of_le hVZ
    have hSc : Nat.card S = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.psl2_even_card (by omega)
    have hd : 2 * f ≤ d := by
      by_cases hf3 : f = 3
      · subst hf3
        have := lemma27_psl2_eight (e.toMonoidHom.comp θ) (e.surjective.comp hθ) ρ hρ hN
        omega
      · exact lemma27_psl2 (by omega) hf3 (hSc ▸ hdvd) ρ hρ hN
    calc Nat.card V ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hVcard 2
      _ = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  ·
    right
    have hB : fusionIsBenderGroup S := Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)
    obtain ⟨D, hD⟩ := G3a.exists_borelSetup hB T
    obtain ⟨hZc, -, -⟩ := hD.orders_sz hn e
    have hΩ := omega1_eq_sylowCenter_of_bender hB T
    have hVZ : V ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (T : Subgroup S) := fun v hv => hΩ ▸ hVΩ v hv
    have hVcard : Nat.card V ≤ 2 ^ (2 * n + 1) := hZc ▸ Subgroup.card_le_of_le hVZ
    have hd : 4 * (2 * n + 1) ≤ d :=
      lemma27_sz hn ((Nat.card_congr e.toEquiv).symm ▸ hdvd) ρ hρ hN
    calc Nat.card V ^ 2 ≤ (2 ^ (2 * n + 1)) ^ 2 := Nat.pow_le_pow_left hVcard 2
      _ = 2 ^ (2 * (2 * n + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    right
    have hB : fusionIsBenderGroup S := Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)
    obtain ⟨D, hD⟩ := G3a.exists_borelSetup hB T
    obtain ⟨hZc, -, -⟩ := hD.orders_psu3 hf e
    have hΩ := omega1_eq_sylowCenter_of_bender hB T
    have hVZ : V ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (T : Subgroup S) := fun v hv => hΩ ▸ hVΩ v hv
    have hVcard : Nat.card V ≤ 2 ^ f := hZc ▸ Subgroup.card_le_of_le hVZ
    have hd : 6 * f ≤ d := lemma27_psu3 hf ((Nat.card_congr e.toEquiv).symm ▸ hdvd) ρ hρ hN
    calc Nat.card V ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hVcard 2
      _ = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    left
    have := hp
    obtain ⟨hcard, -, -⟩ := sylow_of_psl2_odd hpo hf h8 e T
    omega
  ·
    left
    obtain ⟨-, hT8, -, -⟩ := sylow_of_ree_or_j1 (Or.inl hRee) T
    omega
  ·
    left
    obtain ⟨-, hT8, -, -⟩ := sylow_of_ree_or_j1 (Or.inr hJ1) T
    omega

theorem typeBound_of_ker_le
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hS : goldschmidtSimpleType S)
    {V : Subgroup S} (hV : IsElemAbelian 2 V)
    {X : Type*} [Group X] [Finite X] {N : Type*} [Group N] [Finite N] {d : ℕ}
    (hN : Nat.card N = 2 ^ d) (ρ : X →* MulAut N)
    (θ : X →* S) (hθ : Function.Surjective θ) (hker : ρ.ker ≤ θ.ker) :
    Nat.card V ≤ 8 ∨ Nat.card V ^ 2 ≤ 2 ^ d := by
  have hr : Function.Surjective ρ.rangeRestrict := MonoidHom.rangeRestrict_surjective ρ
  have hk : ρ.rangeRestrict.ker ≤ θ.ker := by
    simpa [MonoidHom.ker_rangeRestrict] using hker
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ρ.range →* S, θ'.comp ρ.rangeRestrict = θ :=
    ⟨MonoidHom.liftOfSurjective ρ.rangeRestrict hr ⟨θ, hk⟩,
      MonoidHom.liftOfRightInverse_comp ρ.rangeRestrict (Function.surjInv hr)
        (Function.rightInverse_surjInv hr) ⟨θ, hk⟩⟩
  have hθ'surj : Function.Surjective θ' := by
    intro s
    obtain ⟨x, hx⟩ := hθ s
    exact ⟨ρ.rangeRestrict x, by rw [← MonoidHom.comp_apply, hθ', hx]⟩
  exact typeBound hS hV hN ρ.range.subtype (Subgroup.subtype_injective _) θ' hθ'surj

end CFSG.CGT.T75D
