module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped Pointwise

variable {X : Type} [Group X]

theorem exists_conj_mem_of_card_eq_of_le [Finite X] {H Sc : Subgroup X} (hSH : Sc ≤ H)
    (hScard : Nat.card Sc = 2 ^ (Nat.card H).factorization 2) {x : X} (hxH : x ∈ H)
    (hx2 : x * x = 1) : ∃ h ∈ H, h * x * h⁻¹ ∈ Sc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁ : Nat.card (Sc.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv, hScard]
  have hZ : IsPGroup 2 (zpowers (⟨x, hxH⟩ : H)) :=
    isPGroup_zpowers_of_mul_self (Subtype.ext hx2)
  obtain ⟨T, hT⟩ := hZ.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H T (Sylow.ofCard _ hS₁)
  refine ⟨h, h.2, ?_⟩
  have key : ((h • T : Sylow 2 H) : Subgroup H) = Sc.subgroupOf H := by
    rw [hh, Sylow.coe_ofCard]
  rw [Sylow.coe_subgroup_smul] at key
  have h1 : MulAut.conj h • (⟨x, hxH⟩ : H) ∈ MulAut.conj h • (T : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT (mem_zpowers _))
  rw [key] at h1
  simpa [MulAut.smul_def, MulAut.conj_apply, mem_subgroupOf] using h1

@[expose] def SignalizerNineFusionCountCentralInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ ρ →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
          IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
          IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      (∀ y ∈ S, y * t = t * y) →
      (∀ y ∈ Q, orderOf y = 2 →
        centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ x y : X, y ∈ S → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
        Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥) →
    ∀ s ∈ S, s ∉ Q → ∀ g : X, g⁻¹ * t * g = s →
      g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) → s * s = 1 →
      (∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card) →
    ∀ hsN : s ∈ normalizer (M : Set X), ρ ⟨s, hsN⟩ * ρ ⟨s, hsN⟩ = 1 → ρ ⟨s, hsN⟩ ≠ 1 →
      5 ≤ (ρ ⟨s, hsN⟩).support.card → False

theorem signalizerNineFusionCountReducedInput_of_central (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hFC : SignalizerNineFusionCountCentralInput) : SignalizerNineFusionCountReducedInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ _ a ha g hgs hgH _ hs2 hCa hd4 _ _ _ _
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have ht2 : t * t = 1 := by rw [← sq, ← S₀.pair.1.1, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h2 := S₀.pair.1.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hts : t * s = s * t := (htZ s hsS).symm
  set t₁ := g * t * g⁻¹ with ht₁def
  have hags : a = g * s * g⁻¹ := by rw [← hgs]; group
  have ht₁a : t₁ * a = a * t₁ := by
    rw [ht₁def, hags]
    calc g * t * g⁻¹ * (g * s * g⁻¹) = g * (t * s) * g⁻¹ := by group
      _ = g * (s * t) * g⁻¹ := by rw [hts]
      _ = g * s * g⁻¹ * (g * t * g⁻¹) := by group
  have ht₁H : t₁ ∈ H := hCa (mem_centralizer_singleton_iff.mpr ht₁a)
  have ht₁N : t₁ ∈ normalizer (M : Set X) := hHN ht₁H
  have h6 : 6 ≤ (ρ ⟨t₁, ht₁N⟩).support.card := hd4 t htQ hts ht1 ht₁N
  have ht₁2 : t₁ * t₁ = 1 := by
    rw [ht₁def]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨h, hhH, hh⟩ := exists_conj_mem_of_card_eq_of_le hSH hScard ht₁H ht₁2
  have hhN : h ∈ normalizer (M : Set X) := hHN hhH
  set s' := h * t₁ * h⁻¹ with hs'def
  set g' := g⁻¹ * h⁻¹ with hg'def
  have hgs' : g'⁻¹ * t * g' = s' := by rw [hg'def, hs'def, ht₁def]; group
  have hgH' : g' ∉ H := by
    intro h'
    apply hgH
    have h1 := inv_mem (mul_mem h' hhH)
    rwa [hg'def, show (g⁻¹ * h⁻¹ * h)⁻¹ = g by group] at h1
  have hs'2 : s' * s' = 1 := by
    rw [hs'def]
    calc h * t₁ * h⁻¹ * (h * t₁ * h⁻¹) = h * (t₁ * t₁) * h⁻¹ := by group
      _ = 1 := by rw [ht₁2]; group
  have hs'N : s' ∈ normalizer (M : Set X) := hHN (hSH hh)
  have hkey : ρ ⟨s', hs'N⟩ = ρ ⟨h, hhN⟩ * ρ ⟨t₁, ht₁N⟩ * (ρ ⟨h, hhN⟩)⁻¹ := by
    have h1 : (⟨s', hs'N⟩ : ↥(normalizer (M : Set X))) =
        (⟨h, hhN⟩ : ↥(normalizer (M : Set X))) * ⟨t₁, ht₁N⟩ * (⟨h, hhN⟩)⁻¹ :=
      Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv]
  have h6' : 6 ≤ (ρ ⟨s', hs'N⟩).support.card := by
    rw [hkey, Perm.card_support_conj]
    exact h6
  have hρs'1 : ρ ⟨s', hs'N⟩ ≠ 1 := by
    intro h1
    rw [h1, Perm.support_one, Finset.card_empty] at h6'
    omega
  have hs'Q : s' ∉ Q := by
    intro h1
    exact hρs'1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK h1).2)
  have hρs'2 : ρ ⟨s', hs'N⟩ * ρ ⟨s', hs'N⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨s', hs'N⟩ : ↥(normalizer (M : Set X))) * ⟨s', hs'N⟩ = 1 := Subtype.ext hs'2
    rw [h1, map_one]
  have hd4' : ∀ y ∈ Q, y * s' = s' * y → y ≠ 1 →
      ∀ hy : g' * y * g'⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g' * y * g'⁻¹, hy⟩).support.card := fun y hy hys hy1 hyN =>
    S₀.six_le_card_support_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hQK hQ2
      hQcard htQ hQS hSH hS2 hCQ hh hs'Q htQ hgs' hs'2 hy hys hy1 hyN
  exact hFC X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s' hh hs'Q g' hgs' hgH' hs'2 hd4' hs'N hρs'2 hρs'1 (by omega)

end CFSG.ComponentClassification.SolMax
