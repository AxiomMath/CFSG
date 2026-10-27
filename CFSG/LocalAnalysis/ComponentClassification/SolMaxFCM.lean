module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCK
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixGenBase

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_alternatingGroup_fin_nine_of_eight {σ : Perm (Fin 9)} (h2 : σ * σ = 1)
    (h8 : σ.support.card = 8) : σ ∈ alternatingGroup (Fin 9) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType,
    SixGen.cycleType_of_mul_self (k := 4) h2 (by norm_num) h8]
  decide

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem false_of_eight_of_conj (S₀ : Sig36 X t J 9 e E D) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hL8 : SignalizerNineFusionCountEightInput)
    (hW : Sol78.signalizerCompletion E E ≠ ⊥) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ)
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9))) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hScard : Nat.card Sc =
      2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2)
    (htZ : ∀ y ∈ Sc, y * t = t * y)
    (hCQ : ∀ y ∈ Q, orderOf y = 2 →
      centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hd3 : ∀ x y : X, y ∈ Sc → y ∉ Q → y ∈ Q.map (MulAut.conj x).toMonoidHom →
      Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥)
    {x g : X} (hxH : x ∈ normalizer (Sol78.signalizerCompletion E E : Set X)) (hx2 : x * x = 1)
    (hgx : g⁻¹ * t * g = x) (hgH : g ∉ normalizer (Sol78.signalizerCompletion E E : Set X))
    (h8 : (ρ ⟨x, hHN hxH⟩).support.card = 8) : False := by
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hxN : x ∈ normalizer (M : Set X) := hHN hxH
  have hρx2 : ρ ⟨x, hxN⟩ * ρ ⟨x, hxN⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hxN⟩ : ↥(normalizer (M : Set X))) * ⟨x, hxN⟩ = 1 := Subtype.ext hx2
    rw [h1, map_one]
  have hxA : ρ ⟨x, hxN⟩ ∈ alternatingGroup (Fin 9) := mem_alternatingGroup_fin_nine_of_eight hρx2 h8
  obtain ⟨h₁, hh₁H, hh₁⟩ := exists_conj_mem_of_card_eq_of_le hSH hScard hxH hx2
  have hh₁N : h₁ ∈ normalizer (M : Set X) := hHN hh₁H
  have hx'N : h₁ * x * h₁⁻¹ ∈ normalizer (M : Set X) := hHN (hSH hh₁)
  have hρx' := apply_conj_of_mem_normalizer ρ hh₁N hxN hx'N
  have hx'2 : h₁ * x * h₁⁻¹ * (h₁ * x * h₁⁻¹) = 1 := by
    calc h₁ * x * h₁⁻¹ * (h₁ * x * h₁⁻¹) = h₁ * (x * x) * h₁⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'A : ρ ⟨h₁ * x * h₁⁻¹, hHN (hSH hh₁)⟩ ∈ alternatingGroup (Fin 9) := by
    rw [hρx']
    exact (alternatingGroup.normal (α := Fin 9)).conj_mem _ hxA _
  obtain ⟨h₂, hh₂H, hh₂, hsplit⟩ :=
    exists_split_conj hMH hHN hρ hQK hQ2 hQcard hQS hSH hS2 hScard hh₁ hx'2 hx'A
  have hh₂N : h₂ ∈ normalizer (M : Set X) := hHN hh₂H
  set x'' := h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ with hx''def
  have hx''N : x'' ∈ normalizer (M : Set X) := hHN (hSH hh₂)
  have hρx'' : ρ ⟨x'', hx''N⟩ = ρ ⟨h₂, hh₂N⟩ * (ρ ⟨h₁, hh₁N⟩ * ρ ⟨x, hxN⟩ * (ρ ⟨h₁, hh₁N⟩)⁻¹) *
      (ρ ⟨h₂, hh₂N⟩)⁻¹ := by
    rw [apply_conj_of_mem_normalizer ρ hh₂N hx'N hx''N, hρx']
  have h8'' : (ρ ⟨x'', hx''N⟩).support.card = 8 := by
    rw [hρx'', Perm.card_support_conj, Perm.card_support_conj]
    exact h8
  have hρx''1 : ρ ⟨x'', hx''N⟩ ≠ 1 := by
    intro h1
    rw [h1, Perm.support_one, Finset.card_empty] at h8''
    omega
  have hx''Q : x'' ∉ Q := fun h1 =>
    hρx''1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK h1).2)
  have hx''2 : x'' * x'' = 1 := by
    rw [hx''def]
    calc h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹ * (h₂ * (h₁ * x * h₁⁻¹) * h₂⁻¹) =
        h₂ * (h₁ * (x * x) * h₁⁻¹) * h₂⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hρx''2 : ρ ⟨x'', hx''N⟩ * ρ ⟨x'', hx''N⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x'', hx''N⟩ : ↥(normalizer (M : Set X))) * ⟨x'', hx''N⟩ = 1 := Subtype.ext hx''2
    rw [h1, map_one]
  have hx''A : ρ ⟨x'', hx''N⟩ ∈ alternatingGroup (Fin 9) :=
    mem_alternatingGroup_fin_nine_of_eight hρx''2 h8''
  set g'' := g * h₁⁻¹ * h₂⁻¹ with hg''def
  have hgs'' : g''⁻¹ * t * g'' = x'' := by rw [hg''def, hx''def, ← hgx]; group
  have hgH'' : g'' ∉ H := by
    intro h'
    apply hgH
    have h1 := mul_mem (mul_mem h' hh₂H) hh₁H
    rwa [hg''def, show g * h₁⁻¹ * h₂⁻¹ * h₂ * h₁ = g by group] at h1
  have hd4'' : ∀ y ∈ Q, y * x'' = x'' * y → y ≠ 1 →
      ∀ hy : g'' * y * g''⁻¹ ∈ normalizer (M : Set X),
        6 ≤ (ρ ⟨g'' * y * g''⁻¹, hy⟩).support.card := fun y hy hys hy1 hyN =>
    S₀.six_le_card_support_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN hsup θ hρ hQK hQ2
      hQcard htQ hQS hSH hS2 hCQ hh₂ hx''Q htQ hgs'' hx''2 hy hys hy1 hyN
  exact hL8 X t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 x'' hh₂ hx''Q g'' hgs'' hgH'' hx''2 hd4'' hx''N hρx''2 hρx''1
    (by omega) hx''A hsplit

end Sig36

end CFSG.ComponentClassification.SolMax
