module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36O
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36Q

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerNineStrongClosureInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (E : Subgroup X) (D : Finset (Fin 9)),
    Sig36 X t J 9 e E D → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M → normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)) →
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ Q S : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ S →
      S ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 S →
      Nat.card S =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ Q

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem false_of_strongClosure (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hGT : Sol78.StronglyClosedResidualInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    (hSC : ∀ Q Sc : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q → Q ≤ Sc →
      Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X) → IsPGroup 2 Sc →
      Nat.card Sc =
        2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2 →
      ∀ a ∈ Q, ∀ g : X, g⁻¹ * a * g ∈ Sc → g⁻¹ * a * g ∈ Q) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hn9 := S.nine_le
  have hCt := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  have htH : t ∈ H := hCt (mem_centralizer_singleton_iff.mpr rfl)
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have htK := S.t_mem_coreActionKernel_of_sup h33 h35 hT13 hML hSch hHN hsup
  obtain ⟨Q, htQ, hQK, hQ2, hQcard⟩ :=
    exists_twoSylow_le (K := H ⊓ UnbalancedLayer.coreActionKernel M)
      (zpowers_le.mpr (mem_inf.mpr ⟨htH, htK⟩)) (isPGroup_zpowers_of_mul_self ht2)
  have htQ' : t ∈ Q := htQ (mem_zpowers t)
  have hQH : Q ≤ H := hQK.trans inf_le_left
  have hQc : Q ≤ UnbalancedLayer.coreActionKernel M := hQK.trans inf_le_right
  have hNQ := S.normalizer_le_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQH hQc hQ2 htQ'
  have hSC' : IsStronglyClosedIn (normalizer (Q : Set X)) (Q : Set X) := by
    refine ⟨fun x hx => le_normalizer hx, fun a ha g hg => ?_⟩
    have hbH : g⁻¹ * a * g ∈ H := hNQ hg
    have hb2 : IsPGroup 2 (zpowers (g⁻¹ * a * g)) := by
      have h1 : IsPGroup 2 ((zpowers a).map (MulAut.conj g⁻¹).toMonoidHom) :=
        (hQ2.to_le (zpowers_le.mpr ha)).map _
      rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1
    have hQb : IsPGroup 2 ↥(Q ⊔ zpowers (g⁻¹ * a * g)) :=
      IsPGroup.to_sup_of_normal_left' hQ2 hb2 (zpowers_le.mpr hg)
    obtain ⟨S₁, hS₁, hS₁H, hS₁2, hS₁card⟩ :=
      exists_twoSylow_le (K := H) (sup_le hQH (zpowers_le.mpr hbH)) hQb
    have hbS : g⁻¹ * a * g ∈ S₁ :=
      hS₁ ((le_sup_right : zpowers (g⁻¹ * a * g) ≤ Q ⊔ zpowers (g⁻¹ * a * g)) (mem_zpowers _))
    exact hSC Q S₁ hQK hQ2 hQcard htQ' (le_sup_left.trans hS₁) hS₁H hS₁2 hS₁card a ha g hbS
  have hnorm := hGT X Q hQ2 hSC'
  rw [pPrimeCore_two_eq_bot S.pair.1.1, sup_bot_eq] at hnorm
  obtain ⟨-, hLC, hpc, θL, -⟩ := S.layer_facts_of_sup h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup
    hQH hQc hQ2 htQ'
  have hLp := UnbalancedCorr.commutator_eq_of_isPComponent hLC hpc
  have hLR := le_perfectResidual_map hLC hLp
  rcases hnorm.eq_bot_or_eq_top with h | h
  ·
    rw [h, le_bot_iff] at hLR
    have h1 : Nat.card (↥(GSLit.fixedLayer M Q) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer M Q)) = 1 := by
      have h2 : Nat.card ↥(GSLit.fixedLayer M Q) = 1 := by rw [hLR, Subgroup.card_bot]
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (pPrimeCore 2 ↥(GSLit.fixedLayer M Q))
      rw [h2] at h3
      exact Nat.eq_one_of_mul_eq_one_right h3.symm
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr θL.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
    have h4 : 4 ≤ n.factorial / 2 := by
      have h5 : (4 : ℕ).factorial ≤ n.factorial := Nat.factorial_le (by omega)
      have h6 : (4 : ℕ).factorial = 24 := rfl
      omega
    omega
  ·
    have hCQ : centralizer (Q : Set X) = ⊤ := eq_top_iff.mpr (h ▸ map_subtype_le _)
    have htZ : t ∈ center X := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ centralizer (Q : Set X) := hCQ ▸ mem_top g
      exact (mem_centralizer_iff.mp hg t htQ').symm
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with hz | hz
    · rw [hz, mem_bot] at htZ
      have h1 := S.pair.1.1
      rw [htZ, orderOf_one] at h1
      exact absurd h1 (by decide)
    · obtain ⟨a, b, hab⟩ := S.nonab
      exact hab (mem_center_iff.mp (hz ▸ mem_top a : a ∈ center X) b).symm

end Sig36

theorem signalizerNineInput_of_strongClosure (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hGT : Sol78.StronglyClosedResidualInput) (hSC9 : SignalizerNineStrongClosureInput) :
    SignalizerNineInput := by
  intro X _ _ _ t J e E D S hW M hMH hMpc hJM hHN hθ hsup
  obtain ⟨θ⟩ := hθ
  exact S.false_of_strongClosure h33 h35 hT13 hML hSch hGT hMH hMpc hHN θ hsup
    (hSC9 X t J e E D S hW M hMH hMpc hJM hHN ⟨θ⟩ hsup)

end CFSG.ComponentClassification.SolMax
