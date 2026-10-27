module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_ne_one_of_diag [Finite X] {Y M' D : Subgroup X} {τ : X} (hτY : τ ∈ Y)
    (hM'Y : M' ≤ Y) (hM'pc : IsPComponent 2 (M'.subgroupOf Y))
    {ψ : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)}
    {ρ : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)} (hρ : IsPermActionZ ψ ρ)
    (hDle : D ≤ M' ⊔ M'.map (MulAut.conj τ).toMonoidHom) (hDτ : D ≤ centralizer ({τ} : Set X))
    (hDperf : ⁅D, D⁆ = D) (hDq : Nontrivial (↥D ⧸ pPrimeCore 2 ↥D))
    (hDN : D ≤ normalizer (M' : Set X)) : ∃ l : ↥D, ρ (inclusion hDN l) ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hall
  push Not at hall
  have hM'perf : ⁅M', M'⁆ = M' := UnbalancedCorr.commutator_eq_of_isPComponent hM'Y hM'pc
  have hDK : D ≤ UnbalancedLayer.coreActionKernel M' := fun l hl =>
    hρ.mem_coreActionKernel hM'perf (hDN hl) (hall ⟨l, hl⟩)
  have hDK' : D ≤ UnbalancedLayer.coreActionKernel (M'.map (MulAut.conj τ).toMonoidHom) := by
    intro l hl
    have h1 := coreActionKernel_map_conj (hDK hl) τ
    have h2 : τ * l * τ⁻¹ = l := by
      have h3 : l * τ = τ * l := mem_centralizer_singleton_iff.mp (hDτ hl)
      rw [← h3]
      group
    rwa [h2] at h1
  obtain ⟨hτY', hτpc⟩ := isPComponent_conj hM'Y hM'pc hτY
  obtain ⟨-, -, hO1, hO2⟩ := GSThmB.B5a.pComponent_sup_facts hM'Y hτY' hM'pc hτpc
  have hDsup : D ≤ UnbalancedLayer.coreActionKernel (M' ⊔ M'.map (MulAut.conj τ).toMonoidHom) :=
    fun l hl => GSThmB.B5a.mem_coreActionKernel_sup hO1 hO2 (hDK hl) (hDK' hl)
  exact not_le_coreActionKernel_of_le hDle hDperf hDq hDsup

theorem mem_coreActionKernel_of_eq_one_of_image [Finite X] {M' T : Subgroup X}
    {ρ : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)} (hTN : T ≤ normalizer (M' : Set X))
    (θT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin 7))
    (hsurj : ∀ g ∈ alternatingGroup (Fin 7), ∃ l : ↥T, ρ (inclusion hTN l) = g)
    (hA : ∀ l : ↥T, ρ (inclusion hTN l) ∈ alternatingGroup (Fin 7))
    (hO : ∀ l : ↥T, l ∈ pPrimeCore 2 ↥T → ρ (inclusion hTN l) = 1) {z : X}
    (hzN : z ∈ normalizer (M' : Set X)) (hzT : z ∈ normalizer (T : Set X))
    (hz1 : ρ ⟨z, hzN⟩ = 1) : z ∈ UnbalancedLayer.coreActionKernel T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥T →* Perm (Fin 7) := ρ.comp (inclusion hTN) with hfdef
  have hrange : f.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨l, rfl⟩
      exact hA l
    · intro g hg
      obtain ⟨l, hl⟩ := hsurj g hg
      exact ⟨l, hl⟩
  have hOk : pPrimeCore 2 ↥T ≤ f.ker := fun l hl => hO l hl
  have hcard1 : Nat.card ↥T = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hcard2 : Nat.card ↥T = Nat.card (↥T ⧸ pPrimeCore 2 ↥T) * Nat.card (pPrimeCore 2 ↥T) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcard3 : Nat.card f.range = Nat.card (↥T ⧸ pPrimeCore 2 ↥T) := by
    rw [hrange, Nat.card_congr θT.toEquiv]
  have hpos : 0 < Nat.card (↥T ⧸ pPrimeCore 2 ↥T) := Nat.card_pos
  have hker : f.ker = pPrimeCore 2 ↥T := by
    refine (Subgroup.eq_of_le_of_card_ge hOk ?_).symm
    have h1 : Nat.card (↥T ⧸ pPrimeCore 2 ↥T) * Nat.card f.ker =
        Nat.card (↥T ⧸ pPrimeCore 2 ↥T) * Nat.card (pPrimeCore 2 ↥T) := by
      rw [← hcard3, ← hcard1, hcard2, hcard3]
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).le
  refine ⟨hzT, fun l hl => ?_⟩
  have hw : l⁻¹ * z⁻¹ * l * z ∈ T := by
    have h1 : z⁻¹ * l * z⁻¹⁻¹ ∈ T := (mem_normalizer_iff.mp (inv_mem hzT) l).mp hl
    rw [inv_inv] at h1
    have h2 := mul_mem (inv_mem hl) h1
    rwa [show l⁻¹ * (z⁻¹ * l * z) = l⁻¹ * z⁻¹ * l * z by group] at h2
  have hwk : (⟨_, hw⟩ : ↥T) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : f ⟨_, hw⟩ = ρ (⟨l, hTN hl⟩⁻¹ * (⟨z, hzN⟩ : ↥(normalizer (M' : Set X)))⁻¹ *
        ⟨l, hTN hl⟩ * ⟨z, hzN⟩) := rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hz1]
    group
  rw [hker] at hwk
  exact ⟨_, hwk, rfl⟩

end CFSG.ComponentClassification.SolMax
