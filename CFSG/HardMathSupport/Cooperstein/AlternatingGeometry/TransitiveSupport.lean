module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltNormalClosure
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFourCocycle

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem normalizer_of_transitive_support (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 7 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (Δ : Finset (Fin N)) (hΔ : 5 ≤ Δ.card) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j)
    (l : ↥L) (hl : ∀ i : Fin N, i ∉ Δ → θ (Subgroup.inclusion le_sup_left l) i = i) :
    (l : G) ∈ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨π, hπ, hker, hAθ, hequiv, hf⟩ := hNS
  have hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N) :=
    theta_mem_alternatingGroup hL.perfect θ
  have hvS : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, ∀ t ∈ S, t * v = v * t := by
    intro v hv t ht
    have hvC : v ∈ Subgroup.centralizer (S : Set G) :=
      ((Subgroup.closure_le _).2 (fun x hx => hx.1.2) :
        CFSG.Quasithin.omegaOneCenterOf S ≤ Subgroup.centralizer (S : Set G)) hv
    exact Subgroup.mem_centralizer_iff.1 hvC t ht
  have hcent : ∀ v ∈ CFSG.Quasithin.omegaOneCenterOf S, (l : G) * v * (l : G)⁻¹ = v :=
    fun v hv => conj_eq_of_fix hN hker hAθ hequiv hf hLA Δ hΔ hΓ P hPS hPfix
      hPtrans (omegaOneCenterOf_le_blockV hA hL hSL hv) (hvS v hv) l hl
  have hlN : (l : G) ∈ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hcent h hh]
      exact hh
    · intro hh
      have h2 := hcent _ hh
      have h3 : (l : G) * h * (l : G)⁻¹ = h := by
        calc (l : G) * h * (l : G)⁻¹ =
            (l : G)⁻¹ * ((l : G) * ((l : G) * h * (l : G)⁻¹) * (l : G)⁻¹) * (l : G) := by group
          _ = (l : G)⁻¹ * ((l : G) * h * (l : G)⁻¹) * (l : G) := by rw [h2]
          _ = h := by group
      rwa [h3] at hh
  have hle : X ⊓ Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf S : Set G) ≤
      CFSG.Quasithin.cgsIn X S :=
    le_iSup_of_le (CFSG.Quasithin.omegaOneCenterOf S)
      (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S)
        (le_iSup_of_le (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot
          hA.twoRadical.isPGroup hA.twoRadical.2.1)
          (le_iSup_of_le (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S) le_rfl)))
  rw [hA.cgs] at hle
  exact (hle ⟨hL.le l.2, hlN⟩).2

theorem false_of_transitive_support (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 7 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (Δ : Finset (Fin N)) (hΔ : 5 ≤ Δ.card) (hΓ : ∃ k : Fin N, k ∉ Δ)
    (P : Subgroup (Perm (Fin N)))
    (hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p)
    (hPfix : ∀ p ∈ P, ∀ i : Fin N, i ∉ Δ → p i = i)
    (hPtrans : ∀ i ∈ Δ, ∀ j ∈ Δ, ∃ p ∈ P, p i = j) : False := by
  classical
  have hNS' := hNS
  obtain ⟨π, hπ, hker, hAθ, hequiv, hf⟩ := hNS'
  have hLA : ∀ l : ↥L, θ (Subgroup.inclusion le_sup_left l) ∈ alternatingGroup (Fin N) :=
    theta_mem_alternatingGroup hL.perfect θ
  set Z : Subgroup (Perm (Fin N)) := (S.subgroupOf (L ⊔ S)).map θ with hZ
  have hZ2 : IsPGroup 2 Z := (hA.twoRadical.isPGroup.comap_subtype (K := L ⊔ S)).map θ
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ Δ, ∃ j ∈ Δ, i ≠ j := by
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (show 1 < Δ.card by omega)
    exact ⟨i, hi, j, hj, hij⟩
  obtain ⟨p, hpP, hpij⟩ := hPtrans i hi j hj
  have hp1 : p ≠ 1 := fun h => hij (by rw [← hpij, h]; rfl)
  obtain ⟨lp, hlpS, hlp⟩ := hPS p hpP
  have hpZ : p ∈ Z := by
    refine ⟨Subgroup.inclusion le_sup_left lp, Subgroup.mem_subgroupOf.2 hlpS, hlp⟩
  have hpA : p ∈ alternatingGroup (Fin N) := hlp ▸ hLA lp
  refine false_of_alt_normalizes Z hZ2 Δ hΔ hpZ hp1 hpA (hPfix p hpP) ?_
  intro h hhA hhfix
  obtain ⟨l, hl0⟩ := hAθ h hhA
  have hl : θ (Subgroup.inclusion le_sup_left l) = h := hl0
  have hlN := normalizer_of_transitive_support hA hL hSL hN hNS Δ hΔ hΓ P hPS hPfix hPtrans l
    (fun k hk => by rw [hl]; exact hhfix k hk)
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hlN' := Subgroup.mem_normalizer_iff.1 hlN
  have hι : ∀ (m : ↥(L ⊔ S)), ((Subgroup.inclusion le_sup_left l * m *
      (Subgroup.inclusion le_sup_left l)⁻¹ : ↥(L ⊔ S)) : G) = (l : G) * (m : G) * (l : G)⁻¹ := by
    intro m; simp
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨Subgroup.inclusion le_sup_left l * m * (Subgroup.inclusion le_sup_left l)⁻¹, ?_, ?_⟩
    · show _ ∈ S.subgroupOf (L ⊔ S)
      rw [Subgroup.mem_subgroupOf, hι]
      exact (hlN' (m : G)).1 (Subgroup.mem_subgroupOf.1 hm)
    · rw [map_mul, map_mul, map_inv, hl]
  · rintro ⟨m, hm, hz⟩
    refine ⟨(Subgroup.inclusion le_sup_left l)⁻¹ * m * Subgroup.inclusion le_sup_left l, ?_, ?_⟩
    · show _ ∈ S.subgroupOf (L ⊔ S)
      rw [Subgroup.mem_subgroupOf]
      have hm' := Subgroup.mem_subgroupOf.1 hm
      have h1 : (((Subgroup.inclusion le_sup_left l)⁻¹ * m * Subgroup.inclusion le_sup_left l : ↥(L ⊔ S))
          : G) = (l : G)⁻¹ * (m : G) * (l : G) := by simp
      rw [h1]
      have h2 := (hlN' ((l : G)⁻¹ * (m : G) * (l : G))).2
      refine h2 ?_
      have : (l : G) * ((l : G)⁻¹ * (m : G) * (l : G)) * (l : G)⁻¹ = (m : G) := by group
      rw [this]; exact hm'
    · have : z = h⁻¹ * (h * z * h⁻¹) * h := by group
      rw [this, ← hz, map_mul, map_mul, map_inv, hl]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
