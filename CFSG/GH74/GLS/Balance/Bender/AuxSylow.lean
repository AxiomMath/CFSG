module

public import CFSG.GH74.GLS.Balance.Bender.Ambient
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalQuotientFrattini

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_mem_normalizer_not_mem {P' P : Subgroup G} (hP' : IsPGroup p ↥P') (hPP' : P ≤ P')
    (hne : ¬ P' ≤ P) : ∃ g ∈ P', g ∈ normalizer (P : Set G) ∧ g ∉ P := by
  have : Group.IsNilpotent ↥P' := hP'.isNilpotent
  have hlt : P.subgroupOf P' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥P') ∈ P.subgroupOf P' := by rw [h]; trivial
    exact this
  have h2 := Group.normalizerCondition_of_isNilpotent (G := ↥P') (P.subgroupOf P') hlt
  obtain ⟨g, hg, hgn⟩ := Set.exists_of_ssubset h2
  refine ⟨(g : G), g.2, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxP' : x ∈ P' := hPP' hx
      have := (mem_normalizer_iff.mp hg ⟨x, hxP'⟩).mp hx
      exact this
    · intro hx
      have hxP' : (g : G) * x * (g : G)⁻¹ ∈ P' := hPP' hx
      have hx' : x ∈ P' := by
        have := P'.mul_mem (P'.mul_mem (P'.inv_mem g.2) hxP') g.2
        simpa [mul_assoc] using this
      have := (mem_normalizer_iff.mp hg ⟨x, hx'⟩).mpr hx
      exact this
  · intro hgP
    exact hgn hgP

omit [Finite G] [Fact p.Prime] in
theorem isPGroup_sup_of_le_normalizer {P S : Subgroup G} (hP : IsPGroup p ↥P) (hS : IsPGroup p ↥S)
    (h : P ≤ normalizer (S : Set G)) : IsPGroup p ↥(P ⊔ S) := by
  set M : Subgroup G := P ⊔ S with hM
  have hPM : P ≤ M := le_sup_left
  have hSM : S ≤ M := le_sup_right
  have hMn : M ≤ normalizer (S : Set G) := sup_le h Subgroup.le_normalizer
  have : (S.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSM).2 hMn
  have hP' : IsPGroup p ↥(P.subgroupOf M) := hP.comap_of_injective M.subtype M.subtype_injective
  have hS' : IsPGroup p ↥(S.subgroupOf M) := hS.comap_of_injective M.subtype M.subtype_injective
  have hsup : IsPGroup p ↥(P.subgroupOf M ⊔ S.subgroupOf M) := hP'.to_sup_of_normal_right hS'
  have htop : P.subgroupOf M ⊔ S.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPM hSM, ← hM, Subgroup.subgroupOf_self]
  rw [htop] at hsup
  exact hsup.of_surjective (Subgroup.topEquiv (G := ↥M)).toMonoidHom
    (Subgroup.topEquiv (G := ↥M)).surjective

theorem le_of_inf_normalizer_le {P S : Subgroup G} (hP : IsPGroup p ↥P) (hS : IsPGroup p ↥S)
    (hn : P ≤ normalizer (S : Set G)) (h : S ⊓ normalizer (P : Set G) ≤ P) : S ≤ P := by
  by_contra hSP
  have hM : IsPGroup p ↥(P ⊔ S) := isPGroup_sup_of_le_normalizer hP hS hn
  have hne : ¬ (P ⊔ S) ≤ P := fun hMP => hSP (le_sup_right.trans hMP)
  obtain ⟨g, hgM, hgN, hgP⟩ := exists_mem_normalizer_not_mem hM le_sup_left hne
  have hg' : g ∈ S ⊔ P := by rw [sup_comm]; exact hgM
  obtain ⟨s, hs, q, hq, hsq⟩ := (mem_sup_of_le_normalizer (N := S) (V₁ := P) hn).1 hg'
  have hsN : s ∈ normalizer (P : Set G) := by
    have hqN : q ∈ normalizer (P : Set G) := Subgroup.le_normalizer hq
    have : g * q⁻¹ ∈ normalizer (P : Set G) := (normalizer (P : Set G)).mul_mem hgN
      ((normalizer (P : Set G)).inv_mem hqN)
    rwa [← hsq, mul_inv_cancel_right] at this
  have hsP : s ∈ P := h ⟨hs, hsN⟩
  exact hgP (by rw [← hsq]; exact P.mul_mem hsP hq)

theorem exists_invariant_sylow {K P : Subgroup G} (hP : IsPGroup p ↥P)
    (hn : P ≤ normalizer (K : Set G)) :
    ∃ S : Subgroup G, IsSylowIn p S K ∧ P ≤ normalizer (S : Set G) := by
  set M : Subgroup G := K ⊔ P with hM
  have hKM : K ≤ M := le_sup_left
  have hPM : P ≤ M := le_sup_right
  have hMn : M ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hn
  have hKn : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hMn
  have hP' : IsPGroup p ↥(P.subgroupOf M) := hP.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨R, hR⟩ := CFSG.SignalizerFunctor.Helpers.normal_subgroup_sylow_intersection p
    (Fact.out : p.Prime) (K.subgroupOf M) S'
  refine ⟨(K.subgroupOf M ⊓ (S' : Subgroup ↥M)).map M.subtype, ?_, ?_⟩
  · have h1 := isSylowIn_of_sylow p R
    rw [hR] at h1
    have h2 := IsSylowIn.map M.subtype_injective h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hKM] at h2
  · have key : ∀ g ∈ P, ∀ x ∈ (K.subgroupOf M ⊓ (S' : Subgroup ↥M)).map M.subtype,
        g * x * g⁻¹ ∈ (K.subgroupOf M ⊓ (S' : Subgroup ↥M)).map M.subtype := by
      intro g hg x hx
      obtain ⟨t, ⟨htK, htS⟩, rfl⟩ := hx
      have hgS : (⟨g, hPM hg⟩ : ↥M) ∈ (S' : Subgroup ↥M) := hS' hg
      refine ⟨⟨g, hPM hg⟩ * t * ⟨g, hPM hg⟩⁻¹, ⟨?_, ?_⟩, ?_⟩
      · exact hKn.conj_mem t htK ⟨g, hPM hg⟩
      · exact (S' : Subgroup ↥M).mul_mem ((S' : Subgroup ↥M).mul_mem hgS htS)
          ((S' : Subgroup ↥M).inv_mem hgS)
      · rfl
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact key g hg x hx
    · intro hx
      have := key g⁻¹ (P.inv_mem hg) _ hx
      simpa [mul_assoc] using this

end CFSG.GH74.GLS.Balance
