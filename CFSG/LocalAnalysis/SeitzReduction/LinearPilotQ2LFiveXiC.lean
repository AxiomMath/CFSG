module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiA
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylLang

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

section TypeFree

variable {G : Type} [Group G]

theorem map_subgroupOf_normalizerMonoidHom {S H : Subgroup G} (hHS : H ≤ S) {g : G}
    (hg : g ∈ normalizer (S : Set G)) :
    (H.subgroupOf S).map (S.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom =
      (H.map (MulAut.conj g).toMonoidHom).subgroupOf S := by
  ext ⟨x, hx⟩
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨y, hyS⟩, hyH, hy⟩
    refine ⟨y, hyH, ?_⟩
    have h1 := congrArg Subtype.val hy
    rw [normalizerMonoidHom_apply_apply_coe] at h1
    simpa [MulAut.conj_apply] using h1
  · rintro ⟨y, hyH, hy⟩
    refine ⟨⟨y, hHS hyH⟩, hyH, Subtype.ext ?_⟩
    rw [normalizerMonoidHom_apply_apply_coe]
    simpa [MulAut.conj_apply] using hy

theorem map_conj_le_of_le_of_mem_normalizer {S H : Subgroup G} (hHS : H ≤ S) {g : G}
    (hg : g ∈ normalizer (S : Set G)) : H.map (MulAut.conj g).toMonoidHom ≤ S := by
  rintro _ ⟨y, hyH, rfl⟩
  exact (mem_normalizer_iff.1 hg y).1 (hHS hyH)

theorem map_conj_eq_of_map_normalizerMonoidHom_eq {S H H' : Subgroup G} (hHS : H ≤ S)
    (hH'S : H' ≤ S) {g : G} (hg : g ∈ normalizer (S : Set G))
    (h : (H.subgroupOf S).map (S.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom = H'.subgroupOf S) :
    H.map (MulAut.conj g).toMonoidHom = H' := by
  rw [map_subgroupOf_normalizerMonoidHom hHS hg, subgroupOf_inj,
    inf_of_le_left (map_conj_le_of_le_of_mem_normalizer hHS hg), inf_of_le_left hH'S] at h
  exact h

theorem mem_normalizer_of_characteristic_of_le {S H : Subgroup G} (hHS : H ≤ S)
    (hchar : (H.subgroupOf S).Characteristic) {g : G} (hg : g ∈ normalizer (S : Set G)) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  exact map_conj_eq_of_map_normalizerMonoidHom_eq hHS hHS hg
    (characteristic_iff_map_eq.1 hchar _)

theorem mem_normalizer_map_conj_of_mul_comm {W : Subgroup G} {t d : G} (hdt : d * t = t * d)
    (htW : t ∈ normalizer (W : Set G)) :
    t ∈ normalizer ((W.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G) := by
  have htd : t * d = d * t := hdt.symm
  rw [mem_normalizer_iff]
  intro x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have h1 : d * t⁻¹ = t⁻¹ * d := ((Commute.inv_left (show Commute t d from htd)).eq).symm
  have h2 : t * d⁻¹ = d⁻¹ * t := (Commute.inv_right (show Commute t d from htd)).eq
  constructor
  · rintro ⟨w, hwW, rfl⟩
    refine ⟨t * w * t⁻¹, (mem_normalizer_iff.1 htW w).1 hwW, ?_⟩
    calc d * (t * w * t⁻¹) * d⁻¹ = (d * t) * w * (d * t)⁻¹ := by group
      _ = (t * d) * w * (t * d)⁻¹ := by rw [htd]
      _ = t * (d * w * d⁻¹) * t⁻¹ := by group
  · rintro ⟨w, hwW, hw⟩
    refine ⟨t⁻¹ * w * t, inv_mul_mul_mem_of_mem_normalizer htW hwW, ?_⟩
    calc d * (t⁻¹ * w * t) * d⁻¹ = (d * t⁻¹) * w * (t * d⁻¹) := by group
      _ = (t⁻¹ * d) * w * (d⁻¹ * t) := by rw [h1, h2]
      _ = t⁻¹ * (d * w * d⁻¹) * t := by group
      _ = t⁻¹ * (t * x * t⁻¹) * t := by rw [hw]
      _ = x := by group

theorem map_conj_eq_or_of_orbit [Finite G] {S₀ W : Subgroup G} {d g : G} (hWS : W ≤ S₀)
    (hdS : d ∈ normalizer (S₀ : Set G)) (hdW : d ∉ normalizer (W : Set G))
    (hgS : g ∈ normalizer (S₀ : Set G))
    (horb : ∀ φ ψ : MulAut S₀, (W.subgroupOf S₀).map φ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map ψ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map φ.toMonoidHom = (W.subgroupOf S₀).map ψ.toMonoidHom) :
    W.map (MulAut.conj g).toMonoidHom = W ∨
      W.map (MulAut.conj g).toMonoidHom = W.map (MulAut.conj d).toMonoidHom := by
  rcases horb (S₀.normalizerMonoidHom ⟨g, hgS⟩) (S₀.normalizerMonoidHom ⟨d, hdS⟩) with h | h | h
  · exact Or.inl (map_conj_eq_of_map_normalizerMonoidHom_eq hWS hWS hgS h)
  · exact absurd (by
      rw [mem_normalizer_iff_map_conj_eq]
      exact map_conj_eq_of_map_normalizerMonoidHom_eq hWS hWS hdS h) hdW
  · rw [map_subgroupOf_normalizerMonoidHom hWS hdS] at h
    exact Or.inr (map_conj_eq_of_map_normalizerMonoidHom_eq hWS
      (map_conj_le_of_le_of_mem_normalizer hWS hdS) hgS h)

theorem conj_mem_normalizer_of_orbit [Finite G] {S₀ W : Subgroup G} {t d s : G} (hWS : W ≤ S₀)
    (htW : t ∈ normalizer (W : Set G)) (hdt : d * t = t * d)
    (hdS : d ∈ normalizer (S₀ : Set G)) (hdW : d ∉ normalizer (W : Set G))
    (hsS : s ∈ normalizer (S₀ : Set G))
    (horb : ∀ φ ψ : MulAut S₀, (W.subgroupOf S₀).map φ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map ψ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map φ.toMonoidHom = (W.subgroupOf S₀).map ψ.toMonoidHom) :
    s * t * s⁻¹ ∈ normalizer (W : Set G) := by
  have htX : t ∈ normalizer ((W.map (MulAut.conj s⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rcases map_conj_eq_or_of_orbit hWS hdS hdW (inv_mem hsS) horb with h | h
    · rw [h]
      exact htW
    · rw [h]
      exact mem_normalizer_map_conj_of_mul_comm hdt htW
  refine mem_normalizer_of_conj_into_self fun w hw => ?_
  have h1 : s⁻¹ * w * s ∈ W.map (MulAut.conj s⁻¹).toMonoidHom :=
    ⟨w, hw, by simp⟩
  obtain ⟨w', hw', heq⟩ := (mem_normalizer_iff.1 htX _).1 h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at heq
  have h2 : s * t * s⁻¹ * w * (s * t * s⁻¹)⁻¹ = s * (t * (s⁻¹ * w * s) * t⁻¹) * s⁻¹ := by group
  rw [h2, ← heq]
  have h3 : s * (s⁻¹ * w' * s) * s⁻¹ = w' := by group
  rw [h3]
  exact hw'

theorem not_mul_mem_of_orbit [Finite G] {S₀ W : Subgroup G} {t d s : G} (hWS : W ≤ S₀)
    (hS₀W : S₀ ≤ normalizer (W : Set G)) (htW : t ∈ normalizer (W : Set G))
    (hdt : d * t = t * d) (hdS : d ∈ normalizer (S₀ : Set G))
    (hdW : d ∉ normalizer (W : Set G)) (hsS : s ∈ normalizer (S₀ : Set G))
    (horb : ∀ φ ψ : MulAut S₀, (W.subgroupOf S₀).map φ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map ψ.toMonoidHom = W.subgroupOf S₀ ∨
        (W.subgroupOf S₀).map φ.toMonoidHom = (W.subgroupOf S₀).map ψ.toMonoidHom) :
    s * t * s⁻¹ * d ∉ S₀ ∧ s * t * s⁻¹ * (d * t) ∉ S₀ := by
  have hy := conj_mem_normalizer_of_orbit hWS htW hdt hdS hdW hsS horb
  constructor
  · intro h
    apply hdW
    have h1 := mul_mem (inv_mem hy) (hS₀W h)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
  · intro h
    apply hdW
    have h1 := mul_mem (mul_mem (inv_mem hy) (hS₀W h)) (inv_mem htW)
    have h2 : (s * t * s⁻¹)⁻¹ * (s * t * s⁻¹ * (d * t)) * t⁻¹ = d := by group
    rwa [h2] at h1

end TypeFree

@[expose] def LFiveGraphSylowCharInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      (S₀.subgroupOf (S₀ ⊔ zpowers d ⊔ zpowers t)).Characteristic

@[expose] def LFiveFieldSylowRadicalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      ∀ φ ψ : MulAut S₀, (W₁.subgroupOf S₀).map φ.toMonoidHom = W₁.subgroupOf S₀ ∨
        (W₁.subgroupOf S₀).map ψ.toMonoidHom = W₁.subgroupOf S₀ ∨
        (W₁.subgroupOf S₀).map φ.toMonoidHom = (W₁.subgroupOf S₀).map ψ.toMonoidHom

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem graphSylowData_wOne_facts
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {S₀ : Subgroup G} {d : G} (hdata : IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d) :
    W₁ ≤ S₀ ∧ S₀ ≤ normalizer (W₁ : Set G) ∧ d ∉ normalizer (W₁ : Set G) := by
  obtain ⟨hS₀p, hS₀N, hS₀syl, -, -, hdt, -, hdo⟩ := hdata
  obtain ⟨hW₁Nt, -, -, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  exact ⟨wOne_le_of_not_two_dvd_relIndex (IsPGroup.of_card hW₁c) (seitzTilde_le_normalizer W₁ Kc)
      hS₀p hS₀N hW₁Nt hS₀syl, hS₀N.trans (seitzTilde_le_normalizer W₁ Kc),
    not_mem_normalizer_wOne_of_outer hset hK e ht hKt c hW₁t
      (mem_centralizer_singleton_iff.2 hdt) hdo⟩

theorem lFiveGraphMcBrideInput_of_char
    (hC1 : LFiveGraphSylowCharInput) (hC2 : LFiveFieldSylowRadicalInput) :
    LFiveGraphMcBrideInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀
    hdata s hsN _
  obtain ⟨hW₁S₀, hS₀W, hdW⟩ :=
    graphSylowData_wOne_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hdata
  obtain ⟨-, -, -, -, hdS₀, hdt, -, -⟩ := id hdata
  have hsS₀ : s ∈ normalizer (S₀ : Set G) :=
    mem_normalizer_of_characteristic_of_le (le_sup_left.trans le_sup_left)
      (hC1 G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀ hdata)
      hsN
  exact not_mul_mem_of_orbit hW₁S₀ hS₀W htN hdt hdS₀ hdW hsS₀
    (hC2 G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀)

end Setting

end CFSG.SeitzReduction.LinearPilot
