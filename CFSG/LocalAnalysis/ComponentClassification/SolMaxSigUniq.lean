module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigConj
public import CFSG.LocalAnalysis.ComponentClassification.Sol78HAltPair

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem le_pPrimeCore_map {p : ℕ} {N Y : Subgroup X} (hNY : N ≤ Y)
    (hnorm : Y ≤ normalizer (N : Set X)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ (pPrimeCore p Y).map Y.subtype := by
  have hnormal : (N.subgroupOf Y).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf Y)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]
  have hle : N.subgroupOf Y ≤ pPrimeCore p Y := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNY]
  exact Subgroup.map_mono hle

theorem le_normalizer_pPrimeCore {L : Subgroup X} {g : X} (hg : g ∈ normalizer (L : Set X)) :
    g ∈ normalizer (((pPrimeCore 2 L).map L.subtype : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq]
  have hL : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hg
  exact SolMax.map_pPrimeCore_map_subtype_of_eq (MulAut.conj g) hL

theorem inf_mem_normalizer' {A B : Subgroup X} {g : X} (hA : g ∈ normalizer (A : Set X))
    (hB : g ∈ normalizer (B : Set X)) : g ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [mem_inf] at hA hB ⊢
  rw [hA h, hB h]

theorem commutator_le_core_join [Finite X] {Y L₁ L₂ : Subgroup X} (h₁ : L₁ ≤ Y) (h₂ : L₂ ≤ Y)
    (hp₁ : IsPComponent 2 (L₁.subgroupOf Y)) (hp₂ : IsPComponent 2 (L₂.subgroupOf Y))
    (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ (pPrimeCore 2 ↥(L₁ ⊔ L₂)).map (L₁ ⊔ L₂).subtype := by
  have hne' : L₁.subgroupOf Y ≠ L₂.subgroupOf Y := fun h =>
    hne (by rw [← map_subgroupOf_eq_of_le h₁, h, map_subgroupOf_eq_of_le h₂])
  obtain ⟨-, hdist⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ hp₁ hp₂
  obtain ⟨hN₂, hN₁, hcomm, -⟩ := hdist hne'
  let e₁ : L₁.subgroupOf Y ≃* L₁ := subgroupOfEquivOfLe h₁
  let e₂ : L₂.subgroupOf Y ≃* L₂ := subgroupOfEquivOfLe h₂
  have hO₁ : ((pPrimeCore 2 (L₁.subgroupOf Y)).map (L₁.subgroupOf Y).subtype).map Y.subtype =
      (pPrimeCore 2 L₁).map L₁.subtype := by
    rw [← pPrimeCore_map_iso 2 e₁, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hO₂ : ((pPrimeCore 2 (L₂.subgroupOf Y)).map (L₂.subgroupOf Y).subtype).map Y.subtype =
      (pPrimeCore 2 L₂).map L₂.subtype := by
    rw [← pPrimeCore_map_iso 2 e₂, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hc : ⁅L₁, L₂⁆ ≤ (pPrimeCore 2 L₁).map L₁.subtype ⊓ (pPrimeCore 2 L₂).map L₂.subtype := by
    have h1 := Subgroup.map_mono (f := Y.subtype) hcomm
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le h₁, map_subgroupOf_eq_of_le h₂] at h1
    refine h1.trans ?_
    rw [← hO₁, ← hO₂]
    exact Subgroup.map_inf_le _ _ _
  have hN₁X : L₁ ≤ normalizer (L₂ : Set X) := by
    have h1 := map_normalizer_subgroupOf_le h₂
    intro x hx
    exact h1 ⟨⟨x, h₁ hx⟩, hN₁ (show (⟨x, h₁ hx⟩ : Y) ∈ L₁.subgroupOf Y from hx), rfl⟩
  have hN₂X : L₂ ≤ normalizer (L₁ : Set X) := by
    have h1 := map_normalizer_subgroupOf_le h₁
    intro x hx
    exact h1 ⟨⟨x, h₂ hx⟩, hN₂ (show (⟨x, h₂ hx⟩ : Y) ∈ L₂.subgroupOf Y from hx), rfl⟩
  refine hc.trans (le_pPrimeCore_map ?_ ?_ ?_)
  · exact inf_le_left.trans ((map_subtype_le _).trans le_sup_left)
  · rw [sup_le_iff]
    constructor
    · intro x hx
      exact inf_mem_normalizer' (le_normalizer_pPrimeCore (le_normalizer hx))
        (le_normalizer_pPrimeCore (hN₁X hx))
    · intro x hx
      exact inf_mem_normalizer' (le_normalizer_pPrimeCore (hN₂X hx))
        (le_normalizer_pPrimeCore (le_normalizer hx))
  · have h1 : Nat.card ↥((pPrimeCore 2 L₁).map L₁.subtype ⊓ (pPrimeCore 2 L₂).map L₂.subtype) ∣
        Nat.card ↥((pPrimeCore 2 L₁).map L₁.subtype) := Subgroup.card_dvd_of_le inf_le_left
    rw [Subgroup.card_map_of_injective L₁.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card

theorem isPComponent_conj [Finite X] {Y L : Subgroup X} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) {c : X} (hc : c ∈ Y) :
    L.map (MulAut.conj c).toMonoidHom ≤ Y ∧
      IsPComponent 2 ((L.map (MulAut.conj c).toMonoidHom).subgroupOf Y) := by
  have hle : L.map (MulAut.conj c).toMonoidHom ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hc (hLY hx)) (inv_mem hc)
  refine ⟨hle, ?_⟩
  have h1 := ((LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2 Nat.prime_two
    (MulAut.conj (⟨c, hc⟩ : Y))).1 (L.subgroupOf Y)).mp hL
  have h2 : (L.subgroupOf Y).map (MulAut.conj (⟨c, hc⟩ : Y)).toMonoidHom =
      (L.map (MulAut.conj c).toMonoidHom).subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [map_subtype_map_conj, map_subgroupOf_eq_of_le hLY, map_subgroupOf_eq_of_le hle]
  rwa [h2] at h1

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_normalizer (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    centralizer ({t} : Set X) ≤ normalizer (J : Set X) := by
  have hCt : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq t
  have ht := S.pair.1.1
  have hT1 : zpowers t ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht
    exact absurd ht (by decide)
  have hT2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hJT : FooteLit.IsTwoComponentIn J (centralizer ((zpowers t : Subgroup X) : Set X)) := by
    rw [hCt]
    exact ⟨S.pair.1.2.1, S.pair.1.2.2.1⟩
  have hN := Sol78H.normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt hT13 hML hSch
    S.nonab S.kProper S.unbal S.notU S.pair.2.1 S.pair.2.2.1 ⟨t, J, S.pair.1⟩ S.pair.2.2.2.1 hT1
    hT2 hJT S.pair.1.2.2.2
  intro c hc
  apply hN
  rw [← hCt] at hc
  exact Subgroup.centralizer_le_normalizer _ hc

end Sig36

end CFSG.ComponentClassification.SolMax
