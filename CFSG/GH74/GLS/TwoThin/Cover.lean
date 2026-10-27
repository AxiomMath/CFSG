module

public import CFSG.GH74.GLS.TwoThin.Unique
public import CFSG.GH74.GLS.TwoThin.Basic

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def hatMap {A K : Subgroup G} (h : A ≤ K) :
    ↥A →* (↥K ⧸ pPrimeCore 2 ↥K) :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion h)

omit [Finite G] in
theorem hatMap_eq_one_iff {A K : Subgroup G} (h : A ≤ K) (a : ↥A) :
    hatMap h a = 1 ↔ (a : G) ∈ pPrimeCoreOf 2 K := by
  unfold hatMap
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hk
    exact ⟨Subgroup.inclusion h a, hk, rfl⟩
  · rintro ⟨k, hk, hka⟩
    have : k = Subgroup.inclusion h a := Subtype.ext hka
    rwa [← this]

omit [Finite G] in
theorem hatMap_surjective {A K : Subgroup G} (h : A ≤ K)
    (hcov : ∀ k ∈ K, ∃ c ∈ A, ∃ o ∈ pPrimeCoreOf 2 K, k = c * o) :
    Function.Surjective (hatMap h) := by
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) y
  obtain ⟨c, hc, o, ho, hk⟩ := hcov k k.2
  refine ⟨⟨c, hc⟩, ?_⟩
  obtain ⟨o', ho', hoo⟩ := ho
  change QuotientGroup.mk' (pPrimeCore 2 ↥K) (Subgroup.inclusion h ⟨c, hc⟩) =
    QuotientGroup.mk' (pPrimeCore 2 ↥K) k
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have : (Subgroup.inclusion h ⟨c, hc⟩)⁻¹ * k = o' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    have : (o' : G) = o := hoo
    rw [this, hk]
    group
  rw [this]
  exact ho'

theorem normal_odd_le_ker {A B : Type*} [Group A] [Group B] [Finite B] (ψ : A →* B)
    (hψ : Function.Surjective ψ) (hB : pPrimeCore 2 B = ⊥) (N : Subgroup A) [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N ≤ ψ.ker := by
  have hnorm : (N.map ψ).Normal := Subgroup.Normal.map hN ψ hψ
  have hodd' : Odd (Nat.card (N.map ψ)) := hodd.of_dvd_nat (Subgroup.card_map_dvd N ψ)
  have hle : N.map ψ ≤ pPrimeCore 2 B := le_sSup ⟨hnorm, Nat.coprime_two_left.mpr hodd'⟩
  rw [hB, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff N).mp hle

omit [Finite G] in
theorem ker_hatMap_eq_comap {A K : Subgroup G} (h : A ≤ K) :
    (hatMap h).ker = (pPrimeCore 2 ↥K).comap (Subgroup.inclusion h) := by
  unfold hatMap
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem odd_card_ker_hatMap {A K : Subgroup G} (h : A ≤ K) : Odd (Nat.card (hatMap h).ker) := by
  rw [ker_hatMap_eq_comap]
  exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective h))

theorem ker_hatMap_eq_pPrimeCore {X K : Subgroup G} (hXK : X ≤ K)
    (hcov : ∀ k ∈ K, ∃ c ∈ X, ∃ o ∈ pPrimeCoreOf 2 K, k = c * o) :
    (hatMap hXK).ker = pPrimeCore 2 ↥X := by
  have hsurj := hatMap_surjective hXK hcov
  apply le_antisymm
  · have hnorm : (hatMap hXK).ker.Normal := MonoidHom.normal_ker _
    exact le_sSup ⟨hnorm, Nat.coprime_two_left.mpr (odd_card_ker_hatMap hXK)⟩
  · exact normal_odd_le_ker (hatMap hXK) hsurj (pPrimeCore_quotient_eq_bot ↥K) _
      (Nat.coprime_two_left.mp pPrimeCore_coprime_card)

theorem quasisimple_of_cover {X K : Subgroup G} (hXK : X ≤ K)
    (hcov : ∀ k ∈ K, ∃ c ∈ X, ∃ o ∈ pPrimeCoreOf 2 K, k = c * o)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) :
    CFSG.IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X) := by
  have hsurj := hatMap_surjective hXK hcov
  have hker := ker_hatMap_eq_pPrimeCore hXK hcov
  let e₃ := QuotientGroup.quotientKerEquivOfSurjective (hatMap hXK) hsurj
  let e₄ : (↥X ⧸ pPrimeCore 2 ↥X) ≃* (↥X ⧸ (hatMap hXK).ker) :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e₄.trans e₃).symm hKq

theorem cover_data {K X : Subgroup G} (hXK : X ≤ K)
    (hcov : ∀ k ∈ K, ∃ c ∈ X, ∃ o ∈ pPrimeCoreOf 2 K, k = c * o)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) :
    ∃ Λ : Subgroup G, Λ ≤ X ∧ IsPCompIn 2 X Λ ∧ (∀ L : Subgroup G, IsPCompIn 2 X L → L = Λ) ∧
      pLayerOf 2 X = Λ ∧
      (∀ z ∈ X, (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ Λ) ∧
      (∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 K, k = l * o) := by
  have hXq := quasisimple_of_cover hXK hcov hKq
  obtain ⟨Λz, hΛz, huniq, hmap, h2el⟩ := exists_unique_isTwoComponent hXq
  have hker := ker_hatMap_eq_pPrimeCore hXK hcov
  set Λ : Subgroup G := Λz.map X.subtype with hΛdef
  have hΛX : Λ ≤ X := by
    rintro _ ⟨l, -, rfl⟩
    exact l.2
  have hsub : Λ.subgroupOf X = Λz :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective Λz
  have hpc : IsPCompIn 2 X Λ := isPCompIn_two_iff.mpr ⟨hΛX, by rw [hsub]; exact hΛz⟩
  have huniqL : ∀ L : Subgroup G, IsPCompIn 2 X L → L = Λ := by
    intro L hL
    obtain ⟨hLX, hL2⟩ := isPCompIn_two_iff.mp hL
    have h1 := huniq _ hL2
    rw [← Subgroup.map_subgroupOf_eq_of_le hLX, h1]
  have hlayer : pLayerOf 2 X = Λ := by
    unfold pLayerOf
    have hset : {L | IsPCompIn 2 X L} = {Λ} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨huniqL L, by rintro rfl; exact hpc⟩
    rw [hset, sSup_singleton]
  refine ⟨Λ, hΛX, hpc, huniqL, hlayer, ?_, ?_⟩
  · intro z hz ⟨n, hn⟩
    have hz' : (⟨z, hz⟩ : ↥X) ∈ Λz := h2el ⟨z, hz⟩ ⟨n, Subtype.ext hn⟩
    exact ⟨⟨z, hz⟩, hz', rfl⟩
  · intro k hk
    obtain ⟨c, hc, o, ho, hkco⟩ := hcov k hk
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥X) (⟨c, hc⟩ : ↥X) ∈
        Λz.map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
      rw [hmap]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlc⟩ := hmem
    have h1 : l⁻¹ * (⟨c, hc⟩ : ↥X) ∈ pPrimeCore 2 ↥X := by
      rw [← QuotientGroup.eq]
      exact hlc
    rw [← hker, MonoidHom.mem_ker] at h1
    have h2 := (hatMap_eq_one_iff hXK _).mp h1
    refine ⟨l, ⟨l, hl, rfl⟩, ((l⁻¹ * (⟨c, hc⟩ : ↥X) : ↥X) : G) * o, mul_mem h2 ho, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at *
    rw [hkco]
    group

end CFSG.GH74.GLS.TwoThin
