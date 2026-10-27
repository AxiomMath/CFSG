module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Facts
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup CFSG.Open

variable {G G' : Type*} [Group G] [Group G']

theorem pCoreOf_map_injective (φ : G →* G') (hφ : Function.Injective φ) (K : Subgroup G) :
    pCoreOf 2 (K.map φ) = (pCoreOf 2 K).map φ := by
  let e : K ≃* (K.map φ) := K.equivMapOfInjective φ hφ
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem centIn_map_injective (φ : G →* G') (hφ : Function.Injective φ) (L : Subgroup G) (y : G) :
    centIn (L.map φ) (φ y) = (centIn L y).map φ := by
  ext x'
  simp only [centIn, mem_inf, mem_map, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, h⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply hφ
    rw [map_mul, map_mul]
    exact h
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul, h]

variable {L : Subgroup G} {z : G} {c₂ c₃ : ℕ}

theorem hasEighthRoot_map (φ : G →* G') (hφ : Function.Injective φ) (L : Subgroup G) (y : G) :
    HasEighthRoot (L.map φ) (φ y) ↔ HasEighthRoot L y := by
  constructor
  · rintro ⟨v', ⟨v, hv, rfl⟩, h⟩
    exact ⟨v, hv, hφ (by rw [map_pow]; exact h)⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨φ v, ⟨v, hv, rfl⟩, by rw [← map_pow, h]⟩

theorem invType_map (φ : G →* G') (hφ : Function.Injective φ) (L : Subgroup G) (z : G) (c : ℕ)
    (y : G) : InvType (L.map φ) (φ z) c (φ y) ↔ InvType L z c y := by
  unfold InvType
  rw [hasEighthRoot_map φ hφ, centIn_map_injective φ hφ, Subgroup.card_map_of_injective hφ,
    orderOf_injective φ hφ, Subgroup.mem_map_iff_mem hφ, hφ.ne_iff]

theorem Co0Facts.map (φ : G →* G') (hφ : Function.Injective φ) (F : Co0Facts L z c₂ c₃) :
    Co0Facts (L.map φ) (φ z) c₂ c₃ where
  classify := by
    rintro y' ⟨y, hy, rfl⟩ hord hne
    have hord' : orderOf y = 2 := by rwa [orderOf_injective φ hφ] at hord
    have hne' : y ≠ z := fun h => hne (by rw [h])
    rw [centIn_map_injective φ hφ, Subgroup.card_map_of_injective hφ]
    exact F.classify y hy hord' hne'
  pCore_typeC := by
    intro y' hy'
    obtain ⟨y, -, rfl⟩ := hy'.1
    rw [invType_map φ hφ] at hy'
    obtain ⟨hzE, hEL, hcomm, hsq, hcard, hcent⟩ := F.pCore_typeC y hy'
    rw [centIn_map_injective φ hφ, pCoreOf_map_injective φ hφ]
    refine ⟨⟨z, hzE, rfl⟩, Subgroup.map_mono hEL, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hsq a ha, map_one]
    · rw [Subgroup.card_map_of_injective hφ, hcard]
    · rintro _ ⟨⟨x, hx, rfl⟩, hxc⟩
      refine ⟨x, hcent ⟨hx, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩, rfl⟩
      apply hφ
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.1 hxc (φ e) ⟨e, he, rfl⟩
  orbit_typeC := by
    intro y' hy'
    obtain ⟨y, -, rfl⟩ := hy'.1
    rw [invType_map φ hφ] at hy'
    obtain ⟨hcard, htrans⟩ := F.orbit_typeC y hy'
    rw [centIn_map_injective φ hφ, pCoreOf_map_injective φ hφ]
    refine ⟨?_, ?_⟩
    · have : {t : G' | t ∈ (pCoreOf 2 (centIn L y)).map φ ∧ InvType (L.map φ) (φ z) c₃ t} =
          φ '' {t : G | t ∈ pCoreOf 2 (centIn L y) ∧ InvType L z c₃ t} := by
        ext t'
        constructor
        · rintro ⟨⟨t, ht, rfl⟩, hty⟩
          exact ⟨t, ⟨ht, (invType_map φ hφ L z c₃ t).1 hty⟩, rfl⟩
        · rintro ⟨t, ⟨ht, hty⟩, rfl⟩
          exact ⟨⟨t, ht, rfl⟩, (invType_map φ hφ L z c₃ t).2 hty⟩
      rw [this, Nat.card_image_of_injective hφ, hcard]
    · rintro t' ⟨t, ht, rfl⟩ hty
      rw [invType_map φ hφ] at hty
      obtain ⟨n, hn, hnt⟩ := htrans t ht hty
      have hnorm := Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hn).2
      refine ⟨φ n, ⟨⟨n, (Subgroup.mem_inf.1 hn).1, rfl⟩,
        Subgroup.mem_normalizer_iff.2 fun h' => ?_⟩, by rw [← map_mul, ← map_inv, ← map_mul, hnt]⟩
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨n * e * n⁻¹, (hnorm e).1 he, by rw [map_mul, map_mul, map_inv]⟩
      · rintro ⟨e, he, hee⟩
        refine ⟨n⁻¹ * e * n, (hnorm (n⁻¹ * e * n)).2 (by simpa [mul_assoc] using he), ?_⟩
        rw [map_mul, map_mul, map_inv, hee]
        group

end CFSG.EvenSporadicStandard.TwoCo1
