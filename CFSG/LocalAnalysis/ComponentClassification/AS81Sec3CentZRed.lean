module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentZ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CentZOdd

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.ABGLocalTools CFSG.Open

section Vocabulary

variable {G : Type} [Group G]

@[expose] def sec3SHat (Q₁ Zs : Subgroup G) : Subgroup G :=
  pCoreOf 2 (sec3F Q₁ ⊓ centralizer (Zs : Set G))

end Vocabulary

@[expose] def Sec3SHatNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      centralizer (Zs : Set G) ≤ normalizer ((sec3SHat (Q₀ ⊔ Q) Zs ⊔
        AS76b.oddCoreIn (centralizer (Zs : Set G)) : Subgroup G) : Set G)

@[expose] def Sec3SHatNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
    (Zs P T Q B₀ : Subgroup G) (z y : G) (D J U V₀ V Q₀ : Subgroup G),
    Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ →
      centralizer (Zs : Set G) ⊓ normalizer (sec3SHat (Q₀ ⊔ Q) Zs : Set G) ≤
        normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G)

theorem sec3CentZNormalizes_of
    (h17 : Step17G24Odd) (h1 : Sec3SHatNormal) (h2 : Sec3SHatNormalizer) :
    Sec3CentZNormalizes := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (Zs : Set G) with hCdef
  set S := sec3SHat (Q₀ ⊔ Q) Zs with hSdef
  set O := AS76b.oddCoreIn C with hOdef
  have hON : O ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    sec3_oddCoreIn_centralizer_le_normalizer h17 hQ
  have hSC : S ≤ C := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  have hSN : S ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_left.trans (Quasithin.perfectCore_le _))
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hMN : S ⊔ O ≤ normalizer ((Q₀ ⊔ Q : Subgroup G) : Set G) := sup_le hSN hON
  have hMC : S ⊔ O ≤ C := sup_le hSC (AS76b.oddCoreIn_le C)
  have hSO : S ≤ normalizer (O : Set G) := hSC.trans (AS76b.le_normalizer_oddCoreIn C)
  have hcardM : Nat.card ↥(S ⊔ O) = Nat.card S * Nat.card O := by
    have h := card_sup_mul_card_inf hSO
    have hinf : O ⊓ S = ⊥ := AS76b.oddCoreIn_inf_eq_bot hS2
    rw [hinf, card_bot, mul_one, sup_comm, mul_comm] at h
    exact h
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn C
  have hsyl : ∀ S' : Subgroup G, S' ≤ S ⊔ O → IsPGroup 2 S' → Nat.card S' = Nat.card S →
      IsSylowOf 2 S' (S ⊔ O) := by
    intro S' hS'M hS'2 hS'card
    refine isSylowOf_iff.mpr ⟨hS'M, hS'2, ?_⟩
    have h := Subgroup.relIndex_mul_card S' (S ⊔ O)
    rw [inf_of_le_left hS'M, hS'card, hcardM, mul_comm (Nat.card S)] at h
    have hpos : 0 < Nat.card S := Nat.card_pos
    rw [Nat.eq_of_mul_eq_mul_right hpos h]
    exact hOodd.not_two_dvd_nat
  intro c hc
  have hcM : c ∈ normalizer ((S ⊔ O : Subgroup G) : Set G) := h1 G A A₁ R g E F x Zs P T Q B₀ z y
    D J U V₀ V Q₀ hQ hc
  set S' := S.map (MulAut.conj c).toMonoidHom with hS'def
  have hS'M : S' ≤ S ⊔ O := by
    rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hcM s).mp (mem_sup_left hs)
  have hS'card : Nat.card S' = Nat.card S := card_map_of_injective (MulAut.conj c).injective
  obtain ⟨k, hkM, hk⟩ := IsSylowOf.exists_mem_conj (hsyl S le_sup_left hS2 rfl)
    (hsyl S' hS'M (hS2.map _) hS'card)
  have hkcS : k⁻¹ * c ∈ normalizer (S : Set G) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨s, hs, rfl⟩
    have h1 : c * s * c⁻¹ ∈ S' := ⟨s, hs, rfl⟩
    have h2 := (hk _).mp h1
    show k⁻¹ * c * s * (k⁻¹ * c)⁻¹ ∈ S
    rwa [show k⁻¹ * c * s * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * s * c⁻¹) * k by group]
  have hkc : k⁻¹ * c ∈ C ⊓ normalizer (S : Set G) :=
    mem_inf.mpr ⟨mul_mem (inv_mem (hMC hkM)) hc, hkcS⟩
  have h3 := h2 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ hkc
  rw [show c = k * (k⁻¹ * c) by group]
  exact mul_mem (hMN hkM) h3

end CFSG.ComponentClassification.AS81
