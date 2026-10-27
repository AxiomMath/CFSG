module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeNormC
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step42
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Hexa
open CFSG.ABGLocalTools CFSG.LargeExtraspecial
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem card_sylow_eq (hM : HeModelFacts) (hQ : Sec4Q G A R g E F S₁ Q z)
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2))))) :
    Nat.card S₁ = 1024 := by
  have hCz := card_centralizer_eq hM hC
  have hcardS : Nat.card S₁ = 2 ^ (Nat.card G).factorization 2 := by
    have := hQ.sylow.card_eq
    rwa [card_top] at this
  set k := (Nat.card G).factorization 2 with hk
  have h1 : 2 ^ k ∣ 21504 := by
    rw [← hcardS, ← hCz]
    exact card_dvd_of_le hQ.le_centralizer
  have h2 : 2 ^ 10 ∣ Nat.card G := by
    have h := card_subgroup_dvd_card (centralizer ({z} : Set G))
    rw [hCz] at h
    exact (by norm_num : 2 ^ 10 ∣ 21504).trans h
  have h3 : 10 ≤ k :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
  have h4 : k ≤ 10 := by
    by_contra h
    have : 2 ^ 11 ∣ 21504 := (Nat.pow_dvd_pow 2 (by omega)).trans h1
    omega
  rw [hcardS, show k = 10 by omega]
  norm_num

theorem sylow_le_normalizer_left {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hS : Sec4Setting G A R g E F)
    (hS₁N : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)))
    (hS₁ : Nat.card S₁ = 1024) : S₁ ≤ normalizer (E : Set G) := by
  rcases step42_quot_of hE16 h11 hS hS₁N with ⟨-, -, hle⟩ | ⟨⟨φ, hφ, hφk⟩, -⟩
  · exact hle
  · exfalso
    have hD := planeData_of hE16 h11 hS.frame hS.even
    have hEFS := sup_le_of_isSylowOf_normalizer hS hS₁N
    have h := card_eq_card_ker_mul φ hφ
    rw [hφk, Nat.card_congr (subgroupOfEquivOfLe hEFS).toEquiv, hD.card_sup,
      DihedralGroup.nat_card, hS₁] at h
    norm_num at h

theorem sylow_le_normalizer {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hQ : Sec4Q G A R g E F S₁ Q z) (hS₁ : Nat.card S₁ = 1024) :
    S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G) := by
  have hS := hQ.setting
  have hS' : Sec4Setting G A R g F E :=
    ⟨hS.frame.swap, hS.type, hS.even, hS.below, hS.top⟩
  have hS₁N' : IsSylowOf 2 S₁ (normalizer ((F ⊔ E : Subgroup G) : Set G)) := by
    rw [sup_comm]
    exact hQ.sylowN
  exact le_inf (sylow_le_normalizer_left hE16 h11 hS hQ.sylowN hS₁)
    (sylow_le_normalizer_left hE16 h11 hS' hS₁N' hS₁)

theorem sylow_le_iX (hQ : Sec4Q G A R g E F S₁ Q z) (hS₁ : Nat.card S₁ = 1024)
    (hN : S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G)) : S₁ ≤ iX z E ⊓ iX z F := by
  have hc : Nat.card S₁ = 2 ^ 10 := by rw [hS₁]; norm_num
  exact le_inf (le_oUpper_of_card (le_inf hQ.le_centralizer (hN.trans inf_le_left)) hc)
    (le_oUpper_of_card (le_inf hQ.le_centralizer (hN.trans inf_le_right)) hc)

omit [Finite G] in
theorem card_iX_eq {X : Subgroup G} (hXI : X ≤ iX z X)
    {φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)}
    (hφ : Function.Surjective φ) (hφk : φ.ker = X.subgroupOf (iX z X))
    (hX64 : Nat.card X = 64) : Nat.card (iX z X) = 3072 := by
  rw [card_eq_card_ker_mul φ hφ, hφk, Nat.card_congr (subgroupOfEquivOfLe hXI).toEquiv, hX64,
    Nat.card_prod, Nat.card_perm, Nat.card_fin]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [this]
  decide

theorem sec4He_inputs {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) (hM : HeModelFacts)
    (hQ : Sec4Q G A R g E F S₁ Q z)
    (h46 : ∀ X ∈ ({E, F} : Set (Subgroup G)),
      X ≤ iX z X ∧
        ∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
          Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X))
    (hC : Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2))))) :
    Nat.card S₁ = 1024 ∧ S₁ ≤ normalizer (E : Set G) ⊓ normalizer (F : Set G) ∧ E ⊔ F ≤ S₁ ∧
      S₁ ≤ iX z E ⊓ iX z F ∧ Nat.card (iX z E) = 3072 ∧ Nat.card (iX z F) = 3072 := by
  have hS₁ := card_sylow_eq hM hQ hC
  have hN := sylow_le_normalizer hE16 h11 hQ hS₁
  have hF := hQ.setting.frame
  obtain ⟨hEI, φE, hφE, hφEk⟩ := h46 E (by simp)
  obtain ⟨hFI, φF, hφF, hφFk⟩ := h46 F (by simp)
  exact ⟨hS₁, hN, sup_le_of_isSylowOf_normalizer hQ.setting hQ.sylowN, sylow_le_iX hQ hS₁ hN,
    card_iX_eq hEI hφE hφEk hF.cardE, card_iX_eq hFI hφF hφFk hF.cardF⟩

end CFSG.ComponentClassification.AS81.HeTri
