module

public import CFSG.GF2Type.Aschbacher1976Full.HSDischarge
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBasic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartE

variable {G : Type} [Group G] [Finite G] {z : G} {T V : Subgroup G}

theorem card_sylow_eq_of_le (P : Sylow 2 G) {K : Subgroup G} (hK : (P : Subgroup G) ≤ K) :
    Nat.card (P : Subgroup G) = 2 ^ (Nat.card K).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Sylow.card_eq_multiplicity P
  have h2 : Nat.card K ∣ Nat.card G := Subgroup.card_subgroup_dvd_card K
  have h3 : Nat.card (P : Subgroup G) ∣ Nat.card K := Subgroup.card_dvd_of_le hK
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have h4 : (Nat.card K).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.factorization_le_iff_dvd hK0 hG0).mpr h2 2
  have h5 : (Nat.card G).factorization 2 ≤ (Nat.card K).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hK0, ← h1]
    exact h3
  rw [h1, le_antisymm h4 h5]

@[expose] def sylowOfHSV (hV : HSV z T V) : Sylow 2 G where
  toSubgroup := T
  isPGroup' := hV.sylow.1
  is_maximal' := fun {Q} hQ hle => hV.sylow.2 Q hQ hle

theorem sylowOfHSV_coe (hV : HSV z T V) : (sylowOfHSV hV : Subgroup G) = T := rfl

theorem factorization_two_7680 : Nat.factorization 7680 2 = 9 := by
  have h1 : 2 ^ 9 ∣ 7680 := by norm_num
  have h2 : ¬ 2 ^ 10 ∣ 7680 := by norm_num
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)] at h1 h2
  omega

theorem factorization_two_168 : Nat.factorization 168 2 = 3 := by
  have h1 : 2 ^ 3 ∣ 168 := by norm_num
  have h2 : ¬ 2 ^ 4 ∣ 168 := by norm_num
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)] at h1 h2
  omega

theorem card_Hz_of_S5 (hF : Nat.card (Fz z) = 64) (hs5 : HSS5 z) : Nat.card (Hz z) = 7680 := by
  obtain ⟨φ, hφ, hker⟩ := hs5
  have h1 := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Shape.Fz_le_Hz z)).toEquiv, hF,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h1
  rw [← h1]
  decide

theorem card_T_eq (hset : HSSetting G z) (hs5 : HSS5 z) (hV : HSV z T V) :
    Nat.card T = 512 := by
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hset.2
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hF : Nat.card (Fz z) = 64 := (Width.card_Fz hD hz).trans (by norm_num)
  have h := card_sylow_eq_of_le (sylowOfHSV hV) (K := Hz z) hV.le_H
  rw [sylowOfHSV_coe] at h
  rw [h, card_Hz_of_S5 hF hs5, factorization_two_7680]
  norm_num

theorem factorization_card_C (hset : HSSetting G z) (hs5 : HSS5 z) (hV : HSV z T V) :
    (Nat.card (Subgroup.centralizer (V : Set G))).factorization 2 = 6 := by
  have h1 := card_T_eq hset hs5 hV
  have hN := (autStmt_holds hset hV).2.1
  have h2 := card_sylow_eq_of_le (sylowOfHSV hV)
    (K := Subgroup.normalizer (V : Set G)) (hsAut_T_le_normalizer hV)
  rw [sylowOfHSV_coe, h1, hN, Nat.factorization_mul (by norm_num) Nat.card_pos.ne',
    Finsupp.add_apply, factorization_two_168] at h2
  have h3 : (2 : ℕ) ^ 9 =
      2 ^ (3 + (Nat.card (Subgroup.centralizer (V : Set G))).factorization 2) := by
    rw [← h2]
    norm_num
  have := Nat.pow_right_injective (le_refl 2) h3
  omega

end CFSG.GF2Type.Aschbacher1976Full.HS.PartE
