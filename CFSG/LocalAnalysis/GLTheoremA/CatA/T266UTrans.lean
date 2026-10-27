module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Trans2
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] [Finite G]

theorem sup_le_normalizer_of {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    K ⊔ B ≤ Subgroup.normalizer (K : Set G) :=
  sup_le Subgroup.le_normalizer hBN

theorem twoLocalRank_le_of_le {X Y : Subgroup G} (h : X ≤ Y) :
    GLATwoLocalRank 3 ↥X ≤ GLATwoLocalRank 3 ↥Y :=
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_twoLocalRank_le_of_injective Nat.prime_three
    (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

theorem glaPPrimeCore_subgroupOf_eq_bot {X K : Subgroup G} (hKX : K ≤ X) (hO : GLAPPrimeCoreOf 3 K = ⊥) :
    GLAPPrimeCore 3 ↥(K.subgroupOf X) = ⊥ := by
  have h1 := map_subtype_glaPPrimeCoreOf_subgroupOf 3 hKX
  rw [hO] at h1
  have h2 : GLAPPrimeCoreOf 3 (K.subgroupOf X) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 h1
  have h3 : (GLAPPrimeCore 3 ↥(K.subgroupOf X)).map (K.subgroupOf X).subtype = ⊥ := h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h3

theorem isQuasisimple_of_core_eq_bot {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (hO : GLAPPrimeCoreOf 3 K = ⊥) : CFSG.Open.IsQuasisimple ↥K := by
  have hO' : GLAPPrimeCore 3 ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective K)).1 hO
  have hPQ : PQuot 3 K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hO').trans QuotientGroup.quotientBot
  exact CFSG.Open.IsQuasisimple.of_mulEquiv hPQ.symm (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK)

theorem card_inf_centMod_subgroupOf {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) (hB : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(B.subgroupOf X ⊓ centModSubgroup 3 (K.subgroupOf X)) = Nat.card ↥(B ⊓ centModSubgroup 3 K) := by
  have hker : ¬ 3 ∣ Nat.card X.subtype.ker := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact Nat.prime_three.not_dvd_one
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : IsPGroup 3 (B.subgroupOf X) :=
    isPGroup_of_isElemAbelian (T171.isElemAbelian_subgroupOf X hBX hB)
  have hAN : B.subgroupOf X ≤ Subgroup.normalizer ((K.subgroupOf X : Subgroup X) : Set X) :=
    T171.le_normalizer_subgroupOf' X hBX hKX hBN
  have h := S267.card_inf_centModSubgroup_map Nat.prime_three X.subtype hker hA1 hAN
  rw [Subgroup.map_subgroupOf_eq_of_le hBX, Subgroup.map_subgroupOf_eq_of_le hKX] at h
  exact h.symm

end Setup

section E0

variable {G : Type} [Group G] [Finite G]

theorem layer_ne_bot_map_iff {X K : Subgroup G} (hKX : K ≤ X) (E' : Subgroup X) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer ((E'.map X.subtype : Subgroup G) : Set G)) ≠ ⊥ ↔
      GLAPLayer 3 (K.subgroupOf X ⊓ Subgroup.centralizer (E' : Set X)) ≠ ⊥ := by
  have hi := X.subtype_injective
  have h1 : (K.subgroupOf X ⊓ Subgroup.centralizer (E' : Set X)).map X.subtype =
      K ⊓ Subgroup.centralizer ((E'.map X.subtype : Subgroup G) : Set G) := by
    rw [T171.map_inf_cent X, Subgroup.map_subgroupOf_eq_of_le hKX]
  rw [← h1, Y10F.glaPLayer_map Nat.prime_three hi, Ne, Ne, Subgroup.map_eq_bot_iff_of_injective _ hi]

theorem isE0_map_subgroupOf {X K B : Subgroup G} (hKX : K ≤ X) (hBX : B ≤ X) {E : Subgroup X}
    (h : S10.IsE0 (B.subgroupOf X) (K.subgroupOf X) E) : S10.IsE0 B K (E.map X.subtype) := by
  refine ⟨?_, (layer_ne_bot_map_iff hKX E).2 h.2.1, ?_⟩
  · calc E.map X.subtype ≤ (B.subgroupOf X).map X.subtype := Subgroup.map_mono h.1
      _ = B := Subgroup.map_subgroupOf_eq_of_le hBX
  · intro E' hE'B hE'
    have hE'X : E' ≤ X := hE'B.trans hBX
    have hE''A : E'.subgroupOf X ≤ B.subgroupOf X := fun x hx => hE'B hx
    have hmap : (E'.subgroupOf X).map X.subtype = E' := Subgroup.map_subgroupOf_eq_of_le hE'X
    have hlay : GLAPLayer 3 (K.subgroupOf X ⊓ Subgroup.centralizer ((E'.subgroupOf X : Subgroup X) : Set X)) ≠ ⊥ := by
      refine (layer_ne_bot_map_iff hKX (E'.subgroupOf X)).1 ?_
      rw [hmap]
      exact hE'
    have hle := h.2.2 (E'.subgroupOf X) hE''A hlay
    calc Nat.card E' = Nat.card ((E'.subgroupOf X).map X.subtype) := by rw [hmap]
      _ = Nat.card (E'.subgroupOf X) := Y10F.card_map_subtype _
      _ ≤ Nat.card E := hle
      _ = Nat.card (E.map X.subtype) := (Y10F.card_map_subtype E).symm

theorem exists_maxLayer {B E₀ : Subgroup G} (P : Subgroup G → Prop) (hB : IsPGroup 3 B) (hE₀B : E₀ ≤ B)
    (hcard : Nat.card B ≤ 3 * Nat.card E₀) (hP : P E₀) :
    ∃ E : Subgroup G, E₀ ≤ E ∧ E ≤ B ∧ P E ∧
      ∀ E' : Subgroup G, E' ≤ B → P E' → Nat.card E' ≤ Nat.card E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hPB : P B
  · exact ⟨B, hE₀B, le_rfl, hPB, fun E' hE' _ => Subgroup.card_le_of_le hE'⟩
  · refine ⟨E₀, le_rfl, hE₀B, hP, fun E' hE'B hE' => ?_⟩
    have hne : E' ≠ B := fun h => hPB (h ▸ hE')
    have hlt : Nat.card E' < Nat.card B := by
      by_contra hge
      exact hne (Subgroup.eq_of_le_of_card_ge hE'B (not_lt.1 hge))
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hE'B
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hB
    have hmdvd : m ∣ 3 ^ k := ⟨Nat.card E', by rw [← hk, hm]; ring⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hmdvd
    have hpos : 0 < Nat.card E' := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      omega
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hm1 (by simpa using hi)
    have h3m : 3 ≤ m := by
      rw [hi]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hi0)
    have h1 : 3 * Nat.card E' ≤ Nat.card B := by
      rw [hm]
      exact Nat.mul_le_mul_right _ h3m |>.trans_eq (by ring)
    omega

end E0

end CFSG.LocalAnalysis.GLTheoremA.T266

end
