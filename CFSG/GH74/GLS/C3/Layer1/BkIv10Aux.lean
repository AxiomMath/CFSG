module

public import CFSG.GH74.GLS.C3.Layer1.BkIv81Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

section Inn

variable {K : Type} [Group K]

theorem mul_conj_mul_inv (φ : MulAut K) (k : K) : φ * MulAut.conj k * φ⁻¹ = MulAut.conj (φ k) := by
  ext a
  simp [MulAut.conj_apply]

theorem conj_range_normal : ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hn
  rw [mul_conj_mul_inv]
  exact MonoidHom.mem_range.mpr ⟨g k, rfl⟩

theorem conj_injective_of_center_bot (h : ∀ a : K, (∀ b : K, a * b = b * a) → a = 1) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply h
  intro b
  have := congrArg (fun φ : MulAut K => φ b) ha
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [this]

end Inn

section Invariant

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_two_subgroup {K : Subgroup G} {y : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (K : Set G)) (hKe : Even (Nat.card K)) :
    ∃ P : Subgroup G, P ≤ K ∧ IsPGroup 2 ↥P ∧ P ≠ ⊥ ∧ y ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  set X : Subgroup G := K ⊔ zpowers y with hXdef
  have hKX : K ≤ X := le_sup_left
  have hZX : zpowers y ≤ X := le_sup_right
  have hXN : X ≤ normalizer (K : Set G) := sup_le le_normalizer (zpowers_le.mpr hyN)
  obtain ⟨P₀, hZP₀⟩ := (hZ2.comap_subtype (K := X)).exists_le_sylow
  have hS : IsSylowOf 2 ((P₀ : Subgroup ↥X).map X.subtype) X := ⟨P₀, rfl⟩
  set S := (P₀ : Subgroup ↥X).map X.subtype with hSdef
  have hyS : y ∈ S := by
    have hyX : y ∈ X := hZX (mem_zpowers y)
    exact ⟨⟨y, hyX⟩, hZP₀ (show (⟨y, hyX⟩ : ↥X) ∈ (zpowers y).comap X.subtype from mem_zpowers y),
      rfl⟩
  have hP : IsSylowOf 2 (S ⊓ K) K := hS.inf_of_le_normalizer hKX hXN
  refine ⟨S ⊓ K, inf_le_right, hP.isPGroup, ?_, ?_⟩
  · intro hb
    have hcard := hP.card_eq
    rw [hb, Subgroup.card_bot] at hcard
    have hev := even_iff_two_dvd.mp hKe
    have hpos : 0 < (Nat.card K).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hev
    have : 2 ≤ 2 ^ (Nat.card K).factorization 2 := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (Nat.card K).factorization 2 := Nat.pow_le_pow_right (by norm_num) hpos
    omega
  · rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hhS, hhK⟩
      exact ⟨S.mul_mem (S.mul_mem hyS hhS) (S.inv_mem hyS),
        (mem_normalizer_iff.mp hyN h).mp hhK⟩
    · rintro ⟨hhS, hhK⟩
      refine ⟨?_, (mem_normalizer_iff.mp hyN h).mpr hhK⟩
      have := S.mul_mem (S.mul_mem (S.inv_mem hyS) hhS) hyS
      simpa [mul_assoc] using this

theorem exists_involution_comm {K : Subgroup G} {y : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (K : Set G)) (hKe : Even (Nat.card K)) :
    ∃ c ∈ K, orderOf c = 2 ∧ c * y = y * c := by
  obtain ⟨P, hPK, hP2, hPne, hyP⟩ := exists_invariant_two_subgroup hy2 hyN hKe
  have hR2 : IsPGroup 2 ↥(zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨u, huP, hu2, hur, -⟩ := exists_involution_central hP2 hR2 hPne (zpowers_le.mpr hyP)
  exact ⟨u, hPK huP, hu2, hur y (mem_zpowers y)⟩

end Invariant

end CFSG.GH74.GLS.C3.Layer1.Bk
