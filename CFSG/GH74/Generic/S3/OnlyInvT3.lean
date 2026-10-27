module

public import CFSG.GH74.Generic.S3.OnlyInvT2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.E2 CFSG.GH74.Generic CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup BenderSuzuki.MatrixGroups

section Cube

variable {L : Type} [Group L] [Finite L] {A : Subgroup L} {K₀ : Type} [Group K₀]
  {p f : ℕ}

theorem IsL3Cover.cube_dvd_card_sub (hc : IsL3Cover ↥A K₀ p f) : (p ^ f) ^ 3 ∣ Nat.card L := by
  have h1 : p ^ (3 * f) ∣ Nat.card K₀ := hc.card_bounds.2.2
  have h2 : Nat.card K₀ ∣ Nat.card A := hc.card_dvd
  have h3 : Nat.card A ∣ Nat.card L := Subgroup.card_subgroup_dvd_card A
  rw [← pow_mul, mul_comm]
  exact h1.trans (h2.trans h3)

theorem IsL3Cover.false_of_card_dvd (hc : IsL3Cover ↥A K₀ p f)
    (hN : Nat.card L ∣ 2 ^ 8 * 2027025) : False :=
  not_cube_dvd hc.big hc.odd_q hN hc.cube_dvd_card_sub

end Cube

section Models

variable {L : Type} [Group L] [Finite L]

theorem card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

omit [Finite L] in
theorem exists_psl2_equiv {r φ : ℕ} (h : LieModel L .PSL 2 r φ) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ^ φ ∧
      Nonempty (L ≃* PSL2MatrixGroup F) := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data h
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

end Models

section Classes

variable {L : Type} [Group L] [Finite L] {A : Subgroup L} {K₀ : Type} [Group K₀]
  {p f : ℕ}

theorem l3Cover_not_inT2 (hLK : InCalK2 L)
    (hc : IsL3Cover ↥A K₀ p f) : ¬ InT2 L := by
  rintro ⟨-, hT⟩
  rcases hT with ⟨r, φ, hr, hφ, ⟨hodd, -⟩, hmodel⟩ | ⟨F, _, _, hodd, ⟨e⟩⟩ | ⟨e⟩ |
    ⟨n, hn7, hn11, hD⟩ | ⟨hL34, -⟩
  ·
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_psl2_equiv hmodel
    have : Fact r.Prime := ⟨hr⟩
    exact false_of_cover_psl2 hF hr2 e hc
  ·
    obtain ⟨r, φ, hr, hφ, hF⟩ := exists_prime_pow_card F
    have hr2 : r ≠ 2 := by
      rintro rfl
      rw [hF] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have : Fact r.Prime := ⟨hr⟩
    exact false_of_cover_sl2 hF hr2 (e.trans (specialLinearGroupEquivStatedSL 2 F).symm) hc
  ·
    obtain ⟨e⟩ := e
    have h7 : Nat.card L = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin 7 (by norm_num)]
      decide
    exact hc.false_of_card_dvd (by rw [h7]; norm_num)
  ·
    obtain ⟨-, hz, ⟨e⟩⟩ := hD
    have hL : Nat.card L = n.factorial := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hz,
        Nat.card_congr e.toEquiv, card_alternatingGroup_fin n (by omega)]
      have : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      omega
    refine hc.false_of_card_dvd ?_
    rw [hL]
    interval_cases n <;> norm_num [Nat.factorial]
  ·
    have hq : Nat.card (L ⧸ center L) = 20160 := by
      rw [card_of_lieModel_PSL (n := 3) (by norm_num) hL34]
      decide
    have hZ : IsPGroup 2 ↥(center L) := by
      rw [hLK.2.1]
      exact CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    have hL : Nat.card L = 20160 * 2 ^ k := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hq, hk]
    have hcube := hc.cube_dvd_card_sub
    rw [hL] at hcube
    have hcop : Nat.Coprime ((p ^ f) ^ 3) (2 ^ k) := by
      apply Nat.Coprime.pow
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      have := hc.odd_q
      omega
    have h2 : (p ^ f) ^ 3 ∣ 20160 := hcop.dvd_of_dvd_mul_right hcube
    exact not_cube_dvd hc.big hc.odd_q (by norm_num : (20160 : ℕ) ∣ 2 ^ 8 * 2027025) h2

theorem l3Cover_not_inC2
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hP : Gen4Comp L)
    (hc : IsL3Cover ↥A K₀ p f) : ¬ InC2 L := by
  intro hC
  rcases c2Shape_of_inC2 hG hE hC hP with ⟨-, hshape⟩ | h2m | h2s
  · rcases hshape with ⟨r, φ, hr, hr2, -, hmodel⟩ | hL28 | hL33 | hU33 | hSz8 | hM11
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_psl2_equiv hmodel
      have : Fact r.Prime := ⟨hr⟩
      exact false_of_cover_psl2 hF hr2 e hc
    · have hcL : Nat.card L = 504 := by
        rw [card_of_lieModel_PSL (n := 2) (by norm_num) hL28]
        decide
      exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
    · have hcL : Nat.card L = 5616 := by
        rw [card_of_lieModel_PSL (n := 3) (by norm_num) hL33]
        decide
      exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
    · have hcL : Nat.card L = 6048 := by
        rw [card_of_lieModel_PSU (n := 3) (by norm_num) (by norm_num) hU33]
        decide
      exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
    · have hcL : Nat.card L = 29120 := by
        rw [card_of_lieModel_twistedB2 hSz8]
        decide
      exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
    · have hcL : Nat.card L = 7920 :=
        (card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 hM11).trans (by norm_num)
      exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
  · obtain ⟨-, hz2, hM⟩ := h2m
    have hcL : Nat.card L = 190080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hz2,
        card_of_isSporadic_M12 hM]
      norm_num
    exact hc.false_of_card_dvd (by rw [hcL]; norm_num)
  · obtain ⟨-, hz2, hS⟩ := h2s
    have hcL : Nat.card L = 58240 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center L), hz2,
        card_of_lieModel_twistedB2 hS]
      decide
    exact hc.false_of_card_dvd (by rw [hcL]; norm_num)

end Classes

end CFSG.GH74.Generic.S3
