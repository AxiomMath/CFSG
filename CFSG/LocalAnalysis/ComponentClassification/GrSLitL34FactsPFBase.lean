module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup

theorem isQuasisimple_of_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hna : ∃ a b : Y, a * b ≠ b * a) : IsQuasisimple Y := by
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hna
  let e : Y ⧸ center Y ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, e.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Y) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      rw [← commutatorElement_eq_one_iff_mul_comm, ← mem_bot, ← h, _root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩

theorem fusionZStar_eq_bot_of_simple {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hna : ∃ a b : Y, a * b ≠ b * a) (h2 : 2 ∣ Nat.card Y) : Open.fusionZStar Y = ⊥ := by
  have hO : pPrimeCore 2 Y ≠ ⊤ := by
    intro h
    have hc := pPrimeCore_coprime_card (p := 2) (G := Y)
    rw [h, Subgroup.card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2 hc
  rw [CatLeaf.fusionZStar_eq_center_of_quasisimple (isQuasisimple_of_simple hna) hO]
  exact CatLeaf.center_eq_bot_of_simple hna

theorem pRank_two_eq_zero_of_eq_bot {Y : Type*} [Group Y] {F : Subgroup Y} (h : F = ⊥) :
    pRank 2 ↥F = 0 := by
  subst h
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro r ⟨A, -, hA⟩
  have : Finite ↥(⊥ : Subgroup Y) := inferInstance
  have h1 : Nat.card A ≤ 1 :=
    (Subgroup.card_le_card_group A).trans (le_of_eq Subgroup.card_bot)
  rw [hA] at h1
  by_contra hr
  have : 1 < 2 ^ r := Nat.one_lt_two_pow (by omega)
  omega

theorem dvd_card_of_isL34Type {P : Type} [Group P] [Finite P]
    (h : IsL34Type (P ⧸ Open.fusionZStar P)) : 20160 ∣ Nat.card P := by
  rw [← CatLeaf.card_of_isL34Type h]
  exact Subgroup.card_quotient_dvd_card _

theorem pRank_fusionZStar_eq_zero_of_simple {P : Type} [Group P]
    [Finite P] [IsSimpleGroup P] (hna : ∃ a b : P, a * b ≠ b * a)
    (h : IsL34Type (P ⧸ Open.fusionZStar P)) : pRank 2 ↥(Open.fusionZStar P) = 0 :=
  pRank_two_eq_zero_of_eq_bot (fusionZStar_eq_bot_of_simple hna
    ((show 2 ∣ 20160 by norm_num).trans (dvd_card_of_isL34Type h)))

theorem eq_top_of_isPComponent_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    {P : Subgroup X} (hP : IsPComponent 2 P) : P = ⊤ := by
  obtain ⟨K, hK, hsub, hmap, -⟩ := hP
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsub with h | h
  · exfalso
    rw [h, Subgroup.map_bot] at hmap
    subst hmap
    obtain ⟨-, hs, -⟩ := hK.1
    have : Subsingleton (↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X)) ⧸
        center ↥(⊥ : Subgroup (X ⧸ pPrimeCore 2 X))) := inferInstance
    exact not_nontrivial_iff_subsingleton.mpr this hs.toNontrivial
  · exact h

theorem nonabelian_of_simple_of_four_dvd {P : Type*} [Group P] [Finite P] [IsSimpleGroup P]
    (h4 : 4 ∣ Nat.card P) : ∃ a b : P, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 (hp := ⟨Nat.prime_two⟩)
    ((show 2 ∣ 4 by norm_num).trans h4)
  have hN : (zpowers x).Normal :=
    ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h | h
  · rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hx
    norm_num at hx
  · have h2 : Nat.card P = 2 := by rw [← Subgroup.card_top, ← h, Nat.card_zpowers, hx]
    omega

theorem pRank_fusionZStar_eq_zero_of_simple' {P : Type} [Group P]
    [Finite P] [IsSimpleGroup P] (h : IsL34Type (P ⧸ Open.fusionZStar P)) :
    pRank 2 ↥(Open.fusionZStar P) = 0 :=
  pRank_fusionZStar_eq_zero_of_simple
    (nonabelian_of_simple_of_four_dvd ((show 4 ∣ 20160 by norm_num).trans
      (dvd_card_of_isL34Type h))) h

end CFSG.ComponentClassification.GrSLit.L34PF
