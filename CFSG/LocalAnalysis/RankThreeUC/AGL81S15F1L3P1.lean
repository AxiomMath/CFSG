module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Frob
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1L3Gl2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.CoreFrobPair
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3 CFSG.LargeExtraspecial.A2Mod

theorem exists_frobenius_pair_of_isLThreeTwo {Y : Type} [Group Y] [Finite Y]
    (hY : IsLThreeTwo (Y ⧸ CFSG.pCore 2 Y)) {y : Y} (hy : orderOf y = 3) :
    ∃ x y' : Y, x ^ 7 = 1 ∧ x ≠ 1 ∧ y' * x * y'⁻¹ = x ^ 2 := by
  have hN : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hc : orderOf (y : Y ⧸ CFSG.pCore 2 Y) = 3 := by
    have h3 : (y : Y ⧸ CFSG.pCore 2 Y) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hy3]; rfl
    have h1 : (y : Y ⧸ CFSG.pCore 2 Y) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      obtain ⟨k, hk⟩ := hN ⟨y, h⟩
      have hk' : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      have h2 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hy] at h2
      have : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h2
      omega
    exact orderOf_eq_prime h3 h1
  obtain ⟨b, hb7, hb1, hbc⟩ := exists_frobenius_pair hY hc
  rcases hbc with h | h
  · have hc' : (y : Y ⧸ CFSG.pCore 2 Y) * b * (y : Y ⧸ CFSG.pCore 2 Y)⁻¹ = b ^ 2 := by
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact exists_frobenius_lift hN hb7 hb1 hc' (y := y) rfl
  · have hc' : (y : Y ⧸ CFSG.pCore 2 Y)⁻¹ * b * ((y : Y ⧸ CFSG.pCore 2 Y)⁻¹)⁻¹ = b ^ 2 := by
      rw [inv_inv, h, mul_assoc, inv_mul_cancel, mul_one]
    exact exists_frobenius_lift hN hb7 hb1 hc' (y := y⁻¹) rfl

section Arith

variable {F : Type} [Field F] [Finite F]

theorem card_facts (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F) :
    (7 : F) ≠ 0 ∧ Nat.Coprime (Nat.card F) 168 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨p, hpchar, n, hp, hcard⟩ := FiniteField.card' F
  have hF : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hp3 : p ≠ 3 := by
    rintro rfl
    rw [hF] at hq
    have : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 n.pos.ne'
    omega
  have hp7 : p ≠ 7 := by
    rintro rfl
    rw [hF] at hq
    have : 7 ^ (n : ℕ) % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hodd (hF ▸ dvd_pow_self 2 n.pos.ne')
  refine ⟨?_, ?_⟩
  · intro h
    have : p ∣ 7 := (CharP.cast_eq_zero_iff F p 7).mp (by exact_mod_cast h)
    exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)
  · rw [hF]
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_)
    intro h
    have h' : p ∣ 2 ^ 3 * 3 * 7 := by norm_num; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h2)
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)

theorem false_of_embed_P1_odd (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F)
    {Y : Subgroup (SL3 F)} (ι : ↥Y →* ↥(P1 : Subgroup (SL3 F))) (hι : Function.Injective ι)
    (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y)) {y : ↥Y} (hy : orderOf y = 3) : False := by
  obtain ⟨h7, hcop⟩ := card_facts hq hodd
  let φ : ↥Y →* GL (Fin 2) F := rho1.comp ι
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hQ : ((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F) ∈ (Q1 : Subgroup (SL3 F)) :=
      mem_ker_rho1.mp hg
    have hpow : g ^ (Nat.card F ^ 2) = 1 := by
      have hx : (⟨((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F), hQ⟩ :
          (Q1 : Subgroup (SL3 F))) ^ Nat.card (Q1 : Subgroup (SL3 F)) = 1 := pow_card_eq_one'
      rw [card_Q1] at hx
      have hx' : ((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F) ^ (Nat.card F ^ 2) = 1 :=
        congrArg Subtype.val hx
      apply hι
      apply Subtype.ext
      simpa [map_pow] using hx'
    have hord : orderOf g ∣ Nat.card F ^ 2 := orderOf_dvd_of_pow_eq_one hpow
    set N := CFSG.pCore 2 ↥Y with hNdef
    have hc1 : orderOf (g : ↥Y ⧸ N) ∣ Nat.card F ^ 2 :=
      (orderOf_map_dvd (QuotientGroup.mk' N) g).trans hord
    have hc2 : orderOf (g : ↥Y ⧸ N) ∣ 168 := by
      have := orderOf_dvd_natCard (g : ↥Y ⧸ N)
      rwa [CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq hY] at this
    have hcop2 : Nat.Coprime (Nat.card F ^ 2) 168 := Nat.Coprime.pow_left 2 hcop
    have hc3 : orderOf (g : ↥Y ⧸ N) = 1 :=
      Nat.dvd_one.mp (hcop2.gcd_eq_one ▸ Nat.dvd_gcd hc1 hc2)
    have hgN : g ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      exact orderOf_eq_one_iff.mp hc3
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨g, hgN⟩
    have hk' : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hord2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop3 : Nat.Coprime (2 ^ k) (Nat.card F ^ 2) := by
      refine Nat.Coprime.pow _ _ ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have : orderOf g = 1 := Nat.dvd_one.mp (hcop3.gcd_eq_one ▸ Nat.dvd_gcd hord2 hord)
    exact orderOf_eq_one_iff.mp this
  obtain ⟨x, y', hx7, hx1, hxy⟩ := exists_frobenius_pair_of_isLThreeTwo hY hy
  refine false_of_conj_pow_two h7 (x := φ x) (y := φ y') ?_ ?_ ?_
  · rw [← map_pow, hx7, map_one]
  · intro h
    exact hx1 (hφ (by rw [h, map_one]))
  · rw [← map_inv, ← map_mul, ← map_mul, hxy, map_pow]

theorem false_of_le_P1_odd (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F)
    {Y : Subgroup (SL3 F)} (hYP : Y ≤ P1) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y))
    {y : ↥Y} (hy : orderOf y = 3) : False :=
  false_of_embed_P1_odd hq hodd (Subgroup.inclusion hYP) (Subgroup.inclusion_injective hYP) hY hy

theorem false_of_le_P2_odd (hq : Nat.card F % 3 = 2) (hodd : ¬ 2 ∣ Nat.card F)
    {Y : Subgroup (SL3 F)} (hYP : Y ≤ P2) (hY : IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y))
    {y : ↥Y} (hy : orderOf y = 3) : False := by
  refine false_of_embed_P1_odd hq hodd
    ((dualAut.toMonoidHom.comp Y.subtype).codRestrict (P1 : Subgroup (SL3 F))
      (fun y => dualAut_mem_P1 (hYP y.2))) ?_ hY hy
  intro x y hxy
  have := congrArg Subtype.val hxy
  exact Subtype.ext (dualAut.injective this)

theorem exists_orderOf_three {Y : Subgroup (SL3 F)} (hAY : (A0 : Subgroup (SL3 F)) ≤ Y) :
    ∃ y : ↥Y, orderOf y = 3 := by
  refine ⟨⟨lev (cGL (F := F)), hAY (Subgroup.mem_zpowers _)⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact (orderOf_injective lev lev_injective cGL).trans orderOf_cGL

end Arith

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
