module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ

open CFSG.Open CFSG.GH74.Uniqueness.SU CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs ambiguousChev)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem isChevSimple_two_alt {K : Type} [Group K] {n : ℕ} (hn : n = 5 ∨ n = 6)
    (e : K ≃* alternatingGroup (Fin n)) : IsChevSimple 2 K := by
  have h5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  refine Or.inr ⟨.alternating n h5, ?_, ⟨e⟩⟩
  rcases hn with rfl | rfl <;> simp [ambiguousChev]

theorem not_equiv_alt_five_six {K : Type} [Group K] (e5 : K ≃* alternatingGroup (Fin 5))
    (e6 : K ≃* alternatingGroup (Fin 6)) : False := by
  have h := Nat.card_congr (e5.symm.trans e6).toEquiv
  have h5 : 2 * Nat.card (alternatingGroup (Fin 5)) = 120 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have h6 : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  omega

theorem false_of_alt_ge_seven (c : KQCfg A p Kb Sb Bb Mb z) (hs : KQStrong A p Mb z)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) {n : ℕ} (e : ↥Kb ≃* alternatingGroup (Fin n)) (hn7 : 7 ≤ n)
    (hpn : p ≤ n) (hn : n < 2 * p) : False := by
  have hp := c.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp5 := c.five_le
  set X : Subgroup A := Kb ⊔ Sb with hX
  have hKX : Kb ≤ X := le_sup_left
  have hSX : Sb ≤ X := le_sup_right
  have hKnorm : (Kb.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr (sup_le_normalizer c)
  have hXiso := hAutE A Kb X n (by omega) (by omega) hKX hKnorm ⟨e⟩
    (fun x hx h => eq_one_of_centralizes c hx h)
  obtain ⟨b, hbB, hb1, hbK⟩ := exists_B1 c hAutO e hpn hn
  have hbX := centralizes_X c hbB hbK
  have hBeq := B_eq_sup c hbB hb1 hbK
  have hzX : z ∈ X := hKX c.z_mem_K
  have hzS : z ∈ normalizer (Sb : Set A) := c.B_le_S c.z_mem_B
  obtain ⟨T, Y, hTS, hT1, hzT, hST, hYTX, hzY, hYsec, hY3⟩ := h2024 A X Sb z n p hXiso
    (by omega) hp hp5 hpn hn c.z_order hzX hSX c.S_two c.S_ne hzS
  have hbT : b ∈ normalizer (T : Set A) :=
    mem_normalizer_of_commute fun t ht => hbX t (hSX (hTS ht))
  have hBT : Bb ≤ normalizer (T : Set A) := by
    rw [hBeq]
    exact sup_le (zpowers_le.mpr hzT) (zpowers_le.mpr hbT)
  have hNT : normalizer (T : Set A) ≤ Mb := c.cover T hTS hT1 hST hBT
  have hYM : Y ≤ Mb := fun y hy => hNT (hYTX hy).1
  have h3 : 3 ∣ Nat.card ↥Y :=
    hY3.trans (Subgroup.index_dvd_card ((rankThreePrimeCore p Y).subgroupOf Y))
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3
  have hyY : (y' : A) ∈ Y := y'.2
  have hyo : orderOf (y' : A) = 3 := by rw [Subgroup.orderOf_coe]; exact hy'
  have hy3 : (y' : A) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (y' : A)
    rwa [hyo] at this
  have hyK : (y' : A) ∈ Kb :=
    mem_of_pow_mem c.S_le_K c.S_two (hYTX hyY).2 Nat.prime_three (by norm_num) hy3
  have hyP : IsPGroup 3 (zpowers (y' : A)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨F, hF, hyF⟩ := exists_isSylowOf_ge (f := 3) (L := Kb) (zpowers_le.mpr hyK) hyP
  have hFY : F ⊓ Y ≠ ⊥ := by
    intro h
    have hmem : (y' : A) ∈ F ⊓ Y := ⟨hyF (mem_zpowers _), hyY⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hyo
    omega
  have hstrong : ∀ F₁ : Subgroup A, F₁ ≤ F → F₁ ≠ ⊥ → normalizer (F₁ : Set A) ≤ Mb :=
    fun F₁ h1 h2 => hs 3 Nat.prime_three (by norm_num) (by omega) Y hYM hzY hYsec hY3 F
      hF.isPGroup hFY F₁ h1 h2
  have hKM : Kb ≤ Mb := h2401 A Kb F (Or.inl ⟨n, hn7, ⟨e⟩⟩) hF Mb fun S₀ hS₀ hS₀1 =>
    inf_le_left.trans (hstrong S₀ hS₀ hS₀1)
  exact c.not_le hKM

theorem not_equiv_alt_ge_seven (c : KQCfg A p Kb Sb Bb Mb z) (hs : KQStrong A p Mb z)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) {n : ℕ} (hn7 : 7 ≤ n) (e : ↥Kb ≃* alternatingGroup (Fin n)) :
    False := by
  have hp := c.prime
  have hp2 : p ≠ 2 := by have := c.five_le; omega
  have hpdvd : p ∣ Nat.card ↥Kb := by
    have h1 : orderOf (⟨z, c.z_mem_K⟩ : ↥Kb) = p := by
      rw [Subgroup.orderOf_mk]
      exact c.z_order
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hpn : p ≤ n := KGAlt.le_of_dvd_card_alt hp (by rwa [← Nat.card_congr e.toEquiv])
  have hn : n < 2 * p := KGAlt.lt_two_mul_of_pRank_le_one hp hp2 e c.rank
  exact false_of_alt_ge_seven c hs hAutO hAutE h2024 h2401 e hn7 hpn hn

theorem kgroup_step4_pair (c : KQCfg A p Kb Sb Bb Mb z) (hs : KQStrong A p Mb z)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix)
    (h : IsChevSimple 2 ↥Kb ∨ ∃ n, Nonempty (↥Kb ≃* alternatingGroup (Fin n))) :
    IsChevSimple 2 ↥Kb ∧ ¬ (Nonempty (↥Kb ≃* alternatingGroup (Fin 6)) ∧
      (Nonempty (↥(Kb ⊔ Sb) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥(Kb ⊔ Sb) ≃* Equiv.Perm (Fin 6)))) := by
  by_cases hex : ∃ n, Nonempty (↥Kb ≃* alternatingGroup (Fin n))
  · obtain ⟨n, ⟨e⟩⟩ := hex
    have hp := c.prime
    have hp2 : p ≠ 2 := by have := c.five_le; omega
    have hpdvd : p ∣ Nat.card ↥Kb := by
      have h1 : orderOf (⟨z, c.z_mem_K⟩ : ↥Kb) = p := by
        rw [Subgroup.orderOf_mk]
        exact c.z_order
      rw [← h1]
      exact orderOf_dvd_natCard _
    have hpn : p ≤ n :=
      KGAlt.le_of_dvd_card_alt hp (by rwa [← Nat.card_congr e.toEquiv])
    have hn : n < 2 * p := KGAlt.lt_two_mul_of_pRank_le_one hp hp2 e c.rank
    have hn5 : 5 ≤ n := c.five_le.trans hpn
    by_cases h7 : 7 ≤ n
    · exact (false_of_alt_ge_seven c hs hAutO hAutE h2024 h2401 e h7 hpn hn).elim
    · have hn56 : n = 5 ∨ n = 6 := by omega
      refine ⟨isChevSimple_two_alt hn56 e, ?_⟩
      rintro ⟨⟨e6⟩, hX⟩
      rcases hn56 with rfl | rfl
      · exact not_equiv_alt_five_six e e6
      · have hp5' := c.five_le
        have hp5 : p = 5 := by
          rcases (show p = 5 ∨ p = 6 by omega) with h | h
          · exact h
          · exact absurd (h ▸ hp) (by norm_num)
        have hzS : z ∈ normalizer (Sb : Set A) := c.B_le_S c.z_mem_B
        have := hAlt6 A (Kb ⊔ Sb) Sb z hX (hp5 ▸ c.z_order) (Subgroup.mem_sup_left c.z_mem_K)
          le_sup_right c.S_two hzS
        exact c.S_ne this
  · exact ⟨h.resolve_right hex, fun ⟨⟨e6⟩, _⟩ => hex ⟨6, ⟨e6⟩⟩⟩

theorem kgroup_step4 (c : KQCfg A p Kb Sb Bb Mb z) (hs : KQStrong A p Mb z)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix)
    (h : IsChevSimple 2 ↥Kb ∨ ∃ n, Nonempty (↥Kb ≃* alternatingGroup (Fin n))) :
    IsChevSimple 2 ↥Kb ∧ ¬ (Nonempty (↥Kb ≃* alternatingGroup (Fin 6)) ∧
      (Nonempty (↥(Kb ⊔ Sb) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥(Kb ⊔ Sb) ≃* Equiv.Perm (Fin 6)))) ∧
    ∀ n : ℕ, 7 ≤ n → ¬ Nonempty (↥Kb ≃* alternatingGroup (Fin n)) := by
  have h' := kgroup_step4_pair c hs hAutO hAutE h2024 h2401 hAlt6 h
  exact ⟨h'.1, h'.2, fun n hn7 ⟨e⟩ => not_equiv_alt_ge_seven c hs hAutO hAutE h2024 h2401 hn7 e⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ
