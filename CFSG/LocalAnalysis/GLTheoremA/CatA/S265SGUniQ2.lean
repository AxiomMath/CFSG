module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly

theorem SG.false_of_uni_two {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (hN : QSNL 3 S B T x D K) (hcat : catalogIs (PSimple 3 K) (tyF 3))
    {F : Type} [Field F] {n d : ℕ} (hn : n = 1) (hF : Nat.card F = (2 ^ n) ^ 2) (hd4 : 4 ≤ d)
    (hd5 : d ≤ 5) (Φ : PSimple 3 S ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) :
    False := by
  subst hn
  obtain ⟨-, -, -, -, -, hKc, -⟩ := hN.cfg.std
  have hdvd := I167.card_pSimple_dvd_of_le Nat.prime_three hN.cfg.quasi (hKc.1.trans inf_le_left)
  rw [Nat.card_congr Φ.toEquiv] at hdvd
  have hR : Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))) = 25920 ∨
      Nat.card (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ 1))) = 13685760 := by
    change Nat.card (StatedProj (StatedSU d (2 ^ 1) F)) = _ ∨
      Nat.card (StatedProj (StatedSU d (2 ^ 1) F)) = _
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (n := d) Nat.prime_two le_rfl hF
      (by omega)]
    interval_cases d <;> decide
  obtain ⟨-, t, m, ht, hm⟩ := SG.lieModel_of_tyF hcat
  have hcard := hm.card_eq_lieOrd (by norm_num)
  have hexp : (2 ^ m) ^ 3 ∣ Nat.card (PSimple 3 K) := by
    rw [hcard]
    rcases ht with rfl | rfl
    · exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSL) (n := 3) (by decide) _
    · exact CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .PSU) (n := 3) (by decide) _
  have hm3 : m ≤ 3 := by
    by_contra hm4
    have h12 : 2 ^ 12 ∣ (2 ^ m) ^ 3 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    have h := (h12.trans hexp).trans hdvd
    rcases hR with hR | hR <;> rw [hR] at h <;> norm_num at h
  obtain ⟨-, hm1, hadm⟩ := hm.admissible
  rw [hcard] at hdvd
  rcases ht with rfl | rfl
  · interval_cases m <;> rcases hR with hR | hR <;> rw [hR] at hdvd <;> revert hdvd <;> decide
  · obtain ⟨-, hq⟩ := hadm
    interval_cases m
    · exact hq rfl
    all_goals rcases hR with hR | hR <;> rw [hR] at hdvd <;> revert hdvd <;> decide

end CFSG.LocalAnalysis.GLTheoremA.S265

end
