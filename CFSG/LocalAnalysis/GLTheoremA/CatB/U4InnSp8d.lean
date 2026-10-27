module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutSp8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem mem_innerAut_of_index_le_two {S : Type} [Group S] {u : MulAut S} (hu3 : u ^ 3 = 1)
    (h : (innerAut S).index = 1 ∨ (innerAut S).index = 2) : u ∈ innerAut S := by
  have hq3 : (QuotientGroup.mk u : MulAut S ⧸ innerAut S) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hu3, QuotientGroup.mk_one]
  have hqn : (QuotientGroup.mk u : MulAut S ⧸ innerAut S) ^ Nat.card (MulAut S ⧸ innerAut S) = 1 :=
    pow_card_eq_one'
  have hcard : Nat.card (MulAut S ⧸ innerAut S) = (innerAut S).index := by
    rw [Subgroup.index_eq_card]
  rw [hcard] at hqn
  refine (QuotientGroup.eq_one_iff u).1 ?_
  rcases h with h | h
  · rw [h, pow_one] at hqn
    exact hqn
  · rw [h] at hqn
    calc (QuotientGroup.mk u : MulAut S ⧸ innerAut S)
        = (QuotientGroup.mk u) ^ 3 * ((QuotientGroup.mk u) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hq3, hqn]; simp

theorem u4InnAt_sp8two : U4InnAt S9.isSp8two := by
  intro S _ _ hcat hS u hu3 hq
  have hu : u ∈ innerAut S := mem_innerAut_of_index_le_two hu3 (u4Out_index_sp8two hcat)
  obtain ⟨g, rfl⟩ := hu
  obtain ⟨e⟩ := KFacts.bridge_sp8two hcat
  show CFSG.pPrimeCore 3 ↥(u4Fix (MulAut.conj g)) = ⊥
  rw [u4Fix_conj] at hq ⊢
  by_cases hg1 : g = 1
  · subst hg1
    have h3 : 3 ∣ Nat.card S := by
      have h25 := hq.dvd_card
      have : Subgroup.centralizer ({(1 : S)} : Set S) = ⊤ := by
        ext x
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp
      rw [this, Subgroup.card_top] at h25
      exact (show 3 ∣ 25920 by norm_num).trans h25
    have := pPrimeCore_u4Fix_one (M := S) h3
    rw [← u4Fix_conj (1 : S), map_one]
    exact this
  · have hnc : ¬ ∀ a b : S, a * b = b * a := by
      intro hcomm
      apply hq.not_isSolvable
      exact isSolvable_of_comm fun a b => Subtype.ext (hcomm a b)
    have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_of_not_comm hnc
    have hg3 : g ^ 3 = 1 := by
      have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow]; exact hu3
      have h2 := (conj_eq_conj_iff (g ^ 3) 1).1 (by rw [h1, map_one])
      rw [hZ, Subgroup.mem_bot] at h2
      simpa using h2
    have hq' : HasU4Quot (Subgroup.centralizer ({e g} : Set (StatedSp 4 (ZMod 2)))) := by
      rw [← centralizer_map_equiv e g]
      exact hq.map_equiv e
    refine pPrimeCore_centralizer_of_equiv e g ?_
    refine U4Sp8.pPrimeCore_centralizer_sp8 (by rw [← map_pow, hg3, map_one]) ?_ hq'
    intro h
    exact hg1 (e.injective (by rw [h, map_one]))

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
