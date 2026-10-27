module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnD4a
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnRed
public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

theorem om8_le_sp8 : CFSG.AGLEmbedding.Om8 ≤ StatedSp 4 (ZMod 2) := by
  have h1 : CFSG.AGLEmbedding.Om8 ≤
      CFSG.Blueprint.EvenSource.matrixOrthogonal CFSG.StandardType.SpEight.Q0 := by
    show StatedOmega (StatedQuadPlus 4 (ZMod 2)) ≤ _
    rw [CFSG.Blueprint.EvenSource.statedOmega_eq_commutator]
    exact Subgroup.commutator_le.2 fun a ha b hb =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
        (Subgroup.inv_mem _ hb)
  exact h1.trans CFSG.StandardType.SpEight.matrixOrthogonal_le_statedSp


theorem pPrimeCore_centralizer_om8 {s : ↥CFSG.AGLEmbedding.Om8}
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hq : HasU4Quot (Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8))) :
    CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)) = ⊥ := by
  let ι : ↥CFSG.AGLEmbedding.Om8 →* ↥(StatedSp 4 (ZMod 2)) := Subgroup.inclusion om8_le_sp8
  have hι : Function.Injective ι := Subgroup.inclusion_injective _
  obtain ⟨L, hLC, hLp, hLd⟩ := hq.exists_perfect
  refine U4Sp8.pPrimeCore_of_le_centralizer (s := ι s)
    (by rw [← map_pow, hs3, map_one]) (fun h => hs1 (hι (by rw [h, map_one])))
    (X := ↥(Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)))
    (ι.comp (Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)).subtype)
    (hι.comp (Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8)).subtype_injective) ?_
    (L.subgroupOf (Subgroup.centralizer ({s} : Set ↥CFSG.AGLEmbedding.Om8))) ?_ ?_
  · intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 x.2
    show ι x.1 * ι s = ι s * ι x.1
    rw [← map_mul, ← map_mul, this]
  · rw [Subgroup.isPerfect_iff]
    exact subgroupOf_perfect hLC hLp
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv]
    exact hLd

theorem u4InnInner_d4two {S : Type} [Group S] [Finite S]
    (hcat : catalogIs S S9.isD4two) (hS : IsSimpleGroup S) (g : S)
    (hu3 : (MulAut.conj g) ^ 3 = 1) (hq : HasU4Quot (u4Fix (MulAut.conj g))) :
    CFSG.pPrimeCore 3 ↥(u4Fix (MulAut.conj g)) = ⊥ := by
  obtain ⟨e⟩ := bridge_d4two hcat
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
    have hq' : HasU4Quot (Subgroup.centralizer ({e g} : Set ↥CFSG.AGLEmbedding.Om8)) := by
      rw [← centralizer_map_equiv e g]
      exact hq.map_equiv e
    refine pPrimeCore_centralizer_of_equiv e g ?_
    refine pPrimeCore_centralizer_om8 (by rw [← map_pow, hg3, map_one]) ?_ hq'
    intro h
    exact hg1 (e.injective (by rw [h, map_one]))

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
