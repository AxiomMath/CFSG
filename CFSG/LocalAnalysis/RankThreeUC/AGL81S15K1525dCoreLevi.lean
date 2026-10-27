module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreBorel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreQuot
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinHolds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcAdjacent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.GL32
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K1525dCoreProof

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin
  KFactsSmall

variable (m : ℕ)

theorem exists_sl3_levi {j j' : Fin (dat m).rank} (hj : j'.val = j.val + 1) :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* SLF2 m, Function.Injective l ∧
      l.range = rankOne (dat m).rootGroup j ⊔ rankOne (dat m).rootGroup j' := by
  have hL := CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear m (ZMod 2)
  obtain ⟨l, hl, hlt⟩ := hL.sl3 j j' hj
  have hroot : ∀ k : Fin (dat m).rank, (Pi.single k 1 : Fin (dat m).rank → ℤ) ∈ (dat m).roots ∧
      (-Pi.single k 1 : Fin (dat m).rank → ℤ) ∈ (dat m).roots := fun k =>
    ⟨(RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).single_mem k,
      (RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).neg_mem _
        ((RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).single_mem k)⟩
  have hX1 : (dat m).rootGroup (Pi.single j 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot j).1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 0 1 c, (hlt c).1⟩
  have hX2 : (dat m).rootGroup (-Pi.single j 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot j).2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 0 c, (hlt c).2.1⟩
  have hX3 : (dat m).rootGroup (Pi.single j' 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot j').1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 2 c, (hlt c).2.2.1⟩
  have hX4 : (dat m).rootGroup (-Pi.single j' 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot j').2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 2 1 c, (hlt c).2.2.2.1⟩
  refine ⟨l, hl, le_antisymm ?_ (sup_le (sup_le hX1 hX2) (sup_le hX3 hX4))⟩
  rintro z ⟨g, rfl⟩
  exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.range_le_of_sl3 hL hj hlt g

theorem isLThreeTwo_levi {j j' : Fin (dat m).rank} (hj : j'.val = j.val + 1) :
    IsLThreeTwo ↥(rankOne (dat m).rootGroup j ⊔ rankOne (dat m).rootGroup j') := by
  obtain ⟨l, hl, hr⟩ := exists_sl3_levi m hj
  exact IsLThreeTwo.of_mulEquiv
    ((K421HoldsProof.slEquivGL2 3).symm.trans
      ((MonoidHom.ofInjective hl).trans (MulEquiv.subgroupCongr hr)))
    Lie.isLThreeTwo_GL_three_two

theorem isL3TwoModO2_of_negIndices {j j' : Fin (dat m).rank} (hj : j'.val = j.val + 1)
    {A : Subgroup (SLF2 m)} (hBA : bor m ≤ A)
    (hI : negIndices (dat m) A = {j, j'}) : IsL3TwoModO2 A := by
  have hct := isCTGroupDatum m (ZMod 2)
  have hext := steinbergExtras m (ZMod 2)
  have hMeq : leviM (dat m) (negIndices (dat m) A) =
      rankOne (dat m).rootGroup j ⊔ rankOne (dat m).rootGroup j' := by
    rw [hI]
    show ⨆ i ∈ ({j, j'} : Set (Fin (dat m).rank)), rankOne (dat m).rootGroup i = _
    rw [iSup_insert, iSup_singleton]
  have hM : IsLThreeTwo ↥(leviM (dat m) (negIndices (dat m) A)) := by
    rw [hMeq]
    exact isLThreeTwo_levi m hj
  have hUA : leviRad (dat m) (negIndices (dat m) A) ≤ A :=
    le_sup_left.trans (leviRad_sup_leviM_le hBA)
  have hMA : leviM (dat m) (negIndices (dat m) A) ≤ A :=
    le_sup_right.trans (leviRad_sup_leviM_le hBA)
  have hAle : A ≤ leviRad (dat m) (negIndices (dat m) A) ⊔ leviM (dat m) (negIndices (dat m) A) := by
    have h := le_torus_sup_leviRad_sup_leviM hct hext hBA
    have h0 : (⨆ k : Fin (dat m).rank, torus m (ZMod 2) k) = ⊥ := iSup_torus_eq_bot m
    rwa [h0, bot_sup_eq] at h
  have hUn : A ≤ Subgroup.normalizer (leviRad (dat m) (negIndices (dat m) A) : Set (SLF2 m)) :=
    (eq_borel_sup_rankOne hct hext hBA).le.trans
      (sup_le (borel_le_normalizer_leviRad hct hext)
        (iSup₂_le fun i hi => rankOne_le_normalizer_leviRad hext hi))
  have hU2 : IsPGroup 2 ↥(leviRad (dat m) (negIndices (dat m) A)) :=
    isPGroup_leviRad hext (borelQuotient_id m).pGroup
  have hM2 : ¬ IsPGroup 2 ↥(leviM (dat m) (negIndices (dat m) A)) := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    have h3 := isLThreeTwo_three_dvd_card hM
    rw [hn] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  obtain ⟨e⟩ := quotient_pCore_equiv hUA hMA hAle hUn hU2 (isLThreeTwo_simple hM) hM2
  exact IsLThreeTwo.of_mulEquiv e.symm hM

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
