module

public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LieType.Universal.Spin.Generation.Datum
public import CFSG.LieType.Universal.Spin.OddCT.Commutator
public import CFSG.LieType.Universal.Spin.OddCT.RankOne
public import CFSG.LieType.Universal.Spin.PlusCT.Commutator
public import CFSG.LieType.Universal.Spin.PlusCT.Weyl
public import CFSG.LieType.Universal.Spin.Structure.TypeB
public import CFSG.LieType.Universal.Spin.Structure.TypeD

public section

namespace CFSG.LieType.Universal.Spin

open CFSG.LieType.Steinberg

variable {n : ℕ} {K : Type} [Field K]

theorem plusDatum_steinbergExtras (hn : 3 ≤ n) :
    SteinbergExtras (plusDatum n K hn) (weylD K hn) (fun k => (torusD K hn k).range) where
  ne_bot := plusDatum_ne_bot hn
  two_smul_le := plusDatum_two_smul_le hn
  commutator_mem := plusDatum_commutator_mem hn
  prodInjective_pos := plusDatum_prodInjective_pos n K hn
  prodInjective_neg := plusDatum_prodInjective_neg n K hn
  posPart_inf_negPart := plusDatum_posPart_inf_negPart n K hn
  rankOne_bruhat := plusDatum_rankOne_bruhat hn
  eq_one_of_mem_normalizer := plusDatum_eq_one_of_mem_normalizer hn
  torus_commute := plusDatum_torus_commute hn
  torus_iSupIndep := plusDatum_torus_iSupIndep n K hn
  torus_inf_posPart := plusDatum_torus_inf_posPart n K hn

theorem oddDatum_steinbergExtras (h2 : (2 : K) ≠ 0) :
    SteinbergExtras (oddDatum n K) (weylB K) (fun k => (torusB K k).range) where
  ne_bot := oddDatum_ne_bot n K
  two_smul_le := oddDatum_two_smul_le n K
  commutator_mem := oddDatum_commutator_mem n K
  prodInjective_pos := oddDatum_prodInjective_pos n K
  prodInjective_neg := oddDatum_prodInjective_neg n K
  posPart_inf_negPart := oddDatum_posPart_inf_negPart n K h2
  rankOne_bruhat := oddDatum_rankOne_bruhat n K
  eq_one_of_mem_normalizer := oddDatum_eq_one_of_mem_normalizer n K
  torus_commute := oddDatum_torus_commute n K
  torus_iSupIndep := oddDatum_torus_iSupIndep n K
  torus_inf_posPart := oddDatum_torus_inf_posPart n K h2

end CFSG.LieType.Universal.Spin

namespace CFSG.LieType.CurtisTits

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

universe w

variable {F : Type} [Field F] [Finite F] {n p f : ℕ}

theorem curtisTitsConclusion_spinPlus (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hF : Nat.card F = p ^ f) (hn : 3 ≤ n) :
    CurtisTitsConclusion.{w} (plusDatum n F hn) .POmegaPlus n p f :=
  curtisTitsConclusion_of (plusDatum_isCTGroupDatum hn (plusDatum_iSup_eq_top n F hn))
    (plusDatum_steinbergExtras hn) (by change 0 < n; omega) (isQuasisimple_spinGroup_quadPlus hn)
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], statedClassicalModel_spin_quadPlus hadm hF⟩)

private theorem two_ne_zero_of_card (hadm : StatedLieAdmissible .POmegaOdd n p f)
    (hF : Nat.card F = p ^ f) : (2 : F) ≠ 0 := by
  obtain ⟨hp, hf, -, hp2⟩ := hadm
  have hq : (ringChar F).Prime := by rw [ringChar_eq_of_card_eq hp hf hF]; exact hp
  rw [Ne, two_eq_zero_iff_ringChar_eq_two hq, ringChar_eq_of_card_eq hp hf hF]
  exact hp2

theorem curtisTitsConclusion_spinOdd (hadm : StatedLieAdmissible .POmegaOdd n p f)
    (hF : Nat.card F = p ^ f) :
    CurtisTitsConclusion.{w} (oddDatum n F) .POmegaOdd n p f :=
  have h2 := two_ne_zero_of_card hadm hF
  have hn : 3 ≤ n := hadm.2.2.1
  curtisTitsConclusion_of (oddDatum_isCTGroupDatum n F (oddDatum_iSup_eq_top n F h2 hn))
    (oddDatum_steinbergExtras h2) (by change 0 < n; omega)
    (isQuasisimple_spinGroup_quadOdd h2 hn)
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], statedClassicalModel_spin_quadOdd hadm hF⟩)

theorem curtisTitsConclusion_spinMinus {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hF : Nat.card F = p ^ f) :
    CurtisTitsConclusion.{w} (Twisted.minusDatum n hirr) .POmegaMinus n p f :=
  have hn : 4 ≤ n := hadm.2.2
  curtisTitsConclusion_of (Twisted.minusDatum_isCTGroupDatum n hirr hn)
    (Twisted.minusDatum_steinbergExtras n hirr) (by change 0 < n - 1; omega)
    (isQuasisimple_spinGroup_quadMinus hn hirr)
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      statedClassicalModel_spin_quadMinus hadm hF hirr⟩)

end CFSG.LieType.CurtisTits
