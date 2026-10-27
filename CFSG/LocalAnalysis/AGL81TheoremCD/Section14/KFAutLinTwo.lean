module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog

import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutCoprime
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoLinTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwoUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.Quasithin.SteinbergOuterPrimeControl
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.Dihedral.Glauberman.DicksonMaxDown
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

noncomputable section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo
  (le_normalizer_of_subgroupOf_eq_normalizer pRank_three_le_one_inf_of_mulEquiv_psl2GF)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
    normalizer_subgroupOf_le_of_isStronglyPEmbedded CentralizerHasPElementOutside)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
  (isCoatom_normalizer_of_mulEquiv_psl2GF good_psl2GF)
open CFSG.LocalAnalysis.UniquenessCase.UCK (not_le_of_isStronglyPEmbedded)
open CFSG.RankThree.PartOne.CTP (outerHom ker_outerHom)
open CFSG.RankThree.PartOne.Sec1511 (spe_fstar)
open CFSG.Glauberman.Dickson.MaxDown (eq_of_isCoatom_le)
open CFSG.Quasithin.OuterPrimeControl (outer_psl2_isCyclic_of_isPGroup)
open CFSG.SectionRank (pRank_mono)

theorem autMAt_psl2GF {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) : AutMAt p N := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, -, hKn, hKC⟩ := spe_fstar Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded (K := K) hO hK1 hN
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN hPK (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    not_le_of_isStronglyPEmbedded hN P hPN hPK T hT (Subgroup.subgroupOf_eq_top.mp h)
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    isCoatom_normalizer_of_mulEquiv_psl2GF hp2 hn e T
  have hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    (eq_of_isCoatom_le hmax hle hne).symm
  set T' : Subgroup X := (T : Subgroup ↥K).map K.subtype with hT'def
  have hT'map : T' = (P : Subgroup X) ⊓ K := by
    rw [hT'def, hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hT1 : T' ≠ ⊥ := by
    rw [hT'map]
    exact hPK
  have hTp : IsPGroup p T' := by
    rw [hT'def]
    exact T.isPGroup'.map K.subtype
  have hT'le : T' ≤ N := by
    have hTN : (T : Subgroup ↥K) ≤ N.subgroupOf K := by
      rw [hNK]
      exact Subgroup.le_normalizer
    calc T' = (T : Subgroup ↥K).map K.subtype := rfl
      _ ≤ (N.subgroupOf K).map K.subtype := Subgroup.map_mono hTN
      _ = N ⊓ K := Subgroup.subgroupOf_map_subtype N K
      _ ≤ N := inf_le_left
  have hNle : N ≤ Subgroup.normalizer ((T' : Subgroup X) : Set X) :=
    le_normalizer_of_subgroupOf_eq_normalizer hNK hT'le
  have hcard : ∀ R : Subgroup X, R ≤ N → (∀ x ∈ R, x ^ 3 = 1) → Nat.card R ≤ 9 := by
    intro R hRN hRexp
    refine card_le_nine_of_map_isCyclic hRexp (outerHom K) ?_ ?_
    · let V : Subgroup (Outer (CFSG.GorensteinWalter.PSL2 (GaloisField p n))) :=
        (R.map (outerHom K)).map (equivalence e).toMonoidHom
      have hexpφ : ∀ y ∈ R.map (outerHom K), y ^ 3 = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hRexp x hx, map_one]
      have hR3 : IsPGroup 3 ↥(R.map (outerHom K)) := fun y =>
        ⟨1, Subtype.ext (by simpa using hexpφ y y.2)⟩
      have hVp : IsPGroup 3 ↥V := hR3.map (equivalence e).toMonoidHom
      have hVcyc : IsCyclic ↥V := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact outer_psl2_isCyclic_of_isPGroup (GaloisField p n) (ℓ := 3) (by norm_num) hVp
      exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (R.map (outerHom K))
        (equivalence e).toMonoidHom (equivalence e).injective)).mpr hVcyc
    · rw [ker_outerHom K hKC]
      have hRK : R ⊓ K ≤ N ⊓ K := inf_le_inf hRN le_rfl
      have hrank : CFSG.Open.pRank 3 (R ⊓ K) ≤ 1 :=
        (pRank_mono (p := 3) (by norm_num : 1 < 3) hRK).trans
          (pRank_three_le_one_inf_of_mulEquiv_psl2GF hp5 hn hO hN e)
      exact card_le_three_of_exponent_three_of_pRank_le_one (fun x hx => hRexp x hx.1) hrank
  have hG : CentralizerHasPElementOutside p N :=
    (good_psl2GF hp2 hn hO hN e).2
  exact autMAt_of_card_le_nine hp5 hcard hTp hT1 hT'le hNle hG

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
