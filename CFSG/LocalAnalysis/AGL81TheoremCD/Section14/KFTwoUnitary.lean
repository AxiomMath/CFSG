module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryStabDerived
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]

theorem le_normalizer_of_subgroupOf_eq_normalizer {K N : Subgroup X} [K.Normal]
    {T : Sylow p ↥K}
    (hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
    (hTle : ((T : Subgroup ↥K).map K.subtype : Subgroup X) ≤ N) :
    N ≤ Subgroup.normalizer (((T : Subgroup ↥K).map K.subtype : Subgroup X) : Set X) := by
  classical
  set Q : Subgroup X := (T : Subgroup ↥K).map K.subtype with hQdef
  have hQle : Q ≤ N := hTle
  have hNKQ : N ⊓ K ≤ Subgroup.normalizer (Q : Set X) := by
    intro y hy
    have hyK : (⟨y, hy.2⟩ : ↥K) ∈ Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) := by
      rw [← hNK, Subgroup.mem_subgroupOf]
      exact hy.1
    have h := Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hyK)
    rwa [hQdef]
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q (N ⊓ K) :=
    (show CFSG.ABGLocalTools.IsSylowOf p Q K from ⟨T, by rw [hQdef]⟩).of_le
      (le_inf hQle (Subgroup.map_subtype_le _)) inf_le_right
  have hNQ : ∀ n ∈ N, Q.map (MulAut.conj n).toMonoidHom = Q := by
    intro n hn
    have hQ'le : Q.map (MulAut.conj n).toMonoidHom ≤ N ⊓ K := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨?_, ?_⟩
      · exact N.mul_mem (N.mul_mem hn (hQle hq)) (N.inv_mem hn)
      · exact Subgroup.Normal.conj_mem (H := K) inferInstance q
          (Subgroup.map_subtype_le _ hq) n
    have hcard : Nat.card ↥(Q.map (MulAut.conj n).toMonoidHom) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    have hQ'syl : CFSG.ABGLocalTools.IsSylowOf p (Q.map (MulAut.conj n).toMonoidHom) (N ⊓ K) :=
      CFSG.ABGLocalTools.isSylowOf_of_card hQ'le (by rw [hcard, hQsyl.card_eq])
    obtain ⟨k, hk, hkQ⟩ := hQsyl.exists_mem_conj hQ'syl
    have hle : Q.map (MulAut.conj n).toMonoidHom ≤ Q := fun x hx => by
      have h1 := (hkQ x).1 hx
      have h2 := ((Subgroup.mem_normalizer_iff.1 (hNKQ hk)) (k⁻¹ * x * k)).1 h1
      have h3 : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rwa [h3] at h2
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : (MulAut.conj n) x ∈ Q.map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hNQ n hn] at h1
    simpa [MulAut.conj_apply] using h1
  · intro hx
    have h1 : (MulAut.conj n) x ∈ Q.map (MulAut.conj n).toMonoidHom := by
      rw [hNQ n hn]
      simpa [MulAut.conj_apply] using hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
    have h2 : y = x := (MulAut.conj n).injective (by simpa using hyx)
    rwa [h2] at hy

theorem isSolvable_of_unitary {d : TauCeti.ValidLieTypeIndex}
    (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    Group.IsSolvable ↥N := by
  classical
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar Fact.out hO hN
  set K := CFSG.generalizedFitting X with hKdef
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
      hO hK1 hN
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hTsub : ((T : Subgroup ↥K).map K.subtype).subgroupOf K = (T : Subgroup ↥K) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hnotle : ¬ K ≤ N :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    CFSG.AGLEmbedding.kFactUnitaryBorelMaximal ↥K p d hd ⟨e⟩ T
  have hsol : Group.IsSolvable ↥(Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by
    refine CFSG.AGLEmbedding.UnitaryModel.isSolvable_of_unitary_sylow_le hd ⟨e⟩ T
      Subgroup.le_normalizer ?_
    intro htop
    have hTN : (T : Subgroup ↥K).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup ↥K) with hbot | htopT
    · have h1 : ((T : Subgroup ↥K).map K.subtype : Subgroup X) = ⊥ := by
        rw [hbot, Subgroup.map_bot]
      rw [h1] at hTmap
      exact hPK hTmap.symm
    · have hKle : K ≤ ((T : Subgroup ↥K).map K.subtype : Subgroup X) := by
        rw [htopT]
        intro x hx
        exact Subgroup.mem_map_of_mem K.subtype (Subgroup.mem_top (⟨x, hx⟩ : ↥K))
      exact hnotle (hKle.trans (by rw [hTmap]; exact inf_le_left.trans hPN))
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    have h := normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN (p := p) (K := K) (Q := (T : Subgroup ↥K).map K.subtype)
      (by rw [hTmap]; exact hPK) (T.isPGroup'.map K.subtype)
      (by rw [hTmap]; exact inf_le_left.trans hPN) (Subgroup.map_subtype_le _)
    rwa [hTsub] at h
  have hne : N.subgroupOf K ≠ ⊤ := fun h => hnotle (Subgroup.subgroupOf_eq_top.1 h)
  have hout : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    CFSG.AGLEmbedding.kFactUnitaryOuterSolvable ↥K p d hd ⟨e⟩
  exact isSolvable_of_isCoatom_normalizer
    hKC hout hmax hsol hle hne

theorem map_conjNormal_eq_of_mem_normalizer {K : Subgroup X} [K.Normal] {T : Subgroup ↥K} {n : X}
    (hn : n ∈ Subgroup.normalizer ((T.map K.subtype : Subgroup X) : Set X)) :
    T.map (MulAut.conjNormal (G := X) (H := K) n).toMonoidHom = T := by
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_map]
  have hcomp : K.subtype.comp (MulAut.conjNormal (G := X) (H := K) n).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp K.subtype := by
    ext k
    simp [MulAut.conjNormal_apply, MulAut.conj_apply]
  rw [hcomp, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hn

theorem pRank_three_commutator_le_one_of_unitary (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 := by
  classical
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar Fact.out hO hN
  set K := CFSG.generalizedFitting X with hKdef
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hTsub : ((T : Subgroup ↥K).map K.subtype).subgroupOf K = (T : Subgroup ↥K) := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hnotle : ¬ K ≤ N :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    CFSG.AGLEmbedding.kFactUnitaryBorelMaximal ↥K p d hd ⟨e⟩ T
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    have h := normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN (p := p) (K := K) (Q := (T : Subgroup ↥K).map K.subtype)
      (by rw [hTmap]; exact hPK) (T.isPGroup'.map K.subtype)
      (by rw [hTmap]; exact inf_le_left.trans hPN) (Subgroup.map_subtype_le _)
    rwa [hTsub] at h
  have hne : N.subgroupOf K ≠ ⊤ := fun h => hnotle (Subgroup.subgroupOf_eq_top.1 h)
  have hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    (hle.eq_or_lt.resolve_right fun hlt => hne (hmax.2 _ hlt)).symm
  have hNle : N ≤ Subgroup.normalizer
      (((T : Subgroup ↥K).map K.subtype : Subgroup X) : Set X) :=
    le_normalizer_of_subgroupOf_eq_normalizer hNK
      (by rw [hTmap]; exact inf_le_left.trans hPN)
  let ρ : X →* MulAut ↥K := MulAut.conjNormal (G := X) (H := K)
  have hρinj : Function.Injective ρ :=
    CFSG.Wreathed.SimpleOddIndexQuotient.conjNormal_injective_of_centralizer_eq_bot K hKC
  have hA : ∀ α ∈ N.map ρ, (T : Subgroup ↥K).map α.toMonoidHom = T := by
    intro α hα
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hα
    exact map_conjNormal_eq_of_mem_normalizer (hNle hn)
  calc CFSG.Open.pRank 3 ⁅N, N⁆
      ≤ CFSG.Open.pRank 3 ((⁅N, N⁆).map ρ) :=
        CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) ρ hρinj _
    _ = CFSG.Open.pRank 3 ⁅N.map ρ, N.map ρ⁆ := by rw [Subgroup.map_commutator]
    _ ≤ 1 := CFSG.AGLEmbedding.UnitaryModel.pRank_three_commutator_le_one_of_stabilizes_sylow
        (by omega : p ≠ 3) hd e T _ hA

theorem isSolvable_and_pRank_three_le_one_of_unitary (hp5 : 5 ≤ p)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex p d)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 :=
  ⟨isSolvable_of_unitary hd hO hN e,
    pRank_three_commutator_le_one_of_unitary hp5 hd hO hN e⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo
