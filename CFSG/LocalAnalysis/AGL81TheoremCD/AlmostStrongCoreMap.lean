module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.Fitting
import CFSG.GroupTheory.PCore.RelPPrimeCoreMap
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Wreath
import CFSG.Open.GLBDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem rankThreeConj_map_conj (g h : G) (H : Subgroup G) :
    rankThreeConj h (H.map (MulAut.conj g).toMonoidHom) =
      (rankThreeConj (g⁻¹ * h * g) H).map (MulAut.conj g).toMonoidHom := by
  unfold rankThreeConj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply]
  change (MulAut.conj h⁻¹) ((MulAut.conj g) x) =
    (MulAut.conj g) ((MulAut.conj (g⁻¹ * h * g)⁻¹) x)
  simp only [MulAut.conj_apply]
  group

theorem rankThreeLayer_map_automorphism_le (φ : MulAut G) (H : Subgroup G) :
    (rankThreeLayer H).map φ.toMonoidHom ≤ rankThreeLayer (H.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map φ hL)

theorem rankThreeLayer_map_automorphism (φ : MulAut G) (H : Subgroup G) :
    rankThreeLayer (H.map φ.toMonoidHom) = (rankThreeLayer H).map φ.toMonoidHom := by
  refine le_antisymm ?_ (rankThreeLayer_map_automorphism_le φ H)
  have h := rankThreeLayer_map_automorphism_le φ.symm (H.map φ.toMonoidHom)
  rw [map_automorphism_symm_map] at h
  have h' := Subgroup.map_mono (f := φ.toMonoidHom) h
  have hX : ((rankThreeLayer (H.map φ.toMonoidHom)).map φ.symm.toMonoidHom).map
      φ.toMonoidHom = rankThreeLayer (H.map φ.toMonoidHom) := by
    simpa using map_automorphism_symm_map (rankThreeLayer (H.map φ.toMonoidHom)) φ.symm
  rwa [hX] at h'

namespace AlmostClauseTwoCore

private theorem centralizer_map_conj (P₀ : Subgroup G) (g : G) :
    Subgroup.centralizer (P₀.map (MulAut.conj g).toMonoidHom : Set G) =
      (Subgroup.centralizer (P₀ : Set G)).map (MulAut.conj g).toMonoidHom :=
  (CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism P₀
    (MulAut.conj g)).symm

private theorem rankThreeLayer_centralizer_map_conj (P₀ : Subgroup G) (g : G) :
    rankThreeLayer (Subgroup.centralizer (P₀.map (MulAut.conj g).toMonoidHom : Set G)) =
      (rankThreeLayer (Subgroup.centralizer (P₀ : Set G))).map
        (MulAut.conj g).toMonoidHom := by
  rw [centralizer_map_conj P₀ g, rankThreeLayer_map_automorphism]

private theorem rankThreePrimeCore_pRank_le_one_map {N : Subgroup G} {p q : ℕ} {g : G}
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (rankThreePrimeCore p N) ≤ 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (rankThreePrimeCore p (N.map (MulAut.conj g).toMonoidHom)) ≤ 1 := by
  have hmap : rankThreePrimeCore p (N.map (MulAut.conj g).toMonoidHom) =
      (rankThreePrimeCore p N).map (MulAut.conj g).toMonoidHom :=
    CFSG.Open.relPPrimeCore_map_mulEquiv (MulAut.conj g) N p
  rw [hmap, CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective q
    (MulAut.conj g).injective]
  exact h q hq hq2

private theorem centralizer_rankThreeLayer_pRank_le_one_map {P₀ : Subgroup G} {q : ℕ} {g : G}
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (Subgroup.centralizer (P₀ : Set G) ⊓
        Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q
      (Subgroup.centralizer (P₀.map (MulAut.conj g).toMonoidHom : Set G) ⊓
        Subgroup.centralizer (rankThreeLayer
          (Subgroup.centralizer (P₀.map (MulAut.conj g).toMonoidHom : Set G)) : Set G)) ≤ 1 := by
  have hcent := centralizer_map_conj P₀ g
  have hlayer := rankThreeLayer_centralizer_map_conj P₀ g
  have hcent2 : Subgroup.centralizer
      (rankThreeLayer (Subgroup.centralizer
        (P₀.map (MulAut.conj g).toMonoidHom : Set G)) : Set G) =
      (Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hlayer]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism
      (rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) (MulAut.conj g)).symm
  rw [hcent2, hcent, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective q
      (MulAut.conj g).injective]
  exact h q hq hq2

theorem map {N P : Subgroup G} {p : ℕ} (h : AlmostClauseTwoCore N P p) (g : G) :
    AlmostClauseTwoCore (N.map (MulAut.conj g).toMonoidHom)
      (P.map (MulAut.conj g).toMonoidHom) p := by
  obtain ⟨hp5, hsolv, P₀, hP₀P, hcard, hweak, hiso, hnotle, hother, hcore, hlayerConj⟩ := h
  refine ⟨hp5, ?_, P₀.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hP₀P, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective
      (f := (N.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom)
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).surjective
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  · intro h' hh'
    set k := g⁻¹ * h' * g
    have hle : rankThreeConj k P₀ ≤ P := by
      rw [rankThreeConj_map_conj g h' P₀] at hh'
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh'
    rw [rankThreeConj_map_conj g h' P₀, hweak k hle]
  · obtain ⟨hpFact, m, hm, ⟨e⟩⟩ := hiso
    refine ⟨hpFact, m, hm, ?_⟩
    have hlayer := rankThreeLayer_centralizer_map_conj P₀ g
    refine ⟨?_⟩
    rw [hlayer]
    exact (Subgroup.equivMapOfInjective (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e
  · intro hle
    apply hnotle
    have hlayer := rankThreeLayer_centralizer_map_conj P₀ g
    rw [hlayer] at hle
    have h' := Subgroup.map_mono (f := (MulAut.conj g).symm.toMonoidHom) hle
    rwa [map_automorphism_symm_map, map_automorphism_symm_map] at h'
  · intro Y hYP hYcard hYne
    set Y₀ := Y.map (MulAut.conj g).symm.toMonoidHom
    have hYeq : Y₀.map (MulAut.conj g).toMonoidHom = Y := by
      change (Y.map (MulAut.conj g).symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = Y
      simpa using map_automorphism_symm_map Y (MulAut.conj g).symm
    have hY₀P : Y₀ ≤ P := by
      have h := Subgroup.map_mono (f := (MulAut.conj g).symm.toMonoidHom) hYP
      rwa [map_automorphism_symm_map] at h
    have hY₀card : Nat.card Y₀ = p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).symm.injective, hYcard]
    have hY₀ne : Y₀ ≠ P₀ := by
      intro h
      apply hYne
      rw [← hYeq, h]
    have hN := hother Y₀ hY₀P hY₀card hY₀ne
    rw [← hYeq, ← Subgroup.map_normalizer_eq_of_bijective Y₀
      (MulAut.conj g).bijective]
    exact Subgroup.map_mono hN
  · intro q hq hq2
    exact rankThreePrimeCore_pRank_le_one_map hcore hq hq2
  · intro q hq hq2
    exact centralizer_rankThreeLayer_pRank_le_one_map hlayerConj hq hq2

end AlmostClauseTwoCore

theorem rankThreeClauseC_map {N P : Subgroup G} (h : rankThreeClauseC N P) (g : G) :
    rankThreeClauseC (N.map (MulAut.conj g).toMonoidHom)
      (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hsolv, ⟨e⟩, hΓ, hY⟩ := h
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hJmap : thompsonSubgroup (P.map (MulAut.conj g).toMonoidHom) =
      (thompsonSubgroup P).map (MulAut.conj g).toMonoidHom := by
    simpa using (CFSG.map_ambientMaxCardThompson_of_injective
      (MulAut.conj g).toMonoidHom P
      ((MulAut.conj g).injective.comp P.subtype_injective)).symm
  refine ⟨?_, ⟨(P.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj).symm.trans e⟩, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective
      (f := (N.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj).toMonoidHom)
      (N.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj).surjective
  · rw [hJmap, ← gamma_map_automorphism 1 3 (by norm_num)]
    exact Subgroup.map_mono hΓ
  · intro Y hYP hYcard hYJ
    set Y₀ := Y.map (MulAut.conj g).symm.toMonoidHom
    have hYeq : Y₀.map (MulAut.conj g).toMonoidHom = Y := by
      change (Y.map (MulAut.conj g).symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = Y
      simpa using map_automorphism_symm_map Y (MulAut.conj g).symm
    have hY₀P : Y₀ ≤ P := by
      have h := Subgroup.map_mono (f := (MulAut.conj g).symm.toMonoidHom) hYP
      rwa [map_automorphism_symm_map] at h
    have hY₀card : Nat.card Y₀ = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).symm.injective, hYcard]
    have hY₀J : ¬ Y₀ ≤ thompsonSubgroup P := by
      intro hle
      apply hYJ
      rw [← hYeq, hJmap]
      exact Subgroup.map_mono hle
    obtain ⟨Q, hQK, hQ2, hidx, hPQ, m, hm, hQ8⟩ := hY Y₀ hY₀P hY₀card hY₀J
    refine ⟨Q.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_, m, hm, ?_⟩
    · change Q.map (MulAut.conj g).toMonoidHom ≤
        relPPrimeCore 3 (N.map (MulAut.conj g).toMonoidHom)
      rw [relPPrimeCore_map_mulEquiv (MulAut.conj g) N 3]
      exact Subgroup.map_mono hQK
    · exact hQ2.of_equiv (Subgroup.equivMapOfInjective Q _ hinj)
    · change ¬ 2 ∣ (Q.map (MulAut.conj g).toMonoidHom).relIndex
        (relPPrimeCore 3 (N.map (MulAut.conj g).toMonoidHom))
      rw [relPPrimeCore_map_mulEquiv (MulAut.conj g) N 3,
        Subgroup.relIndex_map_map_of_injective Q (relPPrimeCore 3 N) hinj]
      exact hidx
    · calc P.map (MulAut.conj g).toMonoidHom
          ≤ (Subgroup.normalizer (Q : Set G)).map (MulAut.conj g).toMonoidHom :=
            Subgroup.map_mono hPQ
        _ = Subgroup.normalizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
            Subgroup.map_normalizer_eq_of_bijective Q (MulAut.conj g).bijective
    · have hinf : (Q.map (MulAut.conj g).toMonoidHom) ⊓
          Subgroup.centralizer ((Y₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
          (Q ⊓ Subgroup.centralizer (Y₀ : Set G)).map
            (MulAut.conj g).toMonoidHom := by
        rw [← CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism,
          ← Subgroup.map_inf _ _ _ hinj]
      rw [← hYeq]
      rw [hinf]
      exact CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsQ8CentralCyclic_map hQ8
        (MulAut.conj g)

namespace AlmostStrongCore

theorem map {N : Subgroup G} {p : ℕ} (hp : 1 < p) (h : AlmostStrongCore N p) (g : G) :
    AlmostStrongCore (N.map (MulAut.conj g).toMonoidHom) p := by
  obtain ⟨P, hPN, hΓ2, hcase⟩ := h
  refine ⟨g • P, ?_, ?_, ?_⟩
  · rw [sylow_conjugate_eq_map]
    exact Subgroup.map_mono hPN
  · rw [sylow_conjugate_eq_map, ← gamma_map_automorphism 2 p hp]
    exact Subgroup.map_mono hΓ2
  · rcases hcase with hΓ1 | hClause2 | ⟨h3, hC⟩
    · left
      rw [sylow_conjugate_eq_map, ← gamma_map_automorphism 1 p hp]
      exact Subgroup.map_mono hΓ1
    · right; left
      exact AlmostClauseTwoCore.map hClause2 g
    · right; right
      exact ⟨h3, rankThreeClauseC_map hC g⟩

end AlmostStrongCore

end CFSG.LocalAnalysis.AGL81TheoremCD
