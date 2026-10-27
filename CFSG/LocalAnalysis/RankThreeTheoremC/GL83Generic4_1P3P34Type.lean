module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Main
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericQuasisimple3NoBM
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open scoped MatrixGroups
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem exists_isPrimeThreeType_of_generic {G : Type} [Group G] [Finite G] (hS : Setting G)
    (hU0 : FullCoreLocal G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic)
    (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hgen : IsGenericPoint p P M x) (hp3 : p = 3) :
    ∃ J : Subgroup G, J ≤ centralizer ({x} : Set G) ∧
      centralizer ({x} : Set G) ≤ normalizer (J : Set G) ∧ Group.IsPerfect J ∧
      rankThreePrimeCore p J < J ∧
      (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
        N = rankThreePrimeCore p J ∨ N = J) ∧ ¬ J ≤ M ∧
      ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
        ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ IsPrimeThreeType Q := by
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨S, hSmap, hsh⟩ := exists_genericShadow3 hS hU0 hp hp3 hM hgen
  have hBM : ∀ L : Subgroup (GenericReduced p x), IsComponentOf L ⊤ → NotBM ↥L :=
    fun L hL => notBM_of_notSecExcl3
      (notSecExcl3_of_noExcludedSection3 hno hL.2.2 (hsh.center_eq_bot K4 hL))
  obtain ⟨Lb, hLbc, hLbn, huniq, hLbZ, hLbΓ, hLblist⟩ := hsh.exists_main3_noBM K4 K1 K2 K3 hBM
  obtain ⟨hxP, ⟨hxM, hx1, hxp, hx3, hCM⟩, hsyl, hrk⟩ := id hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have : Lb.Normal := hLbn
  have hLbperf : ⁅Lb, Lb⁆ = Lb := Subgroup.isPerfect_iff.mp ⟨hLbc.2.2.1⟩
  obtain ⟨hLsimple, -, -⟩ := hsh.simple_nonab_catalog K4 hLbc
  have hLb_ne : Lb ≠ ⊥ := by
    intro h
    have := hLsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot Lb).mp this h
  set J : Subgroup C := perfectCore (Lb.comap π) with hJ
  have hJn : J.Normal := normal_perfectCore _
  have hJperf : ⁅J, J⁆ = J := commutator_perfectCore _
  have hJmap : J.map π = Lb :=
    map_perfectCore_comap π (QuotientGroup.mk'_surjective O) Lb hLbperf
  set JG : Subgroup G := J.map C.subtype with hJG
  have hJGC : JG ≤ C := Subgroup.map_subtype_le J
  have hCJG : C ≤ normalizer (JG : Set G) := le_normalizer_map_subtype J
  have hJGperf : ⁅JG, JG⁆ = JG := commutator_map_subtype J hJperf
  have hsimple : IsSimpleGroup ↥(J.map π) := by rw [hJmap]; exact hLsimple
  have hnot : ¬ JG ≤ M := by
    intro hle
    apply hLbΓ
    have hJ' : J ≤ (C ⊓ M).subgroupOf C := fun j hj =>
      Subgroup.mem_subgroupOf.mpr ⟨j.2, hle ⟨j, hj, rfl⟩⟩
    rw [← hJmap]
    exact Subgroup.map_mono hJ'
  have hlt : rankThreePrimeCore p JG < JG :=
    rankThreePrimeCore_map_subtype_lt J (by rw [hJmap]; exact hLb_ne)
  obtain ⟨ψ, hψ, hψker⟩ := exists_surjective_ker_primeCore (p := p) (C := C) J
  have hlist : IsPrimeThreeType ↥(J.map π) := by
    subst hp3
    rcases hLblist with h | h
    · exact isPrimeThreeType_of_mulEquiv (MulEquiv.subgroupCongr hJmap)
        (isPrimeThreeType_of_isRankTwoSEGroup h)
    · exact isPrimeThreeType_of_mulEquiv (MulEquiv.subgroupCongr hJmap)
        (Or.inr (Or.inr (Or.inr (Or.inr h))))
  exact ⟨JG, hJGC, hCJG, Subgroup.isPerfect_iff.mpr hJGperf, hlt,
    fun N hN hn hON => eq_or_eq_of_normal J hsimple N hN hn hON, hnot, ↥(J.map π), inferInstance,
    ψ, hψ, hψker, hlist⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
