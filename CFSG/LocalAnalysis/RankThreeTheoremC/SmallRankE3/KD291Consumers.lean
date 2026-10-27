module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3L613
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4L63
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291GammaP
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Beta
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3Bridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5IiiBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613
open CFSG.LocalAnalysis.RankFourTheoremC (KD29Inner)

@[expose] def KD291PPerf : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (P : Sylow p X) (x : X),
    CFSG.AGLEmbedding.CatalogSimpleSections X → x ∈ (P : Subgroup X) → x ≠ 1 → x ^ p = 1 →
    Open.pRank p (P : Subgroup X) = 3 → Open.pRank p (centralizer ({x} : Set X)) = 2 →
    (∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) →
    (∀ Q : Subgroup X, Q ≠ ⊥ → IsPGroup 2 Q → Open.pRank 3 (normalizer (Q : Set X)) ≤ 3) →
    (∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
    ∀ (S : Type) [Group S] [IsSimpleGroup S], (¬ ∀ a b : S, a * b = b * a) → p ∣ Nat.card S →
      ¬ IsSecOf (centralizer ({x} : Set X)) S

theorem kd291PPerf_of_gamma (hγ : N3.GammaStructureP) (hI : KD29Inner) : KD291PPerf := by
  intro p hp hp5 X _ _ P x hcat hxP hx1 hx5 hP hC hperf _ hcomp S _ _ hnab hpS hsec
  obtain ⟨L, hLn, hLs, hLnab, hLcat, hLlu, hLC, hxL, -⟩ :=
    hγ p hp hp5 X P x hcat hxP hx1 hx5 hP hC hperf hcomp
  haveI := hLn
  haveI : Fact p.Prime := ⟨hp⟩
  have hxo : orderOf x = p := orderOf_eq_prime hx5 hx1
  have hY : 3 ≤ Open.pRank p (⊤ : Subgroup (X ⧸ primeComplementCore (G := X) p)) :=
    (N3.kd291_pRank_quot hp P hP).ge
  have hsolv := N3.kd291_solvable_of_inner hp hp5 hI L hLs hLnab hLcat hLlu hLC hY hxL
    (N3.kd291_orderOf_mk hp hxo) (N3.kd291_pRank_cent_quot hp hxo hC.le)
  exact N3.kd291_not_isSecOf_of_solvable _ hsolv S hnab
    (N3.kd291_isSecOf_quot hp hxo S hnab hpS hsec)

theorem p622L613_of_kd291PPerf (hK : KD291PPerf) (hβ : NoTwoComponentsGen) : P622L613 := by
  intro G _ _ hSet _ _ _ p hp3 P M hs x z hx hz hpc H K hHM hsec hpS _ _ _ _ _
  exfalso
  have hprime : p.Prime := sigmaA_prime p hs.mem_sigmaA
  have hp2 : p ≠ 2 := sigmaA_odd p hs.mem_sigmaA
  have hp4 : p ≠ 4 := by
    intro h
    have hd : 2 ∣ p := ⟨2, by omega⟩
    rcases hprime.eq_one_or_self_of_dvd 2 hd with h' | h' <;> omega
  have hp5 : 5 ≤ p := by
    have := hprime.two_le
    omega
  obtain ⟨hPM, hxM, hzM, hpl⟩ := n4_plane63E3 hSet hs hp5 hx hz
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI hKn : (K.subgroupOf H).Normal := hsec.2.1
  haveI hsimp : IsSimpleGroup (↥H ⧸ K.subgroupOf H) := isSimpleGroup_quotient_of_section hsec
  have hnab := not_comm_quotient_of_section hsec
  have hpS' : p ∣ Nat.card (↥H ⧸ K.subgroupOf H) := hpS
  have hS1 := isSecOf_of_section (K := K) hxM hHM
  have hne : M ≠ ⊤ := fun h => hx.not_centralizer_le (h ▸ le_top)
  obtain ⟨L₀, hL₀, -, -, hL₀p, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component
      hSet.kProper M hne p hprime
      (fun h => hpc (CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_of_hasPrimeConstraint h))
  by_cases hmulti : ∃ L K' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      IsComponentOf L ⊤ ∧ IsComponentOf K' ⊤ ∧ L ≠ K'
  ·
    obtain ⟨L, K', hL, hK', hLK'⟩ := hmulti
    have hwit : ∃ L₁ K₁ : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
        IsComponentOf L₁ ⊤ ∧ p ∣ Nat.card L₁ ∧ IsComponentOf K₁ ⊤ ∧ K₁ ≠ L₁ := by
      by_cases hK'L₀ : K' = L₀
      · exact ⟨L₀, L, hL₀, hL₀p, hL, fun h => hLK' (h.trans hK'L₀.symm)⟩
      · exact ⟨L₀, K', hL₀, hL₀p, hK', hK'L₀⟩
    exact hβ G hSet p hp5 P M hs x z hx hz hwit
  ·
    push Not at hmulti
    have hxP : (⟨x, hxM⟩ : ↥M) ∈ ((P.subtype hPM : Sylow p ↥M) : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr hx.mem
    have hx1 : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx.ne_one (congrArg Subtype.val h)
    have hxp : (⟨x, hxM⟩ : ↥M) ^ p = 1 := Subtype.ext hx.pow_eq_one
    have hrk2 : Open.pRank p (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) = 2 := by
      refine le_antisymm hpl.rank_centralizer ?_
      have hB := hpl.plane
      refine CFSG.SectionRank.le_pRank hprime.one_lt
        (E := zpowers (⟨x, hxM⟩ : ↥M) ⊔ zpowers (⟨z, hzM⟩ : ↥M)) ?_ hB.isElemAbelian hB.card_eq
      intro b hb
      rw [mem_centralizer_singleton_iff]
      have hxB : (⟨x, hxM⟩ : ↥M) ∈ zpowers (⟨x, hxM⟩ : ↥M) ⊔ zpowers (⟨z, hzM⟩ : ↥M) :=
        Subgroup.mem_sup_left (mem_zpowers _)
      exact (hB.isElemAbelian.1.is_comm.comm ⟨b, hb⟩ ⟨_, hxB⟩) |> congrArg Subtype.val
    exact hK p hprime hp5 ↥M (P.subtype hPM) ⟨x, hxM⟩ hpl.catalog hxP hx1 hxp hpl.pRank_eq hrk2
      (fun N _ hN => n4_eq_top_of_isPGroup_quotient hSet hs N hN)
      (N3.three_rank_normalizer_le hSet.rank M)
      ⟨L₀, hL₀, fun K' hK' => hmulti K' L₀ hK' hL₀⟩ (↥H ⧸ K.subgroupOf H) hnab hpS' hS1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

theorem l613f3E3_of_kd291PPerf (hK : KD291PPerf) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (h64 : CFSG.LocalAnalysis.RankFourTheoremC.KFactCenterCyclicGeFive)
    (h610 : GL83.I_6_10_1) (h7131 : GL83.I_7_13_1) (hsplit : KFactSylowSplit)
    (hI : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input10_20_3) : L613f3E3 := by
  intro G _ _ hSet hD1 P M x z hs hx hz hpc H K hHM hsec hpS h3S
  exfalso
  obtain ⟨hPM, hxM, hzM, hpl⟩ := plane63E3_of_situation hSet hs hx hz
  have hp : (5 : ℕ).Prime := Nat.prime_five
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  haveI hKn : (K.subgroupOf H).Normal := hsec.2.1
  haveI hsimp : IsSimpleGroup (↥H ⧸ K.subgroupOf H) := isSimpleGroup_quotient_of_section hsec
  have hnab := not_comm_quotient_of_section hsec
  have hpS' : 5 ∣ Nat.card (↥H ⧸ K.subgroupOf H) := hpS
  have hS1 := isSecOf_of_section (K := K) hxM hHM
  have hne : M ≠ ⊤ := fun h => hx.not_centralizer_le (h ▸ le_top)
  obtain ⟨L₀, hL₀, -⟩ := CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component
    hSet.kProper M hne 5 hp
    (fun h => hpc (CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_of_hasPrimeConstraint h))
  by_cases hmulti : ∃ L K' : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5),
      IsComponentOf L ⊤ ∧ IsComponentOf K' ⊤ ∧ L ≠ K'
  ·
    have hβs := betaStructure_E3 h64 h610 h7131 hsplit hpl hmulti
    obtain ⟨C₀⟩ : Nonempty (ComponentIndex (↥M ⧸ primeComplementCore (G := ↥M) 5)) :=
      (Nat.card_pos_iff.mp (by rw [hβs.card_components]; exact hp.pos)).1
    have h5C : 5 ∣ Nat.card ↥C₀.1 := hpS'.trans (section_dvd_component_E3 hpl hβs hSch hnab hpS' hS1 C₀)
    have hrk := pRank_ge_of_beta_E3 hβs hI C₀ hp (by norm_num) h5C
    rw [pRank_top_subtype hp.one_lt] at hrk
    have hle : Open.pRank 5 M ≤ 3 :=
      (local_pRank_le_evenRank 5 hp (by norm_num) M hs.isCoreMaxLocal.1.1).trans hSet.rank.le
    omega
  ·
    push Not at hmulti
    have hxP : (⟨x, hxM⟩ : ↥M) ∈ ((P.subtype hPM : Sylow 5 ↥M) : Subgroup ↥M) :=
      Subgroup.mem_subgroupOf.mpr hx.mem
    have hx1 : (⟨x, hxM⟩ : ↥M) ≠ 1 := fun h => hx.ne_one (congrArg Subtype.val h)
    have hx5 : (⟨x, hxM⟩ : ↥M) ^ 5 = 1 := Subtype.ext hx.pow_eq_one
    have hrk2 : Open.pRank 5 (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) = 2 := by
      refine le_antisymm hpl.rank_centralizer ?_
      have hB := hpl.plane
      refine CFSG.SectionRank.le_pRank hp.one_lt (E := zpowers (⟨x, hxM⟩ : ↥M) ⊔ zpowers (⟨z, hzM⟩ : ↥M))
        ?_ hB.isElemAbelian hB.card_eq
      intro b hb
      rw [mem_centralizer_singleton_iff]
      have hxB : (⟨x, hxM⟩ : ↥M) ∈ zpowers (⟨x, hxM⟩ : ↥M) ⊔ zpowers (⟨z, hzM⟩ : ↥M) :=
        Subgroup.mem_sup_left (mem_zpowers _)
      exact (hB.isElemAbelian.1.is_comm.comm ⟨b, hb⟩ ⟨_, hxB⟩) |> congrArg Subtype.val
    exact hK 5 hp le_rfl ↥M (P.subtype hPM) ⟨x, hxM⟩ hpl.catalog hxP hx1 hx5 hpl.pRank_eq hrk2
      (fun N _ hN => n4_eq_top_of_isPGroup_quotient hSet hs N hN)
      (three_rank_normalizer_le hSet.rank M)
      ⟨L₀, hL₀, fun K' hK' => hmulti K' L₀ hK' hL₀⟩ (↥H ⧸ K.subgroupOf H) hnab hpS' hS1

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
