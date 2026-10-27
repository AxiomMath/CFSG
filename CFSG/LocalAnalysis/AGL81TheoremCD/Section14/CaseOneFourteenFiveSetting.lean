module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeAtC
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Quasi

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M H E Q J : Subgroup G}

private theorem inf_normalizer_le_inf_of_isSylowOf {p : ℕ} {K M P : Subgroup G}
    (hp : p.Prime) (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hPM : P ≤ M) :
    ∀ U : Subgroup G, U ≤ P → U ≠ ⊥ → K ⊓ Subgroup.normalizer (U : Set G) ≤ K ⊓ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro U hU hUbot
  have hUp : IsPGroup p U := hP.isPGroup.to_le hU
  have hUM : U ≤ M := hU.trans hPM
  have hNU : Subgroup.normalizer (U : Set G) ≤ M :=
    hstrong.normalizer_le hUbot hUp hUM
  exact le_inf inf_le_left (inf_le_right.trans hNU)

private theorem inf_centralizer_le_pPrimeCore {p : ℕ} {K C : Subgroup G}
    (hcent : Subgroup.centralizer
      (((K.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥C))) :
        Set (↥C ⧸ CFSG.pPrimeCore p ↥C)) = ⊥) :
    C ⊓ Subgroup.centralizer (K : Set G) ≤ (CFSG.pPrimeCore p ↥C).map C.subtype := by
  intro x hx
  obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
  let O : Subgroup ↥C := CFSG.pPrimeCore p ↥C
  let π : ↥C →* (↥C ⧸ O) := QuotientGroup.mk' O
  have hmem : π ⟨x, hxC⟩ ∈
      Subgroup.centralizer (((K.subgroupOf C).map π) : Set (↥C ⧸ O)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hcomm : (k : G) * x = x * (k : G) :=
      (Subgroup.mem_centralizer_iff.mp hxK) (k : G) hkK
    have hcomm' : k * (⟨x, hxC⟩ : ↥C) = (⟨x, hxC⟩ : ↥C) * k := Subtype.ext hcomm
    calc π k * π ⟨x, hxC⟩ = π (k * ⟨x, hxC⟩) := (map_mul π k _).symm
      _ = π ((⟨x, hxC⟩ : ↥C) * k) := by rw [hcomm']
      _ = π ⟨x, hxC⟩ * π k := map_mul π _ k
  have hcent' : Subgroup.centralizer (((K.subgroupOf C).map π) : Set (↥C ⧸ O)) = ⊥ := hcent
  rw [hcent'] at hmem
  have hx1 : π ⟨x, hxC⟩ = 1 := Subgroup.mem_bot.mp hmem
  refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, ?_, rfl⟩
  change (⟨x, hxC⟩ : ↥C) ∈ O
  rw [show O = MonoidHom.ker π from (QuotientGroup.ker_mk' O).symm]
  exact MonoidHom.mem_ker.mpr hx1

theorem S14Choice.caseOne_setting_centralizer (h : S14Choice G M H E Q J) (hA : TypeA M H)
    (h1441 : FourteenFourOneCaseOneAt M) (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) {p : ℕ} (hp : p ∈ sigmaSet G M) {C : Subgroup G}
    (hCtop : C ≠ ⊤) (hCM : ¬ C ≤ M) (h2C : 2 ≤ CFSG.Open.pRank p (M ⊓ C)) :
    5 ≤ p ∧ CFSG.IsQuasisimple ↥(kSub p M C) ∧
      CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p
        (↥(kSub p M C) ⧸ Subgroup.center ↥(kSub p M C)) ∧
      ¬ kSub p M C ≤ M ∧
      C ⊓ M ≤ Subgroup.normalizer (kSub p M C : Set G) ∧
      (∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (kSub p M C) ∧
        ∀ U : Subgroup G, U ≤ P → U ≠ ⊥ →
          kSub p M C ⊓ Subgroup.normalizer (U : Set G) ≤ kSub p M C ⊓ M) ∧
      C ⊓ Subgroup.centralizer (kSub p M C : Set G) ≤
        (CFSG.pPrimeCore p ↥C).map C.subtype := by
  classical
  have hp' : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  haveI : Fact p.Prime := ⟨hp'⟩
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h3 => h.hypCGen.not_mem_sigmaSet (h3 ▸ hp)
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp' hp2 hp3
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M :=
    h1441 H E Q J h hA p hp
  obtain ⟨Q', F', s⟩ :=
    O1217.Setting1417.exists_of_two_le_pRank h.cstar h.maxLocal (h1441 H E Q J h hA) hp
      hCtop hCM h2C
  have hK : CFSG.IsQuasisimple ↥(kSub p M C) := s.isQuasisimple_kSub_of_ne_three h1 h2 hp3
  have hlist := s.nineFourListGroup_quot_center_of_isQuasisimple h1 hK
  have hKM : ¬ kSub p M C ≤ M :=
    not_kSub_le_of_not_pLayerIn_le (p := p) s.not_pLayerIn_le
  have hKC : kSub p M C ≤ C := kSub_le p M C
  have hKnorm : C ≤ Subgroup.normalizer (kSub p M C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp (s.kStructure h1).1
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (Q' ⊓ kSub p M C) (kSub p M C) :=
    s.sylowH.inf_of_le_normalizer hKC hKnorm
  have hPM : Q' ⊓ kSub p M C ≤ M := inf_le_left.trans s.Q_le_M
  refine ⟨hp5, hK, hlist, hKM, inf_le_normalizer_kSub p M C, ?_, ?_⟩
  · exact ⟨Q' ⊓ kSub p M C, hPsyl,
      inf_normalizer_le_inf_of_isSylowOf hp' hstrong hPsyl hPM⟩
  · exact inf_centralizer_le_pPrimeCore (p := p) (K := kSub p M C)
      (s.centralizer_kStar_eq_bot h1)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
