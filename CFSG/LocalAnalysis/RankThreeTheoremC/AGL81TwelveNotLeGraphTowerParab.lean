module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphTowerHat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphTowerPre
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

section Helpers

variable {A : Type} [Group A] [Finite A] {Y P : Subgroup A}

theorem normal_subgroupOf_pCoreOf (H : Subgroup A) : ((pCoreOf 2 H).subgroupOf H).Normal := by
  rw [CFSG.openPCoreOf_subgroupOf]
  exact CFSG.pCore_normal

theorem pCoreOf_le_of_isSylowTwoOf {T H : Subgroup A} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T :=
  CFSG.Quasithin.A4.le_of_normal_of_isSylowTwoOf h (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (normal_subgroupOf_pCoreOf H) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)

theorem not_three_dvd_of_perfect_le_preHatOf {U : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    [Group.IsSolvable ↥U] {K : Subgroup A} (hK : K ≤ preHatOf P U) (hperf : ⁅K, K⁆ = K) :
    ¬ 3 ∣ Nat.card K := by
  have hKP : K ≤ P := hK.trans (preHatOf_le P U)
  have hK'perf : ⁅K.subgroupOf P, K.subgroupOf P⁆ = K.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKP]
    exact hperf
  have hhat : hatOf P K ≤ U := by
    have := hatOf_mono (P := P) hK
    rwa [hatOf_preHatOf] at this
  have hhatperf : ⁅hatOf P K, hatOf P K⁆ = hatOf P K := by
    unfold hatOf
    rw [← Subgroup.map_commutator, hK'perf]
  have hbot : hatOf P K = ⊥ := eq_bot_of_perfect_of_le_solvable hhat hhatperf
  have hKQ : K.subgroupOf P ≤ CFSG.pCore 2 ↥P := by
    intro x hx
    have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) x ∈ hatOf P K :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at hx1
    exact (QuotientGroup.eq_one_iff x).1 hx1
  have h2 : IsPGroup 2 ↥(K.subgroupOf P) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).to_le hKQ
  have h2' : IsPGroup 2 ↥K := h2.of_equiv (Subgroup.subgroupOfEquivOfLe hKP)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2'
  rw [hn]
  intro h3
  have h4 := Nat.prime_three.dvd_of_dvd_pow h3
  omega

theorem exists_tower (hP : IsParabolicTwo Y P) :
    ∃ (T : Subgroup A) (S : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P)),
      IsSylowTwoOf T Y ∧ IsSylowTwoOf T P ∧ (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) = hatOf P T ∧
        IsParabolicTwo Y (preHatOf P (towerHat S)) ∧ T ≤ preHatOf P (towerHat S) ∧
        ∀ K : Subgroup A, K ≤ preHatOf P (towerHat S) → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K := by
  obtain ⟨hPY, T, hT, hTN⟩ := hP
  have hTP : T ≤ P := fun t ht => hTN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hTP' : IsSylowTwoOf T P := CFSG.Quasithin.A4.isSylowTwoOf_mono hT hTP hPY
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P),
      (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) = hatOf P T := by
    refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P))
      (CFSG.Quasithin.A4.toSylow hTP'), ?_⟩
    rw [Sylow.coe_mapSurjective, CFSG.Quasithin.A4.toSylow_coe]
    rfl
  have hYN : Y ⊓ normalizer (T : Set A) ≤ preHatOf P (towerHat S) := by
    rintro x ⟨hxY, hxT⟩
    have hxP : x ∈ P := hTN ⟨hxY, hxT⟩
    rw [mem_preHatOf_iff]
    refine ⟨hxP, normalizer_le_towerHat S ?_⟩
    have hgN : (⟨x, hxP⟩ : ↥P) ∈ normalizer ((T.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTP]
      exact hxT
    rw [hS]
    exact Subgroup.le_normalizer_map (H := T.subgroupOf P)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) (Subgroup.mem_map_of_mem _ hgN)
  refine ⟨T, S, hT, hTP', hS, ⟨(preHatOf_le P _).trans hPY, T, hT, hYN⟩,
    fun t ht => hYN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩, ?_⟩
  intro K hK hperf
  haveI := isSolvable_towerHat S
  exact not_three_dvd_of_perfect_le_preHatOf hK hperf

theorem false_of_isSylowTwoOf_pCoreOf_tower {T : Subgroup A} {S : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hT : IsSylowTwoOf T Y) (hPY : P ≤ Y) (hS : (S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) = hatOf P T)
    (hTP : T ≤ P) (hTU : T ≤ preHatOf P (towerHat S))
    (hsyl : IsSylowTwoOf (pCoreOf 2 (preHatOf P (towerHat S))) Y)
    {X : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hX : Sym.IsSymThree X) (hXs : IsSubnormal X ⊤) :
    False := by
  have hTP'' : IsSylowTwoOf T (preHatOf P (towerHat S)) :=
    CFSG.Quasithin.A4.isSylowTwoOf_mono hT hTU ((preHatOf_le P _).trans hPY)
  have hle : pCoreOf 2 (preHatOf P (towerHat S)) ≤ T := pCoreOf_le_of_isSylowTwoOf hTP''
  have hge : T ≤ pCoreOf 2 (preHatOf P (towerHat S)) :=
    (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.1 hsyl).2.2 T hT.1 hT.2.1 hle
  have hTnorm : preHatOf P (towerHat S) ≤ normalizer (T : Set A) := by
    have h1 := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (preHatOf P (towerHat S))
    rwa [le_antisymm hle hge] at h1
  have hU : towerHat S ≤ normalizer ((S : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) : Set _) := by
    rw [hS]
    have := hatOf_le_normalizer (P := P) hTP hTnorm
    rwa [hatOf_preHatOf] at this
  exact false_of_towerHat_le_normalizer S hU hX hXs

end Helpers

theorem exists_solvThree_parabolic {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hP : IsParabolicTwo Y P) {X : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (hX : Sym.IsSymThree X)
    (hXs : IsSubnormal X ⊤) :
    ∃ P'' : Subgroup A, IsParabolicTwo Y P'' ∧ P'' ≤ P ∧ ¬ IsSylowTwoOf (pCoreOf 2 P'') Y ∧
      ∀ K : Subgroup A, K ≤ P'' → ⁅K, K⁆ = K → ¬ 3 ∣ Nat.card K := by
  obtain ⟨T, S, hT, hTP, hS, hpar, hTU, hsol⟩ := exists_tower hP
  refine ⟨preHatOf P (towerHat S), hpar, preHatOf_le P _, fun hsyl => ?_, hsol⟩
  exact false_of_isSylowTwoOf_pCoreOf_tower hT hP.1 hS hTP.1 hTU hsyl hX hXs

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Tower
