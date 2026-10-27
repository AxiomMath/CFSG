module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Bound
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def CenterCentralizesBlockV {G : Type} [Group G] (X S L : Subgroup G)
    (hLX : L ≤ X) : Prop :=
  ∀ c (hc : c ∈ L), QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨c, hLX hc⟩ ∈
      Subgroup.centralizer (barM X L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) →
    ∀ v ∈ blockV S L, c * v = v * c

@[expose] def CubeNStmt (side : ∀ {G : Type} [Group G] (X S L : Subgroup G), L ≤ X → Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Open.IsKGroup ↥X → Asc81bHyp X S →
    ∀ hL : IsWeakSBlock X S L, Nat.card (Subgroup.center ↥(barM X L)) = 3 →
    Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin 6)) →
    side X S L hL.le →
    ∀ a (ha : a ∈ X), a ∈ Subgroup.normalizer (S : Set G) →
      a ∈ Subgroup.normalizer (L : Set G) →
      (∃ k : ℕ, QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨a, ha⟩ ^ 3 ^ k = 1) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨a, ha⟩ ^ 3 ∈ barM X L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨a, ha⟩ ^ 3 = 1

theorem false_of_threeASix_cubeN {G : Type} [Group G] [Finite G] {P : Sylow 3 G}
    {M H R : Subgroup G}
    (h : D1PhaseThree 3 P M H R) (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hcubeN : ∀ a (ha : a ∈ M), a ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) →
      a ∈ Subgroup.normalizer (L : Set G) →
      (∃ k : ℕ, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩ ^ 3 ^ k = 1) →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩ ^ 3 ∈ barM M L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, ha⟩ ^ 3 = 1)
    {R' : Subgroup G} (hR'P : R' ≤ (P : Subgroup G)) (hR'H : R' ≤ H) {w : G} (hwR : w ∈ R')
    (hwo : orderOf w = 3)
    (hΩP : ∀ g ∈ (P : Subgroup G), (∀ h ∈ (P : Subgroup G), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w)
    (hstr : (∃ y ∈ R', y ^ 3 = z) ∨ (∃ a ∈ R', a ^ 3 ∈ Subgroup.zpowers w ∧ a ^ 3 ≠ 1)) :
    False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hPM : (P : Subgroup G) ≤ M := h.toD1Escape.sylow_le
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hnC : zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨-, hb, -⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  obtain ⟨hPbN, hdec⟩ := D1PhaseThree.dec_of_threeASix h hThree hcyc hzM hz3 hCz hin hrk hL hZ
    hA6
  set Pb := barM M (P : Subgroup G) with hPb
  have hmemPb : ∀ g (hg : g ∈ (P : Subgroup G)), mk ⟨g, hPM hg⟩ ∈ Pb := fun g hg =>
    ⟨⟨g, hPM hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hPbmem : ∀ x ∈ Pb, ∃ g, ∃ hg : g ∈ (P : Subgroup G), mk ⟨g, hPM hg⟩ = x := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
  have hinj : ∀ x y (hx : x ∈ (P : Subgroup G)) (hy : y ∈ (P : Subgroup G)),
      mk ⟨x, hPM hx⟩ = mk ⟨y, hPM hy⟩ → x = y := fun x y hx hy hxy =>
    eq_of_mk_eq_of_three P.isPGroup' hPM hx hy hxy
  have hmkmul : ∀ x y (hx : x ∈ M) (hy : y ∈ M),
      mk ⟨x * y, M.mul_mem hx hy⟩ = mk ⟨x, hx⟩ * mk ⟨y, hy⟩ := fun x y hx hy => by
    rw [← map_mul]; rfl
  have hmkpow : ∀ x (hx : x ∈ (P : Subgroup G)), mk ⟨x, hPM hx⟩ ^ 3 = 1 → x ^ 3 = 1 := by
    intro x hx hx3
    apply hinj _ _ (P.pow_mem hx 3) P.one_mem
    rw [show (⟨x ^ 3, hPM (P.pow_mem hx 3)⟩ : M) = ⟨x, hPM hx⟩ ^ 3 from rfl, map_pow, hx3]
    exact (map_one mk).symm
  have hPb3 : IsPGroup 3 Pb := (P.isPGroup'.comap_subtype (K := M)).map _
  rcases hstr with ⟨y, hyR, hy3⟩ | ⟨a, haR, ha3w, ha31⟩
  ·
    have hyP := hR'P hyR
    apply hnC
    have hy3' : mk ⟨y, hPM hyP⟩ ^ 3 = zb := by
      rw [hzb, ← map_pow]
      congr 1
      exact Subtype.ext (by simpa using hy3)
    rw [← hy3']
    exact pow_three_mem_centralizer_of_dec hPb3 hdec hb (hmemPb y hyP)
  have hwP : w ∈ (P : Subgroup G) := hR'P hwR
  set wb := mk ⟨w, hPM hwP⟩ with hwb
  have hwo' : orderOf wb = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (⟨w, hPM hwP⟩ : M) ^ 3 = 1 := Subtype.ext (by
        simp [← hwo, pow_orderOf_eq_one])
      rw [hwb, ← map_pow, h1, map_one]
    · intro h1
      have := hinj w 1 hwP P.one_mem (by rw [← hwb, h1]; exact (map_one mk).symm)
      rw [this, orderOf_one] at hwo
      norm_num at hwo
  have hΩ : ∀ x ∈ Pb, (∀ y ∈ Pb, Commute x y) → x ^ 3 = 1 → x ∈ Subgroup.zpowers wb := by
    intro x hx hxc hx3
    obtain ⟨g, hg, rfl⟩ := hPbmem x hx
    have hgc : ∀ h' ∈ (P : Subgroup G), Commute g h' := by
      intro h' hh'
      apply hinj _ _ (P.mul_mem hg hh') (P.mul_mem hh' hg)
      rw [hmkmul _ _ (hPM hg) (hPM hh'), hmkmul _ _ (hPM hh') (hPM hg)]
      exact (hxc _ (hmemPb h' hh')).eq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hΩP g hg hgc (hmkpow g hg hx3))
    have : (⟨g, hPM hg⟩ : M) = ⟨w, hPM hwP⟩ ^ k := Subtype.ext (by simp [hk])
    rw [this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  obtain ⟨Pbs, hPbs⟩ := exists_sylow_eq_barM (P := P) hPM
  obtain ⟨-, hwbA, -, -, -⟩ :=
    center_eq_zpowers_of_sylow hZ Pbs (hPbs ▸ hPbN) hwo' (hPbs ▸ hΩ)
  have haP := hR'P haR
  set ab := mk ⟨a, hPM haP⟩ with hab
  have hab3w : ab ^ 3 ∈ Subgroup.zpowers wb := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha3w
    have : (⟨a, hPM haP⟩ : M) ^ 3 = ⟨w, hPM hwP⟩ ^ k := Subtype.ext (by simp [hk])
    rw [hab, ← map_pow, this, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  have hab31 : ab ^ 3 ≠ 1 := fun h1 => ha31 (hmkpow a haP h1)
  have hζA : ab ^ 3 ∈ barM M L := (Subgroup.zpowers_le.mpr hwbA) hab3w
  have haS : a ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hR'H haR)
  have haL : a ∈ Subgroup.normalizer (L : Set G) :=
    D1PhaseThree.mem_normalizer_of_threeASix h hThree hcyc hzM hz3 hCz hin hrk hL hZ hA6
      (hPM haP) (P.isPGroup'.to_le (Subgroup.zpowers_le.mpr haP))
  obtain ⟨k, hk⟩ := hPb3 ⟨ab, hmemPb a haP⟩
  have hpow : ∃ k : ℕ, ab ^ 3 ^ k = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact hab31 (hcubeN a (hPM haP) haS haL hpow hζA)

end CFSG.LocalAnalysis.RankThreeTheoremC
