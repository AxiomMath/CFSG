module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkSylow
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkDiag
public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.CGT.PushingUpLit.BlocksCommute

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

variable {G : Type} [Group G] [Finite G]

theorem isBlockOfInX_conjugate_of_normalizes {N Y : Subgroup G} (hY : IsBlockOfInX N Y) {g : G}
    (hg : g ∈ normalizer (N : Set G)) : IsBlockOfInX N (CFSG.conjugate Y g) := by
  have hNg : CFSG.conjugate N g = N := ThreeFromEight.conjugate_eq_self_of_mem_normalizer hg
  refine ⟨?_, ?_, inClassX_conjugate hY.2.2 g⟩
  · intro x hx
    have hx' : g * x * g⁻¹ ∈ Y := ThreeFromEight.mem_conjugate_iff.mp hx
    have : x ∈ CFSG.conjugate N g := ThreeFromEight.mem_conjugate_iff.mpr (hY.1 hx')
    rwa [hNg] at this
  · have := CFSG.GroupTheory.isSubnormal_subgroupOf_conjugate g hY.2.1
    rwa [hNg] at this

theorem conjugate_pow_inv_ne {Y : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime) (hz : z ^ p = 1)
    (hzY : z ∉ normalizer (Y : Set G)) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    CFSG.conjugate Y (z ^ i)⁻¹ ≠ Y := by
  intro h
  have hg : (z ^ i)⁻¹ ∈ normalizer (Y : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := ThreeFromEight.mem_conjugate_iff (H := Y) (g := (z ^ i)⁻¹) (x := x)
    rw [h] at this
    exact this
  have hzi : z ^ i ∈ normalizer (Y : Set G) := by simpa using Subgroup.inv_mem _ hg
  exact hzY (mem_of_pow_mem hp hz (fun hd => absurd (Nat.le_of_dvd hi0 hd) (by omega)) hzi)

theorem conj_pow_commute {N Y : Subgroup G} {z : G} {p : ℕ} (hchar : IsCharacteristicP 2 ↥N)
    (hp : p.Prime) (hz : z ^ p = 1) (hzN : z ∈ normalizer (N : Set G)) (hY : IsBlockOfInX N Y)
    (hzY : z ∉ normalizer (Y : Set G)) {i : ℕ} (hi0 : 0 < i) (hip : i < p) {x t : G} (hx : x ∈ Y)
    (ht : t ∈ Y) : z ^ i * x * (z ^ i)⁻¹ * t = t * (z ^ i * x * (z ^ i)⁻¹) := by
  have hYi := isBlockOfInX_conjugate_of_normalizes hY
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ hzN i))
  have hcomm := distinct_blocks_commute_of_isBlockOfInX hchar hYi hY
    (conjugate_pow_inv_ne hp hz hzY hi0 hip)
  have hxi : z ^ i * x * (z ^ i)⁻¹ ∈ CFSG.conjugate Y (z ^ i)⁻¹ := by
    rw [ThreeFromEight.mem_conjugate_iff]
    have e : (z ^ i)⁻¹ * (z ^ i * x * (z ^ i)⁻¹) * ((z ^ i)⁻¹)⁻¹ = x := by group
    rw [e]
    exact hx
  have h1 := Subgroup.commutator_mem_commutator hxi ht
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem block_le_of_cycled {N S Y : Subgroup G} {z : G} {p : ℕ} (hp : p.Prime)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S N) (hchar : CFSG.QuasithinUnique.CharTwo N)
    (hY : IsBlockOfInX N Y) (hzN : z ∈ normalizer (N : Set G)) (hzp : z ^ p = 1)
    (hzY : z ∉ normalizer (Y : Set G)) (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hev : 2 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    Y ≤ S ⊔ (N ⊓ centralizer ({z} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar' := CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hchar
  set H : Subgroup G := S ⊔ (N ⊓ centralizer ({z} : Set G)) with hH
  set N' : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hN'
  have hdiag : ∀ y ∈ Y, ∃ d ∈ H, ∀ t ∈ Y, d * t * d⁻¹ = y * t * y⁻¹ := by
    intro y hy
    obtain ⟨d, hd, hdt⟩ := exists_diagonal hp.pos hzp hzN hY.1
      (fun i hi0 hip x hx t ht => conj_pow_commute hchar' hp hzp hzN hY hzY hi0 hip hx ht) hy
    exact ⟨d, Subgroup.mem_sup_right hd, hdt⟩
  haveI hnormal : (H.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hdH, hdt⟩ := hdiag (g : G) g.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hdt _ n.2]
    exact H.mul_mem (H.mul_mem hdH hn) (H.inv_mem hdH)
  have hTfin := isSylowTwoOf_inf_block hS hY
  set T : Subgroup ↥Y := (S ⊓ Y).subgroupOf Y with hT
  have hO2 : pCoreOf 2 Y ≤ S := pCoreOf_block_le hS hY
  have hNT : N' ≤ T := fun n hn => Subgroup.mem_subgroupOf.mpr ⟨hO2 ⟨n, hn, rfl⟩, n.2⟩
  have hTN : T ≤ H.subgroupOf Y := fun t ht =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ht).1)
  have htop := eq_top_of_quasisimple_of_sylow N' hq hev (H.subgroupOf Y) T hTN hNT
    hTfin.2.1.comap_subtype hTfin.2.2
  intro g hg
  have : (⟨g, hg⟩ : ↥Y) ∈ H.subgroupOf Y := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem not_isQuasisimple_of_card_three {K : Type*} [Group K] (hK : Nat.card K = 3) :
    ¬ CFSG.IsQuasisimple K := by
  intro hq
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic K := isCyclic_of_prime_card hK
  have hcomm : IsMulCommutative K :=
    (MonoidHom.id K).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
  have hbot : commutator K = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    refine eq_top_iff.mpr fun g _ => Subgroup.mem_center_iff.mpr fun h => ?_
    exact hcomm.is_comm.comm h g
  have hperf : commutator K = ⊤ := Group.isPerfect_def.mp hq.1
  have h1 : Nat.card (⊤ : Subgroup K) = 3 := by rw [Subgroup.card_top]; exact hK
  rw [← hperf, hbot, Subgroup.card_bot] at h1
  omega

theorem two_dvd_card_top_of_quasisimple {N Y : Subgroup G}
    (hY : IsBlockOfInX N Y) (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    2 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hY.2.2.2 with ⟨n, hn1, hnat⟩ | ⟨n, hn1, hnat⟩
  · obtain ⟨φ, -⟩ := hnat
    have hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) =
        Nat.card (alternatingGroup (Fin (2 * n + 1))) := Nat.card_congr φ.toEquiv
    by_cases hn2 : 2 ≤ n
    · haveI : Nontrivial (Fin (2 * n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      obtain ⟨k, hk⟩ : Nat.factorial 4 ∣ Nat.factorial (2 * n + 1) :=
        Nat.factorial_dvd_factorial (by omega)
      have h24 : Nat.factorial 4 = 24 := by decide
      rw [hk, h24]
      omega
    · exfalso
      have hn : n = 1 := by omega
      subst hn
      refine not_isQuasisimple_of_card_three ?_ hq
      rw [hcard, Nat.card_eq_fintype_card]
      show Fintype.card (alternatingGroup (Fin 3)) = 3
      decide
  · have hn2 : 2 ≤ n := by
      by_contra h
      have h1 : n = 1 := by omega
      subst h1
      exact CFSG.CGT.PushingUp.not_isNaturalSLTwoModule_one hY.2.2.1 hnat
    obtain ⟨φ, -⟩ := hnat
    have hK := benderType_of_sl hn2 φ
    obtain ⟨P⟩ : Nonempty (Sylow 2 (↥Y ⧸ CFSG.pCore 2 ↥Y)) := inferInstance
    have h1 := (sylow_card_comm hK P).1
    have h2 : 2 ∣ Nat.card (P : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
      rw [h1]
      exact dvd_pow_self 2 (by omega)
    exact h2.trans (Subgroup.card_subgroup_dvd_card _)

theorem kFactBlocksInSylowCentralizerQS_holds :
    KFactBlocksInSylowCentralizerQS := by
  intro G _ _ p N S z hp hp5 _ hchar hS hNp hzN hzS hzp Y hY hq
  by_cases hzY : z ∈ normalizer (Y : Set G)
  · exact block_le_of_normalizes hp hp5 hS hNp hY hzS hzp hzY
  · have hq' := hq.resolve_right hzY
    exact block_le_of_cycled hp hS hchar hY hzN hzp hzY hq'
      (two_dvd_card_top_of_quasisimple hY hq')

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
