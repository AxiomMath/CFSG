module

public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.Foundations.Basic
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Holt.General

open MulAction

section Component

variable {G : Type*} [Group G] [Finite G]

theorem le_or_commutator_eq_bot_of_isComponent_of_normal {Y W C M : Subgroup G} (hWY : W ≤ Y)
    (hW : (W.subgroupOf Y).Normal) (hCW : C ≤ W) (hC : CFSG.IsComponent (C.subgroupOf W))
    (hMY : M ≤ Y) (hM : (M.subgroupOf Y).Normal) : C ≤ M ∨ ⁅C, M⁆ = ⊥ := by
  have hWc : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W := fun y hy w hw =>
    Subgroup.mem_subgroupOf.mp
      (hW.conj_mem ⟨w, hWY hw⟩ (Subgroup.mem_subgroupOf.mpr hw) ⟨y, hy⟩)
  have hMc : ∀ y ∈ Y, ∀ m ∈ M, y * m * y⁻¹ ∈ M := fun y hy m hm =>
    Subgroup.mem_subgroupOf.mp
      (hM.conj_mem ⟨m, hMY hm⟩ (Subgroup.mem_subgroupOf.mpr hm) ⟨y, hy⟩)
  have hMn : (M.subgroupOf W).Normal := ⟨fun m hm w => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact hMc w (hWY w.2) m hm⟩
  rcases CFSG.LocalCores.component_normal_subgroup hC hMn with h | h
  · left
    intro c hc
    have hc' : (⟨c, hCW hc⟩ : W) ∈ C.subgroupOf W := Subgroup.mem_subgroupOf.mpr hc
    exact Subgroup.mem_subgroupOf.mp (h hc')
  · right
    have := hC.1.1
    have hP : Group.IsPerfect ((C.subgroupOf W).map W.subtype) := Group.IsPerfect.map W.subtype
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCW] at hP
    apply CFSG.LocalCores.perfect_double_commutator hP
    have h1 : ⁅C, M⁆ ≤ M ⊓ W := by
      rw [Subgroup.commutator_le]
      intro c hc m hm
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.mpr ⟨mul_mem (hMc c (hWY (hCW hc)) m hm) (inv_mem hm), ?_⟩
      have e : c * m * c⁻¹ * m⁻¹ = c * (m * c⁻¹ * m⁻¹) := by group
      rw [e]
      exact mul_mem (hCW hc) (hWc m (hMY hm) c⁻¹ (inv_mem (hCW hc)))
    have h2 : ⁅M ⊓ W, C⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hxM : (⟨x, hx.2⟩ : W) ∈ M.subgroupOf W := Subgroup.mem_subgroupOf.mpr hx.1
      have hc' : (⟨c, hCW hc⟩ : W) ∈ C.subgroupOf W := Subgroup.mem_subgroupOf.mpr hc
      have h3 := Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hc') _ hxM
      exact (congrArg Subtype.val h3).symm
    exact le_bot_iff.mp (h2 ▸ Subgroup.commutator_mono h1 le_rfl)

end Component

section Bender

open CFSG.Open

theorem exists_fusionBenderBorel_two_pow_of_fusionIsBenderGroup {X : Type*} [Group X]
    [Finite X] (h : fusionIsBenderGroup X) : ∃ f k : ℕ, 2 ≤ f ∧ fusionBenderBorel X (2 ^ f) k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have := Finite.of_equiv X e.toEquiv
    exact ⟨f, 1, hf, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
  · have := Finite.of_equiv X e.toEquiv
    exact ⟨f, 3, hf, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
  · have := Finite.of_equiv X e.toEquiv
    exact ⟨2 * a + 1, 2, by omega, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩

theorem twoRankAtLeastTwo_of_fusionBenderBorel_two_pow {X : Type*} [Group X] [Finite X]
    {f k : ℕ} (hf : 2 ≤ f) (hB : fusionBenderBorel X (2 ^ f) k) :
    CFSG.BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨-, -, hsq, hcard, -⟩ := hB S
  set Z := Subgroup.center (S : Subgroup X)
  have hdvd : 2 ^ 2 ∣ Nat.card Z := hcard ▸ pow_dvd_pow 2 hf
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Z) 2 hdvd
  refine ⟨(K.map Z.subtype).map (S : Subgroup X).subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (S : Subgroup X).subtype_injective,
      Subgroup.card_map_of_injective Z.subtype_injective, hK]
    norm_num
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    simpa using congrArg Subtype.val (hsq _ w.2)

theorem false_of_fusionIsBenderGroup_of_le {T : Type} [Group T] [Finite T]
    (hB : fusionIsBenderGroup T) {M : Subgroup T} (hM : CFSG.IsStronglyEmbedded M)
    (P : Sylow 2 T) (hPM : (P : Subgroup T) ≤ M) {Y : Subgroup T} (hYM : Y ≤ M)
    (hY : ¬ Group.IsSolvable Y) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, k, hf, hBB⟩ := exists_fusionBenderBorel_two_pow_of_fusionIsBenderGroup hB
  set N := Subgroup.normalizer ((P : Subgroup T) : Set T)
  have h2T : 2 ∣ Nat.card T :=
    (even_iff_two_dvd.mp hM.2.1).trans (Subgroup.card_subgroup_dvd_card M)
  have hNM : N ≤ M := by
    intro g hg
    by_contra hgM
    have hPle : (P : Subgroup T) ≤ M ⊓ CFSG.conjugate M g := by
      intro p hp
      refine ⟨hPM hp, Subgroup.mem_map.mpr
        ⟨g * p * g⁻¹, hPM ((Subgroup.mem_normalizer_iff.mp hg p).mp hp), ?_⟩⟩
      simp [mul_assoc]
    exact (Nat.not_even_iff_odd.mpr (hM.2.2 g hgM)) (even_iff_two_dvd.mpr
      ((P.dvd_card_of_dvd_card h2T).trans (Subgroup.card_dvd_of_le hPle)))
  have hcoat := CFSG.ShultStronglyClosedTI.rank_two_strongEmbedding_isCoatom
    (twoRankAtLeastTwo_of_fusionBenderBorel_two_pow hf hBB) N (hBB P).1
  have hMN : M = N := (hcoat.le_iff.mp hNM).resolve_left hM.1
  exact CFSG.QuasithinUnique.Lin2.false_of_benderBorel hBB (P.ne_bot_of_dvd_card h2T)
    P.isPGroup' (hYM.trans hMN.le) hY

end Bender

end CFSG.Holt.General
