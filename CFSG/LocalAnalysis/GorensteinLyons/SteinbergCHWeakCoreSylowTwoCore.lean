module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHWeakCoreRankThreeNormalizers
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open scoped Pointwise

namespace SteinbergCH

open CFSG.LargeEvenClassification.Helpers (weakTwoGeneratedPCore WeakCoreLocal)

theorem glaWeakCore_eq_weakTwoGeneratedPCore {G : Type*} [Group G] [Finite G] (p : ℕ)
    (P : Subgroup G) : GLAWeakCore p P = weakTwoGeneratedPCore p P := by
  refine le_antisymm (sSup_le ?_) (iSup_le fun Q => le_sSup ⟨Q.1, Q.2.1, Q.2.2.1, Q.2.2.2, rfl⟩)
  rintro _ ⟨Q, hQP, h2, h3, rfl⟩
  exact CFSG.LargeEvenClassification.Helpers.eligible_normalizer_le_weak_core P Q ⟨hQP, h2, h3⟩

theorem glaWeakCoreLocal_iff {G : Type*} [Group G] [Finite G] (p : ℕ) :
    GLAWeakCoreLocal G p ↔ WeakCoreLocal p G := by
  simp only [GLAWeakCoreLocal, WeakCoreLocal, glaWeakCore_eq_weakTwoGeneratedPCore]

theorem inSubgroup_pCore_two_eq_pCoreOf {G : Type*} [Group G] (H : Subgroup G) :
    CFSG.inSubgroup (CFSG.pCore 2) H = pCoreOf 2 H := by
  rw [CFSG.inSubgroup]
  rfl

theorem normalizer_eq_mul_normalizer_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (P : Sylow p G) {W : Subgroup G} (hPW : (P : Subgroup G) ≤ W)
    (hNP : normalizer (P : Set G) ≤ normalizer (W : Set G)) :
    ((normalizer (W : Set G) : Subgroup G) : Set G) =
      (W : Set G) * (normalizer (P : Set G) : Set G) := by
  ext g
  constructor
  · intro hg
    have hgW : W.map (MulAut.conj g).toMonoidHom = W := mem_normalizer_iff_map_conj_eq.mp hg
    have hQW : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ W := by
      have h1 := map_mono (f := (MulAut.conj g).toMonoidHom) hPW
      rwa [hgW] at h1
    obtain ⟨w, hw⟩ := CFSG.LargeEvenClassification.Helpers.sylow_contains_conjugate_inside hp P W
      _ hPW hQW (P.isPGroup'.map _)
    have hcomp : ((P : Subgroup G).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (w : G)).toMonoidHom =
        (P : Subgroup G).map (MulAut.conj ((w : G) * g)).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [mul_assoc]
    rw [hcomp] at hw
    have hmap : (P : Subgroup G).map (MulAut.conj ((w : G) * g)).toMonoidHom = P := by
      refine eq_of_le_of_card_ge hw ?_
      rw [card_map_of_injective (MulAut.conj ((w : G) * g)).injective]
    exact Set.mem_mul.mpr ⟨(w : G)⁻¹, inv_mem w.2, (w : G) * g,
      mem_normalizer_iff_map_conj_eq.mpr hmap, by group⟩
  · intro hg
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg
    exact mul_mem (le_normalizer ha) (hNP hb)

theorem weakCore_sylow_facts {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (P : Sylow p G) (hP3 : 3 ≤ CFSG.Open.pRank p (P : Subgroup G)) :
    (P : Subgroup G) ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∃ P' : Sylow p (GLAWeakCore p (P : Subgroup G)),
      (P' : Subgroup (GLAWeakCore p (P : Subgroup G))) =
        (P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) ∧
    CFSG.Open.pRank p (GLAWeakCore p (P : Subgroup G)) = CFSG.Open.pRank p (⊤ : Subgroup G) ∧
    CFSG.Open.pRank p (P : Subgroup G) = CFSG.Open.pRank p (⊤ : Subgroup G) ∧
    GLAWeakCore p ((P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) = ⊤ ∧
    normalizer (P : Set G) ≤ normalizer (GLAWeakCore p (P : Subgroup G) : Set G) ∧
    ((normalizer (GLAWeakCore p (P : Subgroup G) : Set G) : Subgroup G) : Set G) =
      (GLAWeakCore p (P : Subgroup G) : Set G) * (normalizer (P : Set G) : Set G) ∧
    (GLAWeakCoreLocal (GLAWeakCore p (P : Subgroup G)) p ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) := by
  have := Fact.mk hp
  have hp1 := hp.one_lt
  have hWeq := glaWeakCore_eq_weakTwoGeneratedPCore p (P : Subgroup G)
  have hPW : (P : Subgroup G) ≤ GLAWeakCore p (P : Subgroup G) :=
    le_normalizer.trans (DeltaWeakCore.normalizer_le_weakCore le_rfl (by omega)
      (hP3.trans (CFSG.SectionRank.pRank_mono hp1 le_sup_left)))
  have hrankP := (CFSG.SectionRank.pRank_sylow P).1
  have hNP : normalizer (P : Set G) ≤ normalizer (GLAWeakCore p (P : Subgroup G) : Set G) := by
    rw [hWeq]
    exact CFSG.LargeEvenClassification.Helpers.normalizer_parent_le_normalizer_weak_core hp1 _
  refine ⟨hPW, ⟨P.subtype hPW, Sylow.coe_subtype P hPW⟩,
    le_antisymm (CFSG.SectionRank.pRank_mono hp1 le_top)
      (hrankP ▸ CFSG.SectionRank.pRank_mono hp1 hPW), hrankP, ?_, hNP,
    normalizer_eq_mul_normalizer_sylow hp P hPW hNP, ?_⟩
  · rw [hWeq, glaWeakCore_eq_weakTwoGeneratedPCore]
    exact CFSG.LargeEvenClassification.Helpers.weak_core_internal_eq_top hp1 _ (hWeq ▸ hPW)
  · rw [inSubgroup_pCore_two_eq_pCoreOf, glaWeakCoreLocal_iff, hWeq]
    exact CFSG.LargeEvenClassification.Helpers.weak_core_internal_locality_iff hp P hP3

theorem weak_core_sylow_and_two_core {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2) {p : ℕ}
    (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) {B D₀ S₀ : Subgroup G}
    (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀ : IsElemAbelian p D₀)
    (hD₀card : Nat.card D₀ = p ^ 2) (hW : IsDeltaSeedWitness p B D₀ S₀) {S : Subgroup G}
    (hS : Maximal (· ∈ deltaSeededFamily p B S₀) S) {A H Q R : Subgroup G}
    (hA : A = B ⊓ centralizer (S : Set G)) (hH : H = normalizer (S : Set G))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) H) (hR : R = Q ⊓ centralizer (S : Set G))
    {F : Subgroup G → Subgroup G} (hF : ∀ D : Subgroup G, F D = Q ⊓ centralizer (D : Set G))
    {L : Set (Subgroup G)} (hL : L = {D | D ≤ A ∧ Nat.card D = p ∧ S < F D})
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalsContaining (H : Set G))
    (P : Sylow p G) (hBP : B ≤ (P : Subgroup G)) :
    (P : Subgroup G) ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∃ P' : Sylow p (GLAWeakCore p (P : Subgroup G)),
      (P' : Subgroup (GLAWeakCore p (P : Subgroup G))) =
        (P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) ∧
    CFSG.Open.pRank p (GLAWeakCore p (P : Subgroup G)) = CFSG.Open.pRank p (⊤ : Subgroup G) ∧
    CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧ 4 ≤ CFSG.Open.pRank p B ∧
    GLAWeakCore p ((P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) = ⊤ ∧
    normalizer (P : Set G) ≤ normalizer (GLAWeakCore p (P : Subgroup G) : Set G) ∧
    ((normalizer (GLAWeakCore p (P : Subgroup G) : Set G) : Subgroup G) : Set G) =
      (GLAWeakCore p (P : Subgroup G) : Set G) * (normalizer (P : Set G) : Set G) ∧
    (GLAWeakCoreLocal G p ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (IsCharacteristicP 2 (GLAWeakCore p (P : Subgroup G)) ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (GLAWeakCoreLocal (GLAWeakCore p (P : Subgroup G)) p ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (GLAWeakCoreLocal G p → GLAWeakCore p (P : Subgroup G) < ⊤) ∧
    (¬ GLAWeakCoreLocal G p →
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) = ⊥ ∧
      ¬ IsCharacteristicP 2 (GLAWeakCore p (P : Subgroup G)) ∧
      ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E → ∀ U : Subgroup G, U ≠ ⊥ →
        IsPGroup 2 U → E ≤ normalizer (U : Set G) →
        IsCharacteristicP 2
          (GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G) : Subgroup G)) := by
  classical
  have hpp : p.Prime := hp.1
  have hp1 : 1 < p := hpp.one_lt
  obtain ⟨hBr, h4, hBW, -, -, -, -, -, -, -, -, hYfacts, -, -, -, hlast⟩ :=
    delta_weak_core_contains_local_two_cores hnab hchar hp hfail hB hD₀B hD₀ hD₀card hW hS hA hH
      hQ hR hF hL hM P hBP
  have hlocal := (actual_weak_core_rank_three_normalizer_intersections hnab hchar hp hfail hB hD₀B
    hD₀ hD₀card hW hS hA hH hQ hR hF hL hM P hBP).1
  have hB4 : 4 ≤ CFSG.Open.pRank p B := hBr ▸ h4
  have hP3 : 3 ≤ CFSG.Open.pRank p (P : Subgroup G) :=
    (by omega : 3 ≤ CFSG.Open.pRank p B).trans (CFSG.SectionRank.pRank_mono hp1 hBP)
  obtain ⟨hPW, hsyl, hrankW, hrankP, htop, hNP, hfrat, hloc⟩ := weakCore_sylow_facts hpp P hP3
  set W := GLAWeakCore p (P : Subgroup G) with hWdef
  have hBne : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = 1 := by rw [h]; exact card_bot
    rw [hB.2.1] at h1
    have h2 := Nat.one_lt_pow (by omega : GLATwoLocalRank p G ≠ 0) hp1
    omega
  have hpos : GLAWeakCoreLocal G p →
      CFSG.inSubgroup (CFSG.pCore 2) W ≠ ⊥ ∧ IsCharacteristicP 2 W ∧ W < ⊤ := by
    intro hwcl
    obtain ⟨Y, hY, hWY⟩ := hwcl.2 P
    obtain ⟨-, hYne, hYle, hYchar, -, -⟩ := hYfacts Y hY (hBW.trans hWY)
    rw [inf_eq_left.mpr hWY] at hYle hYchar
    exact ⟨fun h => hYne (le_bot_iff.mp (h ▸ hYle)), hYchar, lt_top_iff_ne_top.mpr fun h =>
      CFSG.LargeEvenClassification.Helpers.twoLocal_ne_top G hnab Y hY
        (top_le_iff.mp (h ▸ hWY))⟩
  have hneg : CFSG.inSubgroup (CFSG.pCore 2) W ≠ ⊥ → GLAWeakCoreLocal G p := fun hO =>
    by_contra fun h => hO (hlast h)
  have hcharO : IsCharacteristicP 2 W → CFSG.inSubgroup (CFSG.pCore 2) W ≠ ⊥ := by
    intro hC hO
    have hO' : CFSG.pCore 2 W = ⊥ :=
      (map_eq_bot_iff_of_injective _ W.subtype_injective).mp hO
    have hall : ∀ x : W, x = 1 := by
      intro x
      have hx : x ∈ centralizer (CFSG.pCore 2 W : Set W) := by
        rw [mem_centralizer_iff]
        intro y hy
        rw [hO', SetLike.mem_coe, mem_bot] at hy
        rw [hy, one_mul, mul_one]
      have h1 := hC hx
      rwa [hO', mem_bot] at h1
    obtain ⟨b, hbB, hb1⟩ := (bot_or_exists_ne_one B).resolve_left hBne
    exact hb1 (congrArg Subtype.val (hall ⟨b, hBW hbB⟩))
  have hiff : GLAWeakCoreLocal G p ↔ CFSG.inSubgroup (CFSG.pCore 2) W ≠ ⊥ :=
    ⟨fun h => (hpos h).1, hneg⟩
  refine ⟨hPW, hsyl, hrankW, hrankP ▸ CFSG.SectionRank.pRank_mono hp1 hBP, hB4, htop, hNP, hfrat,
    hiff, ⟨hcharO, fun hO => (hpos (hneg hO)).2.1⟩, hloc, fun h => (hpos h).2.2, fun h => ?_⟩
  refine ⟨hlast h, fun hC => h (hneg (hcharO hC)), ?_⟩
  intro E hEB hE3 U hU1 hU2 hEU
  exact (hlocal E hEB hE3 U hU1 hU2 hEU).2.2.2.2.1

end SteinbergCH

open SteinbergCH

theorem actual_weak_core_sylow_and_two_core_reduction {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hchar : IsCharacteristicPType G 2)
    {p : ℕ} (hp : p ∈ GLABeta 4 G) (hfail : ¬ GLADeltaZero G p) {B D₀ S₀ : Subgroup G}
    (hB : GLAIsBmax p B) (hD₀B : D₀ ≤ B) (hD₀ : IsElemAbelian p D₀)
    (hD₀card : Nat.card D₀ = p ^ 2) (hW : IsDeltaSeedWitness p B D₀ S₀) {S : Subgroup G}
    (hS : Maximal (· ∈ deltaSeededFamily p B S₀) S) {A H Q R : Subgroup G}
    (hA : A = B ⊓ centralizer (S : Set G)) (hH : H = normalizer (S : Set G))
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) H) (hR : R = Q ⊓ centralizer (S : Set G))
    {F : Subgroup G → Subgroup G} (hF : ∀ D : Subgroup G, F D = Q ⊓ centralizer (D : Set G))
    {L : Set (Subgroup G)} (hL : L = {D | D ≤ A ∧ Nat.card D = p ∧ S < F D})
    {M : Subgroup G} (hM : M ∈ maximalTwoLocalsContaining (H : Set G))
    (P : Sylow p G) (hBP : B ≤ (P : Subgroup G)) :
    (P : Subgroup G) ≤ GLAWeakCore p (P : Subgroup G) ∧
    (∃ P' : Sylow p (GLAWeakCore p (P : Subgroup G)),
      (P' : Subgroup (GLAWeakCore p (P : Subgroup G))) =
        (P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) ∧
    CFSG.Open.pRank p (GLAWeakCore p (P : Subgroup G)) = CFSG.Open.pRank p (⊤ : Subgroup G) ∧
    CFSG.Open.pRank p B ≤ CFSG.Open.pRank p (⊤ : Subgroup G) ∧ 4 ≤ CFSG.Open.pRank p B ∧
    GLAWeakCore p ((P : Subgroup G).subgroupOf (GLAWeakCore p (P : Subgroup G))) = ⊤ ∧
    normalizer (P : Set G) ≤ normalizer (GLAWeakCore p (P : Subgroup G) : Set G) ∧
    ((normalizer (GLAWeakCore p (P : Subgroup G) : Set G) : Subgroup G) : Set G) =
      (GLAWeakCore p (P : Subgroup G) : Set G) * (normalizer (P : Set G) : Set G) ∧
    (GLAWeakCoreLocal G p ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (IsCharacteristicP 2 (GLAWeakCore p (P : Subgroup G)) ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (GLAWeakCoreLocal (GLAWeakCore p (P : Subgroup G)) p ↔
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) ≠ ⊥) ∧
    (GLAWeakCoreLocal G p → GLAWeakCore p (P : Subgroup G) < ⊤) ∧
    (¬ GLAWeakCoreLocal G p →
      CFSG.inSubgroup (CFSG.pCore 2) (GLAWeakCore p (P : Subgroup G)) = ⊥ ∧
      ¬ IsCharacteristicP 2 (GLAWeakCore p (P : Subgroup G)) ∧
      ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E → ∀ U : Subgroup G, U ≠ ⊥ →
        IsPGroup 2 U → E ≤ normalizer (U : Set G) →
        IsCharacteristicP 2
          (GLAWeakCore p (P : Subgroup G) ⊓ normalizer (U : Set G) : Subgroup G)) ∧
    (CFSG.IsKProper G → GLAWeakCore p (P : Subgroup G) < ⊤ →
      CFSG.IsKGroup (GLAWeakCore p (P : Subgroup G))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    weak_core_sylow_and_two_core hnab hchar hp hfail hB hD₀B hD₀ hD₀card hW hS hA hH hQ hR hF hL
      hM P hBP
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun hK hlt => hK _ hlt.ne⟩

end CFSG.LocalAnalysis.GorensteinLyons
