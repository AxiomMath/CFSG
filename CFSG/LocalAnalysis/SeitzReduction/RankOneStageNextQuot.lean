module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneStage
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

section ElemAb

variable {G : Type*} [Group G]

theorem isElementaryAbelian_two_of_forall {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1) :
    IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

theorem normalizer_le_centralizer_of_card_eq_two [Finite G] {R : Subgroup G}
    (hR : Nat.card R = 2) : normalizer (R : Set G) ≤ centralizer (R : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1, one_mul, mul_one]
  · have hord : orderOf r = 2 := by
      have h1 := Subgroup.orderOf_dvd_natCard R hr
      rw [hR] at h1
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h2 | h2
      · exact absurd (orderOf_eq_one_iff.1 h2) hr1
      · exact h2
    have hRr : R = zpowers r :=
      (eq_of_le_of_card_ge (zpowers_le.2 hr) (by rw [hR, Nat.card_zpowers, hord])).symm
    have hrr : r * r = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
    have h1 := GMS28.conj_eq_of_mem_normalizer_zpowers hrr hr1 (hRr ▸ hg)
    calc r * g = g * r * g⁻¹ * g := by rw [h1]
      _ = g * r := by group

end ElemAb

section Quot

variable {D : Type*} [Group D] {U K L : Subgroup D}

abbrev stageMk (U : Subgroup D) : ↥(normalizer (U : Set D)) →* StageQuot U :=
  QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set D)))

theorem stageImg_eq_map (U K : Subgroup D) :
    stageImg U K = (K.subgroupOf (normalizer (U : Set D))).map (stageMk U) := rfl

theorem stageMk_surjective (U : Subgroup D) : Function.Surjective (stageMk U) :=
  QuotientGroup.mk'_surjective _

theorem ker_stageMk (U : Subgroup D) :
    (stageMk U).ker = U.subgroupOf (normalizer (U : Set D)) :=
  QuotientGroup.ker_mk' _

theorem stageMk_eq_one_iff (x : normalizer (U : Set D)) : stageMk U x = 1 ↔ (x : D) ∈ U := by
  rw [← MonoidHom.mem_ker, ker_stageMk, mem_subgroupOf]

theorem stageMk_eq_iff (x y : normalizer (U : Set D)) :
    stageMk U x = stageMk U y ↔ (x : D)⁻¹ * y ∈ U := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, stageMk_eq_one_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  constructor
  · intro h
    have := (mem_normalizer_iff.mp (inv_mem y.2) _).mp h
    simpa [mul_assoc] using inv_mem this
  · intro h
    have := (mem_normalizer_iff.mp y.2 _).mp (inv_mem h)
    simpa [mul_assoc] using this

theorem stageMk_mem_stageImg (x : normalizer (U : Set D)) (hx : (x : D) ∈ K) :
    stageMk U x ∈ stageImg U K :=
  mem_map_of_mem _ (mem_subgroupOf.mpr hx)

theorem exists_of_mem_stageImg {y : StageQuot U} (hy : y ∈ stageImg U K) :
    ∃ x : normalizer (U : Set D), (x : D) ∈ K ∧ stageMk U x = y := by
  obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
  exact ⟨x, mem_subgroupOf.mp hx, rfl⟩

theorem comap_stageImg (hUK : U ≤ K) :
    (stageImg U K).comap (stageMk U) = K.subgroupOf (normalizer (U : Set D)) := by
  rw [stageImg_eq_map, comap_map_eq, ker_stageMk]
  exact sup_eq_left.mpr fun x hx => hUK hx

theorem stageMk_mem_stageImg_iff (hUK : U ≤ K) (x : normalizer (U : Set D)) :
    stageMk U x ∈ stageImg U K ↔ (x : D) ∈ K := by
  rw [← mem_comap, comap_stageImg hUK, mem_subgroupOf]

theorem stageImg_mono (hKL : K ≤ L) : stageImg U K ≤ stageImg U L :=
  map_mono fun _ hx => hKL hx

theorem stageImg_sup (hK : K ≤ normalizer (U : Set D)) (hL : L ≤ normalizer (U : Set D)) :
    stageImg U (K ⊔ L) = stageImg U K ⊔ stageImg U L := by
  rw [stageImg_eq_map, subgroupOf_sup hK hL, Subgroup.map_sup]
  rfl

theorem stageImg_self : stageImg U U = ⊥ := by
  rw [stageImg_eq_map, Subgroup.map_eq_bot_iff, ker_stageMk]

theorem stageImg_sup_left (hK : K ≤ normalizer (U : Set D)) :
    stageImg U (U ⊔ K) = stageImg U K := by
  rw [stageImg_sup le_normalizer hK, stageImg_self, bot_sup_eq]

theorem stageImg_inf (hUK : U ≤ K) (hUL : U ≤ L) :
    stageImg U (K ⊓ L) = stageImg U K ⊓ stageImg U L := by
  refine le_antisymm (le_inf (stageImg_mono inf_le_left) (stageImg_mono inf_le_right))
    fun y hy => ?_
  obtain ⟨x, rfl⟩ := stageMk_surjective U y
  obtain ⟨hK, hL⟩ := mem_inf.mp hy
  exact stageMk_mem_stageImg x (mem_inf.mpr ⟨(stageMk_mem_stageImg_iff hUK x).mp hK,
    (stageMk_mem_stageImg_iff hUL x).mp hL⟩)

theorem card_stageImg (hK : K ≤ normalizer (U : Set D)) :
    Nat.card (stageImg U K) = U.relIndex K := by
  rw [← relIndex_bot_left, stageImg_eq_map, ← relIndex_comap, MonoidHom.comap_bot, ker_stageMk,
    relIndex_subgroupOf hK]

theorem card_stageImg_mul (hUK : U ≤ K) (hK : K ≤ normalizer (U : Set D)) :
    Nat.card (stageImg U K) * Nat.card U = Nat.card K := by
  rw [card_stageImg hK, ← relIndex_mul_card U K, inf_eq_left.mpr hUK]

theorem relIndex_stageImg (hUK : U ≤ K) (hL : L ≤ normalizer (U : Set D)) :
    (stageImg U K).relIndex (stageImg U L) = K.relIndex L := by
  rw [stageImg_eq_map U L, ← relIndex_comap, comap_stageImg hUK, relIndex_subgroupOf hL]

theorem isSylowOf_stageImg [Finite D] {p : ℕ} [Fact p.Prime] (hUK : U ≤ K)
    (hL : L ≤ normalizer (U : Set D)) (h : IsSylowOf p K L) :
    IsSylowOf p (stageImg U K) (stageImg U L) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hKL, hK, hdvd⟩ := h
  refine ⟨stageImg_mono hKL, ?_, by rwa [relIndex_stageImg hUK hL]⟩
  rw [stageImg_eq_map]
  exact (hK.comap_subtype (K := normalizer (U : Set D))).map _

theorem normalizer_stageImg (hUK : U ≤ K) (hK : K ≤ normalizer (U : Set D)) :
    normalizer ((stageImg U K : Subgroup (StageQuot U)) : Set (StageQuot U)) =
      stageImg U (normalizer (K : Set D)) := by
  rw [← map_comap_eq_self_of_surjective (stageMk_surjective U)
      (normalizer ((stageImg U K : Subgroup (StageQuot U)) : Set (StageQuot U))),
    comap_normalizer_eq_of_surjective _ (stageMk_surjective U), comap_stageImg hUK,
    ← subgroupOf_normalizer_eq hK]
  rfl

theorem stageMk_mem_normalizer_iff (hUK : U ≤ K) (hK : K ≤ normalizer (U : Set D))
    (g : normalizer (U : Set D)) :
    stageMk U g ∈ normalizer ((stageImg U K : Subgroup (StageQuot U)) : Set (StageQuot U)) ↔
      (g : D) ∈ normalizer (K : Set D) := by
  rw [normalizer_stageImg hUK hK, stageMk_mem_stageImg_iff (hUK.trans le_normalizer)]

theorem stageMk_mem_centralizer_iff (hK : K ≤ normalizer (U : Set D))
    (g : normalizer (U : Set D)) :
    stageMk U g ∈ centralizer ((stageImg U K : Subgroup (StageQuot U)) : Set (StageQuot U)) ↔
      ∀ x ∈ K, (g : D) * x * (g : D)⁻¹ * x⁻¹ ∈ U := by
  rw [mem_centralizer_iff]
  constructor
  · intro h x hx
    have h1 := h _ (stageMk_mem_stageImg ⟨x, hK hx⟩ hx)
    rw [← map_mul, ← map_mul, stageMk_eq_iff] at h1
    have h2 : ((⟨x, hK hx⟩ * g : normalizer (U : Set D)) : D)⁻¹ *
        ((g * ⟨x, hK hx⟩ : normalizer (U : Set D)) : D) ∈ U := h1
    simp only [Subgroup.coe_mul, mul_inv_rev] at h2
    have h3 := (mem_normalizer_iff.mp (mul_mem (hK hx) g.2) _).mp h2
    have e : x * (g : D) * ((g : D)⁻¹ * x⁻¹ * ((g : D) * x)) * (x * (g : D))⁻¹ =
        (g : D) * x * (g : D)⁻¹ * x⁻¹ := by group
    rw [← e]
    simpa only [mul_assoc] using h3
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_stageImg hy
    rw [← map_mul, ← map_mul, stageMk_eq_iff]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    have h1 := (mem_normalizer_iff.mp (inv_mem (mul_mem (x : normalizer (U : Set D)).2 g.2)) _).mp
      (h x hx)
    have e : ((x : D) * (g : D))⁻¹ * ((g : D) * x * (g : D)⁻¹ * (x : D)⁻¹) *
        ((x : D) * (g : D))⁻¹⁻¹ = (g : D)⁻¹ * (x : D)⁻¹ * ((g : D) * x) := by group
    rw [e] at h1
    simpa only [mul_assoc] using h1

theorem isElementaryAbelian_stageImg (hK : K ≤ normalizer (U : Set D))
    (hsq : ∀ x ∈ K, x * x ∈ U) (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ U) :
    IsElementaryAbelian 2 (stageImg U K) := by
  refine isElementaryAbelian_two_of_forall (fun a ha b hb => ?_) fun a ha => ?_
  · obtain ⟨y, hy, rfl⟩ := exists_of_mem_stageImg hb
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_stageImg ha
    have h1 := (stageMk_mem_centralizer_iff hK x).mpr (fun z hz => hcomm x hx z hz)
      (stageMk U y) (stageMk_mem_stageImg y hy)
    exact h1.symm
  · obtain ⟨x, hx, rfl⟩ := exists_of_mem_stageImg ha
    rw [← map_mul, stageMk_eq_one_iff]
    exact hsq x hx

end Quot

end CFSG.SeitzReduction.RankOne
