module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRBridge
import CFSG.LocalAnalysis.AGLEmbedding.Sp62Core
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem map_gnV_eq_mModule (hSM : S ≤ M) :
    (gnV (S.subgroupOf M)).map M.subtype = mModule M S := by
  have hΩ : (omegaOneCenterOf (S.subgroupOf M)).map M.subtype = omegaOneCenterOf S := by
    rw [← CFSG.Quasithin.C1GN.omegaOneCenterOf_map_subtype M (S.subgroupOf M),
      Subgroup.map_subgroupOf_eq_of_le hSM]
  apply le_antisymm
  ·
    have hle : gnV (S.subgroupOf M) ≤ (mModule M S).subgroupOf M := by
      have hn : ((mModule M S).subgroupOf M).Normal := ⟨fun x hx g => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        have := (Subgroup.mem_normalizer_iff.mp (normalizer_mModule M S g.2) x).mp hx
        simpa using this⟩
      refine Subgroup.normalClosure_le_normal ?_
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have : (t : G) ∈ omegaOneCenterOf S := hΩ ▸ ⟨t, ht, rfl⟩
      exact omegaOneCenterOf_le_mModule M S this
    calc (gnV (S.subgroupOf M)).map M.subtype ≤ ((mModule M S).subgroupOf M).map M.subtype :=
          Subgroup.map_mono hle
      _ = mModule M S ⊓ M := Subgroup.subgroupOf_map_subtype _ _
      _ ≤ mModule M S := inf_le_left
  · refine mModule_le ?_ ?_
    · rw [← hΩ]
      exact Subgroup.map_mono (Subgroup.subset_normalClosure)
    · intro m hm
      have hN : (gnV (S.subgroupOf M)).Normal := Subgroup.normalClosure_normal
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨m, hm⟩ * v * ⟨m, hm⟩⁻¹, hN.conj_mem v hv ⟨m, hm⟩, by simp⟩
      · rintro ⟨v, hv, hvx⟩
        refine ⟨⟨m, hm⟩⁻¹ * v * ⟨m, hm⟩, ?_, ?_⟩
        · have := hN.conj_mem v hv ⟨m, hm⟩⁻¹
          simpa using this
        · have hvx' : (v : G) = m * x * m⁻¹ := hvx
          show m⁻¹ * (v : G) * m = x
          rw [hvx']
          group

theorem not_le_gnC_of_weakSBlock (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) :
    ¬ L.subgroupOf M ≤ gnC (S.subgroupOf M) := by
  intro h
  apply not_le_centralizer_mModule hA hL
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← map_gnV_eq_mModule hA.twoRadical.1] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hlC : (⟨l, hL.le hl⟩ : ↥M) ∈ gnC (S.subgroupOf M) := h (Subgroup.mem_subgroupOf.mpr hl)
  have := Subgroup.mem_centralizer_iff.mp hlC w hw
  exact congrArg Subtype.val this

theorem fiveStar_isComponent (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) :
    IsComponentOf (gnImg (S.subgroupOf M) (L.subgroupOf M)) ⊤ :=
  blockStar_isComponent le_rfl hA.twoRadical.1 (CFSG.Quasithin.c2_1_pCore_le hA.twoRadical) hL
    hL.le (not_le_gnC_of_weakSBlock hA hL)

omit [Finite G] in
theorem conj_mem_commutator_left {X : Type*} [Group X] {H₁ H₂ : Subgroup X} {a : X} (ha : a ∈ H₁)
    {x : X} (hx : x ∈ ⁅H₁, H₂⁆) : a * x * a⁻¹ ∈ ⁅H₁, H₂⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, hh, k, hk, rfl⟩ := hg
    have e : a * ⁅h, k⁆ * a⁻¹ = ⁅a * h, k⁆ * ⁅a, k⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨a * h, H₁.mul_mem ha hh, k, hk, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨a, ha, k, hk, rfl⟩))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hx

omit [Finite G] in
theorem commutator_barM_thompsonJ_eq (hL : IsWeakSBlock M S L)
    (hSM : S ≤ M) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hJ : ¬ ⁅L, thompsonJ S⁆ ≤ pCoreOf 2 M) :
    ⁅barM M L, barM M (thompsonJ S)⁆ = barM M L := by
  set Lb := barM M L with hLb
  set Jb := barM M (thompsonJ S) with hJb
  have hJS : thompsonJ S ≤ S := CFSG.Quasithin.C1GN.thompsonJ_le S
  have hJbN : Jb ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM (hJS.trans hSL)
  have hKle : ⁅Lb, Jb⁆ ≤ Lb := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b * a⁻¹ * b⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp (hJbN hb) a⁻¹).mp
      (Lb.inv_mem ha)
    have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Lb.mul_mem ha hb'
  have hq : Open.IsQuasisimple ↥Lb := hL.component.2.2
  have hKn : (⁅Lb, Jb⁆.subgroupOf Lb).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using conj_mem_commutator_left g.2 hx⟩
  have hdich : ⁅Lb, Jb⁆.subgroupOf Lb ≤ Subgroup.center ↥Lb ∨ ⁅Lb, Jb⁆.subgroupOf Lb = ⊤ := by
    have : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hq.2
    have := hKn
    have hnormal : ((⁅Lb, Jb⁆.subgroupOf Lb).map
        (QuotientGroup.mk' (Subgroup.center ↥Lb))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hnormal.eq_bot_or_eq_top with hbot | htop
    · left
      have hker := (Subgroup.map_eq_bot_iff _).mp hbot
      simpa only [QuotientGroup.ker_mk'] using hker
    · right
      have hsup : ⁅Lb, Jb⁆.subgroupOf Lb ⊔ Subgroup.center ↥Lb = ⊤ := by
        have hcomap := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center ↥Lb))
          (⁅Lb, Jb⁆.subgroupOf Lb)
        rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
        exact hcomap.symm
      have hderived : commutator ↥Lb ≤ ⁅Lb, Jb⁆.subgroupOf Lb :=
        Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
      rw [hq.1] at hderived
      exact top_unique hderived
  rcases hdich with hc | ht
  · exfalso
    apply hJ
    have h1 : ⁅⁅Lb, Jb⁆, Lb⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hxc := hc (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hKle hx⟩ : ↥Lb) ∈ _)
      have := Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩
      exact congrArg Subtype.val this
    have h2 : ⁅⁅Jb, Lb⁆, Lb⁆ = ⊥ := by rw [Subgroup.commutator_comm Jb Lb]; exact h1
    have h3 : ⁅⁅Lb, Lb⁆, Jb⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [CFSG.AGLEmbedding.barM_perfect hL.le hL.perfect] at h3
    have hLJM : ⁅L, thompsonJ S⁆ ≤ M := (Subgroup.commutator_le.mpr fun a ha b hb =>
      M.mul_mem (M.mul_mem (M.mul_mem (hL.le ha) (hSM (hJS hb))) (M.inv_mem (hL.le ha)))
        (M.inv_mem (hSM (hJS hb))))
    refine le_pCoreOf_of_barM_eq_bot hLJM ?_
    have hmap : barM M ⁅L, thompsonJ S⁆ = ⁅Lb, Jb⁆ := by
      have hsub : ⁅L.subgroupOf M, (thompsonJ S).subgroupOf M⁆ = (⁅L, thompsonJ S⁆).subgroupOf M := by
        apply Subgroup.map_injective M.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL.le,
          Subgroup.map_subgroupOf_eq_of_le (hJS.trans hSM), Subgroup.map_subgroupOf_eq_of_le hLJM]
      change ((⁅L, thompsonJ S⁆).subgroupOf M).map _ = ⁅(L.subgroupOf M).map _,
        ((thompsonJ S).subgroupOf M).map _⁆
      rw [← Subgroup.map_commutator, hsub]
    rw [hmap, h3]
  · apply le_antisymm hKle
    intro x hx
    have : (⟨x, hx⟩ : ↥Lb) ∈ ⁅Lb, Jb⁆.subgroupOf Lb := ht ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end CFSG.AGLEmbeddingD2.McLaughlin
