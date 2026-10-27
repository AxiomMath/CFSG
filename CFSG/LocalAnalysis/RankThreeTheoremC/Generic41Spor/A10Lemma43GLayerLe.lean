module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GLayerComp
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a10t1_ll_le_of_fiveElt {X : Type} [Group X] [Finite X] {C K : Subgroup X}
    (hC : CFSG.IsPComponent 5 C)
    (hK : ∀ g ∈ C, (∃ k : ℕ, g ^ 5 ^ k = 1) → g ∈ K) : C ≤ K := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have htop := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent
    5 C hC
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure] at htop
  have hle : Subgroup.closure {x : ↥C | ∃ k : ℕ, orderOf x = 5 ^ k} ≤ K.comap C.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    refine hK x.1 x.2 ⟨k, ?_⟩
    have h1 : x ^ 5 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val h1
  intro g hg
  have hmem : (⟨g, hg⟩ : ↥C) ∈ Subgroup.closure {x : ↥C | ∃ k : ℕ, orderOf x = 5 ^ k} := by
    rw [htop]; exact Subgroup.mem_top _
  exact hle hmem

theorem a10t1_ll_perfect_le {X : Type} [Group X] {C E D : Subgroup X} [E.Normal]
    (hC : ⁅C, C⁆ = C) (hD : ⁅D, D⁆ = ⊥) (hle : C ≤ E ⊔ D) : C ≤ E := by
  let q := QuotientGroup.mk' E
  have hE : E.map q = ⊥ := (Subgroup.map_eq_bot_iff _).2 (by rw [QuotientGroup.ker_mk'])
  have hq : C.map q ≤ D.map q := by
    calc C.map q ≤ (E ⊔ D).map q := Subgroup.map_mono hle
      _ = E.map q ⊔ D.map q := Subgroup.map_sup _ _ _
      _ = D.map q := by rw [hE, bot_sup_eq]
  have h1 : ⁅C.map q, C.map q⁆ = C.map q := by rw [← Subgroup.map_commutator, hC]
  have h2 : ⁅D.map q, D.map q⁆ = ⊥ := by rw [← Subgroup.map_commutator, hD, Subgroup.map_bot]
  have h3 : C.map q = ⊥ := by
    rw [← h1]
    exact eq_bot_iff.2 (h2 ▸ Subgroup.commutator_mono hq hq)
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h3

theorem a10_layer_le {W O N D E₁ E₂ : Subgroup G} (h : A10EData W O N D E₁ E₂)
    (hc₁ : GLAPComponent 5 W E₁) (hc₂ : GLAPComponent 5 W E₂) {C : Subgroup G}
    (hC : GLAPComponent 5 W C) : C = E₁ ∨ C = E₂ := by
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hCW : C ≤ W := hC.1
  have hE₁W : E₁ ≤ W := hc₁.1
  have hE₂W : E₂ ≤ W := hc₂.1
  have hEW : E₁ ⊔ E₂ ≤ W := sup_le hE₁W hE₂W
  have hC' : CFSG.IsPComponent 5 (C.subgroupOf W) :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hC).2
  have hE₁' : CFSG.IsPComponent 5 (E₁.subgroupOf W) :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hc₁).2
  have hE₂' : CFSG.IsPComponent 5 (E₂.subgroupOf W) :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hc₂).2
  haveI hEsn : ((E₁ ⊔ E₂).subgroupOf W).Normal :=
    ⟨fun n hn g => h.base.E_norm g g.2 n hn⟩
  haveI hNsn : (N.subgroupOf W).Normal := ⟨fun n hn g => h.kd.N_norm g g.2 n hn⟩
  haveI hDcyc : IsCyclic ↥D := h.kd.D_cyc
  have hperf : ⁅C.subgroupOf W, C.subgroupOf W⁆ = C.subgroupOf W :=
    Subgroup.isPerfect_iff.1
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hC')
  have hD : ⁅D.subgroupOf W, D.subgroupOf W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hcomm := mul_comm' (⟨(a : G), ha⟩ : ↥D) ⟨(b : G), hb⟩
    exact Subtype.ext (congrArg Subtype.val hcomm).symm
  have hfive : ∀ g ∈ C.subgroupOf W, (∃ k : ℕ, g ^ 5 ^ k = 1) →
      g ∈ ((E₁ ⊔ E₂).subgroupOf W ⊔ N.subgroupOf W) ⊔ D.subgroupOf W := by
    rintro g - ⟨k, hk⟩
    have hk' : (g : G) ^ 5 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmem := h.five g g.2 ⟨k, hk'⟩
    have hsub : g ∈ (((E₁ ⊔ E₂) ⊔ N) ⊔ D).subgroupOf W := by
      rw [Subgroup.mem_subgroupOf, sup_assoc]
      exact hmem
    rwa [Subgroup.subgroupOf_sup (sup_le hEW h.kd.N_le) h.kd.D_le,
      Subgroup.subgroupOf_sup hEW h.kd.N_le] at hsub
  have hCs : C.subgroupOf W ≤ (E₁ ⊔ E₂).subgroupOf W ⊔ N.subgroupOf W :=
    a10t1_ll_perfect_le hperf hD (a10t1_ll_le_of_fiveElt hC' hfive)
  have hCle : C ≤ (E₁ ⊔ E₂) ⊔ N := by
    intro c hc
    have hmem : (⟨c, hCW hc⟩ : ↥W) ∈ ((E₁ ⊔ E₂) ⊔ N).subgroupOf W := by
      rw [Subgroup.subgroupOf_sup hEW h.kd.N_le]
      exact hCs (Subgroup.mem_subgroupOf.2 hc)
    exact hmem
  have hON : N ≤ Subgroup.normalizer ((E₁ ⊔ E₂ : Subgroup G) : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact h.base.E_norm n (h.kd.N_le hn) x hx
    · intro hx
      have := h.base.E_norm n⁻¹ (inv_mem (h.kd.N_le hn)) _ hx
      simpa [mul_assoc] using this
  have hCE : C ≤ E₁ ⊔ E₂ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup hp hC
      ((Nat.Prime.coprime_iff_not_dvd hp).2 h.kd.N_cop) hON hCle
  have hle' : C.subgroupOf W ≤ sSup {E₁.subgroupOf W, E₂.subgroupOf W} := by
    rw [sSup_pair, ← Subgroup.subgroupOf_sup hE₁W hE₂W]
    intro x hx
    exact hCE hx
  obtain ⟨K, hK, hCK⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.exists_le_of_le_sSup 5 (C.subgroupOf W) hC'
      {E₁.subgroupOf W, E₂.subgroupOf W}
      (by
        intro M hM
        rcases hM with rfl | rfl
        · exact hE₁'.choose_spec.2.1
        · exact hE₂'.choose_spec.2.1)
      hle'
  rcases hK with rfl | rfl
  · left
    have heq := CFSG.ComponentClassification.CatalogueBPrimeJoin.eq_of_le 5 _ _ hC' hE₁' hCK
    rwa [Subgroup.subgroupOf_inj, inf_eq_left.2 hCW, inf_eq_left.2 hE₁W] at heq
  · right
    have heq := CFSG.ComponentClassification.CatalogueBPrimeJoin.eq_of_le 5 _ _ hC' hE₂' hCK
    rwa [Subgroup.subgroupOf_inj, inf_eq_left.2 hCW, inf_eq_left.2 hE₂W] at heq

theorem a10_layer_abstract {W O N D E₁ E₂ : Subgroup G} (h : A10EData W O N D E₁ E₂) :
    GLAPComponent 5 W E₁ ∧ GLAPComponent 5 W E₂ ∧ E₁ ≠ E₂ ∧ GLAPLayer 5 W = E₁ ⊔ E₂ ∧
      Nonempty (↥E₁ ⧸ primeComplementCore (G := ↥E₁) 5 ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (↥E₂ ⧸ primeComplementCore (G := ↥E₂) 5 ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hc₁, hc₂, hne, hA₁, hA₂⟩ := a10_E_comp h
  refine ⟨hc₁, hc₂, hne, ?_, hA₁, hA₂⟩
  have hset : {L : Subgroup G | GLAPComponent 5 W L} = {E₁, E₂} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hL
      exact a10_layer_le h hc₁ hc₂ hL
    · rintro (rfl | rfl)
      · exact hc₁
      · exact hc₂
  unfold GLAPLayer
  rw [hset, sSup_pair]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
