module

public import CFSG.Open.GLBDefs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoBase
import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem pRank_inf_layer_le_two (hp : p.Prime) (P : Sylow p X)
    (hH : CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) ≠ ⊤) :
    Open.pRank p ((P : Subgroup X) ⊓ CFSG.layer X) ≤ 2 := by
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  by_contra h
  exact not_le_of_weakCore_le hp P le_sup_right hH (by omega) le_sup_left

theorem layer_eq_of_component (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (P : Sylow p X)
    (hH : CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) ≠ ⊤) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hnc : ¬ IsCyclic ((P : Subgroup X) ⊓ L : Subgroup X)) :
    CFSG.layer X = L ∧ Open.pRank p ((P : Subgroup X) ⊓ L) = 2 := by
  have h2 : 2 ≤ Open.pRank p ((P : Subgroup X) ⊓ L) :=
    two_le_pRank_of_isPGroup_not_isCyclic hp hp2 (P.isPGroup'.to_le inf_le_left) hnc
  have hle2 := pRank_inf_layer_le_two hp P hH
  have hLE := le_layer_of_isComponentOf hL
  have hall : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L := by
    intro K hK
    by_contra hne
    have hKL : K ≤ Subgroup.centralizer (L : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (ComponentClassification.LocalComponents.commute_of_ne K L hK hL hne)
    obtain ⟨E, hER, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
    obtain ⟨t, ⟨htR, htK⟩, ht, htZ⟩ := exists_mem_sylow_inf_component hp hp2 hcore P hK
    have hEL : E ≤ L := hER.trans inf_le_right
    have h3 : 3 ≤ Open.pRank p ((P : Subgroup X) ⊓ CFSG.layer X) :=
      three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hE hEcard ht
        (fun htE => htZ (Subgroup.le_centralizer_iff.mp hKL (hEL htE)))
        (Subgroup.centralizer_le hEL (hKL htK))
        (le_inf (hER.trans inf_le_left) (hEL.trans hLE)) ⟨htR, le_layer_of_isComponentOf hK htK⟩
    omega
  have hlayer : CFSG.layer X = L := by
    refine le_antisymm ?_ hLE
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun K hK => (hall K ((CFSG.isComponent_iff_open K).mp hK)).le
  exact ⟨hlayer, le_antisymm (hlayer ▸ hle2) h2⟩

private theorem mem_zpowers_of_isCyclic {C : Subgroup X} [IsCyclic C] {x y : X} (hx : x ∈ C)
    (hy : y ∈ C) (hxy : orderOf x = orderOf y) : x ∈ Subgroup.zpowers y := by
  have heq : Subgroup.zpowers (⟨x, hx⟩ : C) = Subgroup.zpowers ⟨y, hy⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxy]
  have hmem : (⟨x, hx⟩ : C) ∈ Subgroup.zpowers ⟨y, hy⟩ := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem normalizer_inf_layer_le_of_forall_isCyclic (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (P : Sylow p X)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup X))
    (hQ2 : Open.pRank p ((P : Subgroup X) ⊓ CFSG.layer X) ≤ 2)
    (hcyc : ∀ L : Subgroup X, IsComponentOf L ⊤ → IsCyclic ((P : Subgroup X) ⊓ L : Subgroup X))
    {L₁ L₂ : Subgroup X} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) :
    Subgroup.normalizer (((P : Subgroup X) ⊓ CFSG.layer X : Subgroup X) : Set X) ≤
      CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  set Q : Subgroup X := (P : Subgroup X) ⊓ CFSG.layer X with hQ
  have h₁₂ : L₁ ≤ Subgroup.centralizer (L₂ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)
  obtain ⟨t₁, ⟨ht₁P, ht₁L⟩, ht₁, -⟩ := exists_mem_sylow_inf_component hp hp2 hcore P h₁
  obtain ⟨t₂, ⟨ht₂P, ht₂L⟩, ht₂, ht₂Z⟩ := exists_mem_sylow_inf_component hp hp2 hcore P h₂
  have ht₁Q : t₁ ∈ Q := ⟨ht₁P, le_layer_of_isComponentOf h₁ ht₁L⟩
  have ht₂Q : t₂ ∈ Q := ⟨ht₂P, le_layer_of_isComponentOf h₂ ht₂L⟩
  have hz₁ : Subgroup.zpowers t₁ ≤ L₁ := Subgroup.zpowers_le.mpr ht₁L
  have hz₂ : Subgroup.zpowers t₂ ≤ L₂ := Subgroup.zpowers_le.mpr ht₂L
  set A : Subgroup X := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hAdef
  have hAQ : A ≤ Q := sup_le (Subgroup.zpowers_le.mpr ht₁Q) (Subgroup.zpowers_le.mpr ht₂Q)
  have hA : IsElemAbelian p A :=
    elementary_abelian_sup_of_commuting p (isElemAbelian_zpowers (ht₁ ▸ pow_orderOf_eq_one t₁))
      (isElemAbelian_zpowers (ht₂ ▸ pow_orderOf_eq_one t₂))
      (hz₁.trans (h₁₂.trans (Subgroup.centralizer_le hz₂)))
  have hAc : Nat.card A = p ^ 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (elementary_isPGroup p A hA)
    have hk2 : k ≤ 2 := (le_csSup (pRank_bddAbove p hp Q) ⟨A, hAQ, hA, hk⟩).trans hQ2
    have hlt : Subgroup.zpowers t₁ < A := lt_of_le_of_ne le_sup_left fun h =>
      ht₂Z (h₁₂ (hz₁ (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂))))
    have hcard := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, ht₁, hk] at hcard
    have h1k : 1 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by simpa using hcard)
    rw [hk, show k = 2 by omega]
  have hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = L₁ ∨ L = L₂ := by
    intro L hL
    by_contra! hL'
    have hC : ∀ {K : Subgroup X}, IsComponentOf K ⊤ → L ≠ K →
        K ≤ Subgroup.centralizer (L : Set X) := fun hK hLK =>
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (ComponentClassification.LocalComponents.commute_of_ne _ L hK hL (Ne.symm hLK))
    have hAC : A ≤ Subgroup.centralizer (L : Set X) :=
      sup_le (hz₁.trans (hC h₁ hL'.1)) (hz₂.trans (hC h₂ hL'.2))
    obtain ⟨t, ⟨htP, htL⟩, ht, htZ⟩ := exists_mem_sylow_inf_component hp hp2 hcore P hL
    have := three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hA hAc ht
      (fun htA => htZ (hAC htA)) (Subgroup.le_centralizer_iff.mp hAC htL) hAQ
      ⟨htP, le_layer_of_isComponentOf hL htL⟩
    omega
  have hNA : Subgroup.normalizer (Q : Set X) ≤ Subgroup.normalizer (A : Set X) := by
    intro g hg
    have hconj : ∀ {t : X} {L : Subgroup X}, IsComponentOf L ⊤ → t ∈ L → t ∈ Q →
        orderOf t = p → g * t * g⁻¹ ∈ A := by
      intro t L hL htL htQ ht
      have hL' : IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
        (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
      have hgt : g * t * g⁻¹ ∈ (P : Subgroup X) ⊓ L.map (MulAut.conj g).toMonoidHom :=
        ⟨((Subgroup.mem_normalizer_iff.mp hg t).mp htQ).1, ⟨t, htL, rfl⟩⟩
      have hord : orderOf (g * t * g⁻¹) = p :=
        ht ▸ (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm
      rcases hall _ hL' with h | h
      · rw [h] at hgt
        have := hcyc L₁ h₁
        exact Subgroup.mem_sup_left
          (mem_zpowers_of_isCyclic hgt ⟨ht₁P, ht₁L⟩ (hord.trans ht₁.symm))
      · rw [h] at hgt
        have := hcyc L₂ h₂
        exact Subgroup.mem_sup_right
          (mem_zpowers_of_isCyclic hgt ⟨ht₂P, ht₂L⟩ (hord.trans ht₂.symm))
    apply mem_normalizer_of_conj_map_le
    rw [hAdef, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (Subgroup.zpowers_le.mpr (hconj h₁ ht₁L ht₁Q ht₁))
      (Subgroup.zpowers_le.mpr (hconj h₂ ht₂L ht₂Q ht₂))
  have hPQ : (P : Subgroup X) ≤ Subgroup.normalizer (Q : Set X) := by
    rw [hQ, inf_comm]
    exact Subgroup.normal_subgroupOf_iff_le_normalizer_inf.mp Subgroup.normal_subgroupOf
  exact hNA.trans (normalizer_le_of_normal_elemAbelian_sq hp P
    ((subgroup_le_weakCore_of_rank p hp _ h3).trans le_sup_right) le_sup_right h3 hA hAc
    (hAQ.trans inf_le_left) (hPQ.trans hNA))

theorem isComponent_layer (hp : p.Prime) (hp2 : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (P : Sylow p X)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup X))
    (hnc : ¬ IsCyclic ((P : Subgroup X) ⊓ CFSG.layer X : Subgroup X))
    (hH : CFSG.layer X ⊔ GLBWeakCore p (P : Subgroup X) ≠ ⊤) :
    CFSG.IsComponent (CFSG.layer X) ∧ Open.pRank p ((P : Subgroup X) ⊓ CFSG.layer X) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  by_cases hcyc : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      IsCyclic ((P : Subgroup X) ⊓ L : Subgroup X)
  · exfalso
    by_cases htwo : ∃ L₁ L₂ : Subgroup X, IsComponentOf L₁ ⊤ ∧ IsComponentOf L₂ ⊤ ∧ L₁ ≠ L₂
    · obtain ⟨L₁, L₂, h₁, h₂, hne⟩ := htwo
      exact not_le_of_normalizer_inf_le P (normalizer_inf_layer_le_of_forall_isCyclic hp hp2
        hcore P h3 (pRank_inf_layer_le_two hp P hH) hcyc h₁ h₂ hne) hH le_sup_left
    · push Not at htwo
      apply hnc
      by_cases hex : ∃ L : Subgroup X, IsComponentOf L ⊤
      · obtain ⟨L, hL⟩ := hex
        have hlayer : CFSG.layer X = L := by
          refine le_antisymm ?_ (le_layer_of_isComponentOf hL)
          rw [CFSG.layer.eq_sSup]
          exact sSup_le fun K hK => (htwo K L ((CFSG.isComponent_iff_open K).mp hK) hL).le
        rw [hlayer]
        exact hcyc L hL
      · push Not at hex
        have hlayer : CFSG.layer X = ⊥ := by
          rw [CFSG.layer.eq_sSup]
          exact sSup_eq_bot.mpr fun K hK => absurd ((CFSG.isComponent_iff_open K).mp hK) (hex K)
        rw [hlayer, inf_bot_eq]
        infer_instance
  · push Not at hcyc
    obtain ⟨L, hL, hLnc⟩ := hcyc
    obtain ⟨hlayer, hrank⟩ := layer_eq_of_component hp hp2 hcore P hH hL hLnc
    rw [hlayer]
    exact ⟨(CFSG.isComponent_iff_open L).mpr hL, hrank⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
