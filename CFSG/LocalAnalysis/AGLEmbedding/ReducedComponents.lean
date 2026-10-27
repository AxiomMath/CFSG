module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponentsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankForm
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Elementary

variable {X : Type*} [Group X] [Finite X]

theorem exists_isElemAbelian_card_sq_of_two_le_pRank {p : ℕ} (hp : p.Prime) {H : Subgroup X}
    (hH : 2 ≤ Open.pRank p H) : ∃ E ≤ H, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAH, hA, hAcard⟩ := PreuniquenessRankFour.Helpers.pRank_attained p hp H
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 2)
    (hAcard ▸ pow_dvd_pow p hH)
  have : IsMulCommutative A := hA.1
  have hB' : IsElemAbelian p B :=
    ⟨inferInstance, fun x _ => Subtype.ext (hA.2 x x.property)⟩
  refine ⟨B.map A.subtype, (Subgroup.map_subtype_le B).trans hAH,
    elementary_abelian_map p hB' A.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hB]

theorem three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer {p : ℕ} (hp : p.Prime)
    {E H : Subgroup X} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) {t : X}
    (ht : orderOf t = p) (htE : t ∉ E) (htC : t ∈ Subgroup.centralizer (E : Set X))
    (hEH : E ≤ H) (htH : t ∈ H) : 3 ≤ Open.pRank p H := by
  have htp : t ^ p = 1 := ht ▸ pow_orderOf_eq_one t
  have hEt : E ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr htC)
  have hJ := elementary_abelian_sup_of_commuting p hE (isElemAbelian_zpowers htp) hEt
  have hJH : E ⊔ Subgroup.zpowers t ≤ H := sup_le hEH (Subgroup.zpowers_le.mpr htH)
  by_contra hlt
  have heq := elementary_subgroup_eq_of_rank_bound p hp hJ le_sup_left 2 hcard
    (by have := PreuniquenessRankFour.Helpers.pRank_mono p hp hJH; omega)
  exact htE (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

end Elementary

section Component

variable {X : Type*} [Group X] [Finite X]

theorem exists_mem_sylow_inf_component {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hcore : primeComplementCore (G := X) p = ⊥) (R : Sylow p X) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) :
    ∃ t ∈ (R : Subgroup X) ⊓ L, orderOf t = p ∧ t ∉ Subgroup.centralizer (L : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, htP, ht, htZ⟩ := exists_mem_sylow_orderOf_eq_not_mem_center hp hodd hL.2.2
    (prime_dvd_card_center_quotient_of_isComponentOf hp hcore hL) P
  refine ⟨t, hP ▸ ⟨t, htP, rfl⟩, by rw [Subgroup.orderOf_coe, ht], fun hc => htZ ?_⟩
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) l l.property)

omit [Finite X] in
theorem le_layer_of_isComponentOf {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    L ≤ CFSG.layer X :=
  le_sSup ((CFSG.isComponent_iff_open L).mpr hL)

end Component

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem sylow_le (h : ReducedNongeneration p X R X₀) : (R : Subgroup X) ≤ X₀ :=
  (subgroup_le_weakCore_of_rank p h.prime _ h.three_le_pRank).trans h.weakCore_le

theorem pRank_le_two_of_normal_le (h : ReducedNongeneration p X R X₀) {N : Subgroup X}
    [N.Normal] (hN : N ≤ X₀) : Open.pRank p N ≤ 2 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ X₀ := by
    by_contra! hall
    exact h.ne_top (eq_top_iff.mpr fun x _ => hall x)
  refine (PreuniquenessRankFour.Helpers.pRank_mono p h.prime (le_inf hN ?_)).trans
    (h.pRank_inf_conj_le x hx)
  intro n hn
  refine ⟨x * n * x⁻¹, hN (‹N.Normal›.conj_mem n hn x), ?_⟩
  simp [mul_assoc]

theorem pRank_le_two_of_normal_isPGroup (h : ReducedNongeneration p X R X₀) {Q : Subgroup X}
    [Q.Normal] (hQ : IsPGroup p Q) : Open.pRank p Q ≤ 2 :=
  h.pRank_le_two_of_normal_le ((hQ.le_sylow_of_normal R).trans h.sylow_le)

theorem card_le_of_normal_isElemAbelian (h : ReducedNongeneration p X R X₀) {Q : Subgroup X}
    [Q.Normal] (hQ : IsElemAbelian p Q) : Nat.card Q ≤ p := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Q := elementary_isPGroup p Q hQ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hk2 : k ≤ 2 :=
    (le_csSup (pRank_bddAbove p hp Q) ⟨Q, le_rfl, hQ, hk⟩).trans
      (h.pRank_le_two_of_normal_isPGroup hQp)
  rcases Nat.lt_or_ge k 2 with hk1 | hk2'
  · rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      _ = p := pow_one p
  · exfalso
    obtain ⟨A, hAR, hA, hAcard⟩ := PreuniquenessRankFour.Helpers.pRank_attained p hp
      (R : Subgroup X)
    have hN := normalizer_le_of_elementary_rank_two_normalized_by_rank_three p hp R h.sylow_le
      h.weakCore_le hA _ h.three_le_pRank hAcard (hAR.trans h.sylow_le) hQ
      (by rw [hk, show k = 2 by omega]) ((hQp.le_sylow_of_normal R).trans h.sylow_le)
      (by rw [Subgroup.normalizer_eq_top Q]; exact le_top)
    rw [Subgroup.normalizer_eq_top Q] at hN
    exact h.ne_top (top_le_iff.mp hN)

theorem not_normalClosure_le (h : ReducedNongeneration p X R X₀) :
    ¬ Subgroup.normalClosure (R : Set X) ≤ X₀ := by
  have : (Subgroup.normalClosure (R : Set X)).Normal := Subgroup.normalClosure_normal
  refine not_le_of_weakCore_le h.prime R h.weakCore_le h.ne_top ?_
  have hle : (R : Subgroup X) ≤ Subgroup.normalClosure (R : Set X) :=
    fun _ hx => Subgroup.subset_normalClosure hx
  rw [inf_eq_left.mpr hle]
  exact h.three_le_pRank

theorem le_of_ne_component (h : ReducedNongeneration p X R X₀) {L₁ L₂ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hrank : 2 ≤ Open.pRank p ((R : Subgroup X) ⊓ L₂)) : L₁ ≤ X₀ := by
  have hp := h.prime
  have h₁₂ : L₁ ≤ Subgroup.centralizer (L₂ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)
  have h₂₁ : L₂ ≤ Subgroup.centralizer (L₁ : Set X) := Subgroup.le_centralizer_iff.mp h₁₂
  obtain ⟨E, hER, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hrank
  obtain ⟨t, ⟨htR, htL⟩, ht, htZ⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₁
  have hEL : (E : Subgroup X) ≤ L₂ := hER.trans inf_le_right
  have hEX₀ : E ≤ X₀ := (hER.trans inf_le_left).trans h.sylow_le
  have htC : t ∈ Subgroup.centralizer (E : Set X) := Subgroup.centralizer_le hEL (h₁₂ htL)
  have hN : Subgroup.normalizer (E : Set X) ≤ X₀ :=
    normalizer_le_of_subgroup_and_centralizer_rank p hp R h.sylow_le h.weakCore_le hEX₀
      (le_csSup (pRank_bddAbove p hp E) ⟨E, le_rfl, hE, hEcard⟩)
      (three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hE hEcard ht
        (fun htE => htZ (h₂₁ (hEL htE)))
        htC (le_inf hEX₀ (Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1))
        ⟨h.sylow_le htR, htC⟩)
  exact (h₁₂.trans (Subgroup.centralizer_le hEL)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)

theorem eq_of_two_le_pRank (h : ReducedNongeneration p X R X₀) {L₁ L₂ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤)
    (hr₁ : 2 ≤ Open.pRank p ((R : Subgroup X) ⊓ L₁))
    (hr₂ : 2 ≤ Open.pRank p ((R : Subgroup X) ⊓ L₂)) : L₁ = L₂ := by
  have hp := h.prime
  by_contra hne
  have hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ X₀ := by
    intro L hL
    by_cases hL₂ : L = L₂
    · subst hL₂
      exact h.le_of_ne_component hL h₁ (Ne.symm hne) hr₁
    · exact h.le_of_ne_component hL h₂ hL₂ hr₂
  have hlayer : CFSG.layer X ≤ X₀ :=
    sSup_le fun L hL => hall L ((CFSG.isComponent_iff_open L).mp hL)
  have h₁₂ : L₁ ≤ Subgroup.centralizer (L₂ : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ hne)
  obtain ⟨E, hER, hE, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hr₂
  obtain ⟨t, ⟨htR, htL⟩, ht, htZ⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₁
  have hEL : (E : Subgroup X) ≤ L₂ := hER.trans inf_le_right
  have hlayerF : CFSG.layer X ≤ CFSG.generalizedFitting X := le_sup_right
  have hrank : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ CFSG.generalizedFitting X) :=
    three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hE hEcard ht
      (fun htE => htZ (Subgroup.le_centralizer_iff.mp h₁₂ (hEL htE)))
      (Subgroup.centralizer_le hEL (h₁₂ htL))
      (le_inf (hER.trans inf_le_left) (hEL.trans ((le_layer_of_isComponentOf h₂).trans hlayerF)))
      ⟨htR, hlayerF (le_layer_of_isComponentOf h₁ htL)⟩
  exact not_layer_le_of_weakCore_le hp h.core_eq_bot R h.weakCore_le h.ne_top hrank hlayer

theorem isCyclic_pCore_of_component (h : ReducedNongeneration p X R X₀) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : IsCyclic (CFSG.pCore p X) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  have : Fact (IsPGroup p (CFSG.pCore p X)) := ⟨CFSG.pCore_isPGroup⟩
  obtain ⟨S, -, hScard, hSelem⟩ := lemma_4_5_a h.ne_two hnc
  set Q := S.map (CFSG.pCore p X).subtype
  have hQ : IsElemAbelian p Q :=
    elementary_abelian_map p ⟨hSelem.toIsMulCommutative,
      fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ _
  have hQcard : Nat.card Q = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (CFSG.pCore p X).subtype_injective, hScard]
  have hQO : Q ≤ CFSG.pCore p X := Subgroup.map_subtype_le S
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hOR : CFSG.pCore p X ≤ R := CFSG.pCore_isPGroup.le_sylow_of_normal R
  have hF : CFSG.fittingSubgroup X = CFSG.pCore p X := CFSG.Fitting_eq_pcore X p h.core_eq_bot
  have hEC : CFSG.layer X ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
    rw [← hF]
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  have hLE := le_layer_of_isComponentOf hL
  obtain ⟨t, ⟨htR, htL⟩, ht, htZ⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hL
  have htQ : t ∉ Q := fun htQ => htZ (Subgroup.le_centralizer_iff.mp (hLE.trans hEC) (hQO htQ))
  have htC : t ∈ Subgroup.centralizer (Q : Set X) := Subgroup.centralizer_le hQO (hEC (hLE htL))
  have hQX₀ : Q ≤ X₀ := hQO.trans (hOR.trans h.sylow_le)
  have hN : Subgroup.normalizer (Q : Set X) ≤ X₀ :=
    normalizer_le_of_subgroup_and_centralizer_rank p hp R h.sylow_le h.weakCore_le hQX₀
      (le_csSup (pRank_bddAbove p hp Q) ⟨Q, le_rfl, hQ, hQcard⟩)
      (three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hQ hQcard ht htQ htC
        (le_inf hQX₀ (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQ.1))
        ⟨h.sylow_le htR, htC⟩)
  have hlayer : CFSG.layer X ≤ X₀ := (hEC.trans (Subgroup.centralizer_le hQO)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN)
  have hOF : CFSG.pCore p X ≤ CFSG.generalizedFitting X := hF ▸ le_sup_left
  have hlayerF : CFSG.layer X ≤ CFSG.generalizedFitting X := le_sup_right
  have hrank : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ CFSG.generalizedFitting X) :=
    three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hQ hQcard ht htQ htC
      (le_inf (hQO.trans hOR) (hQO.trans hOF)) ⟨htR, hlayerF (hLE htL)⟩
  exact not_layer_le_of_weakCore_le hp h.core_eq_bot R h.weakCore_le h.ne_top hrank hlayer

end ReducedNongeneration

end CFSG.AGLEmbedding
