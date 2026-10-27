module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Comp
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Layer

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem le_pCore_of_isSubnormal_of_isPGroup' [Fact p.Prime] {S : Subgroup X}
    (hS : S.IsSubnormal) (hp : IsPGroup p S) : S ≤ CFSG.pCore p X := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = p} hS
  rw [← CFSG.pCore_eq_piCore ↥S p, ← CFSG.pCore_eq_piCore X p] at h
  have htop : CFSG.pCore p ↥S = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.le.trans inf_le_right

theorem center_eq_bot_of_isComponentOf (hp : p.Prime)
    (hcore : primeComplementCore (G := X) p = ⊥) (hQ : CFSG.pCore p X = ⊥) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : center K = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p (center K) := isPGroup_center_of_isComponentOf hp hcore hK
  have hKsub : K.IsSubnormal :=
    ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1 Subgroup.IsSubnormal.top
  set S : Subgroup X := (center K).map K.subtype with hS
  have hSsub : S.IsSubnormal := by
    refine Subgroup.IsSubnormal.step S K (Subgroup.map_subtype_le _) hKsub ?_
    have : S.subgroupOf K = center K :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [this]
    infer_instance
  have hSp : IsPGroup p S := hpg.map K.subtype
  have hle := le_pCore_of_isSubnormal_of_isPGroup' hSsub hSp
  rw [hQ] at hle
  rw [eq_bot_iff]
  intro x hx
  have hxS : (x : X) ∈ S := ⟨x, hx, rfl⟩
  have := hle hxS
  rw [mem_bot] at this ⊢
  exact Subtype.ext this

theorem exists_mem_centralizer_of_normalizes (hp : p.Prime) {A L : Subgroup X}
    (hA : IsPGroup p A) (hnorm : A ≤ normalizer (L : Set X)) (hL : p ∣ Nat.card L) :
    ∃ c ∈ L, orderOf c = p ∧ c ∈ centralizer (A : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  set W : Subgroup X := A ⊔ L with hW
  have hWn : W ≤ normalizer (L : Set X) := sup_le hnorm le_normalizer
  have hAW : A ≤ W := le_sup_left
  have hLW : L ≤ W := le_sup_right
  have hA' : IsPGroup p (A.subgroupOf W) := hA.comap_subtype
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  set S₀ : Subgroup X := (Q : Subgroup W).map W.subtype with hS₀
  have hS₀syl : CFSG.ABGLocalTools.IsSylowOf p S₀ W := ⟨Q, rfl⟩
  have hAS : A ≤ S₀ := by
    intro a ha
    have haW : a ∈ W := hAW ha
    refine ⟨⟨a, haW⟩, hQ ?_, rfl⟩
    exact ha
  have hS₀p : IsPGroup p S₀ := hS₀syl.isPGroup
  have hS₀W : S₀ ≤ W := hS₀syl.le
  have hsylL : CFSG.ABGLocalTools.IsSylowOf p (S₀ ⊓ L) L :=
    hS₀syl.inf_of_le_normalizer hLW hWn
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hfact : 1 ≤ (Nat.card L).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hL0).1 hL
  have hcard : Nat.card (S₀ ⊓ L : Subgroup X) = p ^ (Nat.card L).factorization p :=
    hsylL.card_eq
  have hne : (S₀ ⊓ L : Subgroup X) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have : p ^ 1 ≤ p ^ (Nat.card L).factorization p := Nat.pow_le_pow_right hp.pos hfact
    rw [← hcard] at this
    have := hp.one_lt
    simp at *
    omega
  have hnormS : S₀ ≤ normalizer ((S₀ ⊓ L : Subgroup X) : Set X) :=
    (le_inf le_normalizer (hS₀W.trans hWn)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨c, hcN, hcord, hcC⟩ :=
    exists_mem_inf_center_of_normalizing hp hS₀p hne inf_le_left hnormS
  refine ⟨c, hcN.2, hcord, ?_⟩
  rw [mem_centralizer_iff]
  intro a ha
  exact mem_centralizer_iff.1 hcC a (hAS ha)

end Layer

section RedConfigLayer

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem RedConfig.mem_of_mem_centralizer (h : RedConfig p P z D) {c : X} (hc : orderOf c = p)
    (hcC : c ∈ centralizer (D : Set X)) : c ∈ D := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hcp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
  have hcomm : D ≤ centralizer ((zpowers c : Subgroup X) : Set X) :=
    le_centralizer_iff.mp (zpowers_le.mpr hcC)
  have hel : IsElemAbelian p (D ⊔ zpowers c) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p h.elem
      (isElemAbelian_zpowers hcp) hcomm
  have hQD : D ⊔ zpowers c ≤ centralizer (D : Set X) :=
    sup_le (le_centralizer_iff_isMulCommutative.mpr h.elem.1) (zpowers_le.mpr hcC)
  have hsyl := h.sylow
  have heq : D ⊔ zpowers c = D :=
    hsyl.eq_of_le le_sup_left hQD (elementary_isPGroup p _ hel)
  rw [← heq]
  exact Subgroup.mem_sup_right (mem_zpowers c)

theorem RedConfig.exists_mem_inf_of_normalizes (h : RedConfig p P z D) {L : Subgroup X}
    (hnorm : D ≤ normalizer (L : Set X)) (hL : p ∣ Nat.card L) :
    ∃ c ∈ D ⊓ L, orderOf c = p := by
  have hp := h.prime
  obtain ⟨c, hcL, hcord, hcC⟩ := exists_mem_centralizer_of_normalizes hp
    (elementary_isPGroup p D h.elem) hnorm hL
  exact ⟨c, ⟨h.mem_of_mem_centralizer hcord hcC, hcL⟩, hcord⟩

end RedConfigLayer

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
