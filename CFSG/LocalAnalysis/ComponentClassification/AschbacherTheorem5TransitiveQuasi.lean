module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {X : Type} [Group X]

theorem component_perfect {L : Subgroup X} (hL : IsComponentOf L ⊤) : Group.IsPerfect L :=
  ⟨hL.2.2.1⟩

theorem component_ne_bot {L : Subgroup X} (hL : IsComponentOf L ⊤) : L ≠ ⊥ :=
  L.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hL.2.2)

theorem isPGroup_sup_of_commute [Finite X] {P P' : Subgroup X} (hP : IsPGroup 2 P)
    (hP' : IsPGroup 2 P')
    (hcomm : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x) : IsPGroup 2 (P ⊔ P' : Subgroup X) := by
  have hN : P' ≤ Subgroup.normalizer (P : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx y hy
  exact IsPGroup.to_sup_of_normal_left' hP hP' hN

theorem not_isCyclic_rightConjugate {P : Subgroup X} (hP : ¬ IsCyclic P) (c : X) :
    ¬ IsCyclic (rightConjugate P c) := by
  intro h
  apply hP
  have : IsCyclic (P.map (MulAut.conj c⁻¹).toMonoidHom) := h
  exact isCyclic_of_surjective
    ((P.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom
      (MulAut.conj c⁻¹).injective).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem components_subsingleton_of_sylow [Finite X] {ι : Type*} {Q R : Subgroup X}
    (K : ι → Subgroup X)
    (hK : ∀ i, IsComponentOf (K i) ⊤) (hKQ : ∀ i, K i ≤ Q)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hR : IsSylowOf 2 R Q)
    (hRtype : IsCyclic R ∨ AschbacherTheorem3.IsDihedralTwoGroup R ∨
      AschbacherTheorem3.IsQuaternionTwoGroup R) :
    ∀ i j : ι, i = j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro i j
  by_contra hij
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K i)
  obtain ⟨P', hP'⟩ := exists_isSylowOf 2 (K j)
  have hPc : ¬ IsCyclic P :=
    sylow_not_cyclic_of_perfect (component_perfect (hK i)) (component_ne_bot (hK i)) hP
  have hP'c : ¬ IsCyclic P' :=
    sylow_not_cyclic_of_perfect (component_perfect (hK j)) (component_ne_bot (hK j)) hP'
  have hcommPP' : ∀ x ∈ P, ∀ y ∈ P', x * y = y * x :=
    fun x hx y hy => hcomm i j hij x (hP.le hx) y (hP'.le hy)
  have hsup2 := isPGroup_sup_of_commute hP.isPGroup hP'.isPGroup hcommPP'
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hR hsup2
    (sup_le (hP.le.trans (hKQ i)) (hP'.le.trans (hKQ j)))
  have h1 : rightConjugate P c ≤ R :=
    (Subgroup.map_mono le_sup_left).trans hc
  have h2 : rightConjugate P' c ≤ R :=
    (Subgroup.map_mono le_sup_right).trans hc
  have hcommc : ∀ x ∈ rightConjugate P c, ∀ y ∈ rightConjugate P' c, x * y = y * x := by
    intro x hx y hy
    rw [mem_rightConjugate_iff] at hx hy
    have h := hcommPP' _ hx _ hy
    calc x * y = c⁻¹ * ((c * x * c⁻¹) * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * (c * x * c⁻¹)) * c := by rw [h]
      _ = y * x := by group
  have heq := commuting_noncyclic_eq hRtype h1 h2 (not_isCyclic_rightConjugate hPc c)
    (not_isCyclic_rightConjugate hP'c c) hcommc
  have heq' : P = P' := by
    have := congrArg (fun Y => rightConjugate Y c⁻¹) heq
    simpa only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] using this
  apply sylow_not_le_centralizer_of_perfect (component_perfect (hK i)) (component_ne_bot (hK i))
    hP
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxj : x ∈ K j := hP'.le (heq' ▸ hx)
  exact (hcomm j i (Ne.symm hij) x hxj y hy).symm

theorem components_subsingleton_of_simple [Finite X] {ι : Type*} {Q : Subgroup X}
    (K : ι → Subgroup X)
    (hK : ∀ i, IsComponentOf (K i) ⊤) (hKQ : ∀ i, K i ≤ Q)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hgen : ⨆ i, K i = Q) (hsimple : IsSimpleGroup (AschbacherTheorem3.oTwoPrime Q)) :
    ∀ i j : ι, i = j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := AschbacherTheorem3.oTwoPrime Q with hNdef
  have hNQ : N ≤ Q := by
    rw [hNdef, AschbacherTheorem3.oTwoPrime, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hQK : ∀ i, Q ≤ Subgroup.normalizer (K i : Set X) := by
    intro i
    rw [← hgen]
    refine iSup_le fun l => ?_
    by_cases hli : l = i
    · subst hli
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm l i hli x hx y hy).symm
  have hQN : Q ≤ Subgroup.normalizer (N : Set X) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [hNdef, AschbacherTheorem3.oTwoPrime, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, ⟨hxQ, k, hk⟩, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨Q.mul_mem (Q.mul_mem hq hxQ) (Q.inv_mem hq), k, ?_⟩
      change (q * x * q⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hk]
      group
    · rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
  have hPN : ∀ i (P : Subgroup X), IsSylowOf 2 P (K i) → P ≤ N := by
    intro i P hP x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) ⟨x, hx⟩
    apply Subgroup.subset_closure
    refine ⟨hKQ i (hP.le hx), k, ?_⟩
    have := congrArg Subtype.val (pow_orderOf_eq_one (⟨x, hx⟩ : P))
    rw [hk] at this
    simpa using this
  have hNK : ∀ i, N ≤ K i := by
    intro i
    obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K i)
    have hn : ((K i ⊓ N).subgroupOf N).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
      intro n hn
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hQK i (hNQ hn), Subgroup.le_normalizer hn⟩
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K i ⊓ N).subgroupOf N) with hbot | htop
    · exfalso
      have hinf : K i ⊓ N = ⊥ := by
        have hmap := congrArg (Subgroup.map N.subtype) hbot
        rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot,
          inf_eq_left.mpr (inf_le_right : K i ⊓ N ≤ N)] at hmap
      have hc1 : ⁅N, K i⁆ ≤ K i :=
        Subgroup.le_normalizer_iff_commutator_le_right.mp (hNQ.trans (hQK i))
      have hc2 : ⁅N, K i⁆ ≤ N :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp ((hKQ i).trans hQN)
      have hcbot : ⁅N, K i⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf hc1 hc2)
      apply sylow_not_le_centralizer_of_perfect (component_perfect (hK i))
        (component_ne_bot (hK i)) hP
      exact (hPN i P hP).trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcbot)
    · intro n hn
      have : (⟨n, hn⟩ : N) ∈ (K i ⊓ N).subgroupOf N := htop ▸ Subgroup.mem_top _
      exact this.1
  intro i j
  by_contra hij
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (K i)
  apply sylow_not_le_centralizer_of_perfect (component_perfect (hK i)) (component_ne_bot (hK i))
    hP
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcomm j i (Ne.symm hij) x (hNK j (hPN i P hP hx)) y hy).symm

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
