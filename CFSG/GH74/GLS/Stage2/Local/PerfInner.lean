module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.Stage1.Main.BrPairAbs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

section Abstract

variable {H : Type} [Group H]

theorem perfect_le_of_index_two {N : Subgroup H} [N.Normal] (hN : N.index = 2) {Q : Subgroup H}
    (hQ : Group.IsPerfect ↥Q) : Q ≤ N := by
  have hcard : Nat.card (H ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hcard
  have : IsMulCommutative (H ⧸ N) := IsCyclic.isMulCommutative
  have hc : commutator H ≤ N := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hQc : Q ≤ commutator H := by
    calc Q = ⁅Q, Q⁆ := (Subgroup.isPerfect_iff.mp hQ).symm
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := (commutator_def H).symm
  exact hQc.trans hc

theorem perf_le_of_prodSL2 [Finite H] {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hP : IVK.ProdSL2 H K₁ K₂ F₁ F₂) (h1 : 3 < Nat.card F₁) (h2 : 3 < Nat.card F₂)
    {Q : Subgroup H} (hQ : Group.IsPerfect ↥Q) : Q ≤ K₁ ⊔ K₂ := by
  obtain ⟨hidx, hcomm⟩ := IVK.Proofs2.ivk_3_1g_fixed F₁ F₂ H K₁ K₂ hP h1 h2
  set N : Subgroup H := normalizer (K₁ : Set H) with hNdef
  have hQN : Q ≤ N := by
    have hpos : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases Nat.lt_or_ge N.index 2 with hlt | hge
    · have h1' : N.index = 1 := by omega
      rw [Subgroup.index_eq_one] at h1'
      rw [h1']
      exact le_top
    · have h2' : N.index = 2 := le_antisymm hidx hge
      have : N.Normal := Subgroup.normal_of_index_eq_two h2'
      exact perfect_le_of_index_two h2' hQ
  have hc : ⁅Q, Q⁆ ≤ K₁ ⊔ K₂ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact hcomm a (hQN ha) b (hQN hb)
  calc Q = ⁅Q, Q⁆ := (Subgroup.isPerfect_iff.mp hQ).symm
    _ ≤ K₁ ⊔ K₂ := hc

end Abstract

section Pair

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem prodSL2_of_stage1Pair (hP : Stage1Pair G z S q L₁ L₂) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂),
      Nat.card F₁ = q ∧ Nat.card F₂ = q ∧ IVK.ProdSL2 (CentralizerBar z) L₁ L₂ F₁ F₂ := by
  obtain ⟨F₁, iF₁, fF₁, hF₁q, ⟨e₁⟩⟩ := hP.sl₁
  obtain ⟨F₂, iF₂, fF₂, hF₂q, ⟨e₂⟩⟩ := hP.sl₂
  have hnormal : (L₁ ⊔ L₂).Normal := by
    rw [hP.prod.1]
    exact Stage1.Thm6.Prod.LBar_isNormal z
  have hcent : centralizer ((L₁ ⊔ L₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ≤
      L₁ ⊔ L₂ := by
    rw [hP.prod.1, ← hP.fitting]
    exact CFSG.centralizer_generalizedFitting_le _
  exact ⟨F₁, F₂, iF₁, iF₂, fF₁, fF₂, hF₁q, hF₂q,
    ⟨hP.prod.2.1, ⟨e₁⟩, ⟨e₂⟩, hP.prod.2.2, hnormal, hcent⟩⟩

theorem perfInner_of_pair (hP : Stage1Pair G z S q L₁ L₂) : PerfInner z := by
  intro Q hQ
  obtain ⟨F₁, F₂, _, _, _, _, hF₁, hF₂, hprod⟩ := prodSL2_of_stage1Pair hP
  have h3 : 3 < q := hP.gt3
  have hle := perf_le_of_prodSL2 hprod (by omega) (by omega) hQ
  rw [hP.prod.1, Stage1.Thm6.Prod.LBar_eq z] at hle
  exact hle.trans inf_le_right

end Pair

section LC

variable {G : Type} [Group G] [Finite G]

theorem perfect_le_LC_of (z : G) (hI : PerfInner z) {P : Subgroup G} (hP : P ≤ Cen z)
    (hperf : Group.IsPerfect ↥P) : P ≤ LC z := by
  have hK : Group.IsPerfect ↥(P.subgroupOf (Cen z)) := by
    have e : ↥(P.subgroupOf (Cen z)) ≃* ↥P := Subgroup.subgroupOfEquivOfLe hP
    exact Group.IsPerfect.ofSurjective (G := ↥P) (G' := ↥(P.subgroupOf (Cen z)))
      (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 : P.subgroupOf (Cen z) ≤ oPrimePResidual 2 ↥(Cen z) :=
    Stage1.Main.perfect_le_oPrimePResidual' hK
  have hbar : Group.IsPerfect ↥((P.subgroupOf (Cen z)).map (toBar z)) := by
    have := hK
    exact Group.IsPerfect.map (toBar z)
  have h2 := hI _ hbar
  intro g hg
  have hgC : g ∈ Cen z := hP hg
  have hg' : (⟨g, hgC⟩ : ↥(Cen z)) ∈ P.subgroupOf (Cen z) := hg
  exact (Stage1.Thm6.Prod.mem_LC_iff z ⟨g, hgC⟩).2 ⟨h1 hg', h2 ⟨⟨g, hgC⟩, hg', rfl⟩⟩

end LC

end CFSG.GH74.GLS.Stage2.Local
