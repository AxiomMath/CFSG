module

public import CFSG.GH74.Generic.Certificates
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise

theorem isCyclic_of_sectionalTwoRankLE_one {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (h : SectionalTwoRankLE P 1) : IsCyclic P := by
  obtain ⟨s, hs, hcl⟩ := h ⊤ (hP.to_subgroup ⊤)
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨1, ?_⟩
    rw [zpowers_one_eq_bot, ← hcl, Finset.coe_empty, Subgroup.closure_empty]
  · have hs1 : s = {a} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx => Finset.card_le_one.1 hs x hx a ha⟩
    refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨a, ?_⟩
    rw [zpowers_eq_closure, ← hcl, hs1, Finset.coe_singleton]

theorem isCyclic_of_commuting_e8 {X : Type*} [Group X] [Finite X] (hX : CFSG.GH74.Gen4 X)
    {R P : Subgroup X} (hRcomm : ∀ a b : R, a * b = b * a) (hRsq : ∀ a : R, a * a = 1)
    (hRcard : Nat.card ↥R = 8) (hP : IsPGroup 2 ↥P)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r) (hdisj : R ⊓ P = ⊥) : IsCyclic ↥P := by
  by_contra hnc
  have hcertP : RankCertified ↥P 1 := by
    have hP1 : ¬ SectionalTwoRankLE ↥P 1 := fun h => hnc (isCyclic_of_sectionalTwoRankLE_one hP h)
    let eP : Shrink.{0} ↥P ≃* ↥P := Shrink.mulEquiv
    have : Finite (Shrink.{0} ↥P) := Finite.of_equiv ↥P eP.symm.toEquiv
    exact (rankCertified_of_not_sectionalTwoRankLE
      (fun h => hP1 (SectionalTwoRankLE.of_mulEquiv eP h))).of_mulEquiv eP
  have hcertR : RankCertified ↥R 2 := by
    let eR : Shrink.{0} ↥R ≃* ↥R := Shrink.mulEquiv
    have : Finite (Shrink.{0} ↥R) := Finite.of_equiv ↥R eR.symm.toEquiv
    refine ⟨Shrink.{0} ↥R, Shrink.{0} ↥R, inferInstance, inferInstance, inferInstance,
      eR.toMonoidHom, MonoidHom.id _, Function.surjective_id, ?_, ?_, ?_, ?_⟩
    · intro a b
      apply eR.injective
      rw [map_mul, map_mul]
      exact hRcomm _ _
    · intro a
      apply eR.injective
      rw [map_pow, map_one, sq]
      exact hRsq _
    · rw [Nat.card_congr eR.toEquiv, hRcard]
      norm_num
    · intro x hx
      rw [MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom] at hx
      rw [MonoidHom.mem_ker, MonoidHom.id_apply]
      exact eR.injective (by rw [hx, map_one])
  have hcert : RankCertified (↥R × ↥P) 4 := hcertR.prod hcertP
  have hc : ∀ (m : ↥R) (n : ↥P), Commute (R.subtype m) (P.subtype n) :=
    fun m n => hcomm m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod R.subtype P.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨R.subtype_injective, P.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.2 hdisj
  exact (hcert.of_injective _ hinj).not_gen4 le_rfl hX

theorem exists_noncyclic_two_subgroup_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) : ∃ P : Subgroup Q, IsPGroup 2 ↥P ∧ ¬ IsCyclic ↥P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hScyc : IsCyclic ↥(S : Subgroup Q) := hcon (S : Subgroup Q) S.isPGroup'
  obtain ⟨-, hprod, -, ⟨-, hodd, -, -⟩, -⟩ := cyclic_sylow_normal_odd_complement S hScyc
  set N := pPrimeCore 2 Q with hN
  have hcycq : IsCyclic (Q ⧸ N) := by
    refine isCyclic_of_surjective ((QuotientGroup.mk' N).comp (S : Subgroup Q).subtype) ?_
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hg : g ∈ (N : Set Q) * (S : Set Q) := by rw [hprod]; exact Set.mem_univ g
    obtain ⟨k, hk, s, hs, rfl⟩ := Set.mem_mul.1 hg
    refine ⟨⟨s, hs⟩, ?_⟩
    have hk1 : QuotientGroup.mk' N k = 1 := (QuotientGroup.eq_one_iff k).2 hk
    rw [map_mul, hk1, one_mul]
    rfl
  have hNtop : N = ⊤ := by
    have hperf : commutator Q = ⊤ := hQ.1.commutator_eq_top
    rw [eq_top_iff, ← hperf, _root_.commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsCyclic.commGroup.mul_comm _ _)
  have hQodd : Odd (Nat.card Q) := by
    have : Nat.card N = Nat.card Q := by rw [hNtop]; exact Subgroup.card_top
    rw [← this]; exact hodd
  have hsolv : Group.IsSolvable Q := CFSG.Milestones.odd_order_solvable hQodd
  have : Nontrivial Q := LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hsolv

end CFSG.GH74.Generic
