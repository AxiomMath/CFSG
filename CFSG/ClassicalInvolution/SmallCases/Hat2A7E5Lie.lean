module

public import CFSG.ClassicalInvolution.Omega
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Card
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7E5Order
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofGLS3Split

public section

namespace CFSG.ClassicalInvolution.Hat2A7E5

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (GLS3OddFamilyInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem false_of_lieModel_of_classical2A7 {t : StatedLieTag} (hF : GLS3OddFamilyInput t)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hQS : ∀ α : MulAut S, α * α = 1 → α ≠ 1 → ∀ L : Subgroup (fixedSubgroup α),
      CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L)
    (hna : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hm : CFSG.Blueprint.LieModel S t n p f)
    {K : Subgroup S} {z : S} (hK : Hat2A7.IsClassical2A7 ⊤ K z) : False := by
  have hz : orderOf z = 2 := hK.orderOf_eq_two
  have hz2 : z * z = 1 := hK.mul_self
  have hzc : z ∉ Subgroup.center S := by
    intro hzc
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hzc
      rw [hzc, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · obtain ⟨a, b, hab⟩ := hna
      exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)
  have hσσ : MulAut.conj z * MulAut.conj z = 1 := by rw [← map_mul, hz2, map_one]
  have hσ1 : MulAut.conj z ≠ 1 := by
    intro h1
    apply hzc
    rw [Subgroup.mem_center_iff]
    intro g
    have h2 := congrArg (fun φ : MulAut S => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * z = (z * g * z⁻¹) * z := by rw [h2]
      _ = z * g := by group
  have hσ2 : orderOf (MulAut.conj z) = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hfix : fixedSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set S) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff]
    change z * x * z⁻¹ = x ↔ x * z = z * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hKC : K ≤ fixedSubgroup (MulAut.conj z) := by
    rw [hfix]
    exact hK.le_centralizer
  have hsub : CFSG.Open.IsSubnormal K (Subgroup.centralizer ({z} : Set S)) := by
    have h1 := hK.subnormal
    rwa [top_inf_eq] at h1
  have hP : CFSG.IsPComponent 2 (K.subgroupOf (fixedSubgroup (MulAut.conj z))) := by
    rw [hfix]
    exact (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).2
      (isTwoComponent_subgroupOf_of_perfect hsub hK.perfect.commutator_eq_top hK.witness.1)
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf (fixedSubgroup (MulAut.conj z))) :=
    hQS (MulAut.conj z) hσσ hσ1 _ hP
  have hcomp : CFSG.IsComponent (K.subgroupOf (fixedSubgroup (MulAut.conj z))) :=
    ⟨hq, hP.choose_spec.2.1⟩
  have hw : A7Witness (K.subgroupOf (fixedSubgroup (MulAut.conj z))) :=
    Hat2A7.A7Witness.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKC).symm hK.witness
  have hcard : Nat.card (↥(K.subgroupOf (fixedSubgroup (MulAut.conj z))) ⧸
      Subgroup.center ↥(K.subgroupOf (fixedSubgroup (MulAut.conj z)))) = 2520 :=
    natCard_center_quotient_of_witness ⟨hq.1.commutator_eq_top, hq.2.1⟩ hw
  rcases hF S n p f hp hp2 hadm hm (MulAut.conj z) hσ2 _ hcomp with
    ⟨τ', n', f', hadm', hm'⟩ | ⟨-, -, hnot, -⟩
  · exact lieModel_odd_card_ne_A7 hO hp2 hadm' hm' hcard
  · exact hnot ⟨z, rfl⟩

end CFSG.ClassicalInvolution.Hat2A7E5
