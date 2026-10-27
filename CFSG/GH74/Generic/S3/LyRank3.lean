module

public import CFSG.GH74.GLS.SP.Local.SPLRankTools
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup
open scoped commutatorElement

section

variable {X : Type} [Group X] [Finite X]

theorem rankCertified_one_central_quotient {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    RankCertified (Q ⧸ center Q) 1 :=
  CFSG.GH74.GLS.SP.Local.rankCertified_one_of_quasisimple
    (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hQ le_rfl).1

omit [Finite X] in
theorem mem_center_of_coe_eq_inv {Q : Subgroup X} {c : ↥Q} {u : X} (h : (c : X) = u⁻¹)
    (hu : ∀ g ∈ Q, g * u = u * g) : c ∈ center ↥Q := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : X) * (c : X) = (c : X) * (g : X)
  rw [h]
  exact (Commute.inv_right (show Commute (g : X) u from hu g g.2)).eq

theorem not_gen4_of_three_commuting_quasisimple {A B J : Subgroup X} (hA : IsQuasisimple ↥A)
    (hB : IsQuasisimple ↥B) (hJ : IsQuasisimple ↥J)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAJ : ∀ a ∈ A, ∀ j ∈ J, a * j = j * a)
    (hBJ : ∀ b ∈ B, ∀ j ∈ J, b * j = j * b) : ¬ Gen4 X := by
  intro hX
  have cA := rankCertified_one_central_quotient hA
  have cB := rankCertified_one_central_quotient hB
  have cJ := rankCertified_one_central_quotient hJ
  have cS : RankCertified (((↥A ⧸ center ↥A) × (↥B ⧸ center ↥B)) × (↥J ⧸ center ↥J)) 5 :=
    ((cA.prod cB).prod cJ : RankCertified _ (1 + 1 + 1 + 1 + 1))
  let μ1 : ↥A × ↥B →* X :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun a b => (hAB a a.2 b b.2 : _)
  let μ : (↥A × ↥B) × ↥J →* X :=
    MonoidHom.noncommCoprod μ1 J.subtype fun p j => by
      show (p.1 : X) * (p.2 : X) * (j : X) = (j : X) * ((p.1 : X) * (p.2 : X))
      calc (p.1 : X) * (p.2 : X) * (j : X) = (p.1 : X) * ((p.2 : X) * (j : X)) := by rw [mul_assoc]
        _ = (p.1 : X) * ((j : X) * (p.2 : X)) := by rw [hBJ p.2 p.2.2 j j.2]
        _ = ((p.1 : X) * (j : X)) * (p.2 : X) := by rw [mul_assoc]
        _ = ((j : X) * (p.1 : X)) * (p.2 : X) := by rw [hAJ p.1 p.1.2 j j.2]
        _ = (j : X) * ((p.1 : X) * (p.2 : X)) := by rw [mul_assoc]
  let ψ' : (↥A × ↥B) × ↥J →* ((↥A ⧸ center ↥A) × (↥B ⧸ center ↥B)) × (↥J ⧸ center ↥J) :=
    ((QuotientGroup.mk' (center ↥A)).prodMap (QuotientGroup.mk' (center ↥B))).prodMap
      (QuotientGroup.mk' (center ↥J))
  have hkernel : μ.rangeRestrict.ker ≤ ψ'.ker := by
    rintro ⟨⟨a, b⟩, j⟩ hk
    have h1 : (a : X) * (b : X) * (j : X) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      exact h
    have ha : a ∈ center ↥A := by
      refine mem_center_of_coe_eq_inv (u := (b : X) * (j : X))
        (eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)) fun g hg => ?_
      calc g * ((b : X) * (j : X)) = (g * (b : X)) * (j : X) := by rw [mul_assoc]
        _ = ((b : X) * g) * (j : X) := by rw [hAB g hg b b.2]
        _ = (b : X) * (g * (j : X)) := by rw [mul_assoc]
        _ = (b : X) * ((j : X) * g) := by rw [hAJ g hg j j.2]
        _ = ((b : X) * (j : X)) * g := by rw [mul_assoc]
    have hb : b ∈ center ↥B := by
      have hbj : (a : X) * (j : X) * (b : X) = 1 := by
        calc (a : X) * (j : X) * (b : X) = (a : X) * ((j : X) * (b : X)) := by rw [mul_assoc]
          _ = (a : X) * ((b : X) * (j : X)) := by rw [← hBJ b b.2 j j.2]
          _ = 1 := by rw [← mul_assoc]; exact h1
      refine mem_center_of_coe_eq_inv (u := (a : X) * (j : X)) (eq_inv_of_mul_eq_one_right hbj)
        fun g hg => ?_
      calc g * ((a : X) * (j : X)) = (g * (a : X)) * (j : X) := by rw [mul_assoc]
        _ = ((a : X) * g) * (j : X) := by rw [← hAB a a.2 g hg]
        _ = (a : X) * (g * (j : X)) := by rw [mul_assoc]
        _ = (a : X) * ((j : X) * g) := by rw [hBJ g hg j j.2]
        _ = ((a : X) * (j : X)) * g := by rw [mul_assoc]
    have hj : j ∈ center ↥J := by
      refine mem_center_of_coe_eq_inv (u := (a : X) * (b : X)) (eq_inv_of_mul_eq_one_right h1)
        fun g hg => ?_
      calc g * ((a : X) * (b : X)) = (g * (a : X)) * (b : X) := by rw [mul_assoc]
        _ = ((a : X) * g) * (b : X) := by rw [← hAJ a a.2 g hg]
        _ = (a : X) * (g * (b : X)) := by rw [mul_assoc]
        _ = (a : X) * ((b : X) * g) := by rw [← hBJ b b.2 g hg]
        _ = ((a : X) * (b : X)) * g := by rw [mul_assoc]
    rw [MonoidHom.mem_ker]
    have : ψ' ((a, b), j) = (((QuotientGroup.mk a : ↥A ⧸ center ↥A),
        (QuotientGroup.mk b : ↥B ⧸ center ↥B)), (QuotientGroup.mk j : ↥J ⧸ center ↥J)) := rfl
    rw [this, (QuotientGroup.eq_one_iff a).2 ha, (QuotientGroup.eq_one_iff b).2 hb,
      (QuotientGroup.eq_one_iff j).2 hj]
    rfl
  let ψ := (MonoidHom.liftOfSurjective μ.rangeRestrict μ.rangeRestrict_surjective) ⟨ψ', hkernel⟩
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨⟨a, b⟩, j⟩
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨j', rfl⟩ := QuotientGroup.mk_surjective j
    exact ⟨((a', b'), j'), rfl⟩
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨k, rfl⟩ := hψ' s
    exact ⟨μ.rangeRestrict k, by simp [ψ]⟩
  have : Finite ↥μ.range := inferInstance
  exact (cS.of_surjective ψ hψ).of_subgroup.not_gen4 (by norm_num) hX

end

end CFSG.GH74.Generic.S3
