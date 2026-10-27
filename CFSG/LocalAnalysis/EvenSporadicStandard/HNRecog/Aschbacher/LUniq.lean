module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.MT0b
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GriessLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.LiftSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CentreFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.NoInvolution
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.InnerLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.ML1

variable {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C'] {Q : Subgroup C}
  {Q' : Subgroup C'} [hQn : Q.Normal] [hQn' : Q'.Normal]

theorem AschbacherHyp.nonempty_mulEquiv_commutator (hC : AschbacherHyp C Q)
    (hC' : AschbacherHyp C' Q') : Nonempty (↥(commutator C) ≃* ↥(commutator C')) := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q); infer_instance
  haveI : Finite Q' := hC'.plus.finite
  have hE' : IsExtraspecialPGroup 2 Q' := hC'.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q')) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE'
  haveI : Finite (Additive (Abelianization Q')) := by
    change Finite (Q' ⧸ _root_.commutator Q'); infer_instance
  obtain ⟨e, θ, σ, hθs, hθk, hθb, hσθ, hσi, hirr⟩ := hC.exists_hom_baseEmb
  obtain ⟨e', θ', σ', hθs', hθk', hθb', hσθ', hσi', hirr'⟩ := hC'.exists_hom_baseEmb
  have hq : ∀ g u, extraspecialQuadForm hE (σ g u) = extraspecialQuadForm hE u := by
    intro g u
    obtain ⟨l, rfl⟩ := hθs g
    rw [hσθ l]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (conjLinEquiv_mem hE hQn (l : C))) u
  have hq' : ∀ g u, extraspecialQuadForm hE' (σ' g u) = extraspecialQuadForm hE' u := by
    intro g u
    obtain ⟨l, rfl⟩ := hθs' g
    rw [hσθ' l]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (conjLinEquiv_mem hE' hQn' (l : C'))) u
  have hS : Swap.StdHyp σ := ⟨hσi, by rw [hC.plus.finrank_quotient], hirr⟩
  have hS' : Swap.StdHyp σ' := ⟨hσi', by rw [hC'.plus.finrank_quotient], hirr'⟩
  obtain ⟨a, ψ, haq, haσ⟩ := mt0b (extraspecialQuadForm hE) (extraspecialQuadForm hE')
    (extraspecialQuadForm_nondegenerate hE) (extraspecialQuadForm_nondegenerate hE') σ σ' hS hS' hq hq'
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_of_isometry hE hE' a haq
  have hK : Q ≤ commutator C := hC.le_commutator
  have hK' : Q' ≤ commutator C' := hC'.le_commutator
  have hint : ∀ (l : ↥(commutator C)) (l' : ↥(commutator C')), θ' l' = ψ (θ l) →
      ∀ v, a (conjLinEquiv hQn (l : C) v) = conjLinEquiv hQn' (l' : C') (a v) := by
    intro l l' hl' v
    rw [← hσθ l, ← hσθ' l', hl', haσ]
  obtain ⟨z, hzQ, hz1, hzc, hzcentre⟩ := hC.exists_centre
  have hne : ∀ l : ↥(commutator C), InnerInv (θ l) → l ^ 2 ≠ 1 := fun l hl =>
    hC.sq_ne_one_of_innerInv e θ hθs hθb l hl
  have hne' : ∀ l : ↥(commutator C'), InnerInv (θ' l) → l ^ 2 ≠ 1 := fun l hl =>
    hC'.sq_ne_one_of_innerInv e' θ' hθs' hθb' l hl
  haveI : (Q.subgroupOf (commutator C)).Normal := inferInstance
  refine CoreHyp.nonempty_mulEquiv (N := Q.subgroupOf (commutator C))
    (N' := Q'.subgroupOf (commutator C')) (θ := θ) (θ' := θ') (ψ := ψ)
    (φ := liftSub hK hK' φ₀) (z := ⟨z, hK hzQ⟩) ?_
  exact
    { surj := hθs
      surj' := hθs'
      ker := fun l => (hθk l).trans Subgroup.mem_subgroupOf.symm
      ker' := fun l => (hθk' l).trans Subgroup.mem_subgroupOf.symm
      iso := isSubIso_liftSub hK hK' φ₀
      pgroup := fun x hx => by
        obtain ⟨k, hk⟩ := hC.exists_pow_two_pow_eq_one (x : C) (Subgroup.mem_subgroupOf.mp hx)
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
      z_mem := Subgroup.mem_subgroupOf.mpr hzQ
      z_ne_one := fun h => hz1 (congrArg Subtype.val h)
      z_central := fun l => Subtype.ext (hzc (l : C))
      centre := fun x hx hcomm => by
        have := hzcentre (x : C) (Subgroup.mem_subgroupOf.mp hx) (fun y hy =>
          congrArg Subtype.val (hcomm ⟨y, hK hy⟩ (Subgroup.mem_subgroupOf.mpr hy)))
        rcases this with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      exists_compat := fun l => by
        obtain ⟨l₀, hl₀⟩ := hθs' (ψ (θ l))
        have hcen := compat_central hE' a φ₀ hφ₀ (l : C) (l₀ : C') (hint l l₀ hl₀)
        obtain ⟨q, hqc⟩ := exists_conj_compat hE' φ₀ (l : C) (l₀ : C') hcen
        refine ⟨⟨(q : C') * (l₀ : C'), (commutator C').mul_mem (hK' q.2) l₀.2⟩, ?_, ?_⟩
        · have hqθ : θ' ⟨(q : C'), hK' q.2⟩ = 1 := (hθk' _).mpr q.2
          have : (⟨(q : C') * (l₀ : C'), (commutator C').mul_mem (hK' q.2) l₀.2⟩ :
              ↥(commutator C')) = ⟨(q : C'), hK' q.2⟩ * l₀ := rfl
          rw [this, map_mul, hqθ, one_mul, hl₀]
        · exact (compat_liftSub_iff hK hK' φ₀ l _).mpr hqc
      exists_compat' := fun l' => by
        obtain ⟨l₀, hl₀⟩ := hθs (ψ.symm (θ' l'))
        have hl₀' : θ' l' = ψ (θ l₀) := by rw [hl₀, MulEquiv.apply_symm_apply]
        have hcen := compat_central hE' a φ₀ hφ₀ (l₀ : C) (l' : C') (hint l₀ l' hl₀')
        obtain ⟨q, hqc⟩ := exists_conj_compat' hE φ₀ (l₀ : C) (l' : C') hcen
        refine ⟨⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩, ?_, ?_⟩
        · have hqθ : θ ⟨(q : C), hK q.2⟩ = 1 := (hθk _).mpr q.2
          have : (⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩ :
              ↥(commutator C)) = ⟨(q : C), hK q.2⟩ * l₀ := rfl
          rw [this, map_mul, hqθ, one_mul, hl₀']
        · exact (compat_liftSub_iff hK hK' φ₀ _ l').mpr hqc
      inner_sq_ne := hne
      inner_sq_ne' := hne'
      inner_exists := fun l hl => by
        obtain ⟨q, hqQ, hq2⟩ := hC.exists_mul_mem_sq_eq θ σ hθk hσθ hσi hirr hzQ hzcentre hne l hl
        exact ⟨⟨q, hK hqQ⟩, Subgroup.mem_subgroupOf.mpr hqQ, Subtype.ext (by simpa using hq2)⟩ }

end CFSG.EvenSporadicStandard.HNRecog
