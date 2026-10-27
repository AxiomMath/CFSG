module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaMt0b
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.EtaOuterA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CentreFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CompatCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.GriessLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.InnerLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.LiftSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.NoInvolution

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.ML1
  CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog

variable {C : Type} [Group C] [Finite C] {Q : Subgroup C} [hQn : Q.Normal]

theorem AschbacherHyp.exists_field_aut (hC : AschbacherHyp C Q) :
    ∃ (e : C ⧸ Q ≃* A5WrTwo) (θ : ↥(commutator C) →* A5 × A5)
      (f : ↥(commutator C) ≃* ↥(commutator C)) (c χ : A5 ≃* A5),
      Function.Surjective θ ∧ (∀ l : ↥(commutator C), θ l = 1 ↔ (l : C) ∈ Q) ∧
      (∀ l : ↥(commutator C), A5WrTwo.baseEmb (θ l) = e (QuotientGroup.mk (l : C))) ∧
      (¬ ∃ p : A5, ∀ y : A5, c y = p * y * p⁻¹) ∧
      ∀ l : ↥(commutator C), θ (f l) = (c (θ l).1, χ (θ l).2) := by
  classical
  haveI : Finite Q := hC.plus.finite
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q); infer_instance
  obtain ⟨e, θ, σ, hθs, hθk, hθb, hσθ, hσi, hirr⟩ := hC.exists_hom_baseEmb
  have hq : ∀ g u, extraspecialQuadForm hE (σ g u) = extraspecialQuadForm hE u := by
    intro g u
    obtain ⟨l, rfl⟩ := hθs g
    rw [hσθ l]
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (conjLinEquiv_mem hE hQn (l : C))) u
  have hS : Swap.StdHyp σ := ⟨hσi, by rw [hC.plus.finrank_quotient], hirr⟩
  obtain ⟨c, hc⟩ := exists_outer_aut
  obtain ⟨a, χ, haq, haσ⟩ := exists_isometry_twist (extraspecialQuadForm hE)
    (extraspecialQuadForm_nondegenerate hE) σ hS hq (MulEquiv.prodCongr c (MulEquiv.refl A5))
  let ψ : A5 × A5 ≃* A5 × A5 := MulEquiv.prodCongr c χ
  have haσ' : ∀ g u, a (σ g u) = σ (ψ g) (a u) := fun g u => haσ g.1 g.2 u
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_of_isometry hE hE a haq
  have hK : Q ≤ commutator C := hC.le_commutator
  have hint : ∀ (l l' : ↥(commutator C)), θ l' = ψ (θ l) →
      ∀ v, a (conjLinEquiv hQn (l : C) v) = conjLinEquiv hQn (l' : C) (a v) := by
    intro l l' hl' v
    rw [← hσθ l, ← hσθ l', hl', haσ']
  obtain ⟨z, hzQ, hz1, hzc, hzcentre⟩ := hC.exists_centre
  have hne : ∀ l : ↥(commutator C), InnerInv (θ l) → l ^ 2 ≠ 1 := fun l hl =>
    hC.sq_ne_one_of_innerInv e θ hθs hθb l hl
  haveI : (Q.subgroupOf (commutator C)).Normal := inferInstance
  have hcore : CoreHyp (Q.subgroupOf (commutator C)) (Q.subgroupOf (commutator C)) θ θ ψ
      (liftSub hK hK φ₀) ⟨z, hK hzQ⟩ :=
    { surj := hθs
      surj' := hθs
      ker := fun l => (hθk l).trans Subgroup.mem_subgroupOf.symm
      ker' := fun l => (hθk l).trans Subgroup.mem_subgroupOf.symm
      iso := isSubIso_liftSub hK hK φ₀
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
        obtain ⟨l₀, hl₀⟩ := hθs (ψ (θ l))
        have hcen := compat_central hE a φ₀ hφ₀ (l : C) (l₀ : C) (hint l l₀ hl₀)
        obtain ⟨q, hqc⟩ := exists_conj_compat hE φ₀ (l : C) (l₀ : C) hcen
        refine ⟨⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩, ?_, ?_⟩
        · have hqθ : θ ⟨(q : C), hK q.2⟩ = 1 := (hθk _).mpr q.2
          have : (⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩ :
              ↥(commutator C)) = ⟨(q : C), hK q.2⟩ * l₀ := rfl
          rw [this, map_mul, hqθ, one_mul, hl₀]
        · exact (compat_liftSub_iff hK hK φ₀ l _).mpr hqc
      exists_compat' := fun l' => by
        obtain ⟨l₀, hl₀⟩ := hθs (ψ.symm (θ l'))
        have hl₀' : θ l' = ψ (θ l₀) := by rw [hl₀, MulEquiv.apply_symm_apply]
        have hcen := compat_central hE a φ₀ hφ₀ (l₀ : C) (l' : C) (hint l₀ l' hl₀')
        obtain ⟨q, hqc⟩ := exists_conj_compat' hE φ₀ (l₀ : C) (l' : C) hcen
        refine ⟨⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩, ?_, ?_⟩
        · have hqθ : θ ⟨(q : C), hK q.2⟩ = 1 := (hθk _).mpr q.2
          have : (⟨(q : C) * (l₀ : C), (commutator C).mul_mem (hK q.2) l₀.2⟩ :
              ↥(commutator C)) = ⟨(q : C), hK q.2⟩ * l₀ := rfl
          rw [this, map_mul, hqθ, one_mul, hl₀']
        · exact (compat_liftSub_iff hK hK φ₀ _ l').mpr hqc
      inner_sq_ne := hne
      inner_sq_ne' := hne
      inner_exists := fun l hl => by
        obtain ⟨q, hqQ, hq2⟩ := hC.exists_mul_mem_sq_eq θ σ hθk hσθ hσi hirr hzQ hzcentre hne l hl
        exact ⟨⟨q, hK hqQ⟩, Subgroup.mem_subgroupOf.mpr hqQ, Subtype.ext (by simpa using hq2)⟩ }
  obtain ⟨f, hf⟩ := exists_mulEquiv_of_coreHyp hcore
  exact ⟨e, θ, f, c, χ, hθs, hθk, hθb, hc, fun l => by rw [hf l]; rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
