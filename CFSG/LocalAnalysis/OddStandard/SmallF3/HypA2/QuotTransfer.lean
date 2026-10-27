module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotAux
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.Walter.Bender1970.S2.Inner

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private noncomputable def descCenter (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun σ := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) σ
    (Subgroup.map_center_eq σ)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y => rfl
  map_mul' σ τ := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H z =>
      simp only [map_mul, MulAut.mul_apply]
      rfl

theorem exists_properFixedComponent_quotient {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) {σ : MulAut K} (hσ : ∀ y, σ (σ y) = y) {X : Subgroup K}
    (hXF : X ≤ fixedSubgroup σ) (hX : IsPComponent 2 (X.subgroupOf (fixedSubgroup σ)))
    (hXtop : X ≠ ⊤) :
    ∃ (σ' : MulAut (K ⧸ center K)) (P : Subgroup (K ⧸ center K)),
      CatLeaf.ProperFixedComponent σ' P ∧
        Nonempty (↥X ⧸ Open.fusionZStar ↥X ≃* ↥P ⧸ Open.fusionZStar ↥P) := by
  let σ' : MulAut (K ⧸ center K) := descCenter K σ
  let C : Subgroup (K ⧸ center K) := (fixedSubgroup σ).map (QuotientGroup.mk' (center K))
  let P : Subgroup (K ⧸ center K) := X.map (QuotientGroup.mk' (center K))
  have hσ_comp : σ * σ = 1 := by
    ext y
    exact hσ y
  have hσ'2 : σ' * σ' = 1 := by
    show descCenter K σ * descCenter K σ = 1
    rw [← map_mul (descCenter K) σ σ, hσ_comp, map_one (descCenter K)]
  have hσ' : ∀ y, σ' (σ' y) = y := by
    intro y
    have h := congrArg (fun e : MulAut (K ⧸ center K) => e y) hσ'2
    simpa using h
  have hcomm : ∀ x, (QuotientGroup.mk' (center K)) (σ x) =
      σ' ((QuotientGroup.mk' (center K)) x) := by
    intro x
    show QuotientGroup.mk' (center K) (σ x) =
      QuotientGroup.congr (center K) (center K) σ (Subgroup.map_center_eq σ)
        (QuotientGroup.mk' (center K) x)
    rw [QuotientGroup.congr_mk']
  have hkerZ : (QuotientGroup.mk' (center K)).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
  have hCnorm : (C.subgroupOf (fixedSubgroup σ')).Normal :=
    CFSG.LocalAnalysis.ComponentInitial.fixedImage_normal hkerZ
      (QuotientGroup.mk'_surjective (center K)) hσ hcomm
  have hCA : C ≤ fixedSubgroup σ' := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
    rw [← hcomm x, CFSG.LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff.mp hx]
  have hX2 : HarrisLit.IsTwoComponentIn X (fixedSubgroup σ) :=
    (HarrisLit.isTwoComponentIn_iff hXF).mpr hX
  have hXsub : (X.subgroupOf (fixedSubgroup σ)).IsSubnormal := hX2.2.1
  have hXrel : CFSG.Assembly.IsSubnormal X (fixedSubgroup σ) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hXF).2 hXsub
  have hPrel : CFSG.Assembly.IsSubnormal P C :=
    CFSG.Assembly.IsSubnormal.map (QuotientGroup.mk' (center K)) hXrel
  have hCrel : CFSG.Assembly.IsSubnormal C (fixedSubgroup σ') :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hCA).2 hCnorm.isSubnormal
  have hPArel : CFSG.Assembly.IsSubnormal P (fixedSubgroup σ') :=
    CFSG.Assembly.IsSubnormal.trans hPrel hCrel
  have hPF : P ≤ fixedSubgroup σ' := CFSG.Assembly.IsSubnormal.le hPArel
  have hPsub : (P.subgroupOf (fixedSubgroup σ')).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hPF).1 hPArel
  let f : ↥X →* ↥P := (QuotientGroup.mk' (center K)).subgroupMap X
  have hf : Function.Surjective f :=
    MonoidHom.subgroupMap_surjective (QuotientGroup.mk' (center K)) X
  have hker : f.ker ≤ Subgroup.center ↥X := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : K) * (z : K) = (z : K) * (y : K)
    have hzK : (z : K) ∈ Subgroup.center K := by
      have hz1 : (QuotientGroup.mk' (center K)) (z : K) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
      exact (QuotientGroup.eq_one_iff (z : K)).mp hz1
    exact Subgroup.mem_center_iff.mp hzK (y : K)
  have hQuasi := central_quotient_two_quasisimple f hf hker hX2.2.2
  have hTwoQuasi : HarrisLit.IsTwoQuasisimple ↥P := hQuasi.1
  have hPcomp : IsPComponent 2 (P.subgroupOf (fixedSubgroup σ')) :=
    (HarrisLit.isTwoComponentIn_iff hPF).mp ⟨hPF, hPsub, hTwoQuasi⟩
  have hPtop : P ≠ ⊤ := by
    intro htop
    have hZX : Subgroup.center K ⊔ X = ⊤ := by
      have h1 := QuotientGroup.comap_map_mk' (center K) X
      rw [show X.map (QuotientGroup.mk' (center K)) = ⊤ from htop,
        Subgroup.comap_top] at h1
      exact h1.symm
    have hXsup : X ⊔ Subgroup.center K = ⊤ := by
      rw [sup_comm]
      exact hZX
    have hXeq : X = ⊤ :=
      CFSG.Walter.eq_top_of_sup_center_eq_top hK.1.commutator_eq_top hXsup
    exact hXtop hXeq
  exact ⟨σ', P, ⟨hσ', hPF, hPcomp, hPtop⟩, hQuasi.2⟩

end CFSG.OddStandard.SmallF3.HypA2
