module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.AutProdAct
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalAlmostSimple

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

open CFSG.OddStandard.AltStdSec.SwapPartner (actQuot actQuot_apply_mk)

theorem mem_centralizer_of_actQuot_eq_one {X : Type*} [Group X] {F : Subgroup X}
    (hF : Group.IsPerfect ↥F) {y : Subgroup.normalizer (F : Set X)} (hy : actQuot F y = 1) :
    (y : X) ∈ Subgroup.centralizer (F : Set X) := by
  haveI : Group.IsPerfect ↥F := hF
  have hdelta : ∀ k : F, F.normalizerMonoidHom y k * k⁻¹ ∈ Subgroup.center F := by
    intro k
    have hquot : (QuotientGroup.mk (F.normalizerMonoidHom y k) :
        F ⧸ Subgroup.center F) = (QuotientGroup.mk k : F ⧸ Subgroup.center F) := by
      rw [← actQuot_apply_mk y k (F.normalizerMonoidHom y k)
        (Subgroup.normalizerMonoidHom_apply_apply_coe F y k), hy]
      rfl
    simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp hquot
  let δ : F →* ↥(Subgroup.center F) :=
    { toFun := fun k => ⟨F.normalizerMonoidHom y k * k⁻¹, hdelta k⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hdelta b
        rw [Subgroup.mem_center_iff] at hb
        simp only [map_mul, mul_inv_rev]
        rw [mul_assoc (F.normalizerMonoidHom y a) (F.normalizerMonoidHom y b)
              (b⁻¹ * a⁻¹),
            ← mul_assoc (F.normalizerMonoidHom y b) b⁻¹ a⁻¹,
            ← hb a⁻¹,
            ← mul_assoc (F.normalizerMonoidHom y a) a⁻¹
              (F.normalizerMonoidHom y b * b⁻¹)]
        rfl }
  have htop : (⊤ : Subgroup F) ≤ δ.ker := by
    rw [← Group.IsPerfect.commutator_eq_top (G := F)]
    change ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ ≤ δ.ker
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext ?_)
    exact (Subgroup.mem_center_iff.mp (δ a).2 (δ b).1).symm
  refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
  have hfix : F.normalizerMonoidHom y ⟨k, hk⟩ = ⟨k, hk⟩ := by
    have hker : δ ⟨k, hk⟩ = 1 := by
      have := htop (Subgroup.mem_top (⟨k, hk⟩ : F))
      rwa [MonoidHom.mem_ker] at this
    exact mul_inv_eq_one.mp (congrArg Subtype.val hker)
  have hconj : (y : X) * k * (y : X)⁻¹ = k := by
    have := congrArg (fun z : F => (z : X)) hfix
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem actQuot_eq_conj_of_mem {X : Type*} [Group X] {F : Subgroup X}
    {y : Subgroup.normalizer (F : Set X)} (hy : (y : X) ∈ F) :
    actQuot F y = MulAut.conj
      (QuotientGroup.mk (⟨y, hy⟩ : ↥F) : ↥F ⧸ Subgroup.center ↥F) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H k =>
    let k' : F := ⟨(y : X) * (k : X) * (y : X)⁻¹,
      F.mul_mem (F.mul_mem hy k.2) (F.inv_mem hy)⟩
    rw [actQuot_apply_mk y k k' rfl, MulAut.conj_apply,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem generalizedFitting_eq_range_conj {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) {W : Subgroup (MulAut S)}
    (hW : (MulAut.conj : S →* MulAut S).range ≤ W) :
    CFSG.generalizedFitting ↥W = (MulAut.conj : S →* MulAut S).range.subgroupOf W :=
  (CFSG.ComponentClassification.SmallLocal.almost_simple_inner_generalized_fitting
    hnc W hW).2.2.2.1

theorem nonempty_generalizedFitting_equiv_of_range_conj_le {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a) {W : Subgroup (MulAut S)}
    (hW : (MulAut.conj : S →* MulAut S).range ≤ W) :
    Nonempty (↥(CFSG.generalizedFitting ↥W) ≃* S) := by
  have h := CFSG.ComponentClassification.SmallLocal.almost_simple_inner_generalized_fitting
    hnc W hW
  rw [h.2.2.2.1]
  exact h.2.2.2.2

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
