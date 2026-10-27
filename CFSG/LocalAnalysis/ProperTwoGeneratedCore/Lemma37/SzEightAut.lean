module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverNorm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

variable {X : Type*} [Group X] (J : Subgroup X) [J.Normal]

@[expose] noncomputable def quotientConj : X →* MulAut (J ⧸ Subgroup.center J) where
  toFun x := centralQuotientAut (MulAut.conjNormal x)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H k => rw [centralQuotientAut_mk, map_one]; rfl
  map_mul' x y := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H k => rw [MulAut.mul_apply, centralQuotientAut_mk, centralQuotientAut_mk,
        centralQuotientAut_mk, map_mul, MulAut.mul_apply]

theorem quotientConj_mk (x : X) (k : J) :
    quotientConj J x (k : J ⧸ Subgroup.center J) =
      ((MulAut.conjNormal x k : J) : J ⧸ Subgroup.center J) :=
  centralQuotientAut_mk _ k

variable {J}

theorem conj_injective_of_center_eq_bot {Y : Type*} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  have h := DFunLike.congr_fun ha g
  rw [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * a = a * g * a⁻¹ * a := by rw [h]
    _ = a * g := by group

variable (hodd : Odd (Nat.card (Outer (J ⧸ Subgroup.center J))))
  (hZ : Subgroup.center (J ⧸ Subgroup.center J) = ⊥) (P : Subgroup X) (hP : IsPGroup 2 P)

include hodd hP in
theorem quotientConj_mem_inner (w : P) :
    quotientConj J w ∈ (MulAut.conj : (J ⧸ Subgroup.center J) →* _).range :=
  HighRankPair.le_inner_of_isPGroup_two hodd _ (hP.map (quotientConj J))
    ⟨w, w.2, rfl⟩

@[expose] noncomputable def innerPart : P →* J ⧸ Subgroup.center J :=
  (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).symm.toMonoidHom.comp
    (((quotientConj J).comp P.subtype).codRestrict _
      (quotientConj_mem_inner hodd P hP))

theorem conj_innerPart (w : P) :
    MulAut.conj (innerPart hodd hZ P hP w) = quotientConj J w := by
  rw [← MonoidHom.ofInjective_apply (conj_injective_of_center_eq_bot hZ)]
  simp only [innerPart, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]
  rfl

theorem innerPart_conj_mk (w : P) (k : J) :
    innerPart hodd hZ P hP w * (k : J ⧸ Subgroup.center J) * (innerPart hodd hZ P hP w)⁻¹ =
      ((MulAut.conjNormal (w : X) k : J) : J ⧸ Subgroup.center J) := by
  rw [← quotientConj_mk, ← conj_innerPart hodd hZ P hP w, MulAut.conj_apply]

theorem innerPart_eq_mk (w : P) (hw : (w : X) ∈ J) :
    innerPart hodd hZ P hP w = ((⟨w, hw⟩ : J) : J ⧸ Subgroup.center J) := by
  apply conj_injective_of_center_eq_bot hZ
  rw [conj_innerPart]
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [quotientConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

theorem mem_centralizer_of_innerPart_eq_one (hperf : commutator J = ⊤) (w : P)
    (h : innerPart hodd hZ P hP w = 1) :
    (w : X) ∈ Subgroup.centralizer (J : Set X) := by
  have hc : ∀ k : J, (MulAut.conjNormal (w : X) k : J) = k := by
    intro k
    have h1 := eq_conj_of_perfect hperf (MulAut.conjNormal (w : X)).toMonoidHom 1 (fun k => by
      have h2 := innerPart_conj_mk hodd hZ P hP w k
      rw [h, one_mul, inv_one, mul_one] at h2
      rw [MulEquiv.coe_toMonoidHom, ← h2, one_mul, inv_one, mul_one]) k
    simpa using h1
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := congrArg Subtype.val (hc ⟨k, hk⟩)
  rw [MulAut.conjNormal_apply] at h1
  calc k * (w : X) = (w : X) * k * (w : X)⁻¹ * w := by rw [h1]
    _ = w * k := by group

theorem innerPart_mem_sylow (Q : Sylow 2 (J ⧸ Subgroup.center J))
    (hQ : (Q : Subgroup (J ⧸ Subgroup.center J)) ≤ (innerPart hodd hZ P hP).range) (w : P) :
    innerPart hodd hZ P hP w ∈ (Q : Subgroup (J ⧸ Subgroup.center J)) := by
  have hR : IsPGroup 2 (innerPart hodd hZ P hP).range := by
    rw [MonoidHom.range_eq_map]
    exact (hP.of_equiv (Subgroup.topEquiv).symm).map _
  rw [← Q.is_maximal' hR hQ]
  exact ⟨w, rfl⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
