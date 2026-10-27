module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUTransfer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup CFSG.ASVolI.ChIJK
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn)

theorem centralizer_singleton_eq_fixedSubgroup {Y : Type} [Group Y] (v : Y) :
    Subgroup.centralizer ({v} : Set Y) = fixedSubgroup (MulAut.conj v) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change x * v = v * x ↔ MulAut.conj v x = x
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul, eq_comm]

theorem orderOf_conj_eq_two {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) {v : Y} (hv : orderOf v = 2) :
    orderOf (MulAut.conj v) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hv, pow_orderOf_eq_one]
    exact map_one _
  · intro h1
    have hc : v ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun φ : MulAut Y => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hc
      rw [hc, orderOf_one] at hv
      omega
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center Y := ht ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm

theorem exists_component_fixedSubgroup {Y : Type} [Group Y] {v : Y} {C : Subgroup Y}
    (hC : IsComponentIn C (Subgroup.centralizer ({v} : Set Y))) :
    ∃ Kc : Subgroup (fixedSubgroup (MulAut.conj v)), IsComponent Kc ∧ Nonempty (↥C ≃* ↥Kc) := by
  obtain ⟨hle, hq, hsub⟩ := hC
  have heq := centralizer_singleton_eq_fixedSubgroup v
  have hK : IsComponent (C.subgroupOf (Subgroup.centralizer ({v} : Set Y))) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq, hsub⟩
  let e : ↥(Subgroup.centralizer ({v} : Set Y)) ≃* ↥(fixedSubgroup (MulAut.conj v)) :=
    MulEquiv.subgroupCongr heq
  refine ⟨(C.subgroupOf (Subgroup.centralizer ({v} : Set Y))).map e.toMonoidHom,
    LocalCores.isComponent_map_mulEquiv e hK, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe hle).symm.trans
    ((C.subgroupOf (Subgroup.centralizer ({v} : Set Y))).equivMapOfInjective e.toMonoidHom
      e.injective)

theorem exists_noncommuting_of_isComponentIn {Y : Type} [Group Y] {X C : Subgroup Y}
    (hC : IsComponentIn C X) : ∃ a b : Y, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hC.2.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a', b', fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h

theorem isComponentIn_modelIn_psl {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {p n r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel Y .PSL n p r) {v : Y}
    (hv : orderOf v = 2) {C : Subgroup Y} (hC : IsComponentIn C (Subgroup.centralizer {v})) :
    ModelIn p (luLinTuples n r) C := by
  obtain ⟨Kc, hKc, ⟨e⟩⟩ := exists_component_fixedSubgroup hC
  have hv' := orderOf_conj_eq_two (exists_noncommuting_of_isComponentIn hC) hv
  exact (psl_inner_modelIn hp hp2 hm.admissible hm hv' hKc).of_mulEquiv e

theorem isComponentIn_modelIn_psu {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {p n r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel Y .PSU n p r) {v : Y}
    (hv : orderOf v = 2) {C : Subgroup Y} (hC : IsComponentIn C (Subgroup.centralizer {v})) :
    ModelIn p (luUniTuples n r) C := by
  obtain ⟨Kc, hKc, ⟨e⟩⟩ := exists_component_fixedSubgroup hC
  have hv' := orderOf_conj_eq_two (exists_noncommuting_of_isComponentIn hC) hv
  exact (psu_inner_modelIn hp2 hm.admissible hm hv' hKc).of_mulEquiv e

theorem linUnitInvolutionComponents_holds : F3.LinUnitInvolutionComponents := by
  unfold F3.LinUnitInvolutionComponents
  intro Y _ _ _ p n r hp hp2 hm v hv C hC
  rcases hm with hm | hm
  · exact exists_lieModel_of_modelIn (fun x hx => Or.inl (luLinTuples_fst hx))
      (isComponentIn_modelIn_psl hp hp2 hm hv hC)
  · exact exists_lieModel_of_modelIn (fun x hx => (luUniTuples_fst hx).symm)
      (isComponentIn_modelIn_psu hp hp2 hm hv hC)

end CFSG.OddStandard.HigherRank.LinUnit
