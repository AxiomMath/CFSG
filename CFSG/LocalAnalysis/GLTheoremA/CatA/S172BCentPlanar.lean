module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem coe_pow_three_eq_one {y : ↥(orthDerived Q)} (hy3 : orderOf y = 3) :
    (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 := by
  have := pow_orderOf_eq_one y
  rw [hy3] at this
  exact congrArg Subtype.val this

theorem layerIs_centralizer_planar (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {y : ↥(orthDerived Q)} (hy3 : orderOf y = 3) {m : ℕ} (hm : 4 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m + 2)
    (hfix : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * m)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
      (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype)) :
    GLALayer (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) =
        (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) ∧
      LayerIs 3 (Subgroup.centralizer ({y} : Set ↥(orthDerived Q))) (isOmMA m 2) := by
  have hy3' := coe_pow_three_eq_one hy3
  have hyO : (y : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup y.2
  have hx := oddOrderIsometry_three hQ hyO hy3'
  have hAq := isQuasisimple_supportedFixedDerived_of_finrank hQ hyO hy3' (by omega)
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) with hD
  have hDq : CFSG.IsQuasisimple ↥D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAΩ).symm hAq
  have hDC : D ≤ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) := fun g hg =>
    mem_centralizer_of_mem_isometryCentralizer
      (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hg))
  have hcomm := commutator_centralizer_le_supportedFixedDerived hQ hy3 (by omega)
  obtain ⟨hlayer, hcomp⟩ := glaLayer_eq_of_commutator_le hDC hcomm hDq
  exact ⟨hlayer, layerIs_of_glaLayer_eq hlayer hcomp
    (catalogIs_pSimple_supportedFixedDerived_minus hQ hy3 hm hfix hminus)⟩

private theorem mem_centralizer_pair_of_mem_supportedFixedDerived_inf
    {y d₂ g : ↥(orthDerived Q)}
    (hgH : g ∈ (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q))
    (hgd : g ∈ Subgroup.centralizer ({d₂} : Set ↥(orthDerived Q))) :
    g ∈ Subgroup.centralizer ({d₂, y} : Set ↥(orthDerived Q)) := by
  have hgy : g ∈ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) :=
    mem_centralizer_of_mem_isometryCentralizer
      (supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.1 hgH))
  rw [Subgroup.mem_centralizer_iff] at hgd hgy ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at hgd hgy ⊢
  exact ⟨hgd, hgy⟩

private theorem layerIs_centralizer_pair_planar_aux (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {y d₂ : ↥(orthDerived Q)} (hy3 : orderOf y = 3) {m : ℕ} (hm : 5 ≤ m)
    (hfix : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * m)
    (hd₂A : (d₂ : V ≃ₗ[ZMod 2] V) ∈ supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V))
    (hd₂3 : orderOf d₂ = 3)
    (hcom : finrank (ZMod 2) ↥(fixedSpace (d₂ : V ≃ₗ[ZMod 2] V) ⊓
      fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2) :
    LayerIs 3 ((supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) ⊓
      Subgroup.centralizer ({d₂} : Set ↥(orthDerived Q))) (isUnA (m - 1) 2) := by
  have hx := oddOrderIsometry_three hQ (orthDerived_le_orthogonalGroup y.2) (coe_pow_three_eq_one hy3)
  have hAΩ : supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V) ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  set H : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) with hH
  have hd₂H : d₂ ∈ H := Subgroup.mem_subgroupOf.2 hd₂A
  let φ : ↥H ≃* ↥(orthDerived (Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype)) :=
    (Subgroup.subgroupOfEquivOfLe hAΩ).trans (restrictDerivedEquiv hx)
  obtain ⟨e⟩ := nonempty_mulEquiv_inf_centralizer φ hd₂H
  set d' := φ ⟨d₂, hd₂H⟩ with hd'
  have hd'3 : orderOf d' = 3 := by
    rw [hd', MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hd₂3]
  have hd'fix : finrank (ZMod 2) (fixedSpace (d' : fixedSpace (y : V ≃ₗ[ZMod 2] V) ≃ₗ[ZMod 2]
      fixedSpace (y : V ≃ₗ[ZMod 2] V))) = 2 := by
    have h := finrank_fixedSpace_restrictDerivedEquiv hx ⟨(d₂ : V ≃ₗ[ZMod 2] V), hd₂A⟩
    rw [hcom] at h
    exact h
  have hLd' := layerIs_centralizer_of_finrank_fixed_two
    (R := Q.comp (fixedSpace (y : V ≃ₗ[ZMod 2] V)).subtype) hx.polarBilin_fixed_nondegenerate hm
    (by omega) hd'3 hd'fix
  exact (layerIs_congr_mulEquiv e).2 hLd'

theorem layerIs_centralizer_pair_planar (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {y d₂ : ↥(orthDerived Q)} (hy3 : orderOf y = 3) {m : ℕ} (hm : 5 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m + 2)
    (hfix : finrank (ZMod 2) (fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2 * m)
    (hd₂A : (d₂ : V ≃ₗ[ZMod 2] V) ∈ supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V))
    (hd₂3 : orderOf d₂ = 3)
    (hcom : finrank (ZMod 2) ↥(fixedSpace (d₂ : V ≃ₗ[ZMod 2] V) ⊓
      fixedSpace (y : V ≃ₗ[ZMod 2] V)) = 2) :
    LayerIs 3 (Subgroup.centralizer ({d₂, y} : Set ↥(orthDerived Q))) (isUnA (m - 1) 2) := by
  have hLH := layerIs_centralizer_pair_planar_aux hQ hy3 hm hfix hd₂A hd₂3 hcom
  set H : Subgroup ↥(orthDerived Q) :=
    (supportedFixedDerived Q (y : V ≃ₗ[ZMod 2] V)).subgroupOf (orthDerived Q) with hH
  set X₂ : Subgroup ↥(orthDerived Q) := Subgroup.centralizer ({d₂, y} : Set ↥(orthDerived Q)) with hX₂
  have hX₂y : X₂ ≤ Subgroup.centralizer ({y} : Set ↥(orthDerived Q)) := Subgroup.centralizer_le (by simp)
  have hX₂d : X₂ ≤ Subgroup.centralizer ({d₂} : Set ↥(orthDerived Q)) := Subgroup.centralizer_le (by simp)
  have hHX : H ⊓ Subgroup.centralizer ({d₂} : Set ↥(orthDerived Q)) ≤ X₂ := fun g hg =>
    mem_centralizer_pair_of_mem_supportedFixedDerived_inf (Subgroup.mem_inf.1 hg).1
      (Subgroup.mem_inf.1 hg).2
  have hcomm : ⁅X₂, X₂⁆ ≤ H ⊓ Subgroup.centralizer ({d₂} : Set ↥(orthDerived Q)) :=
    le_inf ((Subgroup.commutator_mono hX₂y hX₂y).trans
      (commutator_centralizer_le_supportedFixedDerived hQ hy3 (by omega)))
      ((Subgroup.commutator_le_self X₂).trans hX₂d)
  haveI := normal_subgroupOf_of_commutator_le hcomm
  exact layerIs_of_normal_solvable hHX (isSolvable_quotient_of_commutator_le hcomm) hLH

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
