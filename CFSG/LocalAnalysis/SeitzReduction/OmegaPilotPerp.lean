module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusCentralizer
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open scoped commutatorElement
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace omegaGroup mem_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Split

variable (K : Type*) [Field K] {ι : Type*} [DecidableEq ι]

@[expose] def perpSub (a b : ι) : Submodule K (ι → K) where
  carrier := {v | v a = 0 ∧ v b = 0}
  add_mem' := by
    rintro v w ⟨hva, hvb⟩ ⟨hwa, hwb⟩
    exact ⟨by simp [hva, hwa], by simp [hvb, hwb]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c v ⟨hva, hvb⟩
    exact ⟨by simp [hva], by simp [hvb]⟩

@[expose] def planeSub (a b : ι) : Submodule K (ι → K) where
  carrier := {v | ∀ i, i ≠ a → i ≠ b → v i = 0}
  add_mem' := by
    intro v w hv hw i hia hib
    simp [hv i hia hib, hw i hia hib]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := by
    intro c v hv i hia hib
    simp [hv i hia hib]

variable {K} {a b : ι}

omit [DecidableEq ι] in
theorem mem_perpSub {v : ι → K} : v ∈ perpSub K a b ↔ v a = 0 ∧ v b = 0 := Iff.rfl

omit [DecidableEq ι] in
theorem mem_planeSub {v : ι → K} : v ∈ planeSub K a b ↔ ∀ i, i ≠ a → i ≠ b → v i = 0 :=
  Iff.rfl

theorem perpPart_mem (hab : a ≠ b) (v : ι → K) : perpPart a b v ∈ perpSub K a b :=
  ⟨perpPart_apply_left hab v, perpPart_apply_right hab v⟩

theorem planePart_mem (v : ι → K) :
    v a • Pi.single a 1 + v b • Pi.single b 1 ∈ planeSub K a b := by
  intro i hia hib
  simp [hia, hib]

theorem perpPart_add_planePart (v : ι → K) :
    perpPart a b v + (v a • Pi.single a 1 + v b • Pi.single b 1) = v := by
  simp only [perpPart]
  abel

theorem eq_planePart_of_mem (hab : a ≠ b) {w : ι → K} (hw : w ∈ planeSub K a b) :
    w = w a • Pi.single a 1 + w b • Pi.single b 1 := by
  ext i
  by_cases hia : i = a
  · subst hia
    simp [hab]
  · by_cases hib : i = b
    · subst hib
      simp [hia]
    · simp [hw i hia hib, hia, hib]

theorem isCompl_perpSub_planeSub (hab : a ≠ b) : IsCompl (perpSub K a b) (planeSub K a b) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv hw
    ext i
    by_cases hia : i = a
    · subst hia
      exact hv.1
    · by_cases hib : i = b
      · subst hib
        exact hv.2
      · exact hw i hia hib
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    exact Submodule.mem_sup.mpr ⟨_, perpPart_mem hab v, _, planePart_mem v,
      perpPart_add_planePart v⟩

end Split

section Extend

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {a b : ι}

open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv)

@[expose] noncomputable def extendLin (hab : a ≠ b) :
    (perpSub K a b ≃ₗ[K] perpSub K a b) →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun g := glue (isCompl_perpSub_planeSub hab) g 1
  map_one' := glue_one _
  map_mul' g g' := by
    rw [← glue_mul, one_mul]

theorem extendLin_apply (hab : a ≠ b) (g : perpSub K a b ≃ₗ[K] perpSub K a b) (v : ι → K) :
    extendLin hab g v = (g ⟨perpPart a b v, perpPart_mem hab v⟩ : ι → K) +
      (v a • Pi.single a 1 + v b • Pi.single b 1) := by
  have h := glue_apply (isCompl_perpSub_planeSub hab) g 1 ⟨perpPart a b v, perpPart_mem hab v⟩
    ⟨_, planePart_mem v⟩
  simp only [perpPart_add_planePart] at h
  exact h

theorem extendLin_apply_perp (hab : a ≠ b) (g : perpSub K a b ≃ₗ[K] perpSub K a b)
    (u : perpSub K a b) : extendLin hab g u = g u := by
  have h := glue_apply (isCompl_perpSub_planeSub hab) g 1 u 0
  simp only [Submodule.coe_zero, add_zero, map_zero] at h
  exact h

theorem extendLin_apply_plane (hab : a ≠ b) (g : perpSub K a b ≃ₗ[K] perpSub K a b)
    {w : ι → K} (hw : w ∈ planeSub K a b) : extendLin hab g w = w := by
  have h := glue_apply (isCompl_perpSub_planeSub hab) g 1 0 ⟨w, hw⟩
  simp only [Submodule.coe_zero, zero_add, map_zero, LinearEquiv.coe_one, id_eq] at h
  exact h

theorem single_left_mem_planeSub : (Pi.single a (1 : K)) ∈ planeSub K a b := by
  intro i hia _
  simp [hia]

theorem single_right_mem_planeSub : (Pi.single b (1 : K)) ∈ planeSub K a b := by
  intro i _ hib
  simp [hib]

theorem extendLin_mem_stabSub (hab : a ≠ b) (g : perpSub K a b ≃ₗ[K] perpSub K a b) :
    extendLin hab g ∈ stabSub a b :=
  ⟨extendLin_apply_plane hab g single_left_mem_planeSub,
    extendLin_apply_plane hab g single_right_mem_planeSub⟩

variable {Q : QuadraticForm K (ι → K)}

theorem IsHypCoord.extendLin_mem_orthogonalGroup (h : IsHypCoord Q a b)
    {g : perpSub K a b ≃ₗ[K] perpSub K a b}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a b).subtype)) :
    extendLin h.ne g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have hgu := (g ⟨perpPart a b v, perpPart_mem h.ne v⟩).2
  have hR := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg
    ⟨perpPart a b v, perpPart_mem h.ne v⟩
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at hR
  rw [extendLin_apply, add_comm, h.map_add_smul _ _ hgu.1 hgu.2, hR, ← h.apply_eq]

theorem IsHypCoord.extendLin_mem_orthDerived (h : IsHypCoord Q a b)
    {g : perpSub K a b ≃ₗ[K] perpSub K a b}
    (hg : g ∈ orthDerived (Q.comp (perpSub K a b).subtype)) :
    extendLin h.ne g ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a b).subtype)).map
      (extendLin h.ne) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g', hg', rfl⟩
    exact h.extendLin_mem_orthogonalGroup hg'
  have hmap : (orthDerived (Q.comp (perpSub K a b).subtype)).map (extendLin h.ne) ≤
      orthDerived Q := by
    rw [orthDerived, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨g, hg, rfl⟩

theorem IsHypCoord.apply_mem_perpSub (h : IsHypCoord Q a b) {g : (ι → K) ≃ₗ[K] (ι → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g ∈ stabSub a b) {u : ι → K}
    (hu : u ∈ perpSub K a b) : g u ∈ perpSub K a b :=
  h.apply_mem_perp_of_mem_stabSub hgO hg hu.1 hu.2

abbrev stabDerived (Q' : QuadraticForm K (ι → K)) (a' b' : ι) : Subgroup (orthDerived Q') :=
  (stabSub (K := K) a' b').subgroupOf (orthDerived Q')

@[expose] noncomputable def IsHypCoord.resHom (h : IsHypCoord Q a b) :
    stabDerived Q a b →* (perpSub K a b ≃ₗ[K] perpSub K a b) where
  toFun y := restrictEquiv (perpSub K a b) (y : orthDerived Q).1
    (fun _ hu => h.apply_mem_perpSub (Subgroup.commutator_le_self _ (y : orthDerived Q).2)
      y.2 hu)
    (fun _ hu => h.apply_mem_perpSub (Subgroup.commutator_le_self _ (y⁻¹ : orthDerived Q).2)
      (y⁻¹).2 hu)
  map_one' := by
    ext u
    rfl
  map_mul' y y' := by
    ext u
    rfl

theorem IsHypCoord.coe_resHom_apply (h : IsHypCoord Q a b) (y : stabDerived Q a b)
    (u : perpSub K a b) :
    ((h.resHom y u : perpSub K a b) : ι → K) = ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) u :=
  rfl

theorem IsHypCoord.extendLin_resHom (h : IsHypCoord Q a b) (y : stabDerived Q a b) :
    extendLin h.ne (h.resHom y) = ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) := by
  ext v i
  rw [extendLin_apply, h.coe_resHom_apply]
  have hy : ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈ stabSub a b := y.2
  conv_rhs => rw [← perpPart_add_planePart (a := a) (b := b) v]
  simp only [map_add, map_smul, hy.1, hy.2]

theorem IsHypCoord.resHom_injective (h : IsHypCoord Q a b) : Function.Injective h.resHom := by
  intro y y' hyy'
  have h1 := h.extendLin_resHom y
  rw [hyy', h.extendLin_resHom y'] at h1
  exact Subtype.ext (Subtype.ext h1.symm)

end Extend

section Dickson

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι}
  {Q : QuadraticForm K (ι → K)}

omit [Fintype ι] in
theorem IsHypCoord.resHom_extendLin (h : IsHypCoord Q a b)
    (g : perpSub K a b ≃ₗ[K] perpSub K a b)
    (hg : extendLin h.ne g ∈ orthDerived Q) :
    h.resHom ⟨⟨extendLin h.ne g, hg⟩, extendLin_mem_stabSub h.ne g⟩ = g := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  rw [h.coe_resHom_apply]
  exact extendLin_apply_perp h.ne g u

omit [Fintype ι] in
theorem IsHypCoord.commSpace_eq_map (h : IsHypCoord Q a b) (y : stabDerived Q a b) :
    commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
      (commSpace (h.resHom y)).map (perpSub K a b).subtype := by
  have hy : ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) ∈ stabSub a b := y.2
  ext x
  rw [mem_commSpace, Submodule.mem_map]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨h.resHom y ⟨perpPart a b v, perpPart_mem h.ne v⟩ -
      ⟨perpPart a b v, perpPart_mem h.ne v⟩, mem_commSpace.mpr ⟨_, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_sub, h.coe_resHom_apply]
    conv_rhs => rw [← perpPart_add_planePart (a := a) (b := b) v]
    simp only [map_add, map_smul, hy.1, hy.2]
    abel
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hz
    exact ⟨u, by simp [h.coe_resHom_apply]⟩

omit [Fintype ι] in
theorem IsHypCoord.finrank_commSpace_resHom (h : IsHypCoord Q a b) (y : stabDerived Q a b) :
    finrank K (commSpace (h.resHom y)) =
      finrank K (commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K))) := by
  rw [h.commSpace_eq_map y, Submodule.finrank_map_subtype_eq]

omit [Fintype ι] in
theorem IsHypCoord.resHom_mem_orthogonalGroup (h : IsHypCoord Q a b) (y : stabDerived Q a b) :
    h.resHom y ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (perpSub K a b).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply, h.coe_resHom_apply]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (Subgroup.commutator_le_self _ (y : orthDerived Q).2) u

theorem IsHypCoord.resHom_mem_orthDerived [Finite K] [CharP K 2] (h : IsHypCoord Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a b), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a b).subtype x = 0)
    (y : stabDerived Q a b) : h.resHom y ∈ orthDerived (Q.comp (perpSub K a b).subtype) := by
  have hev : Even (finrank K (commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)))) :=
    (mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (y : orthDerived Q).2)).2
  apply CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT
  exact mem_omegaGroup.mpr ⟨h.resHom_mem_orthogonalGroup y, by
    rw [h.finrank_commSpace_resHom]
    exact hev⟩

@[expose] noncomputable def IsHypCoord.stabDerivedEquiv [Finite K] [CharP K 2]
    (h : IsHypCoord Q a b) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a b), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a b).subtype x = 0) :
    stabDerived Q a b ≃* orthDerived (Q.comp (perpSub K a b).subtype) where
  toFun y := ⟨h.resHom y, h.resHom_mem_orthDerived hQ hR hT y⟩
  invFun g := ⟨⟨extendLin h.ne (g : perpSub K a b ≃ₗ[K] perpSub K a b),
      h.extendLin_mem_orthDerived g.2⟩,
    extendLin_mem_stabSub h.ne (g : perpSub K a b ≃ₗ[K] perpSub K a b)⟩
  left_inv y := Subtype.ext (Subtype.ext (h.extendLin_resHom y))
  right_inv g := Subtype.ext (h.resHom_extendLin (g : perpSub K a b ≃ₗ[K] perpSub K a b) _)
  map_mul' y y' := Subtype.ext (map_mul h.resHom y y')

end Dickson

section Proj

variable {K : Type} [Field K] {d : ℕ} {a b : Fin d} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def IsHypCoord.pairPerpOfEquiv [Finite K] [CharP K 2]
    (h : IsHypCoord Q a b) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a b), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a b).subtype x = 0) :
    pairPerpOf Q a b ≃* orthDerived (Q.comp (perpSub K a b).subtype) :=
  ((stabDerived Q a b).equivMapOfInjective (projHom Q)
    (projHom_injective h.exists_ne_zero)).symm.trans (h.stabDerivedEquiv hQ hR hT)

theorem IsHypCoord.isQuasisimple_pairPerpOf [Finite K] [CharP K 2]
    (h : IsHypCoord Q a b) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a b), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a b).subtype x = 0) :
    CFSG.IsQuasisimple (pairPerpOf Q a b) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (h.pairPerpOfEquiv hQ hR hT).symm
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)

theorem IsHypCoord.inSubgroup_layer_centralizer_pairTorusOf [Finite K] [CharP K 2]
    (h : IsHypCoord Q a b) (hq : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hT : ∃ T : Submodule K (perpSub K a b), finrank K T = 3 ∧
      ∀ x ∈ T, Q.comp (perpSub K a b).subtype x = 0) :
    inSubgroup layer (centralizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q))) =
      pairPerpOf Q a b :=
  LinearPilot.inSubgroup_layer_eq_of_commutator_mem (h.pairPerpOf_le_centralizer hq)
    (fun _ hx _ hy => h.commutator_mem_pairPerpOf hq hx hy) (h.isQuasisimple_pairPerpOf hQ hR hT)

end Proj

end CFSG.SeitzReduction.OmegaPilot
