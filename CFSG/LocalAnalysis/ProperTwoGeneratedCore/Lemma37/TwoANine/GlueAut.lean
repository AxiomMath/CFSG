module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

variable {X : Type*} [Group X] (J : Subgroup X) [J.Normal]

noncomputable def centerQuotConj (m : X) : (J ⧸ center J) ≃* (J ⧸ center J) :=
  QuotientGroup.congr (center J) (center J) (MulAut.conjNormal m) (Subgroup.map_center_eq _)

theorem centerQuotConj_mk (m : X) (j : J) :
    centerQuotConj J m (j : J ⧸ center J) = ((MulAut.conjNormal m j : J) : J ⧸ center J) :=
  QuotientGroup.congr_mk _ _ _ _ _

noncomputable def centerQuotConjHom : X →* MulAut (J ⧸ center J) where
  toFun := centerQuotConj J
  map_one' := MulEquiv.ext fun q => QuotientGroup.induction_on q fun j => by
    rw [centerQuotConj_mk, map_one]
    rfl
  map_mul' m n := MulEquiv.ext fun q => QuotientGroup.induction_on q fun j => by
    rw [MulAut.mul_apply, centerQuotConj_mk, centerQuotConj_mk, centerQuotConj_mk, map_mul,
      MulAut.mul_apply]

theorem conjNormal_alternatingGroup_bijective :
    Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 9)) :
      Perm (Fin 9) →* MulAut (alternatingGroup (Fin 9))) :=
  CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9 (by norm_num) (by norm_num)

variable {J}

noncomputable def conjPerm (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) : X →* Perm (Fin 9) :=
  (MulEquiv.ofBijective _ conjNormal_alternatingGroup_bijective).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (centerQuotConjHom J))

theorem conjNormal_conjPerm (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) (m : X) :
    MulAut.conjNormal (conjPerm e m) = MulAut.congr e (centerQuotConj J m) :=
  (MulEquiv.ofBijective _ conjNormal_alternatingGroup_bijective).apply_symm_apply _

theorem proj_conjNormal (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) (m : X) (j : J) :
    ((proj e (MulAut.conjNormal m j) : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      conjPerm e m * (proj e j : Perm (Fin 9)) * (conjPerm e m)⁻¹ := by
  rw [← MulAut.conjNormal_apply, conjNormal_conjPerm, MulAut.congr_apply]
  simp [proj_apply, centerQuotConj_mk]

theorem conjPerm_coe (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) (j : J) :
    conjPerm e (j : X) = (proj e j : Perm (Fin 9)) := by
  refine conjNormal_alternatingGroup_bijective.1 (MulEquiv.ext fun a => Subtype.ext ?_)
  obtain ⟨k, rfl⟩ := proj_surjective e a
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← proj_conjNormal]
  have : MulAut.conjNormal (j : X) k = j * k * j⁻¹ := Subtype.ext (MulAut.conjNormal_apply _ _)
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem mem_centralizer_of_conjPerm_eq_one (hJ : Group.IsPerfect J)
    (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) {m : X} (hm : conjPerm e m = 1) :
    m ∈ centralizer (J : Set X) := by
  have hc : ∀ j : J, j⁻¹ * MulAut.conjNormal m j ∈ center J := fun j =>
    (proj_eq_proj_iff e).mp (Subtype.ext (by rw [proj_conjNormal, hm, one_mul, inv_one, mul_one]))
  let δ : J →* center J :=
    { toFun := fun j => ⟨j⁻¹ * MulAut.conjNormal m j, hc j⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb := Subgroup.mem_center_iff.mp (hc a) (b⁻¹)
        change (a * b)⁻¹ * MulAut.conjNormal m (a * b) =
          (a⁻¹ * MulAut.conjNormal m a) * (b⁻¹ * MulAut.conjNormal m b)
        calc (a * b)⁻¹ * MulAut.conjNormal m (a * b)
            = b⁻¹ * (a⁻¹ * (MulAut.conjNormal m) a) * (MulAut.conjNormal m) b := by
              rw [map_mul]
              group
          _ = (a⁻¹ * (MulAut.conjNormal m) a) * b⁻¹ * (MulAut.conjNormal m) b := by rw [hb]
          _ = _ := by group) }
  have hker : δ.ker = ⊤ :=
    top_unique (hJ.commutator_eq_top ▸ Abelianization.commutator_subset_ker δ)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h1 : δ ⟨h, hh⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top _
  have h2 : (⟨h, hh⟩ : J)⁻¹ * MulAut.conjNormal m ⟨h, hh⟩ = 1 := congrArg Subtype.val h1
  have h3 := congrArg Subtype.val (inv_mul_eq_one.mp h2)
  rw [MulAut.conjNormal_apply] at h3
  exact (mul_inv_eq_iff_eq_mul.mp h3.symm).symm

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
