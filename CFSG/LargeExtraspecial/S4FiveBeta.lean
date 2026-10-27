module

public import CFSG.LargeExtraspecial.S4FiveW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def betaAux (g : G) (t : S.O) :
    S.Qt →ₗ[ZMod 2] (Vt S g t →ₗ[ZMod 2] ZMod 2) :=
  (S.q.polarBilin.flip).compl₂ (Vt S g t).subtype

theorem betaAux_apply {t : S.O} (y : S.Qt) (x : Vt S g t) :
    betaAux S g t y x = polar S.q x y :=
  rfl

theorem Wt_le_ker_betaAux {t : S.O} : Wt S g t ≤ LinearMap.ker (betaAux S g t) := by
  intro y hy
  rw [LinearMap.mem_ker]
  ext x
  rw [betaAux_apply, LinearMap.zero_apply]
  exact mem_Wt.mp hy x x.2

@[expose] noncomputable def beta (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    LinearMap.BilinForm (ZMod 2) (Vt S g t) :=
  (((Wt S g t).liftQ (betaAux S g t) Wt_le_ker_betaAux).comp
    (chi H H11 ht ht1 hVQ).symm.toLinearMap).flip

variable (H : Hyp4 S g) (H11 : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g)
include H H11 ht ht1 hVQ

theorem beta_chi (x : Vt S g t) (y : S.Qt) :
    beta H H11 ht ht1 hVQ x (chi H H11 ht ht1 hVQ (Submodule.Quotient.mk y)) =
      polar S.q x y := by
  simp [beta, betaAux_apply]

theorem beta_apply (x y : Vt S g t) {y' : S.Qt}
    (hy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) y' - y' = y) :
    beta H H11 ht ht1 hVQ x y = polar S.q x y' := by
  have : chi H H11 ht ht1 hVQ (Submodule.Quotient.mk y') = y :=
    Subtype.ext (by rw [coe_chi_apply_mk, hy])
  rw [← this, beta_chi]

theorem exists_t_sub_eq (y : Vt S g t) :
    ∃ y' : S.Qt, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) y' - y' = y := by
  have hy : (y : S.Qt) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [(commSpace_t_eq H H11 ht ht1 hVQ).1]
    exact y.2
  exact mem_commSpace.mp hy

theorem beta_isAlt : (beta H H11 ht ht1 hVQ).IsAlt := by
  intro x
  obtain ⟨x', hx'⟩ := exists_t_sub_eq H H11 ht ht1 hVQ x
  rw [beta_apply H H11 ht ht1 hVQ x x hx']
  have hq : S.q (x : S.Qt) = 0 := q_eq_zero_of_mem_Vt H ht1 x.2
  rw [← hx', OrthoF2.vec_sub, map_add_eq, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2,
    OrthoF2.zmod2_add_self, zero_add] at hq
  rw [← hx', OrthoF2.vec_sub, polar_add_left, polar_self_eq_zero, add_zero]
  exact hq

theorem beta_symm (x y : Vt S g t) : beta H H11 ht ht1 hVQ x y = beta H H11 ht ht1 hVQ y x := by
  have h := beta_isAlt H H11 ht ht1 hVQ (x + y)
  simp only [map_add, LinearMap.add_apply] at h
  rw [beta_isAlt H H11 ht ht1 hVQ x, beta_isAlt H H11 ht ht1 hVQ y, zero_add, add_zero] at h
  exact (OrthoF2.zmod2_eq_of_add_eq_zero h).symm

theorem beta_nondegenerate : (beta H H11 ht ht1 hVQ).Nondegenerate := by
  have hleft : ∀ x : Vt S g t, (∀ y, beta H H11 ht ht1 hVQ x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    refine S.q_nondegenerate.1 _ fun w => ?_
    rw [polarBilin_apply_apply]
    have := hx (chi H H11 ht ht1 hVQ (Submodule.Quotient.mk w))
    rwa [beta_chi] at this
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  rw [beta_symm H H11 ht ht1 hVQ]
  exact hy x

theorem beta_apply_resV (r : Rbar S g t) (x y : Vt S g t) :
    beta H H11 ht ht1 hVQ (resV H.conj_mem t r x) (resV H.conj_mem t r y) =
      beta H H11 ht ht1 hVQ x y := by
  obtain ⟨y', hy'⟩ := exists_t_sub_eq H H11 ht ht1 hVQ y
  have hy'' : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y') -
      ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) y' = (resV H.conj_mem t r y : S.Qt) := by
    rw [coe_resV_apply, ← hy', map_sub, ← coe_mul_apply, ← coe_mul_apply,
      commute_of_mem_Rbar H.conj_mem r.2]
  rw [beta_apply H H11 ht ht1 hVQ _ _ hy'', beta_apply H H11 ht ht1 hVQ _ _ hy', coe_resV_apply,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (r : S.O).2]

theorem RmodN_le_isometryGroup :
    RmodN S g t ≤ TauCeti.BilinForm.isometryGroup (beta H H11 ht ht1 hVQ) := by
  rw [← range_resV H.conj_mem t]
  rintro _ ⟨r, rfl⟩
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  exact beta_apply_resV H H11 ht ht1 hVQ r

theorem even_finrank_Vt : Even (finrank (ZMod 2) (Vt S g t)) :=
  LinearMap.BilinForm.IsAlt.even_finrank (beta_isAlt H H11 ht ht1 hVQ)
    (beta_nondegenerate H H11 ht ht1 hVQ)

omit H H11 hVQ in
theorem exists_of_mem_Lbar_ne_one : ∃ α : S.M, (α : G) ∈ S.La g ∧ (α : G) ∉ S.QG ∧ S.ρ α = t := by
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp ht
  exact ⟨y, L0_le_La S g hy, fun h => ht1 ((S.ρ_eq_one_iff y).mpr h), rfl⟩

theorem four_le_finrank_Vt (hNo : NoA2 S g) : 4 ≤ finrank (ZMod 2) (Vt S g t) := by
  have heven := even_finrank_Vt H H11 ht ht1 hVQ
  have hpos : finrank (ZMod 2) (Vt S g t) ≠ 0 := fun h =>
    Vt_ne_bot H ht (Submodule.finrank_eq_zero.mp h)
  have h2 : finrank (ZMod 2) (Vt S g t) ≠ 2 := by
    intro h2
    obtain ⟨α, hαL, hαQ, hα⟩ := exists_of_mem_Lbar_ne_one ht ht1
    apply hNo α hαL hαQ
    unfold Setting.IsTypeAOn
    rw [hα]
    have := isTypeA_t H H11 ht ht1 hVQ
    rwa [h2] at this
  obtain ⟨k, hk⟩ := heven
  omega

end CFSG.LargeExtraspecial.S4
