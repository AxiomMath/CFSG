module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary

theorem exists_subgroup_of_ker_eq {T X Y : Type*} [Group T] [Group X] [Group Y] {p : ℕ}
    [Fact p.Prime] (ρ : T →* X) (φ : T →* Y) (hker : ρ.ker = φ.ker) (V : Subgroup X)
    [IsElementaryAbelian p V] (hV : V ≤ ρ.range) :
    ∃ V' : Subgroup Y, IsElementaryAbelian p V' ∧ Nat.card V' = Nat.card V ∧
      ∀ x ∈ V', ∃ g, φ g = x := by
  set e₂ : T ⧸ ρ.ker →* Y := QuotientGroup.lift ρ.ker φ hker.le with he₂def
  have he₂ : Function.Injective e₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [he₂def, QuotientGroup.lift_mk] at hx
    rw [QuotientGroup.eq_one_iff, hker]
    exact hx
  set j : ρ.range →* Y := e₂.comp (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
    with hjdef
  have hj : Function.Injective j := he₂.comp (QuotientGroup.quotientKerEquivRange ρ).symm.injective
  have hjg : ∀ g, j (ρ.rangeRestrict g) = φ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict g) =
        (g : T ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hjdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, he₂def, QuotientGroup.lift_mk]
  have : IsElementaryAbelian p (V.subgroupOf ρ.range) := IsElementaryAbelian.subgroupOf hV
  refine ⟨(V.subgroupOf ρ.range).map j, IsElementaryAbelian.map j, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv
  · rintro _ ⟨y, -, rfl⟩
    obtain ⟨g, hg⟩ := ρ.mem_range.mp y.2
    refine ⟨g, ?_⟩
    rw [← hjg]
    congr 1
    exact Subtype.ext hg

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem map_hypSU_toLin (h : UnitaryFieldData p f K) :
    (hypSU h r ε).map (Matrix.GeneralLinearGroup.toLin :
      GL (HypIndex r ε) K ≃* LinearMap.GeneralLinearGroup K (HypIndex r ε → K)).toMonoidHom =
        sesqSpecialUnitaryGroup (hypForm h r ε) := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ g').mpr hg'
  · intro hg
    refine ⟨Matrix.GeneralLinearGroup.toLin.symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ _).mp (by
      rw [MulEquiv.apply_symm_apply]
      exact hg)

variable (r ε) in
@[expose] noncomputable def hypSesqSUEquiv (h : UnitaryFieldData p f K) :
    hypSU h r ε ≃* sesqSpecialUnitaryGroup (hypForm h r ε) :=
  (Matrix.GeneralLinearGroup.toLin.subgroupMap (hypSU h r ε)).trans
    (MulEquiv.subgroupCongr (map_hypSU_toLin h))

theorem coe_hypSesqSUEquiv (h : UnitaryFieldData p f K) (g : hypSU h r ε) :
    ((hypSesqSUEquiv r ε h g : sesqSpecialUnitaryGroup (hypForm h r ε)) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) =
        Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) :=
  rfl

theorem eq_scalar_of_toLin_eq {g : GL (HypIndex r ε) K} {c : K}
    (hg : ((Matrix.GeneralLinearGroup.toLin g : LinearMap.GeneralLinearGroup K
      (HypIndex r ε → K)) : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) = c • LinearMap.id) :
    (g : Matrix (HypIndex r ε) (HypIndex r ε) K) = Matrix.scalar (HypIndex r ε) c := by
  have h1 : ∀ v, (g : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v = c • v := fun v => by
    have h2 := LinearMap.congr_fun hg v
    rwa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at h2
  ext a b
  have h3 := congrFun (h1 (Pi.single b 1)) a
  rw [mulVec_single_one, col_apply] at h3
  rw [h3, scalar_apply, diagonal_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

theorem map_hypScalars_hypSesqSUEquiv (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε) :
    (hypScalars h r ε).map (hypSesqSUEquiv r ε h).toMonoidHom =
      unitaryScalars (hypForm h r ε) := by
  ext z
  constructor
  · rintro ⟨g, ⟨c, -, -, hg⟩, rfl⟩
    refine ⟨c, ?_⟩
    change ((Matrix.GeneralLinearGroup.toLin (g : GL (HypIndex r ε) K) :
      LinearMap.GeneralLinearGroup K (HypIndex r ε → K)) :
        (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) = _
    rw [hg]
    refine LinearMap.ext fun v => ?_
    rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, GeneralLinearGroup.coe_scalar,
      LinearMap.smul_apply, LinearMap.id_apply]
    funext a
    simp [scalar_apply, mulVec_diagonal]
  · rintro ⟨c, hc⟩
    refine ⟨(hypSesqSUEquiv r ε h).symm z, ⟨c, ?_, ?_, ?_⟩, MulEquiv.apply_symm_apply _ _⟩
    all_goals
      have hgz : ((Matrix.GeneralLinearGroup.toLin (((hypSesqSUEquiv r ε h).symm z :
          hypSU h r ε) : GL (HypIndex r ε) K) : LinearMap.GeneralLinearGroup K
            (HypIndex r ε → K)) : (HypIndex r ε → K) →ₗ[K] (HypIndex r ε → K)) =
              (c : K) • LinearMap.id := by
        rw [← coe_hypSesqSUEquiv, MulEquiv.apply_symm_apply]
        exact hc
      have hmat := eq_scalar_of_toLin_eq hgz
      have hmem := ((hypSesqSUEquiv r ε h).symm z).2
      rw [mem_hypSU, hmat] at hmem
    · have h1 := hmem.1
      rw [scalar_barTranspose_mul_mul] at h1
      have hJ : ∃ a b : HypIndex r ε, hypGram r ε K a b ≠ 0 := by
        by_contra hall
        push Not at hall
        have hz : hypGram r ε K = 0 := Matrix.ext fun a b => hall a b
        have : Nonempty (HypIndex r ε) := ⟨(Fintype.equivFinOfCardEq card_hypIndex).symm
          ⟨0, by omega⟩⟩
        exact det_hypGram_ne_zero (by rw [hz, Matrix.det_zero])
      obtain ⟨a, b, hab⟩ := hJ
      have h2 := congrFun (congrFun h1 a) b
      rw [Matrix.smul_apply, smul_eq_mul] at h2
      exact mul_right_cancel₀ hab (h2.trans (one_mul _).symm)
    · have h1 := hmem.2
      rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, card_hypIndex] at h1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    · exact Units.ext (by rw [hmat, GeneralLinearGroup.coe_scalar])

variable (r ε) in
@[expose] noncomputable def hypSesqProjEquiv (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε) :
    hypPSU h r ε ≃* unitaryProj (hypForm h r ε) :=
  QuotientGroup.congr _ _ (hypSesqSUEquiv r ε h) (map_hypScalars_hypSesqSUEquiv h hn)

theorem hypSesqProjEquiv_hypProj (h : UnitaryFieldData p f K) (hn : 1 ≤ 2 * r + ε)
    (g : hypSU h r ε) :
    hypSesqProjEquiv r ε h hn (hypProj h r ε g) = unitaryProjMk _ (hypSesqSUEquiv r ε h g) :=
  QuotientGroup.congr_mk _ _ _ _ g

@[expose] noncomputable def semilinearMatrixMap (h : UnitaryFieldData p f K) {ι : Type*}
    [Fintype ι] (A : Matrix ι ι K) : (ι → K) →ₛₗ[h.bar] (ι → K) where
  toFun v := A *ᵥ fun i => h.bar (v i)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext i
    exact map_add h.bar (v i) (w i)
  map_smul' a v := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

theorem semilinearMatrixMap_apply (h : UnitaryFieldData p f K) {ι : Type*} [Fintype ι]
    (A : Matrix ι ι K) (v : ι → K) : semilinearMatrixMap h A v = A *ᵥ fun i => h.bar (v i) :=
  rfl

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
