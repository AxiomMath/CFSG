module

public import CFSG.GF2Type.Smith1980Orth.S2Decomp
public import CFSG.GF2Type.Smith1980Orth.S2Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

variable {M1 : Subgroup S.O} (D : S2Pre S M1)

theorem k_apply_apply (v : S.Qt) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      v + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  have h : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v +
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
      v + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v +
        (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    rw [map_add, map_add, D.k_apply_cube]
    abel
  have h0 := D.k_fix_eq_zero _ h
  rw [eq_neg_of_add_eq_zero_right h0, ZModModule.neg_eq_self]

noncomputable abbrev betaV : LinearMap.BilinForm (ZMod 2) (Vt S D.g D.t) :=
  S4.beta D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ

theorem betaV_isAlt : D.betaV.IsAlt :=
  S4.beta_isAlt D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ

theorem betaV_symm (u v : Vt S D.g D.t) : D.betaV u v = D.betaV v u :=
  S4.beta_symm D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ u v

theorem betaV_nondegenerate : D.betaV.Nondegenerate :=
  S4.beta_nondegenerate D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ

private noncomputable def coordMap : (Vt S D.g D.t × Vt S D.g D.t) →ₗ[ZMod 2] S.Qt :=
  (Vt S D.g D.t).subtype.coprod
    (((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt).comp (Vt S D.g D.t).subtype)

private theorem coordMap_apply (u v : Vt S D.g D.t) :
    D.coordMap (u, v) = (u : S.Qt) + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) :=
  rfl

private theorem coordMap_injective : Function.Injective D.coordMap := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨u, v⟩ h
  rw [coordMap_apply] at h
  have hKv : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) = (u : S.Qt) := by
    rw [eq_neg_of_add_eq_zero_right h, ZModModule.neg_eq_self]
  have hv : (v : S.Qt) = 0 :=
    D.eq_zero_of_k_apply_mem v.2 (by rw [hKv]; exact u.2)
  have hv' : v = 0 := Subtype.ext hv
  subst hv'
  have hu : (u : S.Qt) = 0 := by simpa using h
  exact Prod.ext (Subtype.ext hu) rfl

private theorem coordMap_surjective : Function.Surjective D.coordMap := by
  intro x
  have hx : x ∈ Vt S D.g D.t ⊔ D.Wk := by
    rw [D.isCompl_Vt_Wk.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hw
  exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩

noncomputable def coord : (Vt S D.g D.t × Vt S D.g D.t) ≃ₗ[ZMod 2] S.Qt :=
  LinearEquiv.ofBijective D.coordMap ⟨D.coordMap_injective, D.coordMap_surjective⟩

theorem coord_apply (u v : Vt S D.g D.t) :
    D.coord (u, v) = (u : S.Qt) + (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) := by
  simp [coord, coordMap]

theorem coord_apply_zero_right (u : Vt S D.g D.t) : D.coord (u, 0) = (u : S.Qt) := by
  rw [coord_apply]
  simp

theorem coord_apply_zero_left (v : Vt S D.g D.t) :
    D.coord (0, v) = (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt) := by
  rw [coord_apply]
  simp

theorem coord_apply_self (s : Vt S D.g D.t) :
    D.coord (s, s) = (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (s : S.Qt)) := by
  rw [coord_apply, D.k_apply_apply]

theorem mem_Vt_iff_coord {x : S.Qt} :
    x ∈ Vt S D.g D.t ↔ ∃ u : Vt S D.g D.t, x = D.coord (u, 0) := by
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, (D.coord_apply_zero_right ⟨x, hx⟩).symm⟩
  · rintro ⟨u, rfl⟩
    rw [D.coord_apply_zero_right]
    exact u.2

theorem mem_Wk_iff_coord {x : S.Qt} :
    x ∈ D.Wk ↔ ∃ v : Vt S D.g D.t, x = D.coord (0, v) := by
  rw [D.mem_Wk_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, (D.coord_apply_zero_left ⟨v, hv⟩).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, v.2, (D.coord_apply_zero_left v).symm⟩

theorem mem_Wkt_iff_coord {x : S.Qt} :
    x ∈ D.Wkt ↔ ∃ v : Vt S D.g D.t, x = D.coord (v, v) := by
  rw [D.mem_Wkt_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hw
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [D.coord_apply_self, D.t_k_apply_of_mem hv]
  · rintro ⟨v, rfl⟩
    refine ⟨(D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt), D.k_apply_mem_Wk v.2, ?_⟩
    rw [D.coord_apply_self, D.t_k_apply_of_mem v.2]

theorem k_apply_coord (u v : Vt S D.g D.t) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, v)) = D.coord (v, u + v) := by
  simp only [coord_apply, map_add, Submodule.coe_add, D.k_apply_apply]
  abel

theorem t_apply_coord (u v : Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, v)) = D.coord (u + v, v) := by
  simp only [coord_apply, map_add, Submodule.coe_add, D.t_apply_of_mem u.2,
    D.t_k_apply_of_mem v.2, D.k_apply_apply]
  abel

theorem Cbar_apply_coord (c : D.Cbar) (u v : Vt S D.g D.t) :
    ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, v)) =
      D.coord (D.resC c u, D.resC c v) := by
  have hck : ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)) =
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)) := by
    rw [← coe_mul_apply, ← coe_mul_apply, D.Cbar_comm_k c.2]
  rw [coord_apply, coord_apply, map_add, hck, D.coe_resC_apply, D.coe_resC_apply]

theorem t_k_apply_sub (u : Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt)) -
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt) = (u : S.Qt) := by
  rw [D.t_k_apply_of_mem u.2, D.k_apply_apply, add_sub_cancel_right]

theorem betaV_apply (u v : Vt S D.g D.t) :
    D.betaV u v = polar S.q ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt)) (v : S.Qt) := by
  rw [D.betaV_symm u v,
    S4.beta_apply D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ v u (D.t_k_apply_sub u),
    polar_comm]

theorem polar_k_apply (u v : Vt S D.g D.t) :
    polar S.q (u : S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)) = D.betaV v u := by
  rw [D.betaV_apply, polar_comm]

theorem polar_k_apply_k_apply (u v : Vt S D.g D.t) :
    polar S.q ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (u : S.Qt))
      ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (v : S.Qt)) = 0 := by
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup D.k.2]
  exact polar_eq_zero_of_mem_Vt D.good.H D.good.ht1 u.2 v.2

theorem polar_coord (u v u' v' : Vt S D.g D.t) :
    polar S.q (D.coord (u, v)) (D.coord (u', v')) = D.betaV u v' + D.betaV v u' := by
  have h1 : polar S.q (u : S.Qt) (u' : S.Qt) = 0 :=
    polar_eq_zero_of_mem_Vt D.good.H D.good.ht1 u.2 u'.2
  rw [coord_apply, coord_apply, polar_add_left, polar_add_right, polar_add_right, h1,
    D.polar_k_apply u v', ← D.betaV_apply v u', D.polar_k_apply_k_apply, D.betaV_symm u v']
  abel

theorem q_coord (u v : Vt S D.g D.t) : S.q (D.coord (u, v)) = D.betaV u v := by
  rw [coord_apply, map_add_eq, q_eq_zero_of_mem_Vt D.good.H D.good.ht1 u.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup D.k.2,
    q_eq_zero_of_mem_Vt D.good.H D.good.ht1 v.2, D.polar_k_apply u v, D.betaV_symm u v]
  abel

theorem commute_iff_coord {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) {u v u' v' : Vt S D.g D.t}
    (hxc : S.cl x = D.coord (u, v)) (hyc : S.cl y = D.coord (u', v')) :
    x * y = y * x ↔ D.betaV u v' + D.betaV v u' = 0 := by
  rw [← S.polar_cl_eq_zero_iff hx hy, hxc, hyc, D.polar_coord]

end S2Pre

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

noncomputable def QV : QuadraticForm (ZMod 2) (Vt S D.g D.t) :=
  Classical.choose D.hΩ.exists_form

theorem QV_nondegenerate : D.QV.polarBilin.Nondegenerate :=
  (Classical.choose_spec D.hΩ.exists_form).choose

theorem polarBilin_QV : D.QV.polarBilin = D.betaV :=
  (Classical.choose_spec (Classical.choose_spec D.hΩ.exists_form)).1

theorem RmodN_eq_omegaGroup :
    RmodN S D.g D.t = omegaGroup D.QV D.QV_nondegenerate :=
  (Classical.choose_spec (Classical.choose_spec D.hΩ.exists_form)).2.1

theorem LmodN_eq_pointRadical :
    LmodN S D.g D.t = pointRadical D.QV (aV D.good.ht) :=
  (Classical.choose_spec (Classical.choose_spec D.hΩ.exists_form)).2.2.1

theorem QV_eq_zero_iff {v : Vt S D.g D.t} (hv : v ≠ 0) :
    D.QV v = 0 ↔ v ∈ orbitOf (RmodN S D.g D.t) (aV D.good.ht) :=
  (Classical.choose_spec (Classical.choose_spec D.hΩ.exists_form)).2.2.2 v hv

theorem QV_aV : D.QV (aV D.good.ht) = 0 :=
  (D.QV_eq_zero_iff (aV_ne_zero D.good.H D.good.ht)).mpr ⟨1, one_mem _, rfl⟩

theorem polar_QV (u v : Vt S D.g D.t) : polar D.QV u v = D.betaV u v := by
  rw [← polarBilin_apply_apply, D.polarBilin_QV]

theorem QV_eq_zero_iff_mem_singV {s : Vt S D.g D.t} (hs : s ≠ 0) :
    D.QV s = 0 ↔ (s : S.Qt) ∈ D.singV :=
  (D.QV_eq_zero_iff hs).trans (mem_orbitOf_RmodN_iff D.good.H.conj_mem D.good.ht)

theorem mem_singV_iff {w : S.Qt} :
    w ∈ D.singV ↔ ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧ (s : S.Qt) = w := by
  constructor
  · intro hw
    have hwV := D.singV_subset hw
    have hs0 : (⟨w, hwV⟩ : Vt S D.g D.t) ≠ 0 := fun h => by
      have hw0 : w = 0 := congrArg Subtype.val h
      exact D.zero_notMem_singV (hw0 ▸ hw)
    exact ⟨⟨w, hwV⟩, hs0, (D.QV_eq_zero_iff_mem_singV hs0).mpr hw, rfl⟩
  · rintro ⟨s, hs0, hsQ, rfl⟩
    exact (D.QV_eq_zero_iff_mem_singV hs0).mp hsQ

theorem mem_singW_iff {w : S.Qt} :
    w ∈ D.singW ↔ ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (s : S.Qt) = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs0, hsQ, rfl⟩ := D.mem_singV_iff.mp hx
    exact ⟨s, hs0, hsQ, rfl⟩
  · rintro ⟨s, hs0, hsQ, rfl⟩
    exact ⟨s, D.mem_singV_iff.mpr ⟨s, hs0, hsQ, rfl⟩, rfl⟩

theorem mem_singWt_iff {w : S.Qt} :
    w ∈ D.singWt ↔ ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧
      (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) (s : S.Qt)) = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs0, hsQ, rfl⟩ := D.mem_singW_iff.mp hx
    exact ⟨s, hs0, hsQ, rfl⟩
  · rintro ⟨s, hs0, hsQ, rfl⟩
    exact ⟨_, D.mem_singW_iff.mpr ⟨s, hs0, hsQ, rfl⟩, rfl⟩

theorem mem_orbitMbar_iff_coord {w : S.Qt} :
    w ∈ D.orbitMbar ↔ ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧
      (w = D.coord (s, 0) ∨ w = D.coord (0, s) ∨ w = D.coord (s, s)) := by
  rw [D.orbitMbar_eq]
  constructor
  · rintro ((hw | hw) | hw)
    · obtain ⟨s, hs0, hsQ, rfl⟩ := D.mem_singV_iff.mp hw
      exact ⟨s, hs0, hsQ, Or.inl (D.coord_apply_zero_right s).symm⟩
    · obtain ⟨s, hs0, hsQ, rfl⟩ := D.mem_singW_iff.mp hw
      exact ⟨s, hs0, hsQ, Or.inr (Or.inl (D.coord_apply_zero_left s).symm)⟩
    · obtain ⟨s, hs0, hsQ, rfl⟩ := D.mem_singWt_iff.mp hw
      exact ⟨s, hs0, hsQ, Or.inr (Or.inr (D.coord_apply_self s).symm)⟩
  · rintro ⟨s, hs0, hsQ, rfl | rfl | rfl⟩
    · rw [D.coord_apply_zero_right]
      exact Or.inl (Or.inl (D.mem_singV_iff.mpr ⟨s, hs0, hsQ, rfl⟩))
    · rw [D.coord_apply_zero_left]
      exact Or.inl (Or.inr (D.mem_singW_iff.mpr ⟨s, hs0, hsQ, rfl⟩))
    · rw [D.coord_apply_self]
      exact Or.inr (D.mem_singWt_iff.mpr ⟨s, hs0, hsQ, rfl⟩)

theorem isConj_z_iff_coord {x : G} (hxQ : x ∈ S.QG) (hxz : x ≠ S.z) :
    IsConj S.z x ↔ ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧
      (S.cl x = D.coord (s, 0) ∨ S.cl x = D.coord (0, s) ∨ S.cl x = D.coord (s, s)) := by
  rw [← D.mem_orbitMbar_iff_coord]
  constructor
  · intro hc
    rcases D.conj_mem_Q_iff.mp ⟨hc, hxQ⟩ with h | ⟨-, h⟩
    · exact absurd h hxz
    · exact h
  · intro h
    exact (D.conj_mem_Q_iff.mpr (Or.inr ⟨hxQ, h⟩)).1

theorem QV_resC (c : D.Cbar) (v : Vt S D.g D.t) :
    D.QV (D.resC c v) = D.QV v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (D.range_resC_le_orthogonalGroup (fun _ hv => D.QV_eq_zero_iff hv) ⟨c, rfl⟩) v

end S2Data

end CFSG.GF2Type.Smith1980Orth
