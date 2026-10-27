module

public import CFSG.Open.StatedAPI
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped commutatorElement

section Basic

variable {E : Type} [Field E]

instance statedSL_normal (d : ℕ) : (StatedSL d E).Normal := by
  rw [statedSL_eq_ker_det]
  infer_instance

theorem commutatorElement_mem_statedSL {d : ℕ} (x y : GL (Fin d) E) :
    ⁅x, y⁆ ∈ StatedSL d E := by
  rw [statedSL_eq_ker_det, MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem transvection_toGL_mem_statedSL {d : ℕ} {i j : Fin d} (hij : i ≠ j) (b : E) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij b) ∈
      StatedSL d E := by
  rw [statedSL_eq_range_toGL]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem mul_single_entry {d : ℕ} (M : Matrix (Fin d) (Fin d) E) (i j r s : Fin d) :
    (M * Matrix.single i j (1 : E)) r s = M r i * (if j = s then 1 else 0) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · by_cases hjs : j = s
    · subst hjs; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hjs]
  · intro k _ hk
    simp [Matrix.single_apply, Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem single_mul_entry {d : ℕ} (M : Matrix (Fin d) (Fin d) E) (i j r s : Fin d) :
    (Matrix.single i j (1 : E) * M) r s = (if r = i then 1 else 0) * M j s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · by_cases hri : r = i
    · subst hri; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, hri, Ne.symm hri]
  · intro k _ hk
    simp [Matrix.single_apply, hk, Ne.symm hk]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem matrix_eq_scalar_of_commute_transvection {d : ℕ} (M : Matrix (Fin d) (Fin d) E)
    (h : ∀ i j : Fin d, i ≠ j → M * Matrix.transvection i j 1 = Matrix.transvection i j 1 * M) :
    ∃ c : E, M = Matrix.scalar (Fin d) c := by
  have hmulT : ∀ i j r s : Fin d, (M * Matrix.transvection i j (1 : E)) r s =
      M r s + M r i * (if j = s then 1 else 0) := by
    intro i j r s
    rw [Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_single_entry]
  have hTmul : ∀ i j r s : Fin d, (Matrix.transvection i j (1 : E) * M) r s =
      M r s + (if r = i then 1 else 0) * M j s := by
    intro i j r s
    rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, single_mul_entry]
  have hentry : ∀ i j : Fin d, i ≠ j → ∀ r s : Fin d,
      M r i * (if j = s then 1 else 0) = (if r = i then 1 else 0) * M j s := by
    intro i j hij r s
    have h1 := congrFun (congrFun (h i j hij) r) s
    rw [hmulT, hTmul] at h1
    exact add_left_cancel h1
  have hoff : ∀ r s : Fin d, r ≠ s → M r s = 0 := by
    intro r s hrs
    have h1 := hentry s r (Ne.symm hrs) s s
    rw [if_neg hrs, if_pos rfl, mul_zero, one_mul] at h1
    exact h1.symm
  have hdiag : ∀ a b : Fin d, a ≠ b → M a a = M b b := by
    intro a b hab
    have h1 := hentry a b hab a b
    rw [if_pos rfl, if_pos rfl, mul_one, one_mul] at h1
    exact h1
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, Subsingleton.elim _ _⟩
  · refine ⟨M ⟨0, hd⟩ ⟨0, hd⟩, ?_⟩
    ext r s
    by_cases hrs : r = s
    · subst hrs
      by_cases hr0 : r = ⟨0, hd⟩
      · subst hr0
        simp [Matrix.scalar_apply]
      · have := hdiag r ⟨0, hd⟩ hr0
        simp [Matrix.scalar_apply, this]
    · simp [Matrix.scalar_apply, hrs, hoff r s hrs]

theorem center_statedSL_eq (d : ℕ) :
    Subgroup.center (StatedSL d E) = (StatedScalars (Fin d) E).subgroupOf (StatedSL d E) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · intro hx
    have hscal : (x : GL (Fin d) E) ∈ StatedScalars (Fin d) E := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · have h1 : (x : GL (Fin 0) E) = 1 := Subsingleton.elim _ _
        rw [h1]
        exact Subgroup.one_mem _
      · have hcomm : ∀ i j : Fin d, i ≠ j →
            (Matrix.transvection i j 1 : Matrix (Fin d) (Fin d) E) =
              Matrix.transvection i j 1 := fun _ _ _ => rfl
        have hM : ∀ i j : Fin d, i ≠ j →
            ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) * Matrix.transvection i j 1 =
              Matrix.transvection i j 1 * ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) := by
          intro i j hij
          have hy := hx ⟨_, transvection_toGL_mem_statedSL hij 1⟩
          have hy' := congrArg (fun g : StatedSL d E => (g : GL (Fin d) E)) hy
          have hy'' := congrArg (fun g : GL (Fin d) E => (g : Matrix (Fin d) (Fin d) E)) hy'
          exact hy''.symm
        obtain ⟨c, hc⟩ := matrix_eq_scalar_of_commute_transvection _ hM
        have hc0 : c ≠ 0 := by
          intro hc0
          haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
          have hmul : ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *
              (((x : GL (Fin d) E))⁻¹ : GL (Fin d) E) = 1 := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          simp [hc, hc0] at hmul
        refine MonoidHom.mem_range.mpr ⟨Units.mk0 c hc0, ?_⟩
        apply Units.ext
        simp [Matrix.GeneralLinearGroup.coe_scalar, hc]
    exact hscal
  · intro hx g
    have hcent : (x : GL (Fin d) E) ∈ Subgroup.center (GL (Fin d) E) := by
      rw [statedScalars_eq_center] at hx
      exact hx
    have := Subgroup.mem_center_iff.mp hcent (g : GL (Fin d) E)
    exact Subtype.ext this

theorem nonempty_quotientCenter_equiv_statedProj {Γ : Type*} [Group Γ] {d : ℕ}
    (e : Γ ≃* StatedSL d E) :
    Nonempty (Γ ⧸ Subgroup.center Γ ≃* StatedProj (StatedSL d E)) :=
  ⟨(QuotientGroup.congr (Subgroup.center Γ) (Subgroup.center (StatedSL d E)) e
      (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedSL_eq d))⟩

end Basic

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem isComponentOf_map_of_injective (f : G →* H) (hf : Function.Injective f) {L K : Subgroup G}
    (h : IsComponentOf L K) : IsComponentOf (L.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map f h.2.1,
    (CFSG.Open.IsQuasisimple.congr (L.equivMapOfInjective f hf)).1 h.2.2⟩

theorem isComponentOf_of_map_injective (f : G →* H) (hf : Function.Injective f) {L K : Subgroup G}
    (h : IsComponentOf (L.map f) (K.map f)) : IsComponentOf L K := by
  refine ⟨(Subgroup.map_le_map_iff_of_injective hf).1 h.1, ?_,
    (CFSG.Open.IsQuasisimple.congr (L.equivMapOfInjective f hf)).2 h.2.2⟩
  have hc := CFSG.Open.IsSubnormal.comap f h.2.1
  rwa [Subgroup.comap_map_eq_self_of_injective hf, Subgroup.comap_map_eq_self_of_injective hf] at hc

theorem isComponentOf_top_of_normal' {M : Type*} [Group M] {L K : Subgroup M} [K.Normal]
    (hL : IsComponentOf L K) : IsComponentOf L ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.trans hL.2.1
    (CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤)), hL.2.2⟩

theorem eq_top_of_map_equiv_eq_top {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (X : Subgroup Γ) (h : X.map e.toMonoidHom = ⊤) : X = ⊤ := by
  ext x
  refine ⟨fun _ => Subgroup.mem_top x, fun _ => ?_⟩
  have hx : e x ∈ X.map e.toMonoidHom := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hxy : y = x := e.injective hyx
  exact hxy ▸ hy

end Transport

@[expose] def SLComponentsTrivial : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
    IsComponentOf X ⊤ → X = ⊤

end CFSG.LieType.SemisimpleCentralizers.Held

end
