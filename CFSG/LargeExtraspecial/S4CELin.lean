module

public import CFSG.LargeExtraspecial.S4CEToolTwo
public import CFSG.LieType.Steinberg.Classical.SpecialLinearSteinberg
public import CFSG.LargeExtraspecial.S4Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module
open scoped commutatorElement Matrix

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W]

@[expose] noncomputable def glAut (b : Basis ι (ZMod 2) W) :
    GL ι (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2))).trans
    (ceConj b.equivFun.symm)

theorem glAut_apply (b : Basis ι (ZMod 2) W) (M : GL ι (ZMod 2)) (v : W) :
    glAut b M v = b.equivFun.symm ((M : Matrix ι ι (ZMod 2)) *ᵥ b.equivFun v) :=
  rfl

theorem glAut_transvection (b : Basis ι (ZMod 2) W) {i j : ι} (hij : i ≠ j) (c : ZMod 2)
    (v : W) :
    glAut b (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)) v =
      v + (c * b.repr v j) • b i := by
  rw [glAut_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq, map_add, map_smul, Basis.equivFun_symm_single,
    LinearEquiv.symm_apply_apply, Basis.equivFun_apply]

theorem zmod2_units_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  refine Units.ext ?_
  have h0 : (u : ZMod 2) ≠ 0 := u.ne_zero
  revert h0
  generalize (u : ZMod 2) = x
  revert x
  decide

theorem exists_glAut_toGL_eq (b : Basis ι (ZMod 2) W) (f : W ≃ₗ[ZMod 2] W) :
    ∃ g : Matrix.SpecialLinearGroup ι (ZMod 2),
      glAut b (Matrix.SpecialLinearGroup.toGL g) = f := by
  set M := (glAut b).symm f
  have hdet : (M : Matrix ι ι (ZMod 2)).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply,
      zmod2_units_eq_one (Matrix.GeneralLinearGroup.det M), Units.val_one]
  refine ⟨⟨M, hdet⟩, ?_⟩
  have : Matrix.SpecialLinearGroup.toGL ⟨(M : Matrix ι ι (ZMod 2)), hdet⟩ = M := Units.ext rfl
  rw [this, MulEquiv.apply_symm_apply]

end Mat

section Centre

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem centreGroup_map_conj (g : W ≃ₗ[ZMod 2] W) (c : W) :
    (centreGroup W c).map (MulAut.conj g).toMonoidHom = centreGroup W (g c) := by
  have key : ∀ (f : W ≃ₗ[ZMod 2] W) (c : W), ∀ x ∈ centreGroup W c,
      f * x * f⁻¹ ∈ centreGroup W (f c) := by
    intro f c x hx u
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hx (f⁻¹ u))
    have e1 : (f * x * f⁻¹) u - u = f (x (f⁻¹ u) - f⁻¹ u) := by
      rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, apply_inv_self']
    rw [e1, ← hr, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key g c x hx
  · intro x hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
    have := key g⁻¹ (g c) x hx
    rwa [inv_apply_self'] at this

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem centreGroup_le_closure (b : Basis ι (ZMod 2) W) (i : ι) :
    centreGroup W (b i) ≤
      Subgroup.closure {g : W ≃ₗ[ZMod 2] W | ∃ j, j ≠ i ∧ ∀ v, g v = v + b.repr v j • b i} := by
  classical
  set S := {g : W ≃ₗ[ZMod 2] W | ∃ j, j ≠ i ∧ ∀ v, g v = v + b.repr v j • b i}
  suffices H : ∀ n : ℕ, ∀ e ∈ centreGroup W (b i),
      (Finset.univ.filter fun j => e (b j) ≠ b j).card = n → e ∈ closure S from
    fun e he => H _ e he rfl
  intro n
  induction n with
  | zero =>
    intro e _ hcard
    have he1 : e = 1 := by
      refine LinearEquiv.toLinearMap_injective (b.ext fun j => ?_)
      by_contra hne
      have hj : j ∈ Finset.univ.filter fun j => e (b j) ≠ b j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [Finset.card_eq_zero] at hcard
      rw [hcard] at hj
      exact Finset.notMem_empty _ hj
    rw [he1]
    exact one_mem _
  | succ n ih =>
    intro e he hcard
    obtain ⟨j, hj⟩ : (Finset.univ.filter fun j => e (b j) ≠ b j).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hje : e (b j) ≠ b j := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := fun hji =>
      hje (hji ▸ apply_centre_of_mem_centreGroup (b.ne_zero i) he)
    have hφ : b.coord j (b i) = 0 := by
      rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, ite_eq_right hji.symm]
    set T := LinearEquiv.transvection hφ
    have hT : ∀ v, T v = v + b.repr v j • b i := fun v => by
      rw [LinearEquiv.transvection.apply, Basis.coord_apply]
    have hTS : T ∈ S := ⟨j, hji, hT⟩
    have hej : e (b j) = b j + b i := by
      rcases OrthoF2.mem_span_singleton_iff.mp (he (b j)) with h0 | h1
      · exact absurd (sub_eq_zero.mp h0) hje
      · rw [← h1]
        abel
    have heT : ∀ k, (e * T) (b k) = if k = j then b k else e (b k) := by
      intro k
      rw [LinearEquiv.mul_apply, hT, Basis.repr_self, Finsupp.single_apply]
      by_cases hkj : k = j
      · subst hkj
        rw [ite_eq_left rfl, ite_eq_left rfl, one_smul, map_add, hej,
          apply_centre_of_mem_centreGroup (b.ne_zero i) he, add_assoc, OrthoF2.vec_add_self,
          add_zero]
      · rw [ite_eq_right hkj, ite_eq_right hkj, zero_smul, add_zero]
    have hfilter : (Finset.univ.filter fun k => (e * T) (b k) ≠ b k) =
        (Finset.univ.filter fun k => e (b k) ≠ b k).erase j := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, heT]
      by_cases hkj : k = j
      · simp [hkj]
      · simp [hkj]
    have hmem := ih (e * T) (mul_mem he (transvection_mem_centreGroup hφ)) (by
      rw [hfilter, Finset.card_erase_of_mem hj, hcard]
      rfl)
    rw [show e = e * T * T⁻¹ by group]
    exact mul_mem hmem (inv_mem (subset_closure hTS))

end Centre

section Lift

open CFSG.LieType.Steinberg.SL

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]
  {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {m : ℕ}

@[expose] noncomputable def linIota (b : Basis (Fin (m + 1)) (ZMod 2) V) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) (ZMod 2) →* (V ≃ₗ[ZMod 2] V) :=
  (glAut b).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL

theorem linIota_injective (b : Basis (Fin (m + 1)) (ZMod 2) V) :
    Function.Injective (linIota b) :=
  (glAut b).injective.comp Matrix.SpecialLinearGroup.toGL_injective

theorem linIota_surjective (b : Basis (Fin (m + 1)) (ZMod 2) V) :
    Function.Surjective (linIota b) :=
  fun f => exists_glAut_toGL_eq b f

@[expose] noncomputable def linX (b : Basis (Fin (m + 1)) (ZMod 2) V)
    (s : Fin (m + 1) × Fin (m + 1) × ZMod 2) : V ≃ₗ[ZMod 2] V :=
  linIota b (stGen s)

theorem linX_apply (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j : Fin (m + 1)} (hij : i ≠ j)
    (c : ZMod 2) (v : V) : linX b (i, j, c) v = v + (c * b.repr v j) • b i := by
  rw [linX, stGen_of_ne hij]
  exact glAut_transvection b hij c v

theorem linX_self (b : Basis (Fin (m + 1)) (ZMod 2) V) (i : Fin (m + 1)) (c : ZMod 2) :
    linX b (i, i, c) = 1 := by
  rw [linX, stGen_self, map_one]

theorem linX_apply_basis (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j k : Fin (m + 1)}
    (hkj : k ≠ j) (c : ZMod 2) : linX b (i, j, c) (b k) = b k := by
  by_cases hij : i = j
  · subst hij
    rw [linX_self]
    rfl
  · rw [linX_apply b hij, Basis.repr_self, Finsupp.single_apply, ite_eq_right hkj, mul_zero,
      zero_smul, add_zero]

theorem linX_mem_centreGroup (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j : Fin (m + 1)}
    (hij : i ≠ j) (c : ZMod 2) : linX b (i, j, c) ∈ centreGroup V (b i) := by
  intro v
  rw [linX_apply b hij, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem linX_add (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j : Fin (m + 1)} (hij : i ≠ j)
    (c d : ZMod 2) : linX b (i, j, c + d) = linX b (i, j, c) * linX b (i, j, d) := by
  rw [linX, linX, linX, stGen_of_ne hij, stGen_of_ne hij, stGen_of_ne hij,
    Matrix.SpecialLinearGroup.transvection_add, map_mul]

theorem linX_comm (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j k l : Fin (m + 1)} (hij : i ≠ j)
    (hkl : k ≠ l) (hnot : ¬ (k = j ∧ l = i)) (c d : ZMod 2) :
    ⁅linX b (i, j, c), linX b (k, l, d)⁆ =
      if j = k then linX b (i, l, c * d) else if i = l then linX b (k, j, -(c * d)) else 1 := by
  rw [linX, linX, ← map_commutatorElement, commutatorElement_stGen hij hkl hnot c d]
  split_ifs <;> simp [linX]

theorem exists_apply_eq_basis [FiniteDimensional (ZMod 2) V]
    (h : CEHyp π E a ⊤ (centreGroup V a)) (ha : a ≠ 0) (b : Basis (Fin (m + 1)) (ZMod 2) V)
    (i : Fin (m + 1)) : ∃ k, π k a = b i := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq_of_ne (F := ZMod 2) ha (b.ne_zero i)
  have hgr : g ∈ π.range := h.range_eq ▸ mem_top g
  obtain ⟨k, hk⟩ := hgr
  exact ⟨k, by rw [hk, hg]⟩

theorem linX_mem_map_Ept (h : CEHyp π E a ⊤ (centreGroup V a))
    (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j : Fin (m + 1)} (hp : ∃ k, π k a = b i)
    (hij : i ≠ j) (c : ZMod 2) : linX b (i, j, c) ∈ (Ept π E a (b i)).map π := by
  obtain ⟨k, hk⟩ := hp
  rw [h.map_Ept hk, centreGroup_map_conj, hk]
  exact linX_mem_centreGroup b hij c

@[expose] noncomputable def linY (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K) (a : V)
    (b : Basis (Fin (m + 1)) (ZMod 2) V) (s : Fin (m + 1) × Fin (m + 1) × ZMod 2) : K :=
  open Classical in if s.1 = s.2.1 then 1 else liftPt π E a (b s.1) (linX b s)

theorem linY_of_ne (b : Basis (Fin (m + 1)) (ZMod 2) V) {i j : Fin (m + 1)} (hij : i ≠ j)
    (c : ZMod 2) : linY π E a b (i, j, c) = liftPt π E a (b i) (linX b (i, j, c)) := by
  simp [linY, hij]

theorem linY_self (b : Basis (Fin (m + 1)) (ZMod 2) V) (i : Fin (m + 1)) (c : ZMod 2) :
    linY π E a b (i, i, c) = 1 := by
  simp [linY]

variable [FiniteDimensional (ZMod 2) V] (h : CEHyp π E a ⊤ (centreGroup V a)) (ha : a ≠ 0)
  (b : Basis (Fin (m + 1)) (ZMod 2) V)
include h ha

theorem linY_mem {i j : Fin (m + 1)} (hij : i ≠ j) (c : ZMod 2) :
    linY π E a b (i, j, c) ∈ Ept π E a (b i) := by
  rw [linY_of_ne b hij]
  exact liftPt_mem (linX_mem_map_Ept h b (exists_apply_eq_basis h ha b i) hij c)

theorem apply_linY (s : Fin (m + 1) × Fin (m + 1) × ZMod 2) :
    π (linY π E a b s) = linX b s := by
  obtain ⟨i, j, c⟩ := s
  by_cases hij : i = j
  · subst hij
    rw [linY_self, linX_self, map_one]
  · rw [linY_of_ne b hij]
    exact apply_liftPt (linX_mem_map_Ept h b (exists_apply_eq_basis h ha b i) hij c)

theorem linY_comm {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hnot : ¬ (k = j ∧ l = i))
    (c d : ZMod 2) :
    ⁅linY π E a b (i, j, c), linY π E a b (k, l, d)⁆ =
      if j = k then linY π E a b (i, l, c * d)
        else if i = l then linY π E a b (k, j, -(c * d)) else 1 := by
  have hp := exists_apply_eq_basis h ha b
  by_cases hjk : j = k
  · subst hjk
    have hil : i ≠ l := fun e => hnot ⟨rfl, e.symm⟩
    rw [ite_eq_left rfl, linY_of_ne b hij,
      h.commutatorElement_liftPt (hp i) (linX_mem_map_Ept h b (hp i) hij c)
        (by rw [apply_linY h ha b]; exact linX_apply_basis b hil d),
      apply_linY h ha b, linX_comm b hij hkl hnot, ite_eq_left rfl, linY_of_ne b hil]
  · have hkj : k ≠ j := fun e => hjk e.symm
    rw [ite_eq_right hjk, linY_of_ne b hkl,
      h.commutatorElement_liftPt' (hp k) (linX_mem_map_Ept h b (hp k) hkl d)
        (by rw [apply_linY h ha b]; exact linX_apply_basis b hkj c),
      apply_linY h ha b, linX_comm b hij hkl hnot, ite_eq_right hjk]
    by_cases hil : i = l
    · subst hil
      rw [ite_eq_left rfl, ite_eq_left rfl, linY_of_ne b hkj]
    · rw [ite_eq_right hil, ite_eq_right hil, h.liftPt_one (hp k)]

theorem linY_rels :
    ∀ r ∈ CFSG.Open.steinbergSLRels (m + 1) (ZMod 2), FreeGroup.lift (linY π E a b) r = 1 := by
  rintro r ((⟨i, c, rfl⟩ | ⟨i, j, c, d, hij, rfl⟩) | ⟨i, j, k, l, c, d, hij, hkl, hnot, rfl⟩)
  · rw [FreeGroup.lift_apply_of, linY_self]
  · rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, linY_of_ne b hij, linY_of_ne b hij, linY_of_ne b hij,
      linX_add b hij, h.liftPt_mul (exists_apply_eq_basis h ha b i)
        (linX_mem_map_Ept h b (exists_apply_eq_basis h ha b i) hij c)
        (linX_mem_map_Ept h b (exists_apply_eq_basis h ha b i) hij d), mul_inv_cancel]
  · have hc := linY_comm h ha b hij hkl hnot c d
    rw [commutatorElement_def] at hc
    have hite : FreeGroup.lift (linY π E a b)
        (if j = k then FreeGroup.of (i, l, c * d)
          else if i = l then FreeGroup.of (k, j, -(c * d)) else 1) =
        if j = k then linY π E a b (i, l, c * d)
          else if i = l then linY π E a b (k, j, -(c * d)) else 1 := by
      split_ifs <;> simp [FreeGroup.lift_apply_of]
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, FreeGroup.lift_apply_of,
      FreeGroup.lift_apply_of, hite, ← hc, mul_inv_cancel]

end Lift

open CFSG.LieType.Steinberg.SL in
theorem ker_eq_bot_of_linPair_of_three_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)}
    {E : Subgroup K} {a : V} (ha : a ≠ 0) (hdim : 3 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a ⊤ (centreGroup V a)) : π.ker = ⊥ := by
  obtain ⟨m, hm⟩ : ∃ m, finrank (ZMod 2) V = m + 1 := ⟨finrank (ZMod 2) V - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  set b : Basis (Fin (m + 1)) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hm
  obtain ⟨φ, hφ⟩ := exists_steinbergSLRels_equiv (F := ZMod 2) hm2
  set σ₀ := PresentedGroup.toGroup (linY_rels h ha b)
  have hφs : ∀ s, φ (PresentedGroup.of s) = stGen s := by
    rintro ⟨i, j, c⟩
    by_cases hij : i = j
    · subst hij
      have h1 : (PresentedGroup.of (i, i, c) :
          PresentedGroup (CFSG.Open.steinbergSLRels (m + 1) (ZMod 2))) = 1 :=
        PresentedGroup.one_of_mem (Or.inl (Or.inl ⟨i, c, rfl⟩))
      rw [stGen_self, h1, map_one]
    · apply Subtype.ext
      rw [hφ i j c hij, stGen_of_ne hij]
      rfl
  have hcomp0 : π.comp σ₀ = (linIota b).comp φ.toMonoidHom := PresentedGroup.ext fun s => by
    rw [MonoidHom.comp_apply, PresentedGroup.toGroup.of, apply_linY h ha b,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφs]
    rfl
  set σ := σ₀.comp φ.symm.toMonoidHom
  have hσ : ∀ g, π (σ g) = linIota b g := by
    intro g
    have := DFunLike.congr_fun hcomp0 (φ.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] at this
    exact this
  have hσS : ∀ s, σ (stGen s) = linY π E a b s := by
    intro s
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hφs, MulEquiv.symm_apply_apply,
      PresentedGroup.toGroup.of]
  have hcomp : π.comp σ = linIota b := MonoidHom.ext hσ
  have hp0 := exists_apply_eq_basis h ha b 0
  refine h.ker_eq_bot_of_hom σ (by rw [hcomp]; exact linIota_injective b)
    (by rw [hcomp, MonoidHom.range_eq_top.mpr (linIota_surjective b)]) hp0 ?_
  refine h.Ept_le_range hp0 σ
    (S := {g | ∃ j, j ≠ 0 ∧ ∀ v, g v = v + b.repr v j • b 0}) ?_ ?_
  · obtain ⟨k, hk⟩ := hp0
    rw [h.map_Ept hk, centreGroup_map_conj, hk]
    exact centreGroup_le_closure b 0
  · rintro g ⟨j, hj, hg⟩
    refine ⟨σ (stGen (0, j, 1)), ⟨_, rfl⟩, ?_, ?_⟩
    · rw [hσS]
      exact linY_mem h ha b (Ne.symm hj) 1
    · rw [hσ]
      refine LinearEquiv.ext fun v => ?_
      rw [hg]
      exact (linX_apply b (Ne.symm hj) 1 v).trans (by rw [one_mul])

end CFSG.LargeExtraspecial.S4
