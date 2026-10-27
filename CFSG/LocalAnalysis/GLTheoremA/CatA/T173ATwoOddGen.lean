module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoOddBlock
import CFSG.ClassicalGroups.SpecialLinear.CyclicRootGroups

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp glue glueHom glue_apply_left
  glue_apply_right exists_decomp isCompl_fixSp_comSp)
open Module (Basis)
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[expose] def linTwoCrossTransv {r : ℕ} (P : Fin r → Submodule (ZMod 2) V)
    (V0 : Submodule (ZMod 2) V) : Set (V ≃ₗ[ZMod 2] V) :=
  {t | ∃ (i j : Fin r) (hij : i ≠ j) (a : V) (ha : a ∈ P i) (f : V →ₗ[ZMod 2] ZMod 2)
      (_ : ∀ v ∈ V0, f v = 0) (hfP : ∀ k, k ≠ j → ∀ v ∈ P k, f v = 0),
      t = S172A.GL.tv a f (hfP i hij a ha)}

private theorem comap_subtype_iSup {ι : Type*} {A : ι → Submodule (ZMod 2) V}
    (W : Submodule (ZMod 2) V) (hA : ∀ i, A i ≤ W) :
    (⨆ i, (A i).comap W.subtype) = (⨆ i, A i).comap W.subtype := by
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.coe_injective
  rw [Submodule.map_iSup]
  simp only [Submodule.map_comap_subtype]
  rw [iSup_congr (fun i => inf_of_le_right (hA i)), inf_of_le_right (iSup_le hA)]

private theorem iSupIndep_comap_subtype {r : ℕ} {P : Fin r → Submodule (ZMod 2) V}
    (hindep : iSupIndep P) (W : Submodule (ZMod 2) V) (hW : W = ⨆ i, P i) :
    iSupIndep (fun i => (P i).comap W.subtype) := by
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxi, hxj⟩ := hx
  rw [iSup_subtype'] at hxj
  rw [comap_subtype_iSup (A := fun j : {j : Fin r // j ≠ i} => P j.1) W
    (fun j => by rw [hW]; exact le_iSup P j.1)] at hxj
  have hdisj := hindep i
  rw [iSup_subtype'] at hdisj
  exact Subtype.ext (by simpa using hdisj.le_bot ⟨hxi, hxj⟩)

private theorem isInternal_comap_subtype {r : ℕ} {P : Fin r → Submodule (ZMod 2) V}
    (hindep : iSupIndep P) (W : Submodule (ZMod 2) V) (hW : W = ⨆ i, P i) :
    DirectSum.IsInternal (fun i => (P i).comap W.subtype) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact iSupIndep_comap_subtype hindep W hW
  · rw [eq_top_iff]
    intro x _
    rw [comap_subtype_iSup W (fun j => by rw [hW]; exact le_iSup P j), Submodule.mem_comap]
    exact hW ▸ x.2

private theorem commutator_mem {G : Type*} [Group G] (N : Subgroup G) {x y : G}
    (hx : x ∈ N) (hy : y ∈ N) : ⁅x, y⁆ ∈ N := by
  simp only [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)

private theorem zmod_two_eq_zero_or_one' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

private theorem glueHom_transvection {U Uc : Submodule (ZMod 2) V} (hc : IsCompl U Uc)
    (f : Module.Dual (ZMod 2) U) (d : U) (h : f d = 0) :
    glueHom hc (LinearEquiv.transvection h) =
      LinearEquiv.transvection
        (f := f.comp (Submodule.projectionOnto U Uc hc)) (v := (d : V))
        (by rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left hc d.2, h]) := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨w, u, hx⟩ := exists_decomp hc x
  rw [hx, map_add, map_add]
  rw [show glueHom hc (LinearEquiv.transvection h) (w : V) =
        ((LinearEquiv.transvection h w : U) : V) from glue_apply_left hc _ w,
      show glueHom hc (LinearEquiv.transvection h) (u : V) = (u : V) from
        glue_apply_right hc _ u]
  simp only [LinearEquiv.transvection.apply, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_left hc w.2,
    Submodule.projectionOnto_apply_of_mem_right hc u.2, map_zero, Submodule.coe_add,
    Submodule.coe_smul, zero_smul]
  abel

private theorem toLin'_transvection {r : ℕ} {U : Submodule (ZMod 2) V}
    (bW : Basis (Σ i : Fin r, Fin 2) (ZMod 2) U) (a b : Σ i : Fin r, Fin 2)
    (hab : a ≠ b) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) U
        (Matrix.GeneralLinearGroup.toLin' bW
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hab 1)))
      = LinearEquiv.transvection (f := bW.dualBasis b) (v := bW a)
          (by rw [Basis.dualBasis_apply_self, if_neg hab]) := by
  change (Matrix.GeneralLinearGroup.toLin' bW
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hab 1))).toLinearEquiv
    = LinearEquiv.transvection (f := bW.dualBasis b) (v := bW a)
        (by rw [Basis.dualBasis_apply_self, if_neg hab])
  refine Basis.ext' (b := bW) (fun k => ?_)
  rw [Matrix.GeneralLinearGroup.toLin'_apply, Basis.repr_self,
    LinearEquiv.transvection.apply, Basis.dualBasis_apply_self]
  have hM : ((Matrix.SpecialLinearGroup.toGL (R := ZMod 2)
        (Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2))) :
        Matrix (Σ i : Fin r, Fin 2) (Σ i : Fin r, Fin 2) (ZMod 2))
      = 1 + Matrix.single a b 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.transvection_coe]
  rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul,
    Finsupp.single_eq_pi_single, map_add, map_smul, Fintype.linearCombination_apply_single,
    Fintype.linearCombination_apply_single, one_smul]
  by_cases hkb : k = b
  · subst hkb
    simp
  · simp [hkb]

theorem lin_two_cross_transv_generate {E : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ}
    {x : Fin r → V ≃ₗ[ZMod 2] V} {P : Fin r → Submodule (ZMod 2) V}
    {V0 : Submodule (ZMod 2) V} (hF : LinTwoStdFrame E x P V0) (hr : 2 ≤ r)
    {g : V ≃ₗ[ZMod 2] V} (hg3 : g ^ 3 = 1) (hfix : fixSp g = V0) (hcom : comSp g = ⨆ j, P j) :
    linTwoOddBlock g ≤ Subgroup.closure (linTwoCrossTransv P V0) := by
  have hdir : DirectSum.IsInternal (fun o : Option (Fin r) => o.elim V0 P) := hF.2.1
  have hPdim : ∀ i, Module.finrank (ZMod 2) (P i) = 2 := hF.2.2.1
  have hindep : iSupIndep P := (DirectSum.IsInternal.submodule_iSupIndep hdir).comp
    (f := Option.some) (fun a b h => Option.some.inj h)
  have hPiU : ∀ i, P i ≤ comSp g := fun i => by rw [hcom]; exact le_iSup P i
  have hI : DirectSum.IsInternal (fun i => (P i).comap (comSp g).subtype) :=
    isInternal_comap_subtype hindep (comSp g) hcom
  let v : ∀ i : Fin r, Basis (Fin 2) (ZMod 2) ((P i).comap (comSp g).subtype) := fun i =>
    (Module.finBasisOfFinrankEq (ZMod 2) (P i) (hPdim i)).map
      (Submodule.comapSubtypeEquivOfLe (hPiU i)).symm
  let bW : Basis (Σ i : Fin r, Fin 2) (ZMod 2) (comSp g) := hI.collectedBasis v
  have hbWmem : ∀ (i : Fin r) (k : Fin 2), ((bW ⟨i, k⟩ : comSp g) : V) ∈ P i := by
    intro i k
    have h1 : bW ⟨i, k⟩ = v i k := by rw [hI.collectedBasis_coe v]
    rw [h1]
    exact (v i k).2
  have hdual_zero : ∀ (a : Σ i : Fin r, Fin 2) (j : Fin r) (hj : j ≠ a.1) (w : V)
      (hw : w ∈ P j), bW.dualBasis a ⟨w, hPiU j hw⟩ = 0 := by
    intro a j hj w hw
    rw [Basis.dualBasis_apply]
    exact hI.collectedBasis_repr_of_mem_ne (v := v) (x := ⟨w, hPiU j hw⟩) (i := j)
      (j := a.1) (a := a.2) hj hw
  let H : Subgroup (V ≃ₗ[ZMod 2] V) := Subgroup.closure (linTwoCrossTransv P V0)
  let hc₀ : IsCompl (comSp g) (fixSp g) := (isCompl_fixSp_comSp hg3).symm
  let H' : Subgroup (comSp g ≃ₗ[ZMod 2] comSp g) := H.comap (glueHom hc₀)
  let Elem (a b : Σ i : Fin r, Fin 2) (hab : a ≠ b) : comSp g ≃ₗ[ZMod 2] comSp g :=
    LinearEquiv.transvection (f := bW.dualBasis b) (v := bW a)
      (by rw [Basis.dualBasis_apply_self, if_neg hab])
  have hElem_mem : ∀ (a b : Σ i : Fin r, Fin 2) (hab : a ≠ b), a.1 ≠ b.1 →
      Elem a b hab ∈ H' := by
    intro a b hab habplane
    rw [Subgroup.mem_comap]
    dsimp only [Elem]
    rw [glueHom_transvection]
    apply Subgroup.subset_closure
    refine ⟨a.1, b.1, habplane, (bW a : V), hbWmem a.1 a.2,
      (bW.dualBasis b).comp (Submodule.projectionOnto (comSp g) (fixSp g) hc₀), ?_, ?_, ?_⟩
    · intro w hw
      have hw' : w ∈ fixSp g := by rw [hfix]; exact hw
      rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right hc₀ hw', map_zero]
    · intro k hk w hw
      rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left hc₀ (hPiU k hw)]
      exact hdual_zero b k hk w hw
    · exact LinearEquiv.ext (fun y => rfl)
  let Ψ : Matrix.GeneralLinearGroup (Σ i : Fin r, Fin 2) (ZMod 2) ≃*
      (comSp g ≃ₗ[ZMod 2] comSp g) :=
    (Matrix.GeneralLinearGroup.toLin' bW).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (comSp g))
  let Φ : Matrix.SpecialLinearGroup (Σ i : Fin r, Fin 2) (ZMod 2) →*
      (comSp g ≃ₗ[ZMod 2] comSp g) :=
    Ψ.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
  let N : Subgroup (Matrix.SpecialLinearGroup (Σ i : Fin r, Fin 2) (ZMod 2)) := H'.comap Φ
  have htoLin : ∀ (a b : Σ i : Fin r, Fin 2) (hab : a ≠ b),
      Φ (Matrix.SpecialLinearGroup.transvection hab 1) = Elem a b hab := by
    intro a b hab
    dsimp only [Φ, Ψ, Elem]
    exact toLin'_transvection bW a b hab
  have hNcross : ∀ (a b : Σ i : Fin r, Fin 2) (hab : a ≠ b), a.1 ≠ b.1 →
      Matrix.SpecialLinearGroup.transvection hab 1 ∈ N := by
    intro a b hab habplane
    rw [Subgroup.mem_comap, htoLin a b hab]
    exact hElem_mem a b hab habplane
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have hNsame : ∀ (a b : Σ i : Fin r, Fin 2) (hab : a ≠ b), a.1 = b.1 →
      Matrix.SpecialLinearGroup.transvection hab 1 ∈ N := by
    intro a b hab hplane
    obtain ⟨k, hk⟩ := exists_ne a.1
    let m : Σ i : Fin r, Fin 2 := ⟨k, 0⟩
    have ham : a ≠ m := by
      intro h
      exact hk (congrArg Sigma.fst h).symm
    have hmb : m ≠ b := by
      intro h
      exact hk ((congrArg Sigma.fst h).trans hplane.symm)
    have hcomm := CFSG.ClassicalGroups.SpecialLinear.steinberg_commutator
      (R := ZMod 2) (i := a) (j := m) (k := b) ham hmb hab 1 1
    rw [show (1 : ZMod 2) * 1 = 1 from one_mul 1] at hcomm
    rw [← hcomm]
    refine commutator_mem N (hNcross a m ham ?_) (hNcross m b hmb ?_)
    · exact fun h => hk h.symm
    · exact fun h => hk (h.trans hplane.symm)
  have hN : ∀ (i j : Σ i : Fin r, Fin 2) (hij : i ≠ j) (c : ZMod 2),
      Matrix.SpecialLinearGroup.transvection hij c ∈ N := by
    intro i j hij c
    rcases zmod_two_eq_zero_or_one' c with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero]
      exact N.one_mem
    · by_cases hp : i.1 = j.1
      · exact hNsame i j hij hp
      · exact hNcross i j hij hp
  haveI : Nontrivial (Σ i : Fin r, Fin 2) :=
    ⟨⟨⟨0, by omega⟩, 0⟩, ⟨⟨1, by omega⟩, 0⟩, by
      intro h
      have h1 : (⟨0, by omega⟩ : Fin r) = ⟨1, by omega⟩ := congrArg Sigma.fst h
      exact absurd (congrArg Fin.val h1) (by norm_num)⟩
  have hNtop : N = ⊤ :=
    CFSG.ClassicalGroups.SpecialLinear.eq_top_of_forall_transvection_mem N hN
  have htoGL : (Matrix.SpecialLinearGroup.toGL (n := Σ i : Fin r, Fin 2)
      (R := ZMod 2)).range = ⊤ := by
    haveI : Subsingleton (ZMod 2)ˣ :=
      Fintype.card_le_one_iff_subsingleton.mp (by rw [ZMod.card_units 2])
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, eq_top_iff]
    intro A _
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hΦtop : Φ.range = ⊤ := by
    change (Ψ.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL).range = ⊤
    rw [MonoidHom.range_comp, htoGL,
      Subgroup.map_top_of_surjective _ Ψ.surjective]
  have hΦle : Φ.range ≤ H' := by
    rintro y ⟨A, rfl⟩
    exact Subgroup.mem_comap.mp (show A ∈ N from by rw [hNtop]; exact Subgroup.mem_top A)
  have hH' : H' = ⊤ := eq_top_iff.mpr (hΦtop ▸ hΦle)
  have hrange : (glueHom hc₀).range ≤ H := by
    intro y hy
    obtain ⟨h, rfl⟩ := hy
    exact Subgroup.mem_comap.mp (show h ∈ H' from by rw [hH']; exact Subgroup.mem_top h)
  rw [lin_two_oddBlock_eq_range hg3]
  exact hrange

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
