module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTOmBasic

import CFSG.ClassicalGroups.Orthogonal.NonsingularCount
import CFSG.LocalAnalysis.SteinbergBVA7BinaryIsometryTwoParts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

open Polynomial Module CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.KCSpFull (spEnd_mul spEnd_one)

variable {t : StatedSp 4 (ZMod 2)}

noncomputable def fixQ (t : StatedSp 4 (ZMod 2)) : QuadraticForm (ZMod 2) ↥(fixV t) :=
  Q8.comp (fixV t).subtype

private theorem polarBilin_fixQ (t : StatedSp 4 (ZMod 2)) :
    (fixQ t).polarBilin = (spForm 4 (ZMod 2)).restrict (fixV t) := by
  ext x y
  change ((Q8.comp (fixV t).subtype).polarBilin) x y =
    (((spForm 4 (ZMod 2)).restrict (fixV t)) x) y
  rw [QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply,
    polar_Q8, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
  rfl

private theorem spForm_fixV_movV (ht3 : t ^ 3 = 1) {v w : Fin 4 ⊕ Fin 4 → ZMod 2}
    (hv : v ∈ fixV t) (hw : w ∈ movV t) : spForm 4 (ZMod 2) v w = 0 := by
  obtain ⟨u, rfl⟩ := movV_le_range ht3 hw
  have htv : spEnd t v = v := by
    rw [fixV_eq_ker, LinearMap.mem_ker] at hv
    simpa [LinearMap.sub_apply, sub_eq_zero] using hv
  have huni : spForm 4 (ZMod 2) v (spEnd t u) = spForm 4 (ZMod 2) v u := by
    have h := mem_sesqUnitaryGroup.mp (spLin_mem (g := t)) v u
    rw [htv] at h
    exact h
  have hsub : (spEnd t - 1) u = spEnd t u - u := rfl
  rw [hsub, map_sub, huni, sub_self]

theorem fixQ_nondegenerate (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    (fixQ t).polarBilin.Nondegenerate := by
  rw [polarBilin_fixQ]
  exact (sp8_blocks t (orderOf_eq_prime ht3 ht1)).fixed_nondegenerate

private noncomputable def restrictEquiv {g : StatedSp 4 (ZMod 2)} (hg : g * t = t * g) :
    ↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t) where
  toFun v := ⟨spEnd g v, apply_mem_fixV_of_commute hg v.2⟩
  invFun v :=
    ⟨spEnd g⁻¹ v, apply_mem_fixV_of_commute (by
      calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
        _ = t * g⁻¹ := by group) v.2⟩
  left_inv v := by
    apply Subtype.ext
    change spEnd g⁻¹ (spEnd g v) = v
    rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one]
    rfl
  right_inv v := by
    apply Subtype.ext
    change spEnd g (spEnd g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one]
    rfl
  map_add' v w := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c v := by
    apply Subtype.ext
    simp

private theorem coe_restrictEquiv {g : StatedSp 4 (ZMod 2)} (hg : g * t = t * g)
    (v : ↥(fixV t)) : ((restrictEquiv (t := t) hg v : ↥(fixV t)) : Fin 4 ⊕ Fin 4 → ZMod 2) =
      spEnd g v := rfl

private theorem restrictEquiv_mul {g h : StatedSp 4 (ZMod 2)}
    (hg : g * t = t * g) (hh : h * t = t * h) (hgh : g * h * t = t * (g * h)) :
    restrictEquiv (t := t) hgh = restrictEquiv (t := t) hg * restrictEquiv (t := t) hh := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  change spEnd (g * h) v = spEnd g (spEnd h v)
  rw [spEnd_mul, Module.End.mul_apply]

private theorem one_comm : (1 : StatedSp 4 (ZMod 2)) * t = t * 1 := by
  rw [one_mul, mul_one]

private theorem restrictEquiv_one : restrictEquiv (t := t) one_comm = 1 := by
  apply LinearEquiv.ext
  intro v
  apply Subtype.ext
  change spEnd 1 (v : Fin 4 ⊕ Fin 4 → ZMod 2) = (v : Fin 4 ⊕ Fin 4 → ZMod 2)
  rw [spEnd_one]
  rfl

private theorem commSpace_restrictEquiv_eq (ht3 : t ^ 3 = 1) {g : StatedSp 4 (ZMod 2)}
    (hg : g * t = t * g) (htriv : ∀ v ∈ movV t, spEnd g v = v) :
    (commSpace (restrictEquiv (t := t) hg)).map (fixV t).subtype =
      commSpace (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL)) := by
  have hcomp : ∀ v : ↥(fixV t),
      (((fixV t).subtype.comp
        ((restrictEquiv (t := t) hg : ↥(fixV t) →ₗ[ZMod 2] ↥(fixV t)) - 1)) v) =
        (spEnd g - 1) (v : Fin 4 ⊕ Fin 4 → ZMod 2) := by
    intro v
    rfl
  have htl : ((toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL) :
      (Fin 4 ⊕ Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) :
        (Fin 4 ⊕ Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) - 1 =
      spEnd g - 1 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact congrArg (fun x => x - v) (toLinEquiv_apply g v)
  rw [commSpace, commSpace, htl, ← LinearMap.range_comp]
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact ⟨(v : Fin 4 ⊕ Fin 4 → ZMod 2), hcomp v⟩
  · rintro x ⟨v, rfl⟩
    have hv : v ∈ fixV t ⊔ movV t := by
      rw [fixV_sup_movV ht3]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hcomp]
    change (spEnd g) a - a = (spEnd g - 1) (a + b)
    rw [LinearMap.sub_apply, Module.End.one_apply, map_add, htriv b hb]
    abel

theorem finrank_fixV (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    Module.finrank (ZMod 2) ↥(fixV t) + 2 * primaryMultiplicity (spEnd t) q2 = 8 := by
  obtain ⟨s₀, hs₀, hs4⟩ := dimension_count ht3 ht1
  have hfix : Module.finrank (ZMod 2) ↥(fixV t) = 2 * s₀ := hs₀
  omega

private theorem movV_polar_nondegenerate (ht3 : t ^ 3 = 1) :
    ∀ x : ↥(movV t), (∀ y : ↥(movV t),
      QuadraticMap.polar (Q8.comp (movV t).subtype) x y = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  refine Q8_nondegenerate.1 (x : Fin 4 ⊕ Fin 4 → ZMod 2) (fun v => ?_)
  have hv : v ∈ fixV t ⊔ movV t := by
    rw [fixV_sup_movV ht3]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  have hxa : Q8.polarBilin (x : Fin 4 ⊕ Fin 4 → ZMod 2) a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm, polar_Q8]
    exact spForm_fixV_movV ht3 ha x.2
  have hxb : Q8.polarBilin (x : Fin 4 ⊕ Fin 4 → ZMod 2) b = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    have h := hx ⟨b, hb⟩
    change QuadraticMap.polar Q8 (x : Fin 4 ⊕ Fin 4 → ZMod 2) b = 0 at h
    exact h
  rw [hxa, hxb, add_zero]

private theorem mem_om8_iff_restrict (ht3 : t ^ 3 = 1) {g : StatedSp 4 (ZMod 2)}
    (hg : g * t = t * g) (htriv : ∀ v ∈ movV t, spEnd g v = v)
    (hQ : (fixQ t).polarBilin.Nondegenerate) :
    g ∈ OmInSp CFSG.AGLEmbedding.Om8 ↔
      restrictEquiv (t := t) hg ∈ omegaGroup (fixQ t) hQ := by
  constructor
  · intro hOm
    have hω := (mem_Om8_iff_omegaGroup (g : SpGL)).mp (mem_OmInSp.mp hOm)
    have hQ8 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hω.1
    refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ?_, ?_⟩
    · intro v
      change Q8 (spEnd g (v : Fin 4 ⊕ Fin 4 → ZMod 2)) = Q8 (v : Fin 4 ⊕ Fin 4 → ZMod 2)
      rw [← toLinEquiv_apply g]
      exact hQ8 v
    · have hfin : finrank (ZMod 2) ↥(commSpace (restrictEquiv (t := t) hg)) =
          finrank (ZMod 2) ↥(commSpace
            (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL))) := by
        rw [← Submodule.finrank_map_subtype_eq (fixV t)
          (commSpace (restrictEquiv (t := t) hg)),
          commSpace_restrictEquiv_eq ht3 hg htriv]
      rw [hfin]
      exact hω.2
  · rintro ⟨horth, heven⟩
    have hQfix := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp horth
    have hQ8 : ∀ v, Q8 (spEnd g v) = Q8 v := by
      intro v
      have hv : v ∈ fixV t ⊔ movV t := by
        rw [fixV_sup_movV ht3]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, htriv b hb]
      have hqa : Q8 (spEnd g a) = Q8 a := by
        have h := hQfix ⟨a, ha⟩
        simpa [fixQ, coe_restrictEquiv] using h
      have hBab : spForm 4 (ZMod 2) (spEnd g a) b = 0 := by
        have huni : spForm 4 (ZMod 2) (spEnd g a) (spEnd g b) = spForm 4 (ZMod 2) a b :=
          mem_sesqUnitaryGroup.mp (spLin_mem (g := g)) a b
        rw [htriv b hb] at huni
        rw [huni]
        exact spForm_fixV_movV ht3 ha hb
      calc Q8 (spEnd g a + b)
          = Q8 (spEnd g a) + Q8 b + spForm 4 (ZMod 2) (spEnd g a) b := by
            rw [QuadraticMap.map_add Q8, polar_Q8]
        _ = Q8 a + Q8 b := by rw [hqa, hBab, add_zero]
        _ = Q8 (a + b) := by
            rw [QuadraticMap.map_add Q8, polar_Q8, spForm_fixV_movV ht3 ha hb, add_zero]
    have hO8 : toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL) ∈
        TauCeti.QuadraticMap.orthogonalGroup Q8 := by
      refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ?_
      intro v
      rw [toLinEquiv_apply]
      exact hQ8 v
    have heven' : Even (finrank (ZMod 2) (commSpace
        (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL)))) := by
      have hfin : finrank (ZMod 2) ↥(commSpace (restrictEquiv (t := t) hg)) =
          finrank (ZMod 2) ↥(commSpace
            (toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL))) := by
        rw [← Submodule.finrank_map_subtype_eq (fixV t)
          (commSpace (restrictEquiv (t := t) hg)),
          commSpace_restrictEquiv_eq ht3 hg htriv]
      rw [← hfin]
      exact heven
    exact mem_OmInSp.mpr ((mem_Om8_iff_omegaGroup (g : SpGL)).mpr ⟨hO8, heven'⟩)

private noncomputable def restrictHom (ht3 : t ^ 3 = 1) :
    spSupported t {(X - 1 : (ZMod 2)[X])} →*
      (↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t)) where
  toFun g := restrictEquiv (t := t) ((mem_spSupported_X_sub_one_iff (t := t) ht3).1 g.2).1
  map_one' := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change spEnd (1 : StatedSp 4 (ZMod 2)) (v : Fin 4 ⊕ Fin 4 → ZMod 2) =
      (v : Fin 4 ⊕ Fin 4 → ZMod 2)
    rw [spEnd_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    change spEnd ((g : StatedSp 4 (ZMod 2)) * (h : StatedSp 4 (ZMod 2)))
        (v : Fin 4 ⊕ Fin 4 → ZMod 2) =
      spEnd (g : StatedSp 4 (ZMod 2)) (spEnd (h : StatedSp 4 (ZMod 2))
        (v : Fin 4 ⊕ Fin 4 → ZMod 2))
    rw [spEnd_mul, Module.End.mul_apply]

private noncomputable def restrictOmegaHom (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hQ : (fixQ t).polarBilin.Nondegenerate) :
    ↥(spSupported t {(X - 1 : (ZMod 2)[X])} ⊓ OmInSp CFSG.AGLEmbedding.Om8) →*
      ↥(omegaGroup (fixQ t) hQ) :=
  MonoidHom.codRestrict
    ((restrictHom (t := t) ht3).comp (Subgroup.inclusion inf_le_left))
    (omegaGroup (fixQ t) hQ) (fun g => by
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp g.2
      obtain ⟨hcomm, htriv⟩ := (mem_spSupported_X_sub_one_iff (t := t) ht3).1 hg1
      exact (mem_om8_iff_restrict ht3 hcomm htriv hQ).1 hg2)

private theorem restrictOmegaHom_injective (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hQ : (fixQ t).polarBilin.Nondegenerate) :
    Function.Injective (restrictOmegaHom (t := t) ht3 ht1 hQ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Subtype.ext
  apply eq_one_of_trivial_on_primary (s := t) ht3
  intro k hk v hv
  obtain ⟨hg1, -⟩ := Subgroup.mem_inf.mp a.2
  obtain ⟨hcomm, htriv⟩ := (mem_spSupported_X_sub_one_iff (t := t) ht3).1 hg1
  rcases mem_primaryFactors_pow_three (spEnd_pow ht3) hk with hk1 | hk2
  · rw [hk1] at hv
    have hres : restrictEquiv (t := t) hcomm = 1 := by
      have h := congrArg Subtype.val ha
      simpa [restrictOmegaHom, restrictHom, MonoidHom.codRestrict] using h
    have hpoint := congrArg (fun e : ↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t) =>
      ((e ⟨v, hv⟩ : ↥(fixV t)) : Fin 4 ⊕ Fin 4 → ZMod 2)) hres
    simpa [coe_restrictEquiv] using hpoint
  · rw [hk2] at hv
    exact htriv v hv

private theorem restrictOmegaHom_surjective (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hQ : (fixQ t).polarBilin.Nondegenerate) :
    Function.Surjective (restrictOmegaHom (t := t) ht3 ht1 hQ) := by
  intro h
  by_cases hmem : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd t)
  · obtain ⟨φ, hφ⟩ := (sp8_blocks t (orderOf_eq_prime ht3 ht1)).fixedFactor hmem
    have horth : (h : ↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t)) ∈
        TauCeti.QuadraticMap.orthogonalGroup (fixQ t) := h.2.1
    have hQh := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp horth
    have hpolar : ∀ x y, QuadraticMap.polar (fixQ t) (h.val x) (h.val y) =
        QuadraticMap.polar (fixQ t) x y := by
      intro x y
      simp only [QuadraticMap.polar]
      rw [← h.val.map_add, hQh (x + y), hQh x, hQh y]
    let hGL : LinearMap.GeneralLinearGroup (ZMod 2) ↥(fixV t) :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv (h : ↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t))
    have hsesq : hGL ∈ sesqUnitaryGroup ((spForm 4 (ZMod 2)).restrict (fixV t)) := by
      rw [mem_sesqUnitaryGroup]
      intro x y
      rw [← polarBilin_fixQ t]
      simpa only [QuadraticMap.polarBilin_apply_apply, hGL,
        LinearMap.GeneralLinearGroup.coe_ofLinearEquiv] using hpolar x y
    let g : spSupported t {(X - 1 : (ZMod 2)[X])} := φ.symm ⟨hGL, hsesq⟩
    have hφg : φ g = ⟨hGL, hsesq⟩ := φ.apply_symm_apply _
    have hgact : ∀ v : ↥(fixV t),
        spEnd (g : StatedSp 4 (ZMod 2)) (v : Fin 4 ⊕ Fin 4 → ZMod 2) =
          (h.val v : Fin 4 ⊕ Fin 4 → ZMod 2) := by
      intro v
      have h := hφ g v
      rw [hφg] at h
      simpa [hGL] using h.symm
    have hres : restrictEquiv (t := t)
        ((mem_spSupported_X_sub_one_iff (t := t) ht3).1 g.2).1 = h.val := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact hgact v
    have hOm : (g : StatedSp 4 (ZMod 2)) ∈ OmInSp CFSG.AGLEmbedding.Om8 :=
      (mem_om8_iff_restrict ht3
        ((mem_spSupported_X_sub_one_iff (t := t) ht3).1 g.2).1
        ((mem_spSupported_X_sub_one_iff (t := t) ht3).1 g.2).2 hQ).2
        (by rw [hres]; exact h.2)
    refine ⟨⟨g, Subgroup.mem_inf.mpr ⟨g.2, hOm⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [restrictOmegaHom, restrictHom, MonoidHom.codRestrict] using hres
  · have hbot : fixV t = ⊥ :=
      primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one hmem
    haveI : Subsingleton ↥(fixV t) := by rw [hbot]; infer_instance
    haveI : Subsingleton (↥(fixV t) ≃ₗ[ZMod 2] ↥(fixV t)) :=
      ⟨fun f g => LinearEquiv.ext fun x => Subsingleton.elim (f x) (g x)⟩
    haveI : Subsingleton ↥(omegaGroup (fixQ t) hQ) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact ⟨1, Subsingleton.elim _ h⟩

theorem nonempty_spSupported_inf_om8_equiv (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    Nonempty (↥(spSupported t {X - 1} ⊓ OmInSp CFSG.AGLEmbedding.Om8) ≃*
      ↥(omegaGroup (fixQ t) (fixQ_nondegenerate ht3 ht1))) :=
  ⟨MulEquiv.ofBijective
    (restrictOmegaHom (t := t) ht3 ht1 (fixQ_nondegenerate ht3 ht1))
    ⟨restrictOmegaHom_injective ht3 ht1 (fixQ_nondegenerate ht3 ht1),
      restrictOmegaHom_surjective ht3 ht1 (fixQ_nondegenerate ht3 ht1)⟩⟩


theorem ncard_fixQ_of_mult_one (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (htΩ : t ∈ OmInSp CFSG.AGLEmbedding.Om8) (hm : primaryMultiplicity (spEnd t) q2 = 1) :
    {v | fixQ t v = 1}.ncard = 36 := by
  classical
  haveI : Finite ↥(fixV t) := Module.finite_of_finite (ZMod 2)
  haveI : Finite ↥(movV t) := Module.finite_of_finite (ZMod 2)
  have hV2dim : Module.finrank (ZMod 2) ↥(movV t) = 2 * primaryMultiplicity (spEnd t) q2 := by
    haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
    rw [movV, finrank_primaryComponent, natDegree_q2]
  have hV2card : Nat.card ↥(movV t) = 4 ^ primaryMultiplicity (spEnd t) q2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(movV t)), hV2dim, Nat.card_zmod]
    change 2 ^ (2 * primaryMultiplicity (spEnd t) q2) =
      (2 ^ 2) ^ primaryMultiplicity (spEnd t) q2
    rw [pow_mul]
  have h120 : {v : Fin 4 ⊕ Fin 4 → ZMod 2 | Q8 v = 1}.ncard = 120 := by
    have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadPlus 3
    have h' : 2 * {v : Fin 4 ⊕ Fin 4 → ZMod 2 | Q8 v = 1}.ncard + 2 ^ 4 = 4 ^ 4 := by
      simpa [Q8] using h
    norm_num at h'
    omega
  have hcompl : IsCompl (fixV t) (movV t) :=
    IsCompl.of_eq (fixV_inf_movV t) (fixV_sup_movV ht3)
  have horth : ∀ w₁ ∈ fixV t, ∀ w₂ ∈ movV t, QuadraticMap.polar Q8 w₁ w₂ = 0 := by
    intro w₁ h₁ w₂ h₂
    rw [polar_Q8]
    exact spForm_fixV_movV ht3 h₁ h₂
  set A : ℕ := {w : ↥(fixV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard with hA
  set B : ℕ := {w : ↥(fixV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 0}.ncard with hB
  set C : ℕ := {w : ↥(movV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard with hC
  set D : ℕ := {w : ↥(movV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 0}.ncard with hD
  have hmain : 120 = A * D + B * C := by
    have h := ncard_eq_one_of_isCompl Q8 hcompl horth
    rw [h120] at h
    simpa [hA, hB, hC, hD] using h
  have hsum2 : D + C = 4 := by
    have h := ncard_zero_add_ncard_one Q8 (movV t)
    rw [hV2card, hm] at h
    norm_num at h
    simpa [hC, hD] using h
  have h3dvd : 3 ∣ C := by
    have h := three_dvd_ncard_one_of_fixedPointFree Q8 (movV t) (spEnd t)
      (spEnd_pow ht3) ?_ ?_ ?_
    · simpa [hC] using h
    · intro w hw
      exact apply_mem_movV_of_commute (t := t) (g := t) rfl hw
    · intro w hw hfixw
      have hwfix : w ∈ fixV t := by
        rw [fixV_eq_ker, LinearMap.mem_ker]
        simpa [LinearMap.sub_apply, sub_eq_zero] using hfixw
      have hmem : w ∈ fixV t ⊓ movV t := Submodule.mem_inf.mpr ⟨hwfix, hw⟩
      rw [fixV_inf_movV t, Submodule.mem_bot] at hmem
      exact hmem
    · intro v
      have hω := (mem_Om8_iff_omegaGroup (t : SpGL)).mp (mem_OmInSp.mp htΩ)
      rw [← toLinEquiv_apply t]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hω.1 v
  have hC3 : C = 3 := by
    have hgauss := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic
      (Q8.comp (movV t).subtype) (movV_polar_nondegenerate ht3)
      (m := primaryMultiplicity (spEnd t) q2) hV2card
    rw [hm] at hgauss
    simp only [pow_one] at hgauss
    have hC' : {x : ↥(movV t) | (Q8.comp (movV t).subtype) x = 1}.ncard = C := by
      change {x : ↥(movV t) | Q8 (x : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard = C
      rw [hC]
    rw [hC'] at hgauss
    obtain ⟨k, hk⟩ := h3dvd
    clear hC' hV2dim hV2card hm h120 hsum2
    omega
  have hD1 : D = 1 := by omega
  have hdim : Module.finrank (ZMod 2) ↥(fixV t) = 6 := by
    have hf := finrank_fixV ht3 ht1
    rw [hm] at hf
    omega
  have hsum1 : B + A = 64 := by
    have h := ncard_zero_add_ncard_one Q8 (fixV t)
    have hcard : Nat.card ↥(fixV t) = 64 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixV t)), hdim, Nat.card_zmod]
      norm_num
    rw [hcard] at h
    simpa [hA, hB] using h
  rw [hC3, hD1] at hmain
  change {v : ↥(fixV t) | Q8 (v : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard = 36
  rw [← hA]
  clear hV2dim hV2card h120 hsum2 hdim hC3 hD1 hC hD
  omega


theorem ncard_fixQ_of_mult_two (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (htΩ : t ∈ OmInSp CFSG.AGLEmbedding.Om8) (hm : primaryMultiplicity (spEnd t) q2 = 2) :
    {v | fixQ t v = 1}.ncard = 6 := by
  classical
  haveI : Finite ↥(fixV t) := Module.finite_of_finite (ZMod 2)
  haveI : Finite ↥(movV t) := Module.finite_of_finite (ZMod 2)
  have hV2dim : Module.finrank (ZMod 2) ↥(movV t) = 2 * primaryMultiplicity (spEnd t) q2 := by
    haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
    rw [movV, finrank_primaryComponent, natDegree_q2]
  have hV2card : Nat.card ↥(movV t) = 4 ^ primaryMultiplicity (spEnd t) q2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(movV t)), hV2dim, Nat.card_zmod]
    change 2 ^ (2 * primaryMultiplicity (spEnd t) q2) =
      (2 ^ 2) ^ primaryMultiplicity (spEnd t) q2
    rw [pow_mul]
  have hV2card16 : Nat.card ↥(movV t) = 16 := by
    rw [hV2card, hm]
    norm_num
  have h120 : {v : Fin 4 ⊕ Fin 4 → ZMod 2 | Q8 v = 1}.ncard = 120 := by
    have h := CFSG.LocalAnalysis.SteinbergBV.BinaryTwoParts.two_mul_ncard_quadPlus 3
    have h' : 2 * {v : Fin 4 ⊕ Fin 4 → ZMod 2 | Q8 v = 1}.ncard + 2 ^ 4 = 4 ^ 4 := by
      simpa [Q8] using h
    norm_num at h'
    omega
  have hcompl : IsCompl (fixV t) (movV t) :=
    IsCompl.of_eq (fixV_inf_movV t) (fixV_sup_movV ht3)
  have horth : ∀ w₁ ∈ fixV t, ∀ w₂ ∈ movV t, QuadraticMap.polar Q8 w₁ w₂ = 0 := by
    intro w₁ h₁ w₂ h₂
    rw [polar_Q8]
    exact spForm_fixV_movV ht3 h₁ h₂
  set A : ℕ := {w : ↥(fixV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard with hA
  set B : ℕ := {w : ↥(fixV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 0}.ncard with hB
  set C : ℕ := {w : ↥(movV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard with hC
  set D : ℕ := {w : ↥(movV t) | Q8 (w : Fin 4 ⊕ Fin 4 → ZMod 2) = 0}.ncard with hD
  have hmain : 120 = A * D + B * C := by
    have h := ncard_eq_one_of_isCompl Q8 hcompl horth
    rw [h120] at h
    simpa [hA, hB, hC, hD] using h
  have hsum2 : D + C = 16 := by
    have h := ncard_zero_add_ncard_one Q8 (movV t)
    rw [hV2card16] at h
    simpa [hC, hD] using h
  have h3dvd : 3 ∣ C := by
    have h := three_dvd_ncard_one_of_fixedPointFree Q8 (movV t) (spEnd t)
      (spEnd_pow ht3) ?_ ?_ ?_
    · simpa [hC] using h
    · intro w hw
      exact apply_mem_movV_of_commute (t := t) (g := t) rfl hw
    · intro w hw hfixw
      have hwfix : w ∈ fixV t := by
        rw [fixV_eq_ker, LinearMap.mem_ker]
        simpa [LinearMap.sub_apply, sub_eq_zero] using hfixw
      have hmem : w ∈ fixV t ⊓ movV t := Submodule.mem_inf.mpr ⟨hwfix, hw⟩
      rw [fixV_inf_movV t, Submodule.mem_bot] at hmem
      exact hmem
    · intro v
      have hω := (mem_Om8_iff_omegaGroup (t : SpGL)).mp (mem_OmInSp.mp htΩ)
      rw [← toLinEquiv_apply t]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hω.1 v
  have hC6 : C = 6 := by
    have hgauss := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic
      (Q8.comp (movV t).subtype) (movV_polar_nondegenerate ht3)
      (m := primaryMultiplicity (spEnd t) q2) hV2card
    rw [hm] at hgauss
    have hgauss' : 2 * C + 4 = 16 ∨ 2 * C = 20 := by
      have hC' : {x : ↥(movV t) | (Q8.comp (movV t).subtype) x = 1}.ncard = C := by
        change {x : ↥(movV t) | Q8 (x : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard = C
        rw [hC]
      simpa [hC', pow_two] using hgauss
    obtain ⟨k, hk⟩ := h3dvd
    clear hV2dim hV2card hV2card16 hm h120 hsum2
    omega
  have hD10 : D = 10 := by omega
  have hdim : Module.finrank (ZMod 2) ↥(fixV t) = 4 := by
    have hf := finrank_fixV ht3 ht1
    rw [hm] at hf
    omega
  have hsum1 : B + A = 16 := by
    have h := ncard_zero_add_ncard_one Q8 (fixV t)
    have hcard : Nat.card ↥(fixV t) = 16 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(fixV t)), hdim, Nat.card_zmod]
      norm_num
    rw [hcard] at h
    simpa [hA, hB] using h
  rw [hC6, hD10] at hmain
  change {v : ↥(fixV t) | Q8 (v : Fin 4 ⊕ Fin 4 → ZMod 2) = 1}.ncard = 6
  rw [← hA]
  clear hV2dim hV2card hV2card16 h120 hsum2 hdim hC6 hD10 hC hD
  omega

end CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

end