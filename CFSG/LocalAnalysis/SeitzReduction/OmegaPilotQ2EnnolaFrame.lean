module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaRot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Frame

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {r : ℕ}

structure IsEnnolaFrame (Q : QuadraticForm K (Fin d → K)) (a a' : Fin (r + 1) → Fin d → K) :
    Prop where
  regular : (polarBilin Q).Nondegenerate
  singular : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  unit : ∀ k, IsUnitPlane Q (a k) (a' k)
  orth_aa : ∀ k l, k ≠ l → polar Q (a k) (a l) = 0
  orth_aa' : ∀ k l, k ≠ l → polar Q (a k) (a' l) = 0
  orth_a'a' : ∀ k l, k ≠ l → polar Q (a' k) (a' l) = 0

variable (Q) in
@[expose] noncomputable def ennolaSwap (a a' : Fin (r + 1) → Fin d → K) (i j : Fin (r + 1)) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  eichler Q (a i + a j) (a' i + a' j)

variable {Q : QuadraticForm K (Fin d → K)} {a a' : Fin (r + 1) → Fin d → K}

theorem ennolaSwap_mem_orthogonalGroup (i j : Fin (r + 1)) :
    ennolaSwap Q a a' i j ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup Q _ _

namespace IsEnnolaFrame

variable (hF : IsEnnolaFrame Q a a')
include hF

theorem orth_a'a {k l : Fin (r + 1)} (hkl : k ≠ l) : polar Q (a' k) (a l) = 0 := by
  rw [polar_comm]
  exact hF.orth_aa' l k hkl.symm

theorem planeSwapData {i j : Fin (r + 1)} (hij : i ≠ j) :
    PlaneSwapData Q (a i) (a' i) (a j) (a' j) where
  map_eq := by rw [(hF.unit i).map_left, (hF.unit j).map_left]
  map_eq' := by rw [(hF.unit i).map_right, (hF.unit j).map_right]
  polar_aa := (hF.unit i).polar_eq
  polar_cc := (hF.unit j).polar_eq
  ac := hF.orth_aa i j hij
  ac' := hF.orth_aa' i j hij
  a'c := hF.orth_a'a hij
  a'c' := hF.orth_a'a' i j hij

theorem ennolaSwap_mem_orthDerived [Finite K] (i j : Fin (r + 1)) :
    ennolaSwap Q a a' i j ∈ orthDerived Q :=
  eichler_mem_orthDerived hF.regular hF.singular _ _

theorem planeSwap_left {i j : Fin (r + 1)} (hij : i ≠ j) (k : Fin (r + 1)) :
    ennolaSwap Q a a' i j (a k) = a (Equiv.swap i j k) := by
  have hd := hF.planeSwapData hij
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    exact hd.eichler_left
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right]
      exact hd.eichler_right
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      refine PlaneSwapData.eichler_of_perp (Q := Q) ?_ ?_ ?_ ?_
      · exact hF.orth_aa k i hki
      · exact hF.orth_aa' k i hki
      · exact hF.orth_aa k j hkj
      · exact hF.orth_aa' k j hkj

theorem planeSwap_right {i j : Fin (r + 1)} (hij : i ≠ j) (k : Fin (r + 1)) :
    ennolaSwap Q a a' i j (a' k) = a' (Equiv.swap i j k) := by
  have hd := hF.planeSwapData hij
  by_cases hki : k = i
  · subst hki
    rw [Equiv.swap_apply_left]
    exact hd.eichler_left'
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right]
      exact hd.eichler_right'
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      refine PlaneSwapData.eichler_of_perp (Q := Q) ?_ ?_ ?_ ?_
      · exact hF.orth_a'a hki
      · exact hF.orth_a'a' k i hki
      · exact hF.orth_a'a hkj
      · exact hF.orth_a'a' k j hkj

variable {F : Type} [Field F] (E : EnnolaParam K F)

theorem rotHom_commute {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {k : Fin (r + 1)} (hga : g (a k) = a k)
    (hga' : g (a' k) = a' k) (x : Fˣ) : g * E.rotHom (hF.unit k) x = E.rotHom (hF.unit k) x * g := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, E.rotHom_apply, E.rotHom_apply]
  have h := unitRotLin_conj hg (a k) (a' k) (E.param x).1 (E.param x).2 (g v)
  rw [LinearEquiv.symm_apply_apply, hga, hga'] at h
  exact h

theorem rotHom_commute_rotHom {k l : Fin (r + 1)} (hkl : k ≠ l) (x y : Fˣ) :
    E.rotHom (hF.unit k) x * E.rotHom (hF.unit l) y =
      E.rotHom (hF.unit l) y * E.rotHom (hF.unit k) x :=
  hF.rotHom_commute E (E.rotHom_mem_orthogonalGroup (hF.unit k) x)
    (E.rotHom_of_perp (hF.unit k) x (hF.orth_aa l k hkl.symm) (hF.orth_aa' l k hkl.symm))
    (E.rotHom_of_perp (hF.unit k) x (hF.orth_a'a hkl.symm) (hF.orth_a'a' l k hkl.symm)) y

variable [Finite K]

@[expose] noncomputable def rotOmega (k : Fin (r + 1)) : Fˣ →* orthDerived Q :=
  (E.rotHom (hF.unit k)).codRestrict _
    (fun x => E.rotHom_mem_orthDerived (hF.unit k) hF.regular hF.singular x)

theorem coe_rotOmega (k : Fin (r + 1)) (x : Fˣ) :
    ((hF.rotOmega E k x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      E.rotHom (hF.unit k) x := rfl

theorem commute_rotOmega : Pairwise fun k l =>
    ∀ x y, Commute (hF.rotOmega E k x) (hF.rotOmega E l y) := by
  intro k l hkl x y
  exact Subtype.ext (hF.rotHom_commute_rotHom E hkl x y)

@[expose] noncomputable def torus : (Fin (r + 1) → Fˣ) →* matrixProjectiveDerived Q :=
  (projHom Q).comp (MonoidHom.noncommPiCoprod (hF.rotOmega E) (hF.commute_rotOmega E))

theorem torus_mulSingle (k : Fin (r + 1)) (x : Fˣ) :
    hF.torus E (Pi.mulSingle k x) = projHom Q (hF.rotOmega E k x) := by
  rw [torus, MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_mulSingle]

theorem map_rootParam_torus (k : Fin (r + 1)) :
    (rootParam (K := F) k).map (hF.torus E) = (hF.rotOmega E k).range.map (projHom Q) := by
  rw [rootParam, MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply, torus_mulSingle]

theorem torus_mem_fixVecBar {k : Fin (r + 1)} {t : Fin (r + 1) → Fˣ} (ht : t k = 1) :
    hF.torus E t ∈ fixVecBar Q {a k, a' k} := by
  refine ⟨MonoidHom.noncommPiCoprod (hF.rotOmega E) (hF.commute_rotOmega E) t, ?_, rfl⟩
  rw [MonoidHom.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun j _ => ?_
  rw [mem_subgroupOf, mem_fixVecSub]
  intro v hv
  by_cases hjk : j = k
  · rw [hjk, ht, map_one]
    rfl
  · rw [coe_rotOmega]
    rcases hv with rfl | hv
    · exact E.rotHom_of_perp (hF.unit j) (t j) (hF.orth_aa k j (Ne.symm hjk))
        (hF.orth_aa' k j (Ne.symm hjk))
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact E.rotHom_of_perp (hF.unit j) (t j) (hF.orth_a'a (Ne.symm hjk))
        (hF.orth_a'a' k j (Ne.symm hjk))

theorem fixVecBar_le_centralizer (k : Fin (r + 1)) :
    fixVecBar Q {a k, a' k} ≤ centralizer ((rootParam (K := F) k).map (hF.torus E) :
      Set (matrixProjectiveDerived Q)) := by
  rw [hF.map_rootParam_torus E k]
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hgf := mem_fixVecSub.1 (mem_subgroupOf.1 hg)
  exact (hF.rotHom_commute E (Subgroup.commutator_le_self _ g.2) (hgf _ (by simp))
    (hgf _ (by simp)) x).symm

theorem ennolaSwap_conj_rotOmega {i j : Fin (r + 1)} (hij : i ≠ j) (k : Fin (r + 1)) (x : Fˣ) :
    (⟨ennolaSwap Q a a' i j, hF.ennolaSwap_mem_orthDerived i j⟩ : orthDerived Q) *
        hF.rotOmega E k x *
        (⟨ennolaSwap Q a a' i j, hF.ennolaSwap_mem_orthDerived i j⟩ : orthDerived Q)⁻¹ =
      hF.rotOmega E (Equiv.swap i j k) x := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change ennolaSwap Q a a' i j (E.rotHom (hF.unit k) x ((ennolaSwap Q a a' i j).symm v)) =
    E.rotHom (hF.unit (Equiv.swap i j k)) x v
  rw [E.rotHom_apply, E.rotHom_apply]
  have h := unitRotLin_conj (ennolaSwap_mem_orthogonalGroup (Q := Q) (a := a) (a' := a') i j)
    (a k) (a' k) (E.param x).1 (E.param x).2 v
  rw [hF.planeSwap_left hij, hF.planeSwap_right hij] at h
  exact h

@[expose] def precompHom (π : Equiv.Perm (Fin (r + 1))) :
    (Fin (r + 1) → Fˣ) →* (Fin (r + 1) → Fˣ) where
  toFun s := s ∘ π
  map_one' := rfl
  map_mul' _ _ := rfl

theorem exists_weyl_swap {i j : Fin (r + 1)} (hij : i ≠ j) :
    ∃ w, ∀ s, w * hF.torus E s * w⁻¹ = hF.torus E (s ∘ Equiv.swap i j) := by
  set W : orthDerived Q := ⟨ennolaSwap Q a a' i j, hF.ennolaSwap_mem_orthDerived i j⟩ with hW
  refine ⟨projHom Q W, fun s => ?_⟩
  have key : (MulAut.conj (projHom Q W)).toMonoidHom.comp (hF.torus E) =
      (hF.torus E).comp (precompHom (Equiv.swap i j)) := by
    refine MonoidHom.pi_ext fun k x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    change _ = hF.torus E (Pi.mulSingle k x ∘ Equiv.swap i j)
    rw [Pi.mulSingle_comp_equiv, Equiv.symm_swap, hF.torus_mulSingle, hF.torus_mulSingle,
      ← map_inv, ← map_mul, ← map_mul, hW, hF.ennolaSwap_conj_rotOmega E hij]
  exact DFunLike.congr_fun key s

theorem exists_weyl (π : Equiv.Perm (Fin (r + 1))) :
    ∃ w, ∀ s, w * hF.torus E s * w⁻¹ = hF.torus E (s ∘ π) := by
  refine Equiv.Perm.swap_induction_on π ⟨1, fun s => by simp⟩ ?_
  intro f x y hxy ih
  obtain ⟨w, hw⟩ := ih
  obtain ⟨u, hu⟩ := hF.exists_weyl_swap E hxy
  refine ⟨w * u, fun s => ?_⟩
  rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ← hw, ← hu]
  group

theorem top_le_iSup_perfectCore (hr : 4 ≤ r)
    (hperf : ⁅fixVecBar Q {a 0, a' 0}, fixVecBar Q {a 0, a' 0}⁆ = fixVecBar Q {a 0, a' 0}) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map (hF.torus E) :
      Set (matrixProjectiveDerived Q))) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let ix : Fin 3 → Fin (r + 1) := fun i => ⟨i, by omega⟩
  have hix : Function.Injective ix := fun i j h => Fin.ext (by simpa [ix] using congrArg Fin.val h)
  let v : Fin 3 → Bool → Fin d → K := fun i b => if b then a (ix i) else a' (ix i)
  have hv : OrthPairTriple Q v :=
    { one := fun i => (hF.unit (ix i)).polar_eq
      orth := fun i j hij s t => by
        have hij' : ix i ≠ ix j := hix.ne hij
        cases s <;> cases t
        · exact hF.orth_a'a' _ _ hij'
        · exact hF.orth_a'a hij'
        · exact hF.orth_aa' _ _ hij'
        · exact hF.orth_aa _ _ hij' }
  set i3 : Fin (r + 1) := ⟨3, by omega⟩
  set i4 : Fin (r + 1) := ⟨4, by omega⟩
  have h34 : i3 ≠ i4 := fun h => by simpa [i3, i4] using congrArg Fin.val h
  have hix3 : ∀ i : Fin 3, ix i ≠ i3 := fun i h => by
    have := congrArg Fin.val h
    simp [ix, i3] at this
    omega
  have hix4 : ∀ i : Fin 3, ix i ≠ i4 := fun i h => by
    have := congrArg Fin.val h
    simp [ix, i4] at this
    omega
  let P : HypPair Q :=
    { e := a i3 + a i4
      f := a' i3 + a i4
      Q_e := by
        rw [QuadraticMap.map_add Q, (hF.unit i3).map_left, (hF.unit i4).map_left,
          hF.orth_aa _ _ h34]
        linear_combination h2
      Q_f := by
        rw [QuadraticMap.map_add Q, (hF.unit i3).map_right, (hF.unit i4).map_left,
          hF.orth_a'a h34]
        linear_combination h2
      polar_ef := by
        rw [polar_add_left, polar_add_right, polar_add_right, (hF.unit i3).polar_eq,
          hF.orth_aa _ _ h34, hF.orth_aa' _ _ h34.symm, polar_self_charTwo]
        ring }
  have hve : ∀ i s, polar Q (v i s) P.e = 0 := fun i s => by
    change polar Q (v i s) (a i3 + a i4) = 0
    rw [polar_add_right]
    cases s
    · simp only [v, Bool.false_eq_true, ite_false]
      rw [hF.orth_a'a (hix3 i), hF.orth_a'a (hix4 i), add_zero]
    · simp only [v, ite_true]
      rw [hF.orth_aa _ _ (hix3 i), hF.orth_aa _ _ (hix4 i), add_zero]
  have hvf : ∀ i s, polar Q (v i s) P.f = 0 := fun i s => by
    change polar Q (v i s) (a' i3 + a i4) = 0
    rw [polar_add_right]
    cases s
    · simp only [v, Bool.false_eq_true, ite_false]
      rw [hF.orth_a'a' _ _ (hix3 i), hF.orth_a'a (hix4 i), add_zero]
    · simp only [v, ite_true]
      rw [hF.orth_aa' _ _ (hix3 i), hF.orth_aa _ _ (hix4 i), add_zero]
  have htop := hv.fixVecBar_sup_eq_top hF.regular hF.singular P hve hvf
  have hps : ∀ i : Fin 3, pairSet v i = {a (ix i), a' (ix i)} := fun i => by
    simp [pairSet, v]
  have hix0 : ix 0 = 0 := rfl
  set i1 : Fin (r + 1) := ix 1
  have h01 : (0 : Fin (r + 1)) ≠ i1 := fun h => by simpa [i1, ix] using congrArg Fin.val h
  set C : Fin (r + 1) → Subgroup (matrixProjectiveDerived Q) := fun k =>
    perfectCore (centralizer ((rootParam (K := F) k).map (hF.torus E) :
      Set (matrixProjectiveDerived Q))) with hC
  have hD0 : fixVecBar Q {a 0, a' 0} ≤ C 0 :=
    le_perfectCore_of_perfect (hF.fixVecBar_le_centralizer E 0) hperf
  set W : orthDerived Q := ⟨ennolaSwap Q a a' 0 i1, hF.ennolaSwap_mem_orthDerived 0 i1⟩
  have hD1eq : (fixVecBar Q {a 0, a' 0}).map (MulAut.conj (projHom Q W)).toMonoidHom =
      fixVecBar Q {a i1, a' i1} := by
    rw [map_conj_fixVecBar]
    congr 1
    change (ennolaSwap Q a a' 0 i1) '' {a 0, a' 0} = _
    rw [Set.image_insert_eq, Set.image_singleton, hF.planeSwap_left h01, hF.planeSwap_right h01,
      Equiv.swap_apply_left]
  have hD1 : fixVecBar Q {a i1, a' i1} ≤ C i1 := by
    refine le_perfectCore_of_perfect (hF.fixVecBar_le_centralizer E i1) ?_
    rw [← hD1eq, ← Subgroup.map_commutator, hperf]
  calc (⊤ : Subgroup (matrixProjectiveDerived Q))
      = fixVecBar Q (pairSet v 0 ∪ pairSet v 1) ⊔ fixVecBar Q (pairSet v 0 ∪ pairSet v 2) ⊔
          fixVecBar Q (pairSet v 1 ∪ pairSet v 2) := htop.symm
    _ ≤ C 0 ⊔ C i1 := by
        refine sup_le (sup_le ?_ ?_) ?_
        · refine le_sup_of_le_left ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps, hix0]
          exact hD0
        · refine le_sup_of_le_left ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps, hix0]
          exact hD0
        · refine le_sup_of_le_right ((fixVecBar_anti Set.subset_union_left).trans ?_)
          rw [hps]
          exact hD1
    _ ≤ ⨆ k, C k := sup_le (le_iSup C 0) (le_iSup C i1)

theorem map_rootParam_torus_eq_anisoTorusOf {c c' : Fin d} (hc : IsAnisoCoord Q c c' 1 1)
    (ha : a 0 = Pi.single c 1) (ha' : a' 0 = Pi.single c' 1) :
    (rootParam (K := F) 0).map (hF.torus E) = anisoTorusOf Q hc.ne 1 1 := by
  rw [hF.map_rootParam_torus E 0, anisoTorusOf]
  congr 1
  ext g
  rw [MonoidHom.mem_range, mem_subgroupOf, mem_anisoRotSub]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(E.param x).1, (E.param x).2, ?_, fun v => ?_⟩
    · have := E.norm_param x.ne_zero
      linear_combination this
    · rw [coe_rotOmega, E.rotHom_apply, ← hc.unitRotLin_eq_anisoRotLin, ← ha, ← ha']
  · rintro ⟨p, s, hN, hg⟩
    have hx : E.ι p + E.ι s * E.ω ≠ 0 := by
      intro h0
      have h1 : E.param 0 = (p, s) := (E.param_eq_iff).2 h0
      have h2 : E.param 0 = (0, 0) := (E.param_eq_iff).2 (by simp)
      rw [h2] at h1
      have hp : p = 0 := (congrArg Prod.fst h1).symm
      have hs : s = 0 := (congrArg Prod.snd h1).symm
      rw [hp, hs] at hN
      simp at hN
    have hpar : E.param (E.ι p + E.ι s * E.ω) = (p, s) := (E.param_eq_iff).2 rfl
    refine ⟨Units.mk0 _ hx, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
    rw [coe_rotOmega, E.rotHom_apply, Units.val_mk0, hpar, hg,
      ← hc.unitRotLin_eq_anisoRotLin, ha, ha']

end IsEnnolaFrame

end Frame

end CFSG.SeitzReduction.OmegaPilot
