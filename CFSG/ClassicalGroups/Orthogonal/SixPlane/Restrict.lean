module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
public import CFSG.ClassicalGroups.Orthogonal.Derived

import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OAutFix
import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthRefl
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCSub
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

namespace CFSG.ClassicalGroups.Orthogonal.SixPlane

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Module QuadraticMap
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup commSpace mem_commSpace)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC (perpOf extG extG_injective extG_mem_fixW
  range_extG fixW mem_fixW extHom extHom_apply_of_mem_W extHom_apply_of_mem_U IsFrame MinusPair
  PairPerp Wspan Wspan_nil Wspan_cons planeSpan_le_Wspan nondeg_Wspan isPlusType_Wspan_iff)
open CFSG.GroupTheory.WeirSylow (IsPlusType nonempty_isometry_quadPlus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  plusIndexEquiv reindexQuadraticIsometry)
open CFSG.LieType.Universal.Spin (quadPlus)

variable {n : ℕ}

private theorem perpOf_planeSpan (T : Finset (Fin n)) :
    perpOf (Q n) (planeSpan n T) = planeSpan n Tᶜ := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_planeSpan]
  constructor
  · intro h k hk
    have hkT : planeOf k ∈ T := by simpa using hk
    rcases k with s | s
    · have := h _ (single_mem_planeSpan (k := Sum.inr s) hkT)
      rwa [polarBilin_apply_apply, polar_single_inr_apply] at this
    · have := h _ (single_mem_planeSpan (k := Sum.inl s) hkT)
      rwa [polarBilin_apply_apply, polar_single_inl_apply] at this
  · intro hv u hu
    rw [polarBilin_apply_apply, polar_Q]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ T
    · have hj' : j ∉ Tᶜ := by simpa using hj
      rw [hv (Sum.inl j) hj', hv (Sum.inr j) hj']
      ring
    · rw [mem_planeSpan.mp hu (Sum.inl j) hj, mem_planeSpan.mp hu (Sum.inr j) hj]
      ring

private theorem isCompl_planeSpan (T : Finset (Fin n)) :
    IsCompl (planeSpan n T) (planeSpan n Tᶜ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    funext k
    by_cases hk : planeOf k ∈ T
    · exact mem_planeSpan.mp h2 k (by simpa using hk)
    · exact mem_planeSpan.mp h1 k hk
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    let w : V n := fun k => if planeOf k ∈ T then v k else 0
    have hw : w ∈ planeSpan n T := mem_planeSpan.mpr fun k hk => if_neg hk
    have hvw : v - w ∈ planeSpan n Tᶜ := mem_planeSpan.mpr fun k hk => by
      have hk' : planeOf k ∈ T := by simpa using hk
      simp [w, hk']
    simpa using Submodule.add_mem_sup hw hvw

private abbrev cpair (s : Fin n) : V n × V n :=
  (Pi.single (Sum.inl s) 1, Pi.single (Sum.inr s) 1)

private theorem minusPair_cpair (s : Fin n) : MinusPair (Q n) (cpair s).1 (cpair s).2 :=
  ⟨Q_single n _, Q_single n _, by simp [cpair, polar_single_inl_apply]⟩

private theorem pairPerp_cpair {s t : Fin n} (h : s ≠ t) :
    PairPerp (Q n) (cpair s) (cpair t) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [cpair, polar_single_inl_apply, polar_single_inr_apply, Pi.single_apply, h]

private noncomputable def framePairs (T : Finset (Fin n)) : List (V n × V n) :=
  T.toList.map cpair

private theorem isFrame_framePairs (T : Finset (Fin n)) : IsFrame (Q n) (framePairs T) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨s, -, rfl⟩ := List.mem_map.mp hp
    exact minusPair_cpair s
  · exact List.Pairwise.map cpair (fun _ _ h => pairPerp_cpair h) T.nodup_toList

private theorem length_framePairs (T : Finset (Fin n)) : (framePairs T).length = T.card := by
  simp [framePairs]

private theorem wspan_framePairs (T : Finset (Fin n)) :
    Wspan (framePairs T) = planeSpan n T := by
  apply le_antisymm
  · have key : ∀ l : List (Fin n), (∀ s ∈ l, s ∈ T) → Wspan (l.map cpair) ≤ planeSpan n T := by
      intro l
      induction l with
      | nil =>
        intro _
        rw [List.map_nil, Wspan_nil]
        exact bot_le
      | cons s l ih =>
        intro hl
        rw [List.map_cons, Wspan_cons]
        refine sup_le ?_ (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))
        have hs : s ∈ T := hl s List.mem_cons_self
        refine Submodule.span_le.mpr ?_
        rintro x (rfl | rfl)
        · exact single_mem_planeSpan (k := Sum.inl s) hs
        · exact single_mem_planeSpan (k := Sum.inr s) hs
    exact key _ fun s hs => Finset.mem_toList.mp hs
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : planeOf k ∈ T
    · have hmem : cpair (planeOf k) ∈ framePairs T :=
        List.mem_map.mpr ⟨planeOf k, Finset.mem_toList.mpr hk, rfl⟩
      refine planeSpan_le_Wspan hmem ?_
      have hsm : Pi.single k (v k) = v k • (Pi.single k (1 : ZMod 2) : V n) := by
        rw [← Pi.single_smul', smul_eq_mul, mul_one]
      rw [hsm]
      refine Submodule.smul_mem _ _ ?_
      rcases k with s | s
      · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.left_mem_planeSpan (cpair s)
      · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.right_mem_planeSpan (cpair s)
    · rw [mem_planeSpan.mp hv k hk, Pi.single_zero]
      exact zero_mem _

private theorem rot_eq_kdRot (i : Fin n) :
    rot n i = CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot (Q n) (cpair i).1 (cpair i).2 := by
  have h1 : crefl n (Sum.inl i) = reflect (Q n) (Pi.single (Sum.inl i) (1 : ZMod 2)) :=
    (reflect_eq_reflection (Q := Q n) (v := Pi.single (Sum.inl i) (1 : ZMod 2))).symm
  have h2 : crefl n (Sum.inr i) = reflect (Q n) (Pi.single (Sum.inr i) (1 : ZMod 2)) :=
    (reflect_eq_reflection (Q := Q n) (v := Pi.single (Sum.inr i) (1 : ZMod 2))).symm
  rw [rot, h1, h2]
  rfl

private theorem finrank_commSpace_rot (i : Fin n) :
    finrank (ZMod 2) (commSpace (rot n i)) = 2 := by
  have hp := minusPair_cpair (n := n) i
  have hc : commSpace (rot n i) =
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.planeSpan (cpair i) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      rw [rot_eq_kdRot]
      exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.rot_sub_mem_span hp v
    · intro y hy
      obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC.exists_rot_sub_eq hp hy
      rw [← rot_eq_kdRot] at hx
      exact mem_commSpace.mpr ⟨x, hx⟩
  rw [hc]
  exact hp.finrank_planeSpan

private theorem commSpace_extG_eq {X : Type} [AddCommGroup X] [Module (ZMod 2) X]
    {q : QuadraticForm (ZMod 2) X} {W : Submodule (ZMod 2) X} (hW : IsCompl W (perpOf q W))
    (φ : TauCeti.QuadraticMap.orthogonalGroup (q.restrict (perpOf q W))) :
    commSpace (extG hW φ) =
      (commSpace (φ : perpOf q W ≃ₗ[ZMod 2] perpOf q W)).map (perpOf q W).subtype := by
  ext v
  simp only [commSpace, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ :=
      Submodule.mem_sup.mp (hW.sup_eq_top ▸ Submodule.mem_top (x := z))
    refine ⟨(φ : perpOf q W ≃ₗ[ZMod 2] perpOf q W) ⟨w, hw⟩ - ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
    have h1 := extHom_apply_of_mem_W hW φ hu
    have h2 := extHom_apply_of_mem_U hW φ hw
    change _ = ((extHom hW φ).1 : X ≃ₗ[ZMod 2] X) (u + w) - (u + w)
    rw [map_add, h1, h2]
    simp only [Submodule.subtype_apply, Submodule.coe_sub]
    abel
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w : X), ?_⟩
    have h2 := extHom_apply_of_mem_U hW φ w.2
    change ((extHom hW φ).1 : X ≃ₗ[ZMod 2] X) w - w = _
    rw [h2]
    rfl

private noncomputable abbrev perpPlaneSpan (S : Finset (Fin n)) : Submodule (ZMod 2) (V n) :=
  perpOf (Q n) (planeSpan n Sᶜ)

private theorem perpPlaneSpan_eq_planeSpan (S : Finset (Fin n)) :
    perpPlaneSpan S = planeSpan n S := by
  rw [perpPlaneSpan, perpOf_planeSpan, compl_compl]

private theorem isCompl_planeSpan_compl_perpPlaneSpan (S : Finset (Fin n)) :
    IsCompl (planeSpan n Sᶜ) (perpPlaneSpan S) := by
  rw [perpPlaneSpan_eq_planeSpan]
  exact (isCompl_planeSpan S).symm

private theorem wspan_framePairs_perpPlaneSpan (S : Finset (Fin n)) :
    Wspan (framePairs S) = perpPlaneSpan S :=
  (wspan_framePairs S).trans (perpPlaneSpan_eq_planeSpan S).symm

private theorem finrank_perpPlaneSpan (S : Finset (Fin n)) :
    finrank (ZMod 2) (perpPlaneSpan S) = 2 * S.card := by
  have h := (isFrame_framePairs (n := n) S).finrank_Wspan
  rwa [wspan_framePairs_perpPlaneSpan, length_framePairs] at h

private theorem nondegenerate_polarBilin_restrict_perpPlaneSpan (S : Finset (Fin n)) :
    (polarBilin ((Q n).restrict (perpPlaneSpan S))).Nondegenerate := by
  have h := nondeg_Wspan (isFrame_framePairs (n := n) S)
  rw [wspan_framePairs_perpPlaneSpan] at h
  rwa [show (Q n).comp (perpPlaneSpan S).subtype =
    (Q n).restrict (perpPlaneSpan S) from QuadraticMap.ext fun _ => rfl] at h

private theorem orthDerived_restrict_perpPlaneSpan_eq_omegaGroup {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) :
    orthDerived ((Q n).restrict (perpPlaneSpan S)) =
      omegaGroup ((Q n).restrict (perpPlaneSpan S))
        (nondegenerate_polarBilin_restrict_perpPlaneSpan S) := by
  refine CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup _ ?_
  rw [finrank_perpPlaneSpan]
  omega

private theorem orthDerived_restrict_perpPlaneSpan_le_orthogonalGroup {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) :
    orthDerived ((Q n).restrict (perpPlaneSpan S)) ≤
      TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S)) := by
  rw [orthDerived_restrict_perpPlaneSpan_eq_omegaGroup hS]
  exact fun _ h => h.1

private theorem finrank_commSpace_extG {S : Finset (Fin n)}
    (φ : TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S))) :
    finrank (ZMod 2) (commSpace (extG (isCompl_planeSpan_compl_perpPlaneSpan S) φ)) =
      finrank (ZMod 2)
        (commSpace (φ : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S))) := by
  rw [commSpace_extG_eq (isCompl_planeSpan_compl_perpPlaneSpan S) φ,
    Submodule.finrank_map_subtype_eq]

private theorem extG_mem_supp_iff {S : Finset (Fin n)} (hS : 3 ≤ S.card)
    (φ : TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S))) :
    extG (isCompl_planeSpan_compl_perpPlaneSpan S) φ ∈ supp n S ↔
      (φ : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)) ∈
        orthDerived ((Q n).restrict (perpPlaneSpan S)) := by
  rw [orthDerived_restrict_perpPlaneSpan_eq_omegaGroup hS]
  constructor
  · intro h
    refine ⟨φ.2, ?_⟩
    rw [← finrank_commSpace_extG φ]
    exact (mem_supp.mp h).1.2
  · intro h
    refine mem_supp.mpr ⟨⟨(extHom (isCompl_planeSpan_compl_perpPlaneSpan S) φ).2, ?_⟩,
      (extG_mem_fixW (isCompl_planeSpan_compl_perpPlaneSpan S) φ).2⟩
    rw [finrank_commSpace_extG φ]
    exact h.2

private theorem exists_mulEquiv_orthDerived_perpPlaneSpan {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) :
    ∃ R : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))) ≃* ↥(supp n S),
      (∀ x : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))),
        ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) =
          extG (isCompl_planeSpan_compl_perpPlaneSpan S)
            ⟨x, orthDerived_restrict_perpPlaneSpan_le_orthogonalGroup hS x.2⟩) ∧
      (∀ (y : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))))
        (v : ↥(perpPlaneSpan S)),
        ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) v =
          (((y : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)) v :
            ↥(perpPlaneSpan S)) : V n)) := by
  classical
  have hle : orthDerived ((Q n).restrict (perpPlaneSpan S)) ≤
      TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S)) :=
    orthDerived_restrict_perpPlaneSpan_le_orthogonalGroup hS
  let R₀ : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))) →* ↥(supp n S) :=
    { toFun := fun x =>
        ⟨extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨x, hle x.2⟩,
          (extG_mem_supp_iff (S := S) hS _).2 x.2⟩
      map_one' := Subtype.ext (map_one (extG (isCompl_planeSpan_compl_perpPlaneSpan S)))
      map_mul' := fun x y => Subtype.ext
        (map_mul (extG (isCompl_planeSpan_compl_perpPlaneSpan S))
          ⟨x, hle x.2⟩ ⟨y, hle y.2⟩) }
  have hR₀ : ∀ x : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))),
      ((R₀ x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) =
        extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨x, hle x.2⟩ := fun _ => rfl
  have hbij : Function.Bijective R₀ := by
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · have h : extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨x, hle x.2⟩ =
          extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨y, hle y.2⟩ := by
        rw [← hR₀ x, ← hR₀ y, hxy]
      have h' := extG_injective (isCompl_planeSpan_compl_perpPlaneSpan S) h
      exact Subtype.ext (by simpa using congrArg Subtype.val h')
    · have hy : (y : V n ≃ₗ[ZMod 2] V n) ∈
          (extG (isCompl_planeSpan_compl_perpPlaneSpan S)).range := by
        rw [range_extG (isCompl_planeSpan_compl_perpPlaneSpan S)]
        exact mem_fixW.mpr ⟨(mem_supp.mp y.2).1.1, (mem_supp.mp y.2).2⟩
      obtain ⟨φ, hφ⟩ := MonoidHom.mem_range.mp hy
      have hφΩ : (φ : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)) ∈
          orthDerived ((Q n).restrict (perpPlaneSpan S)) :=
        (extG_mem_supp_iff (S := S) hS φ).1 (by rw [hφ]; exact y.2)
      exact ⟨⟨(φ : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)), hφΩ⟩,
        Subtype.ext ((hR₀ ⟨(φ : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)),
          hφΩ⟩).trans hφ)⟩
  let R : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))) ≃* ↥(supp n S) :=
    MulEquiv.ofBijective R₀ hbij
  have hR : ∀ x : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))),
      ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) =
        extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨x, hle x.2⟩ := fun _ => rfl
  refine ⟨R, hR, fun y v => ?_⟩
  rw [hR y]
  exact extHom_apply_of_mem_U (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨y, hle y.2⟩ v.2

theorem exists_isometry_of_mulEquiv_fix_rot {S : Finset (Fin n)} (hS : S.card = 4)
    (θ : ↥(supp n S) ≃* ↥(supp n S)) {i : Fin n} (hi : i ∈ S)
    (hfix : θ ⟨rot n i, rot_mem_supp (n := n) hi⟩ = ⟨rot n i, rot_mem_supp (n := n) hi⟩) :
    ∃ g : V n ≃ₗ[ZMod 2] V n,
      g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q n) ∧
      (∀ v ∈ planeSpan n Sᶜ, g v = v) ∧
      ∀ y : ↥(supp n S), (θ y : V n ≃ₗ[ZMod 2] V n) =
        g * (y : V n ≃ₗ[ZMod 2] V n) * g⁻¹ := by
  classical
  have hS3 : 3 ≤ S.card := by omega
  have hnd := nondegenerate_polarBilin_restrict_perpPlaneSpan (n := n) (S := S)
  have hdim : finrank (ZMod 2) (perpPlaneSpan S) = 2 * 4 := by
    rw [finrank_perpPlaneSpan, hS]
  have hplus : IsPlusType ((Q n).restrict (perpPlaneSpan S)) := by
    have h := (isPlusType_Wspan_iff (isFrame_framePairs (n := n) S)).2
      (by rw [length_framePairs, hS]; exact ⟨2, rfl⟩)
    rw [wspan_framePairs_perpPlaneSpan] at h
    rwa [show (Q n).comp (perpPlaneSpan S).subtype =
      (Q n).restrict (perpPlaneSpan S) from QuadraticMap.ext fun _ => rfl] at h
  obtain ⟨e₀⟩ := nonempty_isometry_quadPlus hnd hdim hplus
  let e : ((Q n).restrict (perpPlaneSpan S)).IsometryEquiv (coordinateQuadPlus 4 (ZMod 2)) :=
    e₀.trans (reindexQuadraticIsometry (plusIndexEquiv 4) (quadPlus 4 (ZMod 2)))
  obtain ⟨R, hR, -⟩ := exists_mulEquiv_orthDerived_perpPlaneSpan (n := n) (S := S) hS3
  let α : MulAut ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))) := (R.trans θ).trans R.symm
  let b : ↥(orthDerived ((Q n).restrict (perpPlaneSpan S))) :=
    R.symm ⟨rot n i, rot_mem_supp (n := n) hi⟩
  have hRb : R b = ⟨rot n i, rot_mem_supp (n := n) hi⟩ := R.apply_symm_apply _
  have hb3 : b ^ 3 = 1 := by
    apply R.injective
    rw [map_pow, hRb, map_one]
    exact Subtype.ext (by simpa using rot_pow_three (n := n) i)
  have hαb : α b = b := by
    show R.symm (θ (R b)) = R.symm ⟨rot n i, rot_mem_supp (n := n) hi⟩
    rw [hRb, hfix]
  have hle : orthDerived ((Q n).restrict (perpPlaneSpan S)) ≤
      TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S)) :=
    orthDerived_restrict_perpPlaneSpan_le_orthogonalGroup hS3
  have hb : extG (isCompl_planeSpan_compl_perpPlaneSpan S)
      ⟨(b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)), hle b.2⟩ = rot n i := by
    rw [← hR b, hRb]
  have hb6 : finrank (ZMod 2)
      (LinearMap.ker ((b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)).toLinearMap -
        1)) = 6 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)).toLinearMap - 1)
    have h2 : finrank (ZMod 2)
        (commSpace (b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S))) = 2 := by
      have h3 := finrank_commSpace_extG
        ⟨(b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)), hle b.2⟩
      rw [hb, finrank_commSpace_rot] at h3
      exact h3.symm
    change finrank (ZMod 2)
      (commSpace (b : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S))) + _ = _ at h
    rw [h2, hdim] at h
    omega
  obtain ⟨g', hg', hconj⟩ :=
    CFSG.StandardType.QTwo.qtwoDL1_orthAut_of_fix_six_of_isometry (K := ZMod 2)
      (V := ↥(perpPlaneSpan S)) (by simp) e α hb3 hb6 hαb
  refine ⟨extG (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨g', hg'⟩,
    (extHom (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨g', hg'⟩).2,
    (extG_mem_fixW (isCompl_planeSpan_compl_perpPlaneSpan S) ⟨g', hg'⟩).2,
    fun y => ?_⟩
  obtain ⟨x, rfl⟩ := R.surjective y
  have hαx :
      (⟨(α x : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)), hle (α x).2⟩ :
        TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (perpPlaneSpan S))) =
        ⟨g', hg'⟩ *
          ⟨(x : ↥(perpPlaneSpan S) ≃ₗ[ZMod 2] ↥(perpPlaneSpan S)), hle x.2⟩ *
          ⟨g', hg'⟩⁻¹ :=
    Subtype.ext (hconj x)
  have hθ : θ (R x) = R (α x) := by
    show θ (R x) = R (R.symm (θ (R x)))
    rw [R.apply_symm_apply]
  rw [hθ, hR, hR, hαx, map_mul, map_mul, map_inv]

private theorem exists_mulEquiv_orthDerived_of_eq {S : Finset (Fin n)}
    {P₀ : Submodule (ZMod 2) (V n)} (hP : perpOf (Q n) (planeSpan n Sᶜ) = P₀)
    (hS : 3 ≤ S.card) :
    ∃ R : ↥(orthDerived ((Q n).restrict P₀)) ≃* ↥(supp n S),
      ∀ (y : ↥(orthDerived ((Q n).restrict P₀))) (v : ↥P₀),
        ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) v =
          (((y : ↥P₀ ≃ₗ[ZMod 2] ↥P₀) v : ↥P₀) : V n) := by
  subst hP
  exact (exists_mulEquiv_orthDerived_perpPlaneSpan (n := n) (S := S) hS).imp
    fun _ hR => hR.2

theorem exists_mulEquiv_orthDerived_restrict {S : Finset (Fin n)} (hS : 3 ≤ S.card) :
    ∃ R : ↥(orthDerived ((Q n).restrict (planeSpan n S))) ≃* ↥(supp n S),
      ∀ (y : ↥(orthDerived ((Q n).restrict (planeSpan n S)))) (v : ↥(planeSpan n S)),
        ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) v =
          (((y : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) v : ↥(planeSpan n S)) : V n) := by
  exact exists_mulEquiv_orthDerived_of_eq (P₀ := planeSpan n S) (perpPlaneSpan_eq_planeSpan S) hS

private theorem nondegenerate_polarBilin_restrict_planeSpan (S : Finset (Fin n)) :
    (polarBilin ((Q n).restrict (planeSpan n S))).Nondegenerate := by
  rw [← perpPlaneSpan_eq_planeSpan]
  exact nondegenerate_polarBilin_restrict_perpPlaneSpan S

private theorem finrank_planeSpan_eq_two_mul_card (S : Finset (Fin n)) :
    finrank (ZMod 2) (planeSpan n S) = 2 * S.card := by
  rw [← perpPlaneSpan_eq_planeSpan]
  exact finrank_perpPlaneSpan S

private theorem orthDerived_restrict_planeSpan_le_orthogonalGroup {S : Finset (Fin n)}
    (hS : 3 ≤ S.card) :
    orthDerived ((Q n).restrict (planeSpan n S)) ≤
      TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (planeSpan n S)) := by
  rw [← perpPlaneSpan_eq_planeSpan]
  exact orthDerived_restrict_perpPlaneSpan_le_orthogonalGroup hS

private theorem reflect_restrict_apply {S : Finset (Fin n)} {v₀ : V n}
    (hv₀S : v₀ ∈ planeSpan n S) (hv₀ : Q n v₀ = 1) (v : ↥(planeSpan n S)) :
    reflect (Q n) v₀ (v : V n) =
      ((reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ v :
        ↥(planeSpan n S)) : V n) := by
  have hv₀' : (Q n).restrict (planeSpan n S) ⟨v₀, hv₀S⟩ = 1 := hv₀
  rw [reflect_apply (by rw [hv₀]; exact one_ne_zero),
    reflect_apply (by rw [hv₀']; exact one_ne_zero), polar_restrict, hv₀, hv₀']
  rfl

private theorem eq_of_eq_on_planeSpan_of_fixes_compl {S : Finset (Fin n)}
    {g h : V n ≃ₗ[ZMod 2] V n} (hg : ∀ v ∈ planeSpan n Sᶜ, g v = v)
    (hh : ∀ v ∈ planeSpan n Sᶜ, h v = v)
    (heq : ∀ v ∈ planeSpan n S, g v = h v) : g = h := by
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (show v ∈
    planeSpan n S ⊔ planeSpan n Sᶜ by
    rw [(isCompl_planeSpan S).sup_eq_top]
    exact Submodule.mem_top)
  rw [map_add, map_add, heq u hu, hg w hw, hh w hw]

private theorem reflect_conj_mem_map_comap {S : Finset (Fin n)}
    {H : Subgroup (V n ≃ₗ[ZMod 2] V n)} {v₀ : V n}
    (hv₀S : v₀ ∈ planeSpan n S) (hv₀ : Q n v₀ = 1)
    (hrH : ∀ h ∈ H, reflect (Q n) v₀ * h * reflect (Q n) v₀ ∈ H)
    {R : ↥(orthDerived ((Q n).restrict (planeSpan n S))) ≃* ↥(supp n S)}
    (hR : ∀ (y : ↥(orthDerived ((Q n).restrict (planeSpan n S))))
      (v : ↥(planeSpan n S)),
      ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) v =
        (((y : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) v : ↥(planeSpan n S)) : V n)) :
    ∀ h ∈ ((H.subgroupOf (supp n S)).comap R.toMonoidHom).map
        (orthDerived ((Q n).restrict (planeSpan n S))).subtype,
      reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ * h *
          reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ ∈
        ((H.subgroupOf (supp n S)).comap R.toMonoidHom).map
          (orthDerived ((Q n).restrict (planeSpan n S))).subtype := by
  classical
  intro h hh
  obtain ⟨x, hxK, rfl⟩ := Subgroup.mem_map.mp hh
  have hxH : ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) ∈ H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hxK)
  have hfixV : ∀ w ∈ planeSpan n Sᶜ, reflect (Q n) v₀ w = w := by
    intro w hw
    refine reflect_apply_of_polar_eq_zero ?_
    rw [← perpOf_planeSpan] at hw
    simpa [polarBilin_apply_apply] using
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v₀ hv₀S
  have hfixR : ∀ w ∈ planeSpan n Sᶜ,
      ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) w = w :=
    fun w hw => (mem_supp.mp (R x).2).2 w hw
  have hO : reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ ∈
      TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (planeSpan n S)) :=
    reflect_mem_orthogonalGroup _ _
  let r : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S) :=
    reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩
  have hzΩ : r * (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) * r ∈
      orthDerived ((Q n).restrict (planeSpan n S)) := by
    have hnorm := Subgroup.normalizer_commutator_ge_left
      (H₁ := TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (planeSpan n S)))
      (H₂ := TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (planeSpan n S))) hO
    have h := (Subgroup.mem_normalizer_iff.mp hnorm
      (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S))).mp x.2
    simpa [r, reflect_inv] using h
  have hfixConj : ∀ w ∈ planeSpan n Sᶜ,
      (reflect (Q n) v₀ * ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) *
        reflect (Q n) v₀) w = w := by
    intro w hw
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfixV w hw, hfixR w hw, hfixV w hw]
  have hEq : ((R ⟨r * (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) * r, hzΩ⟩ :
        ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) =
      reflect (Q n) v₀ * ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) *
        reflect (Q n) v₀ := by
    refine eq_of_eq_on_planeSpan_of_fixes_compl (S := S) ?_ hfixConj ?_
    · intro w hw
      exact (mem_supp.mp (R ⟨_, hzΩ⟩).2).2 w hw
    · intro v hv
      rw [hR ⟨r * (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) * r, hzΩ⟩ ⟨v, hv⟩]
      simp only [LinearEquiv.mul_apply]
      rw [reflect_restrict_apply hv₀S hv₀ ⟨v, hv⟩]
      rw [hR x (reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ ⟨v, hv⟩)]
      rw [reflect_restrict_apply hv₀S hv₀
        ((x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S))
          (reflect ((Q n).restrict (planeSpan n S)) ⟨v₀, hv₀S⟩ ⟨v, hv⟩))]
  refine Subgroup.mem_map.mpr ⟨⟨r * (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) * r,
    hzΩ⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  change ((R ⟨r * (x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) * r, hzΩ⟩ :
    ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) ∈ H
  rw [hEq]
  exact hrH _ hxH

theorem supp_le_of_reflect {S : Finset (Fin n)} (hS : 3 ≤ S.card)
    {H : Subgroup (V n ≃ₗ[ZMod 2] V n)} (hH : H ≤ supp n S) {v₀ : V n}
    (hv₀S : v₀ ∈ planeSpan n S) (hv₀ : Q n v₀ = 1)
    (hrH : ∀ h ∈ H, reflect (Q n) v₀ * h * reflect (Q n) v₀ ∈ H)
    (htr : ∀ w ∈ planeSpan n S, Q n w = 1 → ∃ h ∈ H, h v₀ = w) :
    supp n S ≤ H := by
  classical
  have hnd : (polarBilin ((Q n).restrict (planeSpan n S))).Nondegenerate :=
    nondegenerate_polarBilin_restrict_planeSpan S
  have h6 : 6 ≤ finrank (ZMod 2) (planeSpan n S) := by
    rw [finrank_planeSpan_eq_two_mul_card]
    omega
  let v₀' : ↥(planeSpan n S) := ⟨v₀, hv₀S⟩
  have hv₀' : (Q n).restrict (planeSpan n S) v₀' = 1 := hv₀
  obtain ⟨R, hR⟩ := exists_mulEquiv_orthDerived_restrict (n := n) (S := S) hS
  let K : Subgroup ↥(orthDerived ((Q n).restrict (planeSpan n S))) :=
    (H.subgroupOf (supp n S)).comap R.toMonoidHom
  let H' : Subgroup (↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) :=
    K.map (orthDerived ((Q n).restrict (planeSpan n S))).subtype
  have hH'le : H' ≤ orthDerived ((Q n).restrict (planeSpan n S)) :=
    Subgroup.map_subtype_le K
  have hH'O : H' ≤ TauCeti.QuadraticMap.orthogonalGroup ((Q n).restrict (planeSpan n S)) :=
    hH'le.trans (orthDerived_restrict_planeSpan_le_orthogonalGroup hS)
  have hrH' : ∀ h ∈ H',
      reflect ((Q n).restrict (planeSpan n S)) v₀' * h *
        reflect ((Q n).restrict (planeSpan n S)) v₀' ∈ H' :=
    reflect_conj_mem_map_comap hv₀S hv₀ hrH (R := R) hR
  have htr' : ∀ w : ↥(planeSpan n S),
      (Q n).restrict (planeSpan n S) w = 1 → ∃ h ∈ H', h v₀' = w := by
    intro w hw
    obtain ⟨h, hh, hhw⟩ := htr (w : V n) w.2 hw
    let x : ↥(orthDerived ((Q n).restrict (planeSpan n S))) := R.symm ⟨h, hH hh⟩
    have hRx : (R x : ↥(supp n S)) = ⟨h, hH hh⟩ := R.apply_symm_apply _
    refine ⟨(x : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)),
      Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩, ?_⟩
    · rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      change ((R x : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) ∈ H
      rw [hRx]
      exact hh
    · apply Subtype.ext
      have h1 := hR x v₀'
      rw [hRx] at h1
      exact h1.symm.trans hhw
  have key : orthDerived ((Q n).restrict (planeSpan n S)) ≤ H' :=
    CFSG.StandardType.QTwo.orthDerived_le_of_reflect hnd h6 hH'O hv₀' hrH' htr'
  intro g hg
  let y : ↥(orthDerived ((Q n).restrict (planeSpan n S))) := R.symm ⟨g, hg⟩
  have hyH' : (y : ↥(planeSpan n S) ≃ₗ[ZMod 2] ↥(planeSpan n S)) ∈ H' := key y.2
  obtain ⟨z, hzK, hzy⟩ := Subgroup.mem_map.mp hyH'
  have hzy' : z = y := Subtype.ext hzy
  rw [hzy'] at hzK
  have hyH : ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) ∈ H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hzK)
  have hRy : ((R y : ↥(supp n S)) : V n ≃ₗ[ZMod 2] V n) = g :=
    congrArg Subtype.val (R.apply_symm_apply (⟨g, hg⟩ : ↥(supp n S)))
  rwa [hRy] at hyH

end CFSG.ClassicalGroups.Orthogonal.SixPlane
