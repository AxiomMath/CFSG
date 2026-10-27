module

public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.ClassicalInvolution.Q3.Q3TWLMap
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
import CFSG.LieType.Universal.Spin.PlusCT.Weyl
import CFSG.LieType.Universal.Spin.Generation.Datum
import CFSG.ClassicalInvolution.WeakCT.TwistedRankOne
import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LieType.TitsSimplicity
import CFSG.LieType.Universal.SpinOmega
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.LieType.CurtisTits CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Q3.Q3TW

variable {m n : ℕ} {K : Type} [Field K]

private theorem quadPlus_extend_eq (σ : Fin m ↪ Fin n) (v : Fin m ⊕ Fin m → K) :
    quadPlus n K (Function.extend (Sum.map σ σ) v (0 : Fin n ⊕ Fin n → K)) = quadPlus m K v := by
  set w : Fin n ⊕ Fin n → K := Function.extend (Sum.map σ σ) v 0 with hw
  have hinj : Function.Injective (Sum.map σ σ) :=
    Function.Injective.sumMap σ.injective σ.injective
  have hout : ∀ i : Fin n, i ∉ Set.range σ → w (.inl i) * w (.inr i) = 0 := by
    intro i hi
    have h1 : w (.inl i) = 0 := by
      rw [hw]
      refine Function.extend_apply' (f := Sum.map σ σ) v (0 : Fin n ⊕ Fin n → K) (.inl i) ?_
      rintro ⟨a, ha⟩
      cases a with
      | inl a' => exact hi ⟨a', by simpa using ha⟩
      | inr a' => simp at ha
    have h2 : w (.inr i) = 0 := by
      rw [hw]
      refine Function.extend_apply' (f := Sum.map σ σ) v (0 : Fin n ⊕ Fin n → K) (.inr i) ?_
      rintro ⟨a, ha⟩
      cases a with
      | inl a' => simp at ha
      | inr a' => exact hi ⟨a', by simpa using ha⟩
    rw [h1, h2, mul_zero]
  have hσ : ∀ a : Fin m, w (.inl (σ a)) * w (.inr (σ a)) = v (.inl a) * v (.inr a) := by
    intro a
    have h1 : w (.inl (σ a)) = v (.inl a) := by
      rw [hw]
      simpa using Function.Injective.extend_apply hinj v (0 : Fin n ⊕ Fin n → K) (.inl a)
    have h2 : w (.inr (σ a)) = v (.inr a) := by
      rw [hw]
      simpa using Function.Injective.extend_apply hinj v (0 : Fin n ⊕ Fin n → K) (.inr a)
    rw [h1, h2]
  rw [quadPlus_apply, quadPlus_apply]
  calc ∑ i : Fin n, w (.inl i) * w (.inr i)
      = ∑ i ∈ Finset.univ.map σ, w (.inl i) * w (.inr i) := by
        refine (Finset.sum_subset (s₁ := Finset.univ.map σ) (s₂ := Finset.univ)
          (f := fun i => w (.inl i) * w (.inr i)) (Finset.subset_univ _) ?_).symm
        intro x _ hx
        exact hout x (by
          intro hxr
          obtain ⟨a, ha⟩ := hxr
          exact hx (Finset.mem_map.mpr ⟨a, Finset.mem_univ a, ha⟩))
    _ = ∑ a : Fin m, w (.inl (σ a)) * w (.inr (σ a)) :=
        Finset.sum_map Finset.univ σ (fun i => w (.inl i) * w (.inr i))
    _ = ∑ a : Fin m, v (.inl a) * v (.inr a) := Finset.sum_congr rfl (fun a _ => hσ a)

@[expose] noncomputable def plusIncl (σ : Fin m ↪ Fin n) : quadPlus m K →qᵢ quadPlus n K where
  toLinearMap := Function.ExtendByZero.linearMap K (Sum.map σ σ)
  map_app' v := by
    change quadPlus n K (Function.extend (Sum.map σ σ) v (0 : Fin n ⊕ Fin n → K)) = quadPlus m K v
    exact quadPlus_extend_eq σ v

theorem plusIncl_injective (σ : Fin m ↪ Fin n) : Function.Injective (plusIncl (K := K) σ) := by
  intro x y h
  have hinj : Function.Injective (Sum.map σ σ) :=
    Function.Injective.sumMap σ.injective σ.injective
  funext a
  have h1 : Function.extend (Sum.map σ σ) x (0 : Fin n ⊕ Fin n → K) (Sum.map σ σ a) =
      Function.extend (Sum.map σ σ) y (0 : Fin n ⊕ Fin n → K) (Sum.map σ σ a) :=
    congr_fun h (Sum.map σ σ a)
  rw [Function.Injective.extend_apply hinj x (0 : Fin n ⊕ Fin n → K) a,
      Function.Injective.extend_apply hinj y (0 : Fin n ⊕ Fin n → K) a] at h1
  exact h1

private theorem function_extend_single {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α → β) (hinj : Function.Injective e) (c : α) :
    Function.extend e (Pi.single c (1 : K)) (0 : β → K) = Pi.single (e c) 1 := by
  funext x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    rw [Function.Injective.extend_apply hinj (Pi.single c (1 : K)) (0 : β → K) y]
    by_cases hy : y = c
    · rw [hy]; simp
    · have hey : e y ≠ e c := fun h => hy (hinj h)
      simp [hy, hey]
  · rw [Function.extend_apply' (f := e) (Pi.single c (1 : K)) (0 : β → K) x hx]
    have hxc : x ≠ e c := fun h => hx ⟨c, h.symm⟩
    simp [hxc]

theorem plusIncl_plusVec (σ : Fin m ↪ Fin n) (a : Fin m) (s : Bool) :
    plusIncl (K := K) σ (plusVec m K a s) = plusVec n K (σ a) s := by
  have hinj : Function.Injective (Sum.map σ σ) :=
    Function.Injective.sumMap σ.injective σ.injective
  cases s
  · rw [plusVec_false, plusVec_false]
    change Function.extend (Sum.map σ σ) (Pi.single (.inr a) (1 : K))
        (0 : Fin n ⊕ Fin n → K) = Pi.single (.inr (σ a)) (1 : K)
    simpa using function_extend_single (Sum.map σ σ) hinj (.inr a)
  · rw [plusVec_true, plusVec_true]
    change Function.extend (Sum.map σ σ) (Pi.single (.inl a) (1 : K))
        (0 : Fin n ⊕ Fin n → K) = Pi.single (.inl (σ a)) (1 : K)
    simpa using function_extend_single (Sum.map σ σ) hinj (.inl a)

theorem spinGroupMap_plusIncl_comp_longRoot (hm : 3 ≤ m) (hn : 3 ≤ n) (σ : Fin m ↪ Fin n)
    {a b : Fin m} (hab : a ≠ b) (s t : Bool) :
    (plusIncl (K := K) σ).spinGroupMap.comp ((plusFrame m K hm).longRoot hab s t) =
      (plusFrame n K hn).longRoot (σ.injective.ne hab) s t := by
  exact CFSG.ClassicalInvolution.Q3.Q3TW.spinGroupMap_comp_longRoot
    (plusIncl (K := K) σ) (plusFrame m K hm) (plusFrame n K hn) hab (σ.injective.ne hab) s t
    (by simpa using plusIncl_plusVec (K := K) σ a s)
    (by simpa using plusIncl_plusVec (K := K) σ b t)

theorem range_spinGroupMap_plusIncl (hm : 3 ≤ m) (σ : Fin m ↪ Fin n) :
    (plusIncl (K := K) σ).spinGroupMap.range =
      ⨆ a, (rankOne (plusDatum m K hm).rootGroup a).map (plusIncl (K := K) σ).spinGroupMap := by
  rw [MonoidHom.range_eq_map]
  have hgen : ⨆ a, rankOne (plusDatum m K hm).rootGroup a = ⊤ :=
    CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_eq_top_of_ct
      (D := plusDatum m K hm)
      (plusDatum_isCTGroupDatum hm (plusDatum_iSup_eq_top m K hm)) rfl
  rw [← hgen, Subgroup.map_iSup]

noncomputable abbrev plusInclRange (σ : Fin m ↪ Fin n) : Submodule K (Fin n ⊕ Fin n → K) :=
  LinearMap.range (plusIncl (K := K) σ).toLinearMap

private theorem polar_comp_subtype_apply (σ : Fin m ↪ Fin n)
    (x y : plusInclRange (K := K) σ) :
    polar ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype) x y =
      polar (quadPlus n K) (x : Fin n ⊕ Fin n → K) (y : Fin n ⊕ Fin n → K) := by
  rw [← QuadraticMap.polarBilin_apply_apply
        ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype) x y,
      ← QuadraticMap.polarBilin_apply_apply (quadPlus n K)
        (x : Fin n ⊕ Fin n → K) (y : Fin n ⊕ Fin n → K),
      QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
  rfl

theorem nondegenerate_polarBilin_comp_plusInclRange (σ : Fin m ↪ Fin n) :
    (polarBilin ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp v.2
  have hvu : (v : Fin n ⊕ Fin n → K) = plusIncl (K := K) σ u := hu.symm
  have hzero : u = 0 := by
    have key : ∀ (a : Fin m) (s : Bool),
        polar (quadPlus m K) u (plusVec m K a s) = 0 := by
      intro a s
      have hv1 : polar (quadPlus n K) (v : Fin n ⊕ Fin n → K)
          (plusIncl (K := K) σ (plusVec m K a s)) = 0 := by
        have h := hv ⟨plusIncl (K := K) σ (plusVec m K a s),
          LinearMap.mem_range.mpr ⟨plusVec m K a s, rfl⟩⟩
        rwa [polar_comp_subtype_apply] at h
      rw [hvu, QuadraticMap.Isometry.polar_apply (plusIncl (K := K) σ)] at hv1
      exact hv1
    funext w
    rcases w with a | a
    · simpa [plusVec_false, polar_quadPlus_single_inr] using key a false
    · simpa [plusVec_true, polar_quadPlus_single_inl] using key a true
  apply Subtype.ext
  rw [hvu, hzero]
  simp

private theorem polarNondegOn_of_nondegenerate' {W : Submodule K (Fin n ⊕ Fin n → K)}
    (h : (polarBilin ((quadPlus n K).comp W.subtype)).Nondegenerate) :
    PolarNondegOn (quadPlus n K) W := by
  intro x hx hxy
  have : (⟨x, hx⟩ : W) = 0 := h.1 ⟨x, hx⟩ fun y => by
    rw [polarBilin_apply_apply, polar_comp_subtype_eq]
    exact hxy y y.2
  exact congrArg Subtype.val this

private noncomputable def plusInclIsometryEquiv (σ : Fin m ↪ Fin n) :
    (quadPlus m K).IsometryEquiv
      ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype) where
  toLinearEquiv :=
    LinearEquiv.ofInjective (plusIncl (K := K) σ).toLinearMap (plusIncl_injective σ)
  map_app' v := (plusIncl (K := K) σ).map_app' v

private theorem plusInclIsometryEquiv_apply_coe (σ : Fin m ↪ Fin n) (v : Fin m ⊕ Fin m → K) :
    (((plusInclIsometryEquiv (K := K) σ) v : plusInclRange (K := K) σ) :
      Fin n ⊕ Fin n → K) = plusIncl (K := K) σ v := rfl

private theorem plusInclIsometryEquiv_toLinearEquiv_apply_coe (σ : Fin m ↪ Fin n)
    (v : Fin m ⊕ Fin m → K) :
    (((plusInclIsometryEquiv (K := K) σ).toLinearEquiv v : plusInclRange (K := K) σ) :
      Fin n ⊕ Fin n → K) = plusIncl (K := K) σ v := rfl

private def fixSuppPerp (σ : Fin m ↪ Fin n) :
    Subgroup ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) where
  carrier := {g | ∀ v ∈ suppPerp (quadPlus n K) (plusInclRange (K := K) σ), g v = v}
  mul_mem' := by
    intro a b ha hb v hv
    rw [LinearEquiv.mul_apply, hb v hv, ha v hv]
  one_mem' := by
    intro v _
    rfl
  inv_mem' := by
    intro a ha v hv
    calc a⁻¹ v = a⁻¹ (a v) := by rw [ha v hv]
      _ = v := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

private theorem spinAction_spinGroupMap_range_fix_suppPerp (hm : 3 ≤ m)
    (σ : Fin m ↪ Fin n) (x : spinGroup (quadPlus m K)) :
    ∀ v ∈ suppPerp (quadPlus n K) (plusInclRange (K := K) σ),
      spinAction (quadPlus n K) ((plusIncl (K := K) σ).spinGroupMap x) v = v := by
  have hn : 3 ≤ n := by
    have h := Fintype.card_le_of_injective (σ : Fin m → Fin n) σ.injective
    simp only [Fintype.card_fin] at h
    omega
  have hle : (plusIncl (K := K) σ).spinGroupMap.range ≤
      (fixSuppPerp (K := K) σ).comap (spinAction (quadPlus n K)) := by
    rw [range_spinGroupMap_plusIncl hm σ]
    refine iSup_le fun a => ?_
    let a' : Fin m := a
    rw [CurtisTits.rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · change ((plusRootGroup m K hm (Pi.single a' 1)).map
          (plusIncl (K := K) σ).spinGroupMap) ≤
        (fixSuppPerp (K := K) σ).comap (spinAction (quadPlus n K))
      rw [plusRootGroup_single hm a', MonoidHom.map_range]
      unfold rootD
      rw [spinGroupMap_plusIncl_comp_longRoot hm hn σ _ true _]
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_comap, ← ofAdd_toAdd c]
      rw [HypFrame.spinAction_longRoot_eq_eichler]
      rw [plusFrame_vec]
      intro v hv
      have hu : plusVec n K (σ (rootIdxD' m a')) (rootSignD m a') ∈
          plusInclRange (K := K) σ :=
        ⟨plusVec m K (rootIdxD' m a') (rootSignD m a'), plusIncl_plusVec σ _ _⟩
      have hw : plusVec n K (σ (rootIdxD m a')) true ∈ plusInclRange (K := K) σ :=
        ⟨plusVec m K (rootIdxD m a') true, plusIncl_plusVec σ _ _⟩
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [polar_comm, mem_suppPerp.mp hv _ hu]
      · rw [polar_smul_right_eq, polar_comm, mem_suppPerp.mp hv _ hw, mul_zero]
    · change ((plusRootGroup m K hm (-Pi.single a' 1)).map
          (plusIncl (K := K) σ).spinGroupMap) ≤
        (fixSuppPerp (K := K) σ).comap (spinAction (quadPlus n K))
      rw [plusRootGroup_neg_single hm a', MonoidHom.map_range]
      unfold negRootD
      rw [spinGroupMap_plusIncl_comp_longRoot hm hn σ _ (!rootSignD m a') false]
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_comap, ← ofAdd_toAdd c]
      rw [HypFrame.spinAction_longRoot_eq_eichler]
      rw [plusFrame_vec]
      intro v hv
      have hu : plusVec n K (σ (rootIdxD m a')) false ∈ plusInclRange (K := K) σ :=
        ⟨plusVec m K (rootIdxD m a') false, plusIncl_plusVec σ _ _⟩
      have hw : plusVec n K (σ (rootIdxD' m a')) (!rootSignD m a') ∈ plusInclRange (K := K) σ :=
        ⟨plusVec m K (rootIdxD' m a') (!rootSignD m a'), plusIncl_plusVec σ _ _⟩
      refine eichler_apply_of_polar_eq_zero ?_ ?_
      · rw [polar_comm, mem_suppPerp.mp hv _ hu]
      · rw [polar_smul_right_eq, polar_comm, mem_suppPerp.mp hv _ hw, mul_zero]
  exact hle (MonoidHom.mem_range.mpr ⟨x, rfl⟩)

private theorem commutatorOrthogonalGroupCongr_plusInclIsometryEquiv_apply_coe
    (σ : Fin m ↪ Fin n) (h : orthDerived (quadPlus m K)) (v : Fin m ⊕ Fin m → K) :
    ((commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ) h :
        (plusInclRange (K := K) σ) ≃ₗ[K] (plusInclRange (K := K) σ))
      ((plusInclIsometryEquiv (K := K) σ) v) : Fin n ⊕ Fin n → K) =
      plusIncl (K := K) σ ((h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) v) := by
  rw [coe_commutatorOrthogonalGroupCongr_apply]
  simp only [LinearEquiv.trans_apply, plusInclIsometryEquiv_toLinearEquiv_apply_coe]
  congr 1
  congr 1
  exact (plusInclIsometryEquiv (K := K) σ).symm_apply_apply v

private theorem map_range_spinGroupMap_le_supportedDerived (hm : 3 ≤ m)
    (σ : Fin m ↪ Fin n) :
    ((plusIncl (K := K) σ).spinGroupMap.range.map (spinAction (quadPlus n K))) ≤
      supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) := by
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [mem_supportedDerived]
  refine ⟨spinAction_spinGroupMap_range_fix_suppPerp hm σ y, ?_⟩
  let h0lin : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) := spinAction (quadPlus m K) y
  have h0mem : h0lin ∈ orthDerived (quadPlus m K) := by
    change h0lin ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆
    rw [← range_spinAction_quadPlus_eq_commutator hm]
    exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  let h0 : orthDerived (quadPlus m K) := ⟨h0lin, h0mem⟩
  let H : orthDerived ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype) :=
    commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ) h0
  let Hlin : (plusInclRange (K := K) σ) ≃ₗ[K] (plusInclRange (K := K) σ) := H
  refine ⟨Hlin, H.2, fun w => ?_⟩
  have hw : (w : Fin n ⊕ Fin n → K) =
      plusIncl (K := K) σ (((plusInclIsometryEquiv (K := K) σ).symm w :
        Fin m ⊕ Fin m → K)) := by
    conv_lhs => rw [← (plusInclIsometryEquiv (K := K) σ).apply_symm_apply w]
    exact plusInclIsometryEquiv_apply_coe σ _
  have hHw : ((Hlin w : plusInclRange (K := K) σ) : Fin n ⊕ Fin n → K) =
      plusIncl (K := K) σ (h0lin ((plusInclIsometryEquiv (K := K) σ).symm w :
        Fin m ⊕ Fin m → K)) := by
    dsimp only [Hlin, H, h0]
    rw [coe_commutatorOrthogonalGroupCongr_apply]
    simp only [LinearEquiv.trans_apply, plusInclIsometryEquiv_toLinearEquiv_apply_coe]
    rfl
  rw [hHw, hw, spinAction_spinGroupMap]

private theorem supportedDerived_le_map_range_spinGroupMap_plusIncl (h2 : (2 : K) = 0)
    (hm : 3 ≤ m) (σ : Fin m ↪ Fin n) :
    supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) ≤
      ((plusIncl (K := K) σ).spinGroupMap.range.map (spinAction (quadPlus n K))) := by
  intro g hg
  obtain ⟨hgperp, h, hh, hagree⟩ := mem_supportedDerived.mp hg
  let h0 : orthDerived (quadPlus m K) :=
    (commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ)).symm ⟨h, hh⟩
  let x : spinGroup (quadPlus m K) := (spinEquivCommutatorQuadPlus hm h2).symm h0
  have hx_action : spinAction (quadPlus m K) x =
      (h0 : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) := by
    rw [← coe_spinEquivCommutatorQuadPlus_apply hm h2 x]
    exact congrArg Subtype.val ((spinEquivCommutatorQuadPlus hm h2).apply_symm_apply h0)
  have h0spec : (commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ)) h0 =
      (⟨h, hh⟩ : orthDerived ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype)) :=
    (commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ)).apply_symm_apply ⟨h, hh⟩
  have hfix : ∀ v ∈ suppPerp (quadPlus n K) (plusInclRange (K := K) σ),
      spinAction (quadPlus n K) ((plusIncl (K := K) σ).spinGroupMap x) v = v :=
    spinAction_spinGroupMap_range_fix_suppPerp hm σ x
  have hP : PolarNondegOn (quadPlus n K) (plusInclRange (K := K) σ) :=
    polarNondegOn_of_nondegenerate' (nondegenerate_polarBilin_comp_plusInclRange σ)
  have hcompl : IsCompl (plusInclRange (K := K) σ)
      (suppPerp (quadPlus n K) (plusInclRange (K := K) σ)) := isCompl_suppPerp hP
  refine Subgroup.mem_map.mpr ⟨(plusIncl (K := K) σ).spinGroupMap x,
    MonoidHom.mem_range.mpr ⟨x, rfl⟩, ?_⟩
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨p, hp, q, hq, hpq⟩ := suppExists_add_of_isCompl hcompl v
  rw [← hpq, map_add, map_add, hfix q hq, hgperp q hq]
  congr 1
  let u : Fin m ⊕ Fin m → K := (plusInclIsometryEquiv (K := K) σ).symm ⟨p, hp⟩
  have hu : (plusInclIsometryEquiv (K := K) σ) u = ⟨p, hp⟩ :=
    (plusInclIsometryEquiv (K := K) σ).apply_symm_apply ⟨p, hp⟩
  have hup : plusIncl (K := K) σ u = p := by
    rw [← plusInclIsometryEquiv_apply_coe σ u, hu]
  have hleft : spinAction (quadPlus n K) ((plusIncl (K := K) σ).spinGroupMap x) p =
      plusIncl (K := K) σ ((h0 : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) u) := by
    rw [← hup, spinAction_spinGroupMap, hx_action]
  have hright : g p =
      plusIncl (K := K) σ ((h0 : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) u) := by
    rw [← hagree ⟨p, hp⟩]
    have hHcoe : ((commutatorOrthogonalGroupCongr (plusInclIsometryEquiv (K := K) σ) h0 :
        orthDerived ((quadPlus n K).comp (plusInclRange (K := K) σ).subtype)) :
        (plusInclRange (K := K) σ) ≃ₗ[K] (plusInclRange (K := K) σ)) = h := by
      rw [h0spec]
    rw [← hHcoe, ← hu]
    exact commutatorOrthogonalGroupCongr_plusInclIsometryEquiv_apply_coe σ h0 u
  exact hleft.trans hright.symm

theorem map_spinAction_range_spinGroupMap_plusIncl [Finite K] (h2 : (2 : K) = 0) (hm : 3 ≤ m)
    (σ : Fin m ↪ Fin n) :
    (plusIncl (K := K) σ).spinGroupMap.range.map (spinAction (quadPlus n K)) =
      supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) :=
  le_antisymm (map_range_spinGroupMap_le_supportedDerived hm σ)
    (supportedDerived_le_map_range_spinGroupMap_plusIncl h2 hm σ)

private theorem range_longRoot_le_range_spinGroupMap (hm : 3 ≤ m) (hn : 3 ≤ n)
    (σ : Fin m ↪ Fin n) {a b : Fin m} (hab : a ≠ b) (s t : Bool) :
    ((plusFrame n K hn).longRoot (σ.injective.ne hab) s t).range ≤
      (plusIncl (K := K) σ).spinGroupMap.range := by
  rw [← spinGroupMap_plusIncl_comp_longRoot hm hn σ hab s t]
  rintro x ⟨y, rfl⟩
  exact ⟨(plusFrame m K hm).longRoot hab s t y, rfl⟩

theorem rankOne_le_range_spinGroupMap_plusIncl (hm : 3 ≤ m) (hn : 3 ≤ n) (σ : Fin m ↪ Fin n)
    (k : Fin n) (hk : rootIdxD n k ∈ Set.range σ) (hk' : rootIdxD' n k ∈ Set.range σ) :
    rankOne (plusDatum n K hn).rootGroup k ≤ (plusIncl (K := K) σ).spinGroupMap.range := by
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hk'
  have hab : a ≠ b := fun h => rootIdxD_ne n (by omega) k (by rw [← ha, ← hb, h])
  change plusRootGroup n K hn (Pi.single k 1) ⊔ plusRootGroup n K hn (-Pi.single k 1) ≤
    (plusIncl (K := K) σ).spinGroupMap.range
  refine sup_le ?_ ?_
  · have h1 : toStdD n (Pi.single k 1) =
        Pi.single (σ a) (boolSign true) + Pi.single (σ b) (boolSign (rootSignD n k)) := by
      rw [toStdD_single_eq (by omega) k, ← ha, ← hb]
    rw [plusRootGroup_eq hn (σ.injective.ne hab) true (rootSignD n k) h1]
    exact range_longRoot_le_range_spinGroupMap hm hn σ hab true (rootSignD n k)
  · have h2 : toStdD n (-Pi.single k 1) =
        Pi.single (σ b) (boolSign (!rootSignD n k)) + Pi.single (σ a) (boolSign false) := by
      rw [toStdD_neg, toStdD_single_eq (by omega) k, boolSign_not, boolSign_false, boolSign_true,
        neg_add, ← Pi.single_neg, ← Pi.single_neg, ← ha, ← hb, add_comm]
    rw [plusRootGroup_eq hn (σ.injective.ne (hab.symm)) (!rootSignD n k) false h2]
    exact range_longRoot_le_range_spinGroupMap hm hn σ (hab.symm) (!rootSignD n k) false

end CFSG.LieType.Universal.Spin

end
