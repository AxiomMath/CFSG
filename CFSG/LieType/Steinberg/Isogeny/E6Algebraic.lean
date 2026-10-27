module

public import CFSG.LieType.Steinberg.Minuscule.FiniteDescent
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyCenter
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
public import CFSG.RankThree.PartOne.KF.ClsLiftS3
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.KLCE.Sector

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem e6ScToBar_centralThree (k : Type) [Field k] [Finite k]
    {Ω : Type} [Field Ω] (ι : k →+* Ω) :
    CFSG.RankThree.PartOne.KFU.CentralThree (e6ScToBar k ι) := by
  have hker (z : e6Data_valid.minGroup k) (hz : e6ScToBar k ι z = 1) :
      z ∈ Subgroup.center (e6Data_valid.minGroup k) := by
    apply ker_e6IsogenyT_le_center k
    change e6Isogeny k z = 1
    apply Subtype.ext
    apply baseChangeGL_injective ι
    change e6ScToBar k ι z = baseChangeGL ι 1
    simpa only [map_one] using hz
  exact
    { central := fun z hz g => Subgroup.mem_center_iff.mp (hker z hz) g
      exp_three := fun z hz =>
        CFSG.ClassicalInvolution.ModelFacts.A2Isogeny.center_pow_three_e6 k (hker z hz) }

end CFSG.StandardType

namespace CFSG.LieType.Steinberg.Isogeny

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem e6ScToBar_minBC {k k' Ω : Type} [Field k] [Finite k] [Field k'] [Finite k']
    [Field Ω] (κ : k →+* k') (ι : k' →+* Ω) (x : e6Data_valid.minGroup k) :
    e6ScToBar k' ι (minBC e6Data_valid κ x) = e6ScToBar k (ι.comp κ) x := by
  change baseChangeGL ι ((e6Isogeny k' (minBC e6Data_valid κ x) : adjointGroup .E6 k') :
    ModGL .E6 k') = baseChangeGL (ι.comp κ) ((e6Isogeny k x : adjointGroup .E6 k) : ModGL .E6 k)
  rw [e6Isogeny_minBC, baseChangeGL_baseChangeGL]

variable {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
  [Algebra.IsAlgebraic (ZMod 2) Ω]

omit
    [CharP Ω 2] in
private theorem exists_common_finite_subfield
    (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (k' : Type) [Field k'] [Finite k'] (ι' : k' →+* Ω) :
    ∃ F : Subfield Ω, Finite F ∧ (∀ x, ι x ∈ F) ∧ ∀ x, ι' x ∈ F := by
  classical
  let : Fintype k := Fintype.ofFinite k
  let : Fintype k' := Fintype.ofFinite k'
  let S := Finset.univ.image ι ∪ Finset.univ.image ι'
  obtain ⟨F, hF, hSF, _⟩ := exists_finite_subfield_of_finset (K := ZMod 2) (L := Ω) S
  refine ⟨F, hF, fun x => hSF ?_, fun x => hSF ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)

private def finiteIsogenyGraph (g : e6Data_valid.minGroup Ω) (a : ModGL .E6 Ω) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k) (ι : k →+* Ω) (x : e6Data_valid.minGroup k),
    minBC e6Data_valid ι x = g ∧ e6ScToBar k ι x = a

private theorem finiteIsogenyGraph_exists (g : e6Data_valid.minGroup Ω) :
    ∃ a, finiteIsogenyGraph g a := by
  classical
  obtain ⟨k, hk, hfin, κ, ι, _, hdesc⟩ := e6Data_valid.exists_finite_subfield_lift
    ({g} : Finset (e6Data_valid.minGroup Ω)) (ZMod 2) (algebraMap (ZMod 2) Ω)
  let : Field k := hk
  let : Finite k := hfin
  obtain ⟨x, hx⟩ := hdesc g (Finset.mem_singleton_self _)
  exact ⟨e6ScToBar k ι x, k, hk, hfin, ι, x, hx, rfl⟩

omit [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω] in
private theorem extend_finite_lift (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (x : e6Data_valid.minGroup k) (F : Subfield Ω) [Finite F] (hF : ∀ c, ι c ∈ F) :
    ∃ y : e6Data_valid.minGroup F,
      minBC e6Data_valid F.subtype y = minBC e6Data_valid ι x ∧
      e6ScToBar F F.subtype y = e6ScToBar k ι x := by
  let κ : k →+* F := ι.codRestrict F hF
  have hκ : F.subtype.comp κ = ι := RingHom.ext fun _ => rfl
  refine ⟨minBC e6Data_valid κ x, ?_, ?_⟩
  · have h := congrArg (fun f => f x) (minBC_comp e6Data_valid κ F.subtype)
    simpa only [MonoidHom.comp_apply, hκ] using h
  · rw [e6ScToBar_minBC, hκ]

omit [CharP Ω 2] in
private theorem finiteIsogenyGraph_unique {g : e6Data_valid.minGroup Ω}
    {a b : ModGL .E6 Ω} (ha : finiteIsogenyGraph g a) (hb : finiteIsogenyGraph g b) : a = b := by
  obtain ⟨k, hk, hfin, ι, x, hx, ha⟩ := ha
  obtain ⟨k', hk', hfin', ι', x', hx', hb⟩ := hb
  let : Field k := hk
  let : Finite k := hfin
  let : Field k' := hk'
  let : Finite k' := hfin'
  obtain ⟨F, hFfin, hF, hF'⟩ := exists_common_finite_subfield k ι k' ι'
  let : Finite F := hFfin
  obtain ⟨y, hy, hya⟩ := extend_finite_lift k ι x F hF
  obtain ⟨y', hy', hyb⟩ := extend_finite_lift k' ι' x' F hF'
  have hyy : y = y' :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux.minBC_injective
      e6Data_valid F.subtype ((hy.trans hx).trans (hy'.trans hx').symm)
  exact ha.symm.trans (hya.symm.trans ((congrArg (e6ScToBar F F.subtype) hyy).trans
    (hyb.trans hb)))

omit [CharP Ω 2] [Algebra.IsAlgebraic (ZMod 2) Ω] in
private theorem finiteIsogenyGraph_one : finiteIsogenyGraph (1 : e6Data_valid.minGroup Ω) 1 :=
  ⟨ZMod 2, inferInstance, inferInstance, algebraMap (ZMod 2) Ω, 1, map_one _, map_one _⟩

omit [CharP Ω 2] in
private theorem finiteIsogenyGraph_mul {g h : e6Data_valid.minGroup Ω} {a b : ModGL .E6 Ω}
    (ha : finiteIsogenyGraph g a) (hb : finiteIsogenyGraph h b) :
    finiteIsogenyGraph (g * h) (a * b) := by
  obtain ⟨k, hk, hfin, ι, x, hx, ha⟩ := ha
  obtain ⟨k', hk', hfin', ι', x', hx', hb⟩ := hb
  let : Field k := hk
  let : Finite k := hfin
  let : Field k' := hk'
  let : Finite k' := hfin'
  obtain ⟨F, hFfin, hF, hF'⟩ := exists_common_finite_subfield k ι k' ι'
  let : Finite F := hFfin
  obtain ⟨y, hy, hya⟩ := extend_finite_lift k ι x F hF
  obtain ⟨y', hy', hyb⟩ := extend_finite_lift k' ι' x' F hF'
  refine ⟨F, inferInstance, hFfin, F.subtype, y * y', ?_, ?_⟩
  · rw [map_mul, hy, hy', hx, hx']
  · rw [map_mul, hya, hyb, ha, hb]

private noncomputable def e6IsogenyAlgebraicValue (g : e6Data_valid.minGroup Ω) : ModGL .E6 Ω :=
  (finiteIsogenyGraph_exists g).choose

private theorem e6IsogenyAlgebraicValue_graph (g : e6Data_valid.minGroup Ω) :
    finiteIsogenyGraph g (e6IsogenyAlgebraicValue g) :=
  (finiteIsogenyGraph_exists g).choose_spec

noncomputable def e6IsogenyAlgebraic : e6Data_valid.minGroup Ω →* ModGL .E6 Ω where
  toFun := e6IsogenyAlgebraicValue
  map_one' := finiteIsogenyGraph_unique (e6IsogenyAlgebraicValue_graph 1) finiteIsogenyGraph_one
  map_mul' g h := finiteIsogenyGraph_unique (e6IsogenyAlgebraicValue_graph (g * h))
    (finiteIsogenyGraph_mul (e6IsogenyAlgebraicValue_graph g) (e6IsogenyAlgebraicValue_graph h))

theorem e6IsogenyAlgebraic_minBC (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (x : e6Data_valid.minGroup k) :
    e6IsogenyAlgebraic (minBC e6Data_valid ι x) = e6ScToBar k ι x :=
  finiteIsogenyGraph_unique (e6IsogenyAlgebraicValue_graph _) ⟨k, inferInstance,
    inferInstance, ι, x, rfl, rfl⟩

theorem range_e6IsogenyAlgebraic :
    (e6IsogenyAlgebraic (Ω := Ω)).range = adjointGroup .E6 Ω := by
  apply le_antisymm
  · rintro a ⟨g, rfl⟩
    obtain ⟨k, hk, hfin, ι, x, _, ha⟩ := e6IsogenyAlgebraicValue_graph g
    let : Field k := hk
    let : Finite k := hfin
    change e6IsogenyAlgebraicValue g ∈ adjointGroup .E6 Ω
    rw [← ha]
    exact baseChangeGL_mem_adjointGroup ι (e6Isogeny k x).property
  · intro a ha
    obtain ⟨S, hS⟩ := exists_finset_descent ha
    obtain ⟨F, hFfin, hSF, _⟩ := exists_finite_subfield_of_finset (K := ZMod 2) (L := Ω) S
    let : Finite F := hFfin
    obtain ⟨a₀, ha₀, ha₀a⟩ := hS F hSF
    obtain ⟨x, hx⟩ := e6Isogeny_surjective F ⟨a₀, ha₀⟩
    refine ⟨minBC e6Data_valid F.subtype x, ?_⟩
    rw [e6IsogenyAlgebraic_minBC]
    change baseChangeGL F.subtype ((e6Isogeny F x : adjointGroup .E6 F) : ModGL .E6 F) = a
    rw [hx]
    exact ha₀a

theorem e6IsogenyAlgebraic_centralThree :
    CFSG.RankThree.PartOne.KFU.CentralThree (e6IsogenyAlgebraic (Ω := Ω)) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz g
    obtain ⟨k, hk, hfin, κ, ι, _, hdesc⟩ := e6Data_valid.exists_finite_subfield_lift
      ({z, g} : Finset (e6Data_valid.minGroup Ω)) (ZMod 2) (algebraMap (ZMod 2) Ω)
    let : Field k := hk
    let : Finite k := hfin
    obtain ⟨z₀, hz₀⟩ := hdesc z (by simp)
    obtain ⟨g₀, hg₀⟩ := hdesc g (by simp)
    have hz₀ker : e6ScToBar k ι z₀ = 1 := by
      rw [← e6IsogenyAlgebraic_minBC, hz₀]
      exact hz
    have hcomm := (CFSG.StandardType.e6ScToBar_centralThree k ι).central z₀ hz₀ker g₀
    have h := congrArg (minBC e6Data_valid ι) hcomm
    simpa only [map_mul, hz₀, hg₀] using h
  · intro z hz
    obtain ⟨k, hk, hfin, κ, ι, _, hdesc⟩ := e6Data_valid.exists_finite_subfield_lift
      ({z} : Finset (e6Data_valid.minGroup Ω)) (ZMod 2) (algebraMap (ZMod 2) Ω)
    let : Field k := hk
    let : Finite k := hfin
    obtain ⟨z₀, hz₀⟩ := hdesc z (by simp)
    have hz₀ker : e6ScToBar k ι z₀ = 1 := by
      rw [← e6IsogenyAlgebraic_minBC, hz₀]
      exact hz
    have h := congrArg (minBC e6Data_valid ι)
      ((CFSG.StandardType.e6ScToBar_centralThree k ι).exp_three z₀ hz₀ker)
    simpa only [map_pow, map_one, hz₀] using h

theorem ker_e6IsogenyAlgebraic_eq_center :
    (e6IsogenyAlgebraic (Ω := Ω)).ker = Subgroup.center (e6Data_valid.minGroup Ω) := by
  apply le_antisymm
  · intro z hz
    exact Subgroup.mem_center_iff.mpr (e6IsogenyAlgebraic_centralThree.central z hz)
  · intro z hz
    have hzG : e6IsogenyAlgebraic z ∈ adjointGroup .E6 Ω := by
      rw [← range_e6IsogenyAlgebraic]
      exact ⟨z, rfl⟩
    have hzC : (⟨e6IsogenyAlgebraic z, hzG⟩ : adjointGroup .E6 Ω) ∈
        Subgroup.center (adjointGroup .E6 Ω) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgπ : (g : ModGL .E6 Ω) ∈ (e6IsogenyAlgebraic (Ω := Ω)).range := by
        rw [range_e6IsogenyAlgebraic]
        exact g.property
      obtain ⟨v, hv⟩ := hgπ
      apply Subtype.ext
      exact (congrArg e6IsogenyAlgebraic (Subgroup.mem_center_iff.mp hz v)) |>
        fun h => by simpa only [map_mul, hv, Subgroup.coe_mul] using h
    rw [center_adjointGroup_eq_bot_field .E6 Ω] at hzC
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hzC)

end CFSG.LieType.Steinberg.Isogeny
