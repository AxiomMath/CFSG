module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinB
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry isometryCentralizer supportedBlock
  specialBlock blockComponent reciprocalPolynomial)

section ToSL

variable {n : ℕ} {K : Type} [Field K]

theorem det_eq_one_of_mem_orthDerived {Q : QuadraticForm K (Fin n → K)}
    {g : (Fin n → K) ≃ₗ[K] (Fin n → K)} (hg : g ∈ orthDerived Q) :
    LinearMap.det (g : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
  have h1 : orthDerived Q ≤ commutator ((Fin n → K) ≃ₗ[K] (Fin n → K)) := by
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have h2 := Abelianization.commutator_subset_ker
    (LinearEquiv.det : ((Fin n → K) ≃ₗ[K] (Fin n → K)) →* Kˣ) (h1 hg)
  rw [MonoidHom.mem_ker] at h2
  rw [← LinearEquiv.coe_det, h2, Units.val_one]

@[expose] noncomputable def orthToSL (Q : QuadraticForm K (Fin n → K)) :
    ↥(orthDerived Q) →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨LinearMap.toMatrix' (g.1 : (Fin n → K) →ₗ[K] (Fin n → K)), by
    rw [LinearMap.det_toMatrix']
    exact det_eq_one_of_mem_orthDerived g.2⟩
  map_one' := Subtype.ext LinearMap.toMatrix'_id
  map_mul' g h := Subtype.ext (by
    change LinearMap.toMatrix' ((g.1 : (Fin n → K) →ₗ[K] (Fin n → K)).comp
      (h.1 : (Fin n → K) →ₗ[K] (Fin n → K))) = _
    rw [LinearMap.toMatrix'_comp]
    rfl)

theorem toLin'_orthToSL (Q : QuadraticForm K (Fin n → K)) (g : ↥(orthDerived Q)) :
    Matrix.toLin' ((orthToSL Q g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (g.1 : (Fin n → K) →ₗ[K] (Fin n → K)) := by
  change Matrix.toLin' (LinearMap.toMatrix' _) = _
  exact Matrix.toLin'_toMatrix' _

theorem orthToSL_injective (Q : QuadraticForm K (Fin n → K)) :
    Function.Injective (orthToSL Q) := by
  intro g h hgh
  have h1 := toLin'_orthToSL Q g
  rw [hgh, toLin'_orthToSL] at h1
  exact Subtype.ext (LinearEquiv.toLinearMap_injective h1.symm)

end ToSL

section Plane

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

theorem planeRep_mem_sesqUnitaryGroup (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v) (e : ↥E0) :
    ρ₀ e ∈ sesqUnitaryGroup (QuadraticMap.polarBilin Q) := by
  intro u v
  change QuadraticMap.polar Q (act ρ₀ e u) (act ρ₀ e v) = QuadraticMap.polar Q u v
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hEQ, hEQ, hEQ]

@[expose] noncomputable def actEquiv (e : ↥E0) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K _ (ρ₀ e)

theorem actEquiv_toLinearMap (e : ↥E0) : (actEquiv e).toLinearMap = act ρ₀ e := rfl

theorem actEquiv_mul (e f : ↥E0) : actEquiv (e * f) = actEquiv e * actEquiv f := by
  unfold actEquiv
  rw [map_mul, map_mul]

theorem actEquiv_pow (e : ↥E0) (k : ℕ) : actEquiv (e ^ k) = actEquiv e ^ k := by
  unfold actEquiv
  rw [map_pow, map_pow]

theorem actEquiv_one : actEquiv (1 : ↥E0) = 1 := by
  unfold actEquiv
  rw [map_one, map_one]

theorem mem_isometryCentralizer_actEquiv {g : (Fin n → K) ≃ₗ[K] (Fin n → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgc : ∀ e : ↥E0, Commute g.toLinearMap (act ρ₀ e)) (e : ↥E0) :
    g ∈ isometryCentralizer Q (actEquiv e) := by
  refine KCOrthogonal.mem_isometryCentralizer.mpr
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO, fun v => ?_⟩
  exact congrArg (fun f : Module.End K (Fin n → K) => f v) (hgc e).eq

variable (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

theorem oddOrderIsometry_actEquiv (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (e : ↥E0) :
    OddOrderIsometry Q p (actEquiv e) where
  mem := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hEQ e)
  pow_eq_one := by rw [← actEquiv_pow, hP.pow e, actEquiv_one]
  cast_ne_zero := hpK
  regular := hreg

theorem polar_projLine_sub (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (u v : Fin n → K) :
    QuadraticMap.polar Q (projLine ρ₀ L u) (v - projLine ρ₀ L v) = 0 := by
  have hsa := isSelfAdj_projLine ρ₀ (planeRep_mem_sesqUnitaryGroup hEQ) L u (v - projLine ρ₀ L v)
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply] at hsa
  rw [hsa, map_sub, projLine_projLine hP hpK hL, sub_self, QuadraticMap.polar_zero_right]

theorem auxEnd_isometry (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0) (v : Fin n → K) :
    Q (auxEnd E0 c d L v) = Q v := by
  have h1 : QuadraticMap.polar Q (act ρ₀ c (projLine ρ₀ L v))
      (act ρ₀ d (v - projLine ρ₀ L v)) = 0 := by
    rw [← projLine_act_apply, map_sub, ← projLine_act_apply]
    exact polar_projLine_sub hP hpK hEQ hL _ _
  have h2 : QuadraticMap.polar Q (projLine ρ₀ L v) (v - projLine ρ₀ L v) = 0 :=
    polar_projLine_sub hP hpK hEQ hL v v
  calc Q (auxEnd E0 c d L v) = Q (projLine ρ₀ L v) + Q (v - projLine ρ₀ L v) := by
        rw [auxEnd_apply, QuadraticMap.map_add (⇑Q), h1, add_zero, hEQ, hEQ]
    _ = Q (projLine ρ₀ L v + (v - projLine ρ₀ L v)) := by
      rw [QuadraticMap.map_add (⇑Q), h2, add_zero]
    _ = Q v := by rw [add_sub_cancel]

@[expose] noncomputable def auxEquiv {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c d : ↥E0) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K _
    (Units.ofPowEqOne (auxEnd E0 c d L) p (auxEnd_pow_eq_one hP hpK hL c d) hP.prime.ne_zero)

theorem oddOrderIsometry_auxEquiv (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) {L : Subgroup ↥E0}
    (hL : L ∈ lines p E0) (c d : ↥E0) : OddOrderIsometry Q p (auxEquiv hP hpK hL c d) where
  mem := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (auxEnd_isometry hP hpK hEQ hL c d)
  pow_eq_one := by
    unfold auxEquiv
    rw [← map_pow, Units.pow_ofPowEqOne, map_one]
  cast_ne_zero := hpK
  regular := hreg

omit hpK in
theorem mem_isometryCentralizer_auxEquiv (hpK : (p : K) ≠ 0)
    {g : (Fin n → K) ≃ₗ[K] (Fin n → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgc : ∀ e : ↥E0, Commute g.toLinearMap (act ρ₀ e)) {L : Subgroup ↥E0}
    (hL : L ∈ lines p E0) (c d : ↥E0) :
    g ∈ isometryCentralizer Q (auxEquiv hP hpK hL c d) := by
  refine KCOrthogonal.mem_isometryCentralizer.mpr
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO, fun v => ?_⟩
  exact congrArg (fun f : Module.End K (Fin n → K) => f v)
    (commute_auxEnd_of_commute E0 hgc c d L).eq

theorem fixedSpace_auxEquiv {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {c d : ↥E0} (hcL : c ∉ L)
    (hdL : d ∈ L) (hd1 : d ≠ 1) :
    KCOrthogonal.fixedSpace (auxEquiv hP hpK hL c d) = LinearMap.range (projTop ρ₀) := by
  rw [KCOrthogonal.fixedSpace_eq_primaryComponent, ← C_1,
    ← primaryComponent_auxEnd_X_sub_one hP hpK hL hcL hdL hd1]
  rfl

omit hP hpK in
theorem act_apply_of_mem_range_projTop (e : ↥E0) {y : Fin n → K}
    (hy : y ∈ LinearMap.range (projTop ρ₀)) : act ρ₀ e y = y := by
  obtain ⟨u, rfl⟩ := hy
  exact avgOp_apply_mem_fixedSpace ρ₀ ⊤ u e (Subgroup.mem_top e)

end Plane

section Block

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem blockComponent_one (hx : OddOrderIsometry Q p x) (h : K[X]) :
    KCOrthogonal.blockComponent hx 1 h = 1 := by
  refine Subtype.ext (LinearEquiv.toLinearMap_injective
    (ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_))
  change (KCOrthogonal.blockComponent hx 1 h).1 v = v
  rw [KCOrthogonal.blockComponent_apply_of_mem hx _ h ha hv]
  split_ifs <;> rfl

theorem blockComponent_mul (hx : OddOrderIsometry Q p x)
    (g g' : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V))) (h : K[X]) :
    KCOrthogonal.blockComponent hx (g * g') h =
      KCOrthogonal.blockComponent hx g h * KCOrthogonal.blockComponent hx g' h := by
  refine Subtype.ext (LinearEquiv.toLinearMap_injective
    (ext_primaryComponent hx.squarefree_minpoly fun a ha v hv => ?_))
  have hv' : g'.1 v ∈ primaryComponent x.toLinearMap a :=
    KCOrthogonal.apply_mem_primaryComponent_of_mem_centralizer g'.2 hv
  change (KCOrthogonal.blockComponent hx (g * g') h).1 v =
    (KCOrthogonal.blockComponent hx g h).1 ((KCOrthogonal.blockComponent hx g' h).1 v)
  rw [KCOrthogonal.blockComponent_apply_of_mem hx _ h ha hv,
    KCOrthogonal.blockComponent_apply_of_mem hx g' h ha hv]
  split_ifs with hc
  · rw [KCOrthogonal.blockComponent_apply_of_mem hx g h ha hv', if_pos hc]
    rfl
  · rw [KCOrthogonal.blockComponent_apply_of_mem hx g h ha hv, if_neg hc]

@[expose] noncomputable def blockComponentHom (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    ↥(isometryCentralizer Q x) →* ↥(supportedBlock Q x h) where
  toFun g := ⟨(KCOrthogonal.blockComponent hx ⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩ h).1,
    hx.blockComponent_mem g.2 hh⟩
  map_one' := Subtype.ext (congrArg Subtype.val (blockComponent_one hx h) :)
  map_mul' g g' := Subtype.ext (congrArg Subtype.val (blockComponent_mul hx
    ⟨g.1, (Subgroup.mem_inf.mp g.2).2⟩ ⟨g'.1, (Subgroup.mem_inf.mp g'.2).2⟩ h) :)

theorem apply_eq_of_isSolvable_supportedBlock (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hsol : Group.IsSolvable ↥(supportedBlock Q x h))
    {R : Subgroup (V ≃ₗ[K] V)} [Group.IsPerfect ↥R] (hR : R ≤ isometryCentralizer Q x)
    {g : V ≃ₗ[K] V} (hg : g ∈ R) {v : V} (hv : v ∈ primaryComponent x.toLinearMap h) :
    g v = v := by
  have h1 := eq_one_of_perfect_of_isSolvable
    ((blockComponentHom hx hh).comp (Subgroup.inclusion hR)) ⟨g, hg⟩
  have h2 : (KCOrthogonal.blockComponent hx ⟨g, (Subgroup.mem_inf.mp (hR hg)).2⟩ h).1 v = v :=
    congrArg (fun s : ↥(supportedBlock Q x h) => s.1 v) h1
  rw [KCOrthogonal.blockComponent_apply_of_mem hx _ h hh hv, if_pos (Or.inl rfl)] at h2
  exact h2

theorem apply_eq_of_isSolvable_fixed (hsol : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace x).subtype)))
    {R : Subgroup (V ≃ₗ[K] V)} [Group.IsPerfect ↥R] (hR : R ≤ isometryCentralizer Q x)
    {g : V ≃ₗ[K] V} (hg : g ∈ R) {v : V} (hv : v ∈ KCOrthogonal.fixedSpace x) : g v = v := by
  let f := (KCOrthogonal.isometryRestrictFixed Q x).codRestrict _
    KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup
  have h1 := eq_one_of_perfect_of_isSolvable (f.comp (Subgroup.inclusion hR)) ⟨g, hg⟩
  exact congrArg (fun s => ((s.1 : KCOrthogonal.fixedSpace x ≃ₗ[K] KCOrthogonal.fixedSpace x)
    ⟨v, hv⟩ : V)) h1

theorem mem_supportedBlock_of_le (hx : OddOrderIsometry Q p x) {y : V ≃ₗ[K] V} {h : K[X]}
    (hself : reciprocalPolynomial h = h) (hhy : h ∈ primaryFactors y.toLinearMap)
    (hle : primaryComponent x.toLinearMap h ≤ primaryComponent y.toLinearMap h)
    (hxy : Commute x.toLinearMap y.toLinearMap) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x h)
    (hgy : g ∈ Subgroup.centralizer ({y} : Set (V ≃ₗ[K] V))) : g ∈ supportedBlock Q y h := by
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  refine KCOrthogonal.mem_supportedBlock.mpr ⟨Subgroup.mem_inf.mpr ⟨hgO, hgy⟩,
    KCOrthogonal.fixes_othersSpace_iff.mpr fun k hk hkh _ v hv => ?_⟩
  have hsq := hx.squarefree_minpoly
  have hsum : ∑ a ∈ primaryFactors x.toLinearMap, primaryProjection x.toLinearMap a v = v := by
    have := LinearMap.congr_fun (sum_primaryProjection hsq) v
    rwa [LinearMap.sum_apply, Module.End.one_apply] at this
  rw [← hsum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h1 : primaryProjection x.toLinearMap a v ∈ primaryComponent x.toLinearMap a :=
    primaryProjection_mem hsq ha v
  by_cases hah : a = h
  · subst hah
    have h2 : primaryProjection x.toLinearMap a v ∈ primaryComponent y.toLinearMap k :=
      apply_mem_primaryComponent (commute_aeval hxy.symm _).symm hv
    rw [eq_zero_of_mem_primaryComponent_ne hhy hk (Ne.symm hkh) (hle h1) h2, map_zero]
  · exact KCOrthogonal.apply_eq_of_mem_supportedBlock hg ha hah (by rwa [hself]) h1

theorem le_specialBlock_of_perfect {h : K[X]} {P : Subgroup (V ≃ₗ[K] V)} [Group.IsPerfect ↥P]
    (hP : P ≤ supportedBlock Q x h) : P ≤ specialBlock Q x h := by
  intro g hg
  have h1 := eq_one_of_perfect_of_isSolvable
    ((KCOrthogonal.blockDet Q x h).toHomUnits.comp (Subgroup.inclusion hP)) ⟨g, hg⟩
  have h2 : KCOrthogonal.blockDet Q x h ⟨g, hP hg⟩ = 1 := by
    have := congrArg Units.val h1
    rwa [MonoidHom.comp_apply, MonoidHom.coe_toHomUnits, Units.val_one] at this
  exact KCOrthogonal.mem_specialBlock.mpr ⟨hP hg, h2⟩

end Block

section Pieces

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

variable (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

theorem commute_act_of_mem_supportedBlock {L : Subgroup ↥E0} (hL : L ∈ lines p E0) {c : ↥E0}
    (hcL : c ∉ L) {h : K[X]} (hX : h ≠ X - C 1) (hself : reciprocalPolynomial h = h)
    {g : (Fin n → K) ≃ₗ[K] (Fin n → K)} (hg : g ∈ supportedBlock Q (auxEquiv hP hpK hL c 1) h)
    (e : ↥E0) : Commute g.toLinearMap (act ρ₀ e) := by
  have hgc := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
  have hgw : Commute g.toLinearMap (auxEnd E0 c 1 L) :=
    KCOrthogonal.commute_toLinearMap_of_mem_centralizer _ hgc
  show g.toLinearMap * act ρ₀ e = act ρ₀ e * g.toLinearMap
  refine ext_primaryComponent (squarefree_minpoly_auxEnd hP hpK hL c 1) fun a ha v hv => ?_
  show g (act ρ₀ e v) = act ρ₀ e (g v)
  by_cases hah : a = h
  · subst hah
    have hvL := mem_range_projLine_of_mem_primaryComponent hP hpK hL hcL ha hX hv
    have hgv : g v ∈ primaryComponent (auxEnd E0 c 1 L) a := apply_mem_primaryComponent hgw hv
    have hgvL := mem_range_projLine_of_mem_primaryComponent hP hpK hL hcL ha hX hgv
    obtain ⟨j, hj⟩ := exists_act_eq_auxEnd_pow hP hpK hL hcL 1 e
    rw [hj v hvL, hj (g v) hgvL]
    exact (congrArg (fun f : Module.End K (Fin n → K) => f v) (hgw.pow_right j).eq)
  · have hev : act ρ₀ e v ∈ primaryComponent (auxEnd E0 c 1 L) a :=
      apply_mem_primaryComponent (commute_act_auxEnd E0 e c 1 L) hv
    have hah' : a ≠ reciprocalPolynomial h := by rwa [hself]
    rw [KCOrthogonal.apply_eq_of_mem_supportedBlock hg ha hah hah' hev,
      KCOrthogonal.apply_eq_of_mem_supportedBlock hg ha hah hah' hv]

theorem commute_act_of_mem_supportedBlock_fixed {L : Subgroup ↥E0} (hL : L ∈ lines p E0)
    {c d : ↥E0} (hcL : c ∉ L) (hdL : d ∈ L) (hd1 : d ≠ 1) {g : (Fin n → K) ≃ₗ[K] (Fin n → K)}
    (hg : g ∈ supportedBlock Q (auxEquiv hP hpK hL c d) (X - 1)) (e : ↥E0) :
    Commute g.toLinearMap (act ρ₀ e) := by
  have hgc := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
  have hgw : Commute g.toLinearMap (auxEnd E0 c d L) :=
    KCOrthogonal.commute_toLinearMap_of_mem_centralizer _ hgc
  show g.toLinearMap * act ρ₀ e = act ρ₀ e * g.toLinearMap
  refine ext_primaryComponent (squarefree_minpoly_auxEnd hP hpK hL c d) fun a ha v hv => ?_
  show g (act ρ₀ e v) = act ρ₀ e (g v)
  by_cases haX : a = X - C 1
  · subst haX
    have hgv : g v ∈ primaryComponent (auxEnd E0 c d L) (X - C 1) :=
      apply_mem_primaryComponent hgw hv
    rw [primaryComponent_auxEnd_X_sub_one hP hpK hL hcL hdL hd1] at hv hgv
    rw [act_apply_of_mem_range_projTop e hv, act_apply_of_mem_range_projTop e hgv]
  · have hev : act ρ₀ e v ∈ primaryComponent (auxEnd E0 c d L) a :=
      apply_mem_primaryComponent (commute_act_auxEnd E0 e c d L) hv
    have h1 : a ≠ X - 1 := by rwa [C_1] at haX
    have h2 : a ≠ reciprocalPolynomial (X - 1) := by
      rwa [KCOrthogonal.reciprocalPolynomial_X_sub_one]
    rw [KCOrthogonal.apply_eq_of_mem_supportedBlock hg ha h1 h2 hev,
      KCOrthogonal.apply_eq_of_mem_supportedBlock hg ha h1 h2 hv]

theorem orth_exists_good_piece (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0)
    {R : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K))} [Group.IsPerfect ↥R] (hR : R ≠ ⊥)
    (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hRc : ∀ g ∈ R, ∀ e : ↥E0, Commute (g : (Fin n → K) →ₗ[K] (Fin n → K)) (act ρ₀ e))
    {L₀ : Subgroup ↥E0} (hL₀ : L₀ ∈ lines p E0) {c d : ↥E0} (hcL₀ : c ∉ L₀) (hdL₀ : d ∈ L₀)
    (hd1 : d ≠ 1) (cL : Subgroup ↥E0 → ↥E0) (hcL : ∀ L ∈ lines p E0, cL L ∉ L) :
    ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace (auxEquiv hP hpK hL₀ c d)).subtype)) ∨
    ∃ L, ∃ hL : L ∈ lines p E0, ∃ h : K[X], h ∈ primaryFactors (auxEnd E0 (cL L) 1 L) ∧
      h ≠ X - C 1 ∧ ¬ Group.IsSolvable ↥(supportedBlock Q (auxEquiv hP hpK hL (cL L) 1) h) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and, not_not] at hcon
  obtain ⟨hsol0, hsolL⟩ := hcon
  have hRw : ∀ {L : Subgroup ↥E0} (hL : L ∈ lines p E0) (c' d' : ↥E0),
      R ≤ isometryCentralizer Q (auxEquiv hP hpK hL c' d') := fun hL c' d' g' hg' =>
    mem_isometryCentralizer_auxEquiv hP hpK (hRO hg') (hRc g' hg') hL c' d'
  apply hR
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix0 : ∀ u ∈ LinearMap.range (projTop ρ₀), g u = u := by
    intro u hu
    rw [← fixedSpace_auxEquiv hP hpK hL₀ hcL₀ hdL₀ hd1] at hu
    exact apply_eq_of_isSolvable_fixed hsol0 (hRw hL₀ c d) hg hu
  have hfixL : ∀ L ∈ lines p E0, ∀ u ∈ LinearMap.range (projLine ρ₀ L), g u = u := by
    intro L hL u hu
    have hxL := oddOrderIsometry_auxEquiv hP hpK hEQ hreg hL (cL L) 1
    have hsq := squarefree_minpoly_auxEnd hP hpK hL (cL L) 1
    have hcomm : Commute (projLine ρ₀ L) (auxEnd E0 (cL L) 1 L) :=
      commute_auxEnd_of_commute E0 (fun e => (commute_act_projLine E0 e L).symm) (cL L) 1 L
    have hsum : ∑ h ∈ primaryFactors (auxEnd E0 (cL L) 1 L),
        primaryProjection (auxEnd E0 (cL L) 1 L) h u = u := by
      have := LinearMap.congr_fun (sum_primaryProjection hsq) u
      rwa [LinearMap.sum_apply, Module.End.one_apply] at this
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    have h1 : primaryProjection (auxEnd E0 (cL L) 1 L) h u ∈
        primaryComponent (auxEnd E0 (cL L) 1 L) h := primaryProjection_mem hsq hh u
    have h2 : primaryProjection (auxEnd E0 (cL L) 1 L) h u ∈ LinearMap.range (projLine ρ₀ L) :=
      aeval_mem_range_of_commute hcomm _ hu
    by_cases hX : h = X - C 1
    · subst hX
      have h3 : auxEnd E0 (cL L) 1 L (primaryProjection (auxEnd E0 (cL L) 1 L) (X - C 1) u) =
          primaryProjection (auxEnd E0 (cL L) 1 L) (X - C 1) u := by
        have := mem_primaryComponent.mp h1
        simp only [map_sub, aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply] at this
        exact sub_eq_zero.mp this
      rw [eq_zero_of_mem_range_of_auxEnd_apply hP hpK hL (hcL L hL) 1 h2 h3, map_zero]
    · exact apply_eq_of_isSolvable_supportedBlock hxL hh (hsolL L hL h hh hX) (hRw hL (cL L) 1)
        hg h1
  refine LinearEquiv.ext fun v => ?_
  have hv : ∑ L ∈ lines p E0, projLine ρ₀ L v + projTop ρ₀ v = v := by
    simpa using LinearMap.congr_fun (sum_projLine_add_projTop ρ₀ hP hpK) v
  show g v = v
  rw [← hv, map_add, map_sum, hfix0 _ (LinearMap.mem_range_self _ v)]
  congr 1
  exact Finset.sum_congr rfl fun L hL => hfixL L hL _ (LinearMap.mem_range_self _ v)

end Pieces

section Concl

variable {n : ℕ} {K : Type} [Field K]

@[expose] def OrthBlockConcl (Q : QuadraticForm K (Fin n → K))
    (E0 : Subgroup (SpecialLinearGroup (Fin n) K)) [Fintype E0] [IsMulCommutative E0] (p : ℕ)
    (â : ↥E0) : Prop :=
  ∃ a' : ↥E0, a' ∉ Subgroup.zpowers â ∧ ∃ P S M : Subgroup ((Fin n → K) ≃ₗ[K] (Fin n → K)),
    P ≤ S ∧ (∀ g ∈ S, ∀ y ∈ P, g * y * g⁻¹ ∈ P) ∧ S ≤ orthDerived Q ∧
    (∀ g ∈ S, ∀ e : ↥E0, Commute g.toLinearMap (act (planeRep E0) e)) ∧
    (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ e : ↥E0, Commute g.toLinearMap (act (planeRep E0) e)) → ∀ y ∈ S, g * y * g⁻¹ ∈ S) ∧
    CFSG.IsQuasisimple ↥P ∧ p ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) ∧
    M ≤ orthDerived Q ∧ M ≤ isometryCentralizer Q (actEquiv a') ∧
    (∀ g ∈ isometryCentralizer Q (actEquiv a'), ∀ y ∈ M, g * y * g⁻¹ ∈ M) ∧
    CFSG.IsQuasisimple ↥M ∧ P ≤ M ∧ p ∣ Nat.card (↥M ⧸ Subgroup.center ↥M) ∧
    actEquiv â ∉ Subgroup.centralizer (M : Set ((Fin n → K) ≃ₗ[K] (Fin n → K)))

end Concl

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
