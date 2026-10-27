module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSmallFieldPerfect
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Blueprint.Catalog

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinaryStabilizer

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Alternating
open LinearMap (BilinForm)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem zmod_two_mul_self (c : ZMod 2) : c * c = c := by
  fin_cases c <;> rfl

theorem polar_self_zmod_two (Q : QuadraticForm (ZMod 2) W) (x : W) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem map_add_smul_of_polar_eq_zero {Q : QuadraticForm (ZMod 2) W} {v x : W} (hv : Q v = 1)
    (hx : polar Q v x = 0) (c : ZMod 2) : Q (x + c • v) = Q x + c := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, polar_smul_right, polar_comm, hx,
    smul_zero, add_zero, smul_eq_mul, mul_one, zmod_two_mul_self]

theorem reflect_apply_eq_add_of_map_eq_one {Q : QuadraticForm (ZMod 2) W} {b : W} (hb : Q b = 1)
    (x : W) : reflect Q b x = x + polar Q x b • b := by
  rw [reflect_apply (by rw [hb]; exact one_ne_zero), hb, div_one, polar_comm, sub_eq_add_neg,
    ← neg_smul, ZMod.neg_eq_self_mod_two]

section Quotient

variable (Q : QuadraticForm (ZMod 2) W) (v : W)

@[expose] def vPerp : Submodule (ZMod 2) W :=
  LinearMap.ker (polarBilin Q v)

variable {Q v} in
theorem mem_vPerp {x : W} : x ∈ vPerp Q v ↔ polar Q v x = 0 := by
  rw [vPerp, LinearMap.mem_ker, polarBilin_apply_apply]

theorem self_mem_vPerp : v ∈ vPerp Q v :=
  mem_vPerp.2 (polar_self_zmod_two Q v)

theorem vPerp_eq_orthogonal :
    vPerp Q v = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span (ZMod 2) {v}) := by
  ext x
  rw [mem_vPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, hx, smul_zero]
  · intro h
    have := h v (Submodule.mem_span_singleton_self v)
    rwa [polarBilin_apply_apply] at this

@[expose] def vLine : Submodule (ZMod 2) (vPerp Q v) :=
  Submodule.span (ZMod 2) {⟨v, self_mem_vPerp Q v⟩}

variable {Q v} in
theorem mem_vLine {x : vPerp Q v} : x ∈ vLine Q v ↔ ∃ c : ZMod 2, (x : W) = c • v := by
  rw [vLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc.symm⟩

abbrev BarW : Type _ :=
  vPerp Q v ⧸ vLine Q v

@[expose] def perpB : BilinForm (ZMod 2) (vPerp Q v) :=
  (polarBilin Q).compl₁₂ (vPerp Q v).subtype (vPerp Q v).subtype

theorem perpB_apply (x y : vPerp Q v) : perpB Q v x y = polar Q x y :=
  polarBilin_apply_apply Q _ _

theorem perpB_eq_zero_of_mem_vLine_right (x : vPerp Q v) {y : vPerp Q v}
    (hy : y ∈ vLine Q v) : perpB Q v x y = 0 := by
  obtain ⟨c, hc⟩ := mem_vLine.1 hy
  rw [perpB_apply, hc, polar_smul_right, polar_comm, mem_vPerp.1 x.2, smul_zero]

theorem perpB_eq_zero_of_mem_vLine_left {x : vPerp Q v} (hx : x ∈ vLine Q v)
    (y : vPerp Q v) : perpB Q v x y = 0 := by
  obtain ⟨c, hc⟩ := mem_vLine.1 hx
  rw [perpB_apply, hc, polar_smul_left, mem_vPerp.1 y.2, smul_zero]

theorem vLine_le_ker_flip : vLine Q v ≤ LinearMap.ker (perpB Q v).flip := fun _ hy =>
  LinearMap.mem_ker.2 (LinearMap.ext fun x => perpB_eq_zero_of_mem_vLine_right Q v x hy)

@[expose] def perpBLeft : vPerp Q v →ₗ[ZMod 2] BarW Q v →ₗ[ZMod 2] ZMod 2 :=
  ((vLine Q v).liftQ (perpB Q v).flip (vLine_le_ker_flip Q v)).flip

theorem perpBLeft_mk (x y : vPerp Q v) :
    perpBLeft Q v x (Submodule.Quotient.mk y) = perpB Q v x y :=
  rfl

theorem vLine_le_ker_perpBLeft : vLine Q v ≤ LinearMap.ker (perpBLeft Q v) := fun x hx =>
  LinearMap.mem_ker.2 (LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun z => by
    rw [perpBLeft_mk, perpB_eq_zero_of_mem_vLine_left Q v hx, LinearMap.zero_apply])

@[expose] def barB : BilinForm (ZMod 2) (BarW Q v) :=
  (vLine Q v).liftQ (perpBLeft Q v) (vLine_le_ker_perpBLeft Q v)

theorem barB_mk (x y : vPerp Q v) :
    barB Q v (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = polar Q x y :=
  perpB_apply Q v x y

theorem barB_isAlt : (barB Q v).IsAlt := fun x =>
  Submodule.Quotient.induction_on _ x fun x => by
    rw [barB_mk]
    exact polar_self_zmod_two Q x

theorem polarBilin_isRefl : (polarBilin Q).IsRefl :=
  (QuadraticMap.isSymm_polarBilin Q).isRefl

variable [FiniteDimensional (ZMod 2) W]

variable {Q} in
theorem exists_eq_smul_of_forall_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {u : W}
    (hu : ∀ x ∈ vPerp Q v, polar Q u x = 0) : ∃ c : ZMod 2, u = c • v := by
  have hmem : u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (vPerp Q v) :=
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => by
      rw [polarBilin_apply_apply, polar_comm]
      exact hu x hx
  rw [vPerp_eq_orthogonal, LinearMap.BilinForm.orthogonal_orthogonal hQ (polarBilin_isRefl Q)]
    at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

variable {Q} in
theorem barB_nondegenerate (hQ : (polarBilin Q).Nondegenerate) : (barB Q v).Nondegenerate := by
  have hrefl : (barB Q v).IsRefl := fun x y h => by
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    rw [barB_mk] at h ⊢
    rwa [polar_comm]
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).2 fun x hx => ?_
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_polar_eq_zero v hQ (u := x) fun y hy => by
    have := hx (Submodule.Quotient.mk ⟨y, hy⟩)
    rwa [barB_mk] at this
  exact (Submodule.Quotient.mk_eq_zero _).2 (mem_vLine.2 ⟨c, hc⟩)

variable {Q v} in
theorem finrank_barW_add_two (hQ : (polarBilin Q).Nondegenerate) (hv : v ≠ 0) :
    finrank (ZMod 2) (BarW Q v) + 2 = finrank (ZMod 2) W := by
  have h1 : finrank (ZMod 2) (BarW Q v) + finrank (ZMod 2) (vLine Q v) =
      finrank (ZMod 2) (vPerp Q v) :=
    Submodule.finrank_quotient_add_finrank (vLine Q v)
  have h2 : finrank (ZMod 2) (vLine Q v) = 1 :=
    finrank_span_singleton (fun h => hv (congrArg Subtype.val h))
  have h3 : finrank (ZMod 2) (vPerp Q v) = finrank (ZMod 2) W - 1 := by
    rw [vPerp_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hv]
  have h4 : 1 ≤ finrank (ZMod 2) W := by
    have := Submodule.finrank_le (Submodule.span (ZMod 2) {v})
    rw [finrank_span_singleton hv] at this
    exact this
  omega

end Quotient

section Stabilizer

variable (Q : QuadraticForm (ZMod 2) W) (v : W)

@[expose] def stabO : Subgroup (W ≃ₗ[ZMod 2] W) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v

@[expose] def stabS : Subgroup (W ≃ₗ[ZMod 2] W) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓
    MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v

variable {Q v}

theorem mem_stabO {g : W ≃ₗ[ZMod 2] W} :
    g ∈ stabO Q v ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g v = v :=
  Iff.rfl

theorem mem_stabS {g : W ≃ₗ[ZMod 2] W} :
    g ∈ stabS Q v ↔
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        g v = v :=
  Iff.rfl

theorem commutator_le_self (H : Subgroup (W ≃ₗ[ZMod 2] W)) : ⁅H, H⁆ ≤ H :=
  (Subgroup.commutator_le).2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem stabS_le_stabO : stabS Q v ≤ stabO Q v := fun _ hg =>
  ⟨commutator_le_self _ hg.1, hg.2⟩

theorem apply_mem_vPerp {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) {x : W}
    (hx : x ∈ vPerp Q v) : g x ∈ vPerp Q v := by
  rw [mem_vPerp] at hx ⊢
  have hgv : g v = v := hg.2
  rw [← hgv, polar_map_of_mem hg.1, hx]

theorem map_vPerp {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) :
    (vPerp Q v).map (g : W →ₗ[ZMod 2] W) = vPerp Q v := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact apply_mem_vPerp hg hx
  · refine ⟨g⁻¹ x, apply_mem_vPerp (inv_mem hg) hx, ?_⟩
    exact LinearEquiv.apply_inv_apply' g x

@[expose] def perpEquiv {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) :
    vPerp Q v ≃ₗ[ZMod 2] vPerp Q v :=
  g.ofSubmodules _ _ (map_vPerp hg)

theorem coe_perpEquiv {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) (x : vPerp Q v) :
    (perpEquiv hg x : W) = g x :=
  rfl

theorem map_vLine {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) :
    (vLine Q v).map (perpEquiv hg : vPerp Q v →ₗ[ZMod 2] vPerp Q v) = vLine Q v := by
  rw [vLine, Submodule.map_span, Set.image_singleton]
  congr 2
  exact Subtype.ext hg.2

@[expose] def barEquiv {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) :
    BarW Q v ≃ₗ[ZMod 2] BarW Q v :=
  Submodule.Quotient.equiv _ _ (perpEquiv hg) (map_vLine hg)

theorem barEquiv_mk {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ stabO Q v) (x : vPerp Q v) :
    barEquiv hg (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEquiv hg x) :=
  rfl

variable (Q v) in
@[expose] def kappaGL : stabO Q v →* (BarW Q v ≃ₗ[ZMod 2] BarW Q v) where
  toFun g := barEquiv g.2
  map_one' := LinearEquiv.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun x => Submodule.Quotient.induction_on _ x fun _ => rfl

theorem kappaGL_mk (g : stabO Q v) (x : vPerp Q v) :
    kappaGL Q v g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (perpEquiv g.2 x) :=
  rfl

theorem kappaGL_mem (g : stabO Q v) :
    kappaGL Q v g ∈ TauCeti.BilinForm.isometryGroup (barB Q v) := by
  refine TauCeti.BilinForm.mem_isometryGroup_iff.2 fun x y => ?_
  induction x using Submodule.Quotient.induction_on
  induction y using Submodule.Quotient.induction_on
  rw [kappaGL_mk, kappaGL_mk, barB_mk, barB_mk, coe_perpEquiv, coe_perpEquiv,
    polar_map_of_mem g.2.1]

variable (Q v) in
@[expose] def kappa : stabO Q v →* TauCeti.BilinForm.isometryGroup (barB Q v) :=
  (kappaGL Q v).codRestrict _ kappaGL_mem

theorem coe_kappa_mk (g : stabO Q v) (x : vPerp Q v) :
    ((kappa Q v g : BarW Q v ≃ₗ[ZMod 2] BarW Q v) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk ⟨(g : W ≃ₗ[ZMod 2] W) x, apply_mem_vPerp g.2 x.2⟩ :=
  rfl

variable (Q v) in
@[expose] def kappaS : stabS Q v →* TauCeti.BilinForm.isometryGroup (barB Q v) :=
  (kappa Q v).comp (Subgroup.inclusion stabS_le_stabO)

theorem coe_kappaS_mk (g : stabS Q v) (x : vPerp Q v) :
    ((kappaS Q v g : BarW Q v ≃ₗ[ZMod 2] BarW Q v) (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk
        ⟨(g : W ≃ₗ[ZMod 2] W) x, apply_mem_vPerp (stabS_le_stabO g.2) x.2⟩ :=
  rfl

end Stabilizer

section Surjective

variable {Q : QuadraticForm (ZMod 2) W} {v : W}

@[expose] def reflectLift (Q : QuadraticForm (ZMod 2) W) (v a : W) : W :=
  a + (Q a + 1) • v

theorem map_reflectLift (hv : Q v = 1) {a : W} (ha : a ∈ vPerp Q v) :
    Q (reflectLift Q v a) = 1 := by
  rw [reflectLift, map_add_smul_of_polar_eq_zero hv (mem_vPerp.1 ha), ← add_assoc,
    CharTwo.add_self_eq_zero, zero_add]

theorem polar_reflectLift (a : W) {x : W} (hx : x ∈ vPerp Q v) :
    polar Q x (reflectLift Q v a) = polar Q x a := by
  rw [reflectLift, polar_add_right, polar_smul_right, polar_comm Q x v, mem_vPerp.1 hx, smul_zero,
    add_zero]

theorem reflect_reflectLift_mem_stabO (hv : Q v = 1) {a : W} (ha : a ∈ vPerp Q v) :
    reflect Q (reflectLift Q v a) ∈ stabO Q v := by
  refine ⟨reflect_mem_orthogonalGroup Q _, ?_⟩
  change reflect Q (reflectLift Q v a) v = v
  rw [reflect_apply_eq_add_of_map_eq_one (map_reflectLift hv ha), polar_reflectLift a
    (self_mem_vPerp Q v), mem_vPerp.1 ha, zero_smul, add_zero]

theorem kappaGL_reflect_lift (hv : Q v = 1) (a : vPerp Q v) (x : BarW Q v) :
    kappaGL Q v ⟨_, reflect_reflectLift_mem_stabO hv a.2⟩ x =
      x + barB Q v x (Submodule.Quotient.mk a) • Submodule.Quotient.mk a := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  rw [kappaGL_mk, barB_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.eq, mem_vLine]
  refine ⟨polar Q x a * (Q a + 1), ?_⟩
  rw [Submodule.coe_sub, coe_perpEquiv, Submodule.coe_add, Submodule.coe_smul,
    reflect_apply_eq_add_of_map_eq_one (map_reflectLift hv a.2), polar_reflectLift (a : W) x.2,
    reflectLift, smul_add, smul_smul]
  abel

theorem kappa_surjective [FiniteDimensional (ZMod 2) W] (hQ : (polarBilin Q).Nondegenerate)
    (hv : Q v = 1) : Function.Surjective (kappa Q v) := by
  intro e
  have hB : (barB Q v).IsAlt := barB_isAlt Q v
  have hBn : (barB Q v).Nondegenerate := barB_nondegenerate v hQ
  have hT : ∀ (a : BarW Q v) (c : ZMod 2),
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BarW Q v)
        (symplecticTransvection (barB Q v) hB a c) ∈ (kappaGL Q v).range := by
    intro a c
    rcases zmod_two_cases c with rfl | rfl
    · rw [symplecticTransvection_zero, map_one]
      exact one_mem _
    · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      refine ⟨⟨_, reflect_reflectLift_mem_stabO hv a.2⟩, LinearEquiv.ext fun x => ?_⟩
      rw [kappaGL_reflect_lift hv a x, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
        symplecticTransvection_apply, one_mul]
  have hcl : ∀ g ∈ Subgroup.closure {g | ∃ (a : BarW Q v) (c : ZMod 2),
      g = symplecticTransvection (barB Q v) hB a c},
      LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BarW Q v) g ∈
        (kappaGL Q v).range := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, c, rfl⟩ := hg
      exact hT a c
    | one => rw [map_one]; exact one_mem _
    | mul g h _ _ hg hh => rw [map_mul]; exact mul_mem hg hh
    | inv g _ hg => rw [map_inv]; exact inv_mem hg
  have hg : LinearMap.GeneralLinearGroup.ofLinearEquiv (e : BarW Q v ≃ₗ[ZMod 2] BarW Q v) ∈
      bilinIsometryGroup (barB Q v) := fun x y =>
    TauCeti.BilinForm.mem_isometryGroup_iff.1 e.2 x y
  rw [alternating_transvection_generation hB hBn] at hg
  obtain ⟨g, hg⟩ := hcl _ hg
  refine ⟨g, Subtype.ext (hg.trans (LinearEquiv.ext fun x => ?_))⟩
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  rfl

end Surjective

section Kernel

variable {Q : QuadraticForm (ZMod 2) W} {v : W}

theorem eq_one_or_eq_reflect [FiniteDimensional (ZMod 2) W] (hQ : (polarBilin Q).Nondegenerate)
    (hv : Q v = 1) (g : stabO Q v) (h1 : kappaGL Q v g = 1) :
    (g : W ≃ₗ[ZMod 2] W) = 1 ∨ (g : W ≃ₗ[ZMod 2] W) = reflect Q v := by
  obtain ⟨g, hgO, hgv⟩ := g
  change g v = v at hgv
  have hfix : ∀ x ∈ vPerp Q v, g x = x := by
    intro x hx
    have h := congrArg (· (Submodule.Quotient.mk (⟨x, hx⟩ : vPerp Q v) : BarW Q v)) h1
    simp only [kappaGL_mk, LinearEquiv.coe_one, id_eq] at h
    obtain ⟨c, hc⟩ := mem_vLine.1 ((Submodule.Quotient.eq _).1 h)
    rw [Submodule.coe_sub, coe_perpEquiv] at hc
    have hgx : g x = x + c • v := by rw [← hc, add_sub_cancel]
    have hQx := map_of_mem hgO x
    rw [hgx, map_add_smul_of_polar_eq_zero hv (mem_vPerp.1 hx), add_eq_left] at hQx
    rw [hgx, hQx, zero_smul, add_zero]
  have hv0 : v ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hv; exact zero_ne_one hv
  obtain ⟨w, hw⟩ := exists_polar_ne_zero hQ hv0
  have hw1 : polar Q v w = 1 := (zmod_two_cases _).resolve_left hw
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_polar_eq_zero v hQ (u := g w - w) fun x hx => by
    rw [polar_sub_left, ← hfix x hx, polar_map_of_mem hgO, hfix x hx, sub_self]
  have hgw : g w = w + c • v := by rw [← hc, add_sub_cancel]
  have hgy : ∀ y, g y = y + (c * polar Q v y) • v := by
    intro y
    have hy : y - polar Q v y • w ∈ vPerp Q v := by
      rw [mem_vPerp, polar_sub_right, polar_smul_right, hw1, smul_eq_mul, mul_one, sub_self]
    have := hfix _ hy
    rw [map_sub, map_smul, hgw, sub_eq_iff_eq_add] at this
    rw [this, mul_comm, ← smul_smul]
    module
  rcases zmod_two_cases c with rfl | rfl
  · left
    exact LinearEquiv.ext fun y => by rw [hgy, zero_mul, zero_smul, add_zero]; rfl
  · right
    exact LinearEquiv.ext fun y => by
      rw [hgy, one_mul, reflect_apply_eq_add_of_map_eq_one hv, polar_comm]

end Kernel

theorem reflect_not_mem_commutator [FiniteDimensional (ZMod 2) W]
    {Q : QuadraticForm (ZMod 2) W} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) W, finrank (ZMod 2) T = 3 ∧ ∀ x ∈ T, Q x = 0) {v : W}
    (hv : Q v ≠ 0) :
    reflect Q v ∉
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨χ, -, hχ, -⟩ := OrthogonalTail.orthogonal_geometry_char_two_reflection_separation hQ hT
  intro hmem
  rw [← Subgroup.map_subtype_commutator] at hmem
  obtain ⟨h, hh, hhv⟩ := hmem
  have h1 : χ h = 1 := Abelianization.commutator_subset_ker χ hh
  have h2 : h = ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ := Subtype.ext hhv
  rw [h2, hχ v hv] at h1
  exact absurd h1 (by decide)

section Symplectic

open CFSG.Assembly.LowTwoRank

@[expose] def statedSpEquivProj (r : ℕ) :
    StatedSp r (ZMod 2) ≃* StatedProj (StatedSp r (ZMod 2)) := by
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hscal : (StatedScalars (Fin r ⊕ Fin r) (ZMod 2)).subgroupOf (StatedSp r (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  exact ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm

theorem lieModel_of_mulEquiv_statedSp {G : Type} [Group G] {r : ℕ} (hr : 3 ≤ r)
    (e : G ≃* StatedSp r (ZMod 2)) : CFSG.Blueprint.LieModel G .PSp r 2 1 := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_⟩,
    ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (statedSpEquivProj r)⟩⟩
  have := congrArg Prod.fst h
  simp only at this
  omega

variable {B : BilinForm (ZMod 2) W}

theorem nonempty_isometryGroup_mulEquiv_statedSp [FiniteDimensional (ZMod 2) W]
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {r : ℕ} (hr : finrank (ZMod 2) W = 2 * r) :
    Nonempty (TauCeti.BilinForm.isometryGroup B ≃* StatedSp r (ZMod 2)) := by
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hBn
  obtain rfl : m = r := by omega
  exact ⟨(CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b B
    hb).trans
      (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)⟩

end Symplectic

theorem binary_nonsingular_vector_stabilizer_symplectic_model {r : ℕ} (hr : 3 ≤ r) {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (hW : finrank (ZMod 2) W = 2 * r + 2) {Q : QuadraticForm (ZMod 2) W}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) W, finrank (ZMod 2) T = 3 ∧ ∀ x ∈ T, Q x = 0) {v : W}
    (hv : Q v = 1) :
    (barB Q v).Nondegenerate ∧ (barB Q v).IsAlt ∧ finrank (ZMod 2) (BarW Q v) = 2 * r ∧
      Function.Bijective (kappaS Q v) ∧ Group.IsPerfect (stabS Q v) ∧
      CFSG.Blueprint.LieModel (stabS Q v) .PSp r 2 1 := by
  have hv0 : v ≠ 0 := fun h => by rw [h, QuadraticMap.map_zero] at hv; exact zero_ne_one hv
  have hBn := barB_nondegenerate v hQ
  have hB := barB_isAlt Q v
  have hdim : finrank (ZMod 2) (BarW Q v) = 2 * r := by
    have := finrank_barW_add_two hQ hv0
    omega
  set Sp := TauCeti.BilinForm.isometryGroup (barB Q v)
  obtain ⟨eSp⟩ := nonempty_isometryGroup_mulEquiv_statedSp hB hBn hdim
  have hSpPerf : Group.IsPerfect Sp := by
    have := symplectic_small_field_perfect r (ZMod 2) (Or.inr ⟨Nat.card_zmod 2, hr⟩)
    exact Group.IsPerfect.ofSurjective (f := eSp.symm.toMonoidHom) eSp.symm.surjective
  have hinj : Function.Injective (kappaS Q v) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : kappaGL Q v (Subgroup.inclusion stabS_le_stabO g) = 1 :=
      congrArg Subtype.val hg
    rcases eq_one_or_eq_reflect hQ hv _ h1 with h | h
    · exact Subtype.ext h
    · exact absurd (h ▸ g.2.1 : reflect Q v ∈ _)
        (reflect_not_mem_commutator hQ hT (by rw [hv]; exact one_ne_zero))
  have hsurj : Function.Surjective (kappaS Q v) := by
    intro s
    have hmap : (commutator (stabO Q v)).map (kappa Q v) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (kappa_surjective hQ hv), ← commutator_def,
        Group.IsPerfect.commutator_eq_top]
    obtain ⟨y, hy, hys⟩ := (hmap ▸ Subgroup.mem_top s : s ∈ (commutator (stabO Q v)).map _)
    have hyX : (y : W ≃ₗ[ZMod 2] W) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      have : (y : W ≃ₗ[ZMod 2] W) ∈ ⁅stabO Q v, stabO Q v⁆ := by
        rw [← Subgroup.map_subtype_commutator]
        exact ⟨y, hy, rfl⟩
      exact Subgroup.commutator_mono inf_le_left inf_le_left this
    exact ⟨⟨y, hyX, y.2.2⟩, hys⟩
  have hbij : Function.Bijective (kappaS Q v) := ⟨hinj, hsurj⟩
  set eS : stabS Q v ≃* Sp := MulEquiv.ofBijective (kappaS Q v) hbij
  refine ⟨hBn, hB, hdim, hbij, ?_, lieModel_of_mulEquiv_statedSp hr (eS.trans eSp)⟩
  exact Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective

end CFSG.LocalAnalysis.ComponentInitial.BinaryStabilizer
