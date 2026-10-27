module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixBasisTransport
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Module Submodule SymplecticFlag
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}

theorem bilin_symm (hb : b.IsAlt) (x y : V) : b x y = b y x := by
  rw [← hb.neg_eq, ZMod.neg_eq_self_mod_two]

variable (b) in
@[expose] def pointMap (u w : V) (c : ZMod 2) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (b.flip w).smulRight u + (b u).smulRight (w + c • u)

theorem pointMap_apply (u w : V) (c : ZMod 2) (v : V) :
    pointMap b u w c v = v + b v w • u + b u v • (w + c • u) := by
  simp [pointMap]

theorem zmod_two_pointMap_identity : ∀ bxy ax ay bx by' c : ZMod 2,
    bxy + ax * by' + bx * (ay + c * by') + ay * bx + by' * (ax + c * bx) = bxy := by
  decide

theorem pointMap_isometry (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) (x y : V) :
    b (pointMap b u w c x) (pointMap b u w c y) = b x y := by
  have huu : b u u = 0 := hb.self_eq_zero u
  have hww : b w w = 0 := hb.self_eq_zero w
  have hwu : b w u = 0 := by rw [bilin_symm hb, hw]
  simp only [pointMap_apply, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, huu, hww, hw, hwu,
    mul_zero, add_zero]
  rw [bilin_symm hb x u, bilin_symm hb w y]
  exact zmod_two_pointMap_identity _ _ _ _ _ _

theorem pointMap_comp (hb : b.IsAlt) {u w w' : V} (hw : b u w = 0) (hw' : b u w' = 0)
    (c c' : ZMod 2) :
    (pointMap b u w c).comp (pointMap b u w' c') =
      pointMap b u (w + w') (c + c' + b w w') := by
  have huu : b u u = 0 := hb.self_eq_zero u
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, pointMap_apply, LinearMap.BilinForm.add_left,
    LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    huu, hw, hw', mul_zero, add_zero]
  rw [bilin_symm hb w' w]
  module

theorem pointMap_zero_zero (u : V) : pointMap b u 0 0 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  simp [pointMap_apply]

theorem pointMap_comp_self (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) :
    (pointMap b u w c).comp (pointMap b u w c) = LinearMap.id := by
  rw [pointMap_comp hb hw hw, add_self_eq_zero_zmod_two w, hb.self_eq_zero w, add_zero,
    zmod_two_add_self_eq_zero c, pointMap_zero_zero]

theorem pointMap_add_smul (hb : b.IsAlt) (u x : V) (d c : ZMod 2) :
    pointMap b u (x + d • u) c = pointMap b u x c := by
  refine LinearMap.ext fun v => ?_
  simp only [pointMap_apply, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right]
  rw [bilin_symm hb v u]
  have key : (d * b u v) • u + b u v • (d • u) = 0 := by
    rw [smul_smul, ← add_smul, mul_comm (b u v) d, zmod_two_add_self_eq_zero, zero_smul]
  calc _ = v + b v x • u + b u v • (x + c • u) + ((d * b u v) • u + b u v • (d • u)) := by
        module
    _ = v + b v x • u + b u v • (x + c • u) := by rw [key, add_zero]

variable (b) in
abbrev pairOrth (u f : V) : Submodule (ZMod 2) V := b.orthogonal (span (ZMod 2) {u, f})

theorem mem_pairOrth {u f x : V} : x ∈ pairOrth b u f ↔ b u x = 0 ∧ b f x = 0 :=
  LinearMap.BilinForm.mem_orthogonal_span_pair_iff b

@[expose] def pointElt (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) :
    bilinIsometryGroup b :=
  ⟨⟨pointMap b u w c, pointMap b u w c, pointMap_comp_self hb hw c,
    pointMap_comp_self hb hw c⟩, pointMap_isometry hb hw c⟩

theorem coe_pointElt (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) :
    (((pointElt hb hw c : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) = pointMap b u w c :=
  rfl

theorem pointElt_ext (hb : b.IsAlt) {u w w' : V} (hw : b u w = 0) (hw' : b u w' = 0)
    {c c' : ZMod 2} (h : pointMap b u w c = pointMap b u w' c') :
    pointElt hb hw c = pointElt hb hw' c' :=
  Subtype.ext (Units.ext h)

theorem pointElt_mul (hb : b.IsAlt) {u w w' : V} (hw : b u w = 0) (hw' : b u w' = 0)
    (c c' : ZMod 2) :
    pointElt hb hw c * pointElt hb hw' c' =
      pointElt hb (by rw [map_add, hw, hw', add_zero] : b u (w + w') = 0) (c + c' + b w w') :=
  Subtype.ext (Units.ext (pointMap_comp hb hw hw' c c'))

theorem pointElt_mul_self (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) :
    pointElt hb hw c * pointElt hb hw c = 1 :=
  Subtype.ext (Units.ext (pointMap_comp_self hb hw c))

theorem pointElt_zero_zero (hb : b.IsAlt) {u : V} (h0 : b u 0 = 0) :
    pointElt hb h0 0 = 1 :=
  Subtype.ext (Units.ext (pointMap_zero_zero u))

theorem pointMap_apply_self (hb : b.IsAlt) {u w : V} (hw : b u w = 0) (c : ZMod 2) :
    pointMap b u w c u = u := by
  rw [pointMap_apply, hw, hb.self_eq_zero, zero_smul, zero_smul, add_zero, add_zero]

theorem conj_pointMap {u : V} {g : bilinIsometryGroup b}
    (hgu : ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u = u) (w : V)
    (c : ZMod 2) :
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) ∘ₗ pointMap b u w c ∘ₗ
        (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) =
      pointMap b u (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) c := by
  refine LinearMap.ext fun v => ?_
  have h1 : b ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v) w =
      b v (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w) := by
    rw [← g.2, apply_inv_apply]
  have h2 : b u ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v) = b u v := by
    rw [← g.2, hgu, apply_inv_apply]
  simp only [LinearMap.comp_apply, pointMap_apply, map_add, map_smul, hgu, apply_inv_apply, h1,
    h2]

variable (b) in
@[expose] def vecStabilizer (v : V) : Subgroup (bilinIsometryGroup b) where
  carrier := {g | ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      (((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = v
    rw [hh, hg]
  inv_mem' {g} hg := by
    change (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) v = v
    conv_lhs => rw [← hg]
    exact inv_apply_apply g v

theorem mem_vecStabilizer {v : V} {g : bilinIsometryGroup b} :
    g ∈ vecStabilizer b v ↔
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v :=
  Iff.rfl

variable (b) in
@[expose] def pairStabilizer (u f : V) : Subgroup (bilinIsometryGroup b) :=
  vecStabilizer b u ⊓ vecStabilizer b f

theorem mem_pairStabilizer {u f : V} {g : bilinIsometryGroup b} :
    g ∈ pairStabilizer b u f ↔
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u = u ∧
        ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f = f :=
  Iff.rfl

@[expose] def bilinIsometryEquivTauCeti {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (B : BilinForm (ZMod 2) M) :
    bilinIsometryGroup B ≃ TauCeti.BilinForm.isometryGroup B where
  toFun g := ⟨LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M g,
    TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => g.2 x y⟩
  invFun h := ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).symm h,
    fun x y => TauCeti.BilinForm.mem_isometryGroup_iff.mp h.2 x y⟩
  left_inv _ := Subtype.ext (MulEquiv.symm_apply_apply _ _)
  right_inv _ := Subtype.ext (MulEquiv.apply_symm_apply _ _)

theorem zmod_two_eq_zero_or_eq_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

theorem zmod_two_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
  decide

theorem apply_mem_pairOrth {u f : V} {g : bilinIsometryGroup b}
    (hgu : ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u = u)
    (hgf : ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f = f) {z : V}
    (hz : z ∈ pairOrth b u f) :
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) z ∈ pairOrth b u f := by
  obtain ⟨h1, h2⟩ := mem_pairOrth.1 hz
  refine mem_pairOrth.2 ⟨?_, ?_⟩
  · rw [← g.2 u z, hgu] at h1
    exact h1
  · rw [← g.2 f z, hgf] at h2
    exact h2

variable (b) in
@[expose] def pairRestrict (u f : V) :
    pairStabilizer b u f →* bilinIsometryGroup (b.restrict (pairOrth b u f)) where
  toFun k :=
    ⟨{ val := (((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V).restrict fun _ hz =>
            apply_mem_pairOrth (mem_pairStabilizer.1 k.2).1 (mem_pairStabilizer.1 k.2).2 hz
       inv := ((((k⁻¹ : pairStabilizer b u f) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V).restrict fun _ hz =>
            apply_mem_pairOrth (mem_pairStabilizer.1 (k⁻¹).2).1
              (mem_pairStabilizer.1 (k⁻¹).2).2 hz
       val_inv := LinearMap.ext fun z =>
        Subtype.ext (apply_inv_apply (k : bilinIsometryGroup b) (z : V))
       inv_val := LinearMap.ext fun z =>
        Subtype.ext (inv_apply_apply (k : bilinIsometryGroup b) (z : V)) },
      fun x y => (k : bilinIsometryGroup b).2 x y⟩
  map_one' := Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))
  map_mul' _ _ := Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))

theorem pairRestrict_apply {u f : V} (k : pairStabilizer b u f) (z : pairOrth b u f) :
    ((((pairRestrict b u f k : bilinIsometryGroup (b.restrict (pairOrth b u f))) :
      LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) : pairOrth b u f →ₗ[ZMod 2]
        pairOrth b u f) z : V) =
      (((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) z :=
  rfl

section Pair

variable (hb : b.IsAlt) {u f : V}
include hb

theorem pairOrth_part_mem (huf : b f u = 1) (v : V) :
    v + b f v • u + b u v • f ∈ pairOrth b u f := by
  have hfu : b u f = 1 := by rw [bilin_symm hb, huf]
  refine mem_pairOrth.2 ⟨?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul, hb.self_eq_zero, hfu, mul_zero, mul_one]
    rw [add_zero, zmod_two_add_self_eq_zero]
  · simp only [map_add, map_smul, smul_eq_mul, hb.self_eq_zero, huf, mul_zero, mul_one, add_zero]
    exact zmod_two_add_self_eq_zero _

omit hb in
theorem eq_pairOrth_part_add (v : V) (s t : ZMod 2) :
    v = (v + s • u + t • f) + (s • u + t • f) := by
  have h1 := add_self_eq_zero_zmod_two (s • u)
  have h2 := add_self_eq_zero_zmod_two (t • f)
  calc v = v + (s • u + s • u) + (t • f + t • f) := by rw [h1, h2, add_zero, add_zero]
    _ = (v + s • u + t • f) + (s • u + t • f) := by abel

theorem pointMap_apply_right (huf : b f u = 1) {w : V} (hw : w ∈ pairOrth b u f) (c : ZMod 2) :
    pointMap b u w c f = f + (w + c • u) := by
  rw [pointMap_apply, (mem_pairOrth.1 hw).2, zero_smul, add_zero, bilin_symm hb u f, huf,
    one_smul]

theorem pointMap_inj (huf : b f u = 1) {w w' : V} (hw : w ∈ pairOrth b u f)
    (hw' : w' ∈ pairOrth b u f) {c c' : ZMod 2} (h : pointMap b u w c = pointMap b u w' c') :
    w = w' ∧ c = c' := by
  have h1 := LinearMap.congr_fun h f
  rw [pointMap_apply_right hb huf hw, pointMap_apply_right hb huf hw', add_right_inj] at h1
  have h2 := congrArg (b f) h1
  simp only [map_add, map_smul, (mem_pairOrth.1 hw).2, (mem_pairOrth.1 hw').2, huf, smul_eq_mul,
    mul_one, zero_add] at h2
  subst h2
  exact ⟨add_right_cancel h1, rfl⟩

omit hb in
theorem mem_pairOrth_left {w : V} (hw : w ∈ pairOrth b u f) : b u w = 0 :=
  (mem_pairOrth.1 hw).1

variable (b) in
@[expose] def pointRadical (u f : V) : Subgroup (bilinIsometryGroup b) where
  carrier := Set.range fun p : pairOrth b u f × ZMod 2 =>
    pointElt hb (mem_pairOrth_left p.1.2) p.2
  one_mem' := ⟨(0, 0), pointElt_zero_zero hb _⟩
  mul_mem' := by
    rintro _ _ ⟨⟨w, c⟩, rfl⟩ ⟨⟨w', c'⟩, rfl⟩
    exact ⟨(w + w', c + c' + b w w'), (pointElt_mul hb _ _ c c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨w, c⟩, rfl⟩
    exact ⟨(w, c), (inv_eq_of_mul_eq_one_right (pointElt_mul_self hb _ c)).symm⟩

theorem pointElt_mem_pointRadical {w : V} (hw : w ∈ pairOrth b u f) (c : ZMod 2) :
    pointElt hb (mem_pairOrth_left hw) c ∈ pointRadical b hb u f :=
  ⟨(⟨w, hw⟩, c), rfl⟩

theorem mem_pointRadical {g : bilinIsometryGroup b} :
    g ∈ pointRadical b hb u f ↔
      ∃ (w : V) (hw : w ∈ pairOrth b u f) (c : ZMod 2),
        g = pointElt hb (mem_pairOrth_left hw) c := by
  constructor
  · rintro ⟨⟨w, c⟩, rfl⟩
    exact ⟨w, w.2, c, rfl⟩
  · rintro ⟨w, hw, c, rfl⟩
    exact pointElt_mem_pointRadical hb hw c

theorem pointRadical_comm {g h : bilinIsometryGroup b} (hg : g ∈ pointRadical b hb u f)
    (hh : h ∈ pointRadical b hb u f) : g * h = h * g := by
  obtain ⟨⟨w, c⟩, rfl⟩ := hg
  obtain ⟨⟨w', c'⟩, rfl⟩ := hh
  rw [pointElt_mul, pointElt_mul]
  apply pointElt_ext
  rw [add_comm (w : V), add_comm c c', bilin_symm hb (w : V)]

theorem pointRadical_mul_self {g : bilinIsometryGroup b} (hg : g ∈ pointRadical b hb u f) :
    g * g = 1 := by
  obtain ⟨⟨w, c⟩, rfl⟩ := hg
  exact pointElt_mul_self hb _ c

theorem isElementaryAbelian_pointRadical : IsElementaryAbelian 2 (pointRadical b hb u f) :=
  { toIsMulCommutative := ⟨⟨fun g h => Subtype.ext (pointRadical_comm hb g.2 h.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, sq, pointRadical_mul_self hb g.2, Subgroup.coe_one]) }

theorem card_pointRadical (huf : b f u = 1) :
    Nat.card (pointRadical b hb u f) = Nat.card (pairOrth b u f) * 2 := by
  have hinj : Function.Injective fun p : pairOrth b u f × ZMod 2 =>
      pointElt hb (mem_pairOrth_left p.1.2) p.2 := by
    rintro ⟨w, c⟩ ⟨w', c'⟩ h
    obtain ⟨h1, h2⟩ := pointMap_inj hb huf w.2 w'.2 (congrArg (fun g : bilinIsometryGroup b =>
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) h)
    exact Prod.ext (Subtype.ext h1) h2
  have h := Nat.card_range_of_injective hinj
  rw [Nat.card_prod, Nat.card_zmod] at h
  exact h

theorem finrank_range_sub_one_le {g : bilinIsometryGroup b} (hg : g ∈ pointRadical b hb u f) :
    finrank (ZMod 2) (LinearMap.range (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) - 1)) ≤ 2 := by
  classical
  obtain ⟨⟨w, c⟩, rfl⟩ := hg
  have hle : LinearMap.range (pointMap b u w c - 1) ≤
      span (ZMod 2) (({u, (w : V) + c • u} : Finset V) : Set V) := by
    rintro _ ⟨v, rfl⟩
    rw [Finset.coe_pair]
    refine Submodule.mem_span_pair.2 ⟨b v w, b u v, ?_⟩
    rw [LinearMap.sub_apply, pointMap_apply, Module.End.one_apply]
    abel
  exact (Submodule.finrank_mono hle).trans ((finrank_span_finset_le_card _).trans
    Finset.card_le_two)

theorem pointRadical_le_vecStabilizer : pointRadical b hb u f ≤ vecStabilizer b u := by
  rintro _ ⟨⟨w, c⟩, rfl⟩
  exact pointMap_apply_self hb (mem_pairOrth_left w.2) c

theorem exists_mem_pointRadical_mul_mem_pairStabilizer (huf : b f u = 1)
    {g : bilinIsometryGroup b} (hg : g ∈ vecStabilizer b u) :
    ∃ a ∈ pointRadical b hb u f, a * g ∈ pairStabilizer b u f := by
  set d := ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f + f with hd
  have hgf : b u (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f) =
      b u f := by
    conv_lhs => rw [← mem_vecStabilizer.1 hg]
    exact g.2 u f
  have hud : b u d = 0 := by
    rw [hd, map_add, hgf, zmod_two_add_self_eq_zero]
  have hw : d + b f d • u ∈ pairOrth b u f := by
    refine mem_pairOrth.2 ⟨?_, ?_⟩
    · rw [map_add, map_smul, hud, hb.self_eq_zero, smul_zero, add_zero]
    · rw [map_add, map_smul, huf, smul_eq_mul, mul_one, zmod_two_add_self_eq_zero]
  refine ⟨pointElt hb (mem_pairOrth_left hw) (b f d), pointElt_mem_pointRadical hb hw _, ?_, ?_⟩
  · change pointMap b u (d + b f d • u) (b f d)
      (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u) = u
    rw [mem_vecStabilizer.1 hg, pointMap_apply_self hb (mem_pairOrth_left hw)]
  · change pointMap b u (d + b f d • u) (b f d)
      (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f) = f
    have hnf : pointMap b u (d + b f d • u) (b f d) f =
        ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) f := by
      rw [pointMap_apply_right hb huf hw, add_assoc d, add_self_eq_zero_zmod_two, add_zero, hd,
        add_comm _ f, ← add_assoc, add_self_eq_zero_zmod_two, zero_add]
    rw [← hnf]
    exact LinearMap.congr_fun (pointMap_comp_self hb (mem_pairOrth_left hw) _) f

theorem pointRadical_inf_pairStabilizer (huf : b f u = 1) :
    pointRadical b hb u f ⊓ pairStabilizer b u f = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨w, c⟩, rfl⟩, -, hgf⟩
  have h1 : pointMap b u w c f = f := hgf
  rw [pointMap_apply_right hb huf w.2, add_eq_left] at h1
  have h3 := congrArg (b f) h1
  simp only [map_add, map_smul, (mem_pairOrth.1 w.2).2, huf, smul_eq_mul, mul_one, zero_add,
    map_zero] at h3
  subst h3
  rw [zero_smul, add_zero] at h1
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Units.ext ?_)
  change pointMap b u w 0 = LinearMap.id
  rw [h1, pointMap_zero_zero]

theorem conj_mem_pointRadical (huf : b f u = 1) {g : bilinIsometryGroup b}
    (hg : g ∈ vecStabilizer b u) {a : bilinIsometryGroup b} (ha : a ∈ pointRadical b hb u f) :
    g * a * g⁻¹ ∈ pointRadical b hb u f := by
  obtain ⟨⟨w, c⟩, rfl⟩ := ha
  set x := ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w with hx
  have hux : b u x = 0 := by
    have h := g.2 u w
    rw [mem_vecStabilizer.1 hg] at h
    rw [hx, h]
    exact mem_pairOrth_left w.2
  have hx' : x + b f x • u ∈ pairOrth b u f := by
    refine mem_pairOrth.2 ⟨?_, ?_⟩
    · rw [map_add, map_smul, hux, hb.self_eq_zero, smul_zero, add_zero]
    · rw [map_add, map_smul, huf, smul_eq_mul, mul_one, zmod_two_add_self_eq_zero]
  refine ⟨(⟨x + b f x • u, hx'⟩, c), Subtype.ext (Units.ext ?_)⟩
  change pointMap b u (x + b f x • u) c =
    ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) ∘ₗ pointMap b u w c ∘ₗ
      (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)
  rw [conj_pointMap (mem_vecStabilizer.1 hg), pointMap_add_smul hb]

theorem mem_span_of_forall_pointMap (hnd : b.Nondegenerate) (huf : b f u = 1) {v : V}
    (hv : ∀ w ∈ pairOrth b u f, ∀ c : ZMod 2, pointMap b u w c v = v) :
    v ∈ span (ZMod 2) {u} := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [map_zero] at huf
    exact absurd huf (by decide)
  have hsmul : ∀ a : ZMod 2, a • u = 0 → a = 0 := by
    intro a ha
    rcases zmod_two_eq_zero_or_eq_one a with h0 | h1
    · exact h0
    · rw [h1, one_smul] at ha
      exact absurd ha hu0
  have huv : b u v = 0 := by
    have h := hv 0 (zero_mem _) 1
    rw [pointMap_apply, map_zero, zero_smul, add_zero, zero_add, one_smul, add_eq_left] at h
    exact hsmul _ h
  have hvw : ∀ w ∈ pairOrth b u f, b v w = 0 := by
    intro w hw
    have h := hv w hw 0
    rw [pointMap_apply, huv, zero_smul, add_zero, add_eq_left] at h
    exact hsmul _ h
  have hz : v + b f v • u ∈ pairOrth b u f := by
    refine mem_pairOrth.2 ⟨?_, ?_⟩
    · rw [map_add, map_smul, huv, hb.self_eq_zero, smul_zero, add_zero]
    · rw [map_add, map_smul, huf, smul_eq_mul, mul_one, zmod_two_add_self_eq_zero]
  have hnd' := hb.restrict_nondegenerate_orthogonal_span_pair huf hnd
  have hz0 : v + b f v • u = 0 := by
    have h := hnd'.1 ⟨v + b f v • u, hz⟩ fun y => by
      change b (v + b f v • u) y = 0
      rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hvw y y.2,
        mem_pairOrth_left y.2, mul_zero, add_zero]
    exact congrArg Subtype.val h
  have hveq : v = b f v • u := by
    calc v = v + (b f v • u + b f v • u) := by rw [add_self_eq_zero_zmod_two, add_zero]
      _ = (v + b f v • u) + b f v • u := by rw [add_assoc]
      _ = b f v • u := by rw [hz0, zero_add]
  rw [hveq]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

theorem normalizer_pointRadical (hnd : b.Nondegenerate) (huf : b f u = 1) :
    Subgroup.normalizer (pointRadical b hb u f : Set (bilinIsometryGroup b)) =
      vecStabilizer b u := by
  apply le_antisymm
  · intro g hg
    have hfix : ∀ w ∈ pairOrth b u f, ∀ c : ZMod 2,
        pointMap b u w c (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u) =
          ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u := by
      intro w hw c
      have hmem : g⁻¹ * pointElt hb (mem_pairOrth_left hw) c * g ∈ pointRadical b hb u f := by
        have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1
          (pointElt_mem_pointRadical hb hw c)
        rwa [inv_inv] at h
      have hfu := mem_vecStabilizer.1 (pointRadical_le_vecStabilizer hb hmem)
      calc pointMap b u w c (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)
          = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
            ((((g⁻¹ * pointElt hb (mem_pairOrth_left hw) c * g : bilinIsometryGroup b) :
              LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u) := by
            change _ = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
              ((((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
                V →ₗ[ZMod 2] V) (pointMap b u w c
                  (((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)))
            rw [apply_inv_apply]
        _ = ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u := by rw [hfu]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (mem_span_of_forall_pointMap hb hnd huf hfix)
    rcases zmod_two_eq_zero_or_eq_one t with h0 | h1
    · rw [h0, zero_smul] at ht
      have h := congrArg (((g⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) ht
      rw [map_zero, inv_apply_apply] at h
      rw [← h, map_zero] at huf
      exact absurd huf (by decide)
    · rw [h1, one_smul] at ht
      exact ht.symm
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨conj_mem_pointRadical hb huf hg, fun h => ?_⟩
    have h' := conj_mem_pointRadical hb huf (inv_mem hg) h
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at h'

theorem eq_one_of_forall_pairOrth (huf : b f u = 1) {k : bilinIsometryGroup b}
    (hk : k ∈ pairStabilizer b u f)
    (hE : ∀ w ∈ pairOrth b u f,
      ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w) : k = 1 := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  change ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
  have hv := eq_pairOrth_part_add (u := u) (f := f) v (b f v) (b u v)
  calc ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v
      = ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
          ((v + b f v • u + b u v • f) + (b f v • u + b u v • f)) := by rw [← hv]
    _ = (v + b f v • u + b u v • f) + (b f v • u + b u v • f) := by
        rw [map_add, hE _ (pairOrth_part_mem hb huf v), map_add, map_smul, map_smul,
          (mem_pairStabilizer.1 hk).1, (mem_pairStabilizer.1 hk).2]
    _ = v := hv.symm

theorem conj_pointElt_of_mem_pairStabilizer {k : bilinIsometryGroup b}
    (hk : k ∈ pairStabilizer b u f) {w : V} (hw : w ∈ pairOrth b u f) (c : ZMod 2) :
    k * pointElt hb (mem_pairOrth_left hw) c * k⁻¹ =
      pointElt hb (mem_pairOrth_left (apply_mem_pairOrth (mem_pairStabilizer.1 hk).1
        (mem_pairStabilizer.1 hk).2 hw)) c :=
  Subtype.ext (Units.ext (conj_pointMap (mem_pairStabilizer.1 hk).1 w c))

theorem centralizer_pointRadical (hnd : b.Nondegenerate) (huf : b f u = 1) :
    Subgroup.centralizer (pointRadical b hb u f : Set (bilinIsometryGroup b)) =
      pointRadical b hb u f := by
  have hA : pointRadical b hb u f ≤
      Subgroup.centralizer (pointRadical b hb u f : Set (bilinIsometryGroup b)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact pointRadical_comm hb hh hg
  refine le_antisymm (fun g hg => ?_) hA
  have hgN : g ∈ vecStabilizer b u := by
    rw [← normalizer_pointRadical hb hnd huf]
    exact Subgroup.centralizer_le_normalizer _ hg
  obtain ⟨a, ha, hk⟩ := exists_mem_pointRadical_mul_mem_pairStabilizer hb huf hgN
  have hkc := mul_mem (hA ha) hg
  have hkE : ∀ w ∈ pairOrth b u f,
      (((a * g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) w = w := by
    intro w hw
    have hcomm := Subgroup.mem_centralizer_iff.1 hkc _ (pointElt_mem_pointRadical hb hw 0)
    have h1 : (a * g) * pointElt hb (mem_pairOrth_left hw) 0 * (a * g)⁻¹ =
        pointElt hb (mem_pairOrth_left hw) 0 := by
      rw [← hcomm, mul_inv_cancel_right]
    rw [conj_pointElt_of_mem_pairStabilizer hb hk hw] at h1
    exact (pointMap_inj hb huf (apply_mem_pairOrth (mem_pairStabilizer.1 hk).1
      (mem_pairStabilizer.1 hk).2 hw) hw (congrArg (fun x : bilinIsometryGroup b =>
        ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) h1)).1
  have h1 := eq_one_of_forall_pairOrth hb huf hk hkE
  rw [eq_inv_of_mul_eq_one_right h1]
  exact inv_mem ha

theorem pointRadical_sup_pairStabilizer (huf : b f u = 1) :
    pointRadical b hb u f ⊔ pairStabilizer b u f = vecStabilizer b u := by
  apply le_antisymm
  · exact sup_le (pointRadical_le_vecStabilizer hb) inf_le_left
  · intro g hg
    obtain ⟨a, ha, hk⟩ := exists_mem_pointRadical_mul_mem_pairStabilizer hb huf hg
    have h : g = a * (a * g) := by rw [← mul_assoc, pointRadical_mul_self hb ha, one_mul]
    rw [h]
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hk)

theorem pairRestrict_injective (huf : b f u = 1) : Function.Injective (pairRestrict b u f) := by
  intro k k' h
  have hE : ∀ w ∈ pairOrth b u f,
      ((((k'⁻¹ * k : pairStabilizer b u f) : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w := by
    intro w hw
    have h1 := congrArg (fun x : bilinIsometryGroup (b.restrict (pairOrth b u f)) =>
      (((x : LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
        pairOrth b u f →ₗ[ZMod 2] pairOrth b u f) ⟨w, hw⟩ : V)) h
    change (((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) w = (((k' : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) w at h1
    change ((((k' : bilinIsometryGroup b)⁻¹ : bilinIsometryGroup b) :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
        ((((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) w) = w
    rw [h1, inv_apply_apply]
  have h1 := eq_one_of_forall_pairOrth hb huf (k'⁻¹ * k).2 hE
  have h2 : k'⁻¹ * k = 1 := Subtype.ext h1
  rw [inv_mul_eq_one] at h2
  exact h2.symm

theorem pairRestrict_surjective (huf : b f u = 1) : Function.Surjective (pairRestrict b u f) := by
  intro S
  set h := ((S : LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
    pairOrth b u f →ₗ[ZMod 2] pairOrth b u f) with hh
  set h' := (((S⁻¹ : bilinIsometryGroup (b.restrict (pairOrth b u f))) :
    LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
      pairOrth b u f →ₗ[ZMod 2] pairOrth b u f) with hh'
  have hhh' : h ∘ₗ h' = LinearMap.id := by
    change ((((S * S⁻¹ : bilinIsometryGroup (b.restrict (pairOrth b u f))) :
      LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
        pairOrth b u f →ₗ[ZMod 2] pairOrth b u f)) = LinearMap.id
    rw [mul_inv_cancel]
    rfl
  have hh'h : h' ∘ₗ h = LinearMap.id := by
    change ((((S⁻¹ * S : bilinIsometryGroup (b.restrict (pairOrth b u f))) :
      LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
        pairOrth b u f →ₗ[ZMod 2] pairOrth b u f)) = LinearMap.id
    rw [inv_mul_cancel]
    rfl
  have hiso : ∀ x y : pairOrth b u f, b (h x) (h y) = b x y := fun x y => S.2 x y
  let k : bilinIsometryGroup b :=
    ⟨⟨pairExt hb huf h, pairExt hb huf h', by
        rw [Module.End.mul_eq_comp, pairExt_comp, hhh', pairExt_id]; rfl, by
        rw [Module.End.mul_eq_comp, pairExt_comp, hh'h, pairExt_id]; rfl⟩,
      fun x y => pairExt_isometry hb huf hiso x y⟩
  have hk : k ∈ pairStabilizer b u f := by
    refine mem_pairStabilizer.2 ⟨?_, ?_⟩
    · change pairExt hb huf h u = u
      rw [pairExt_apply, pairProj_left hb huf, map_zero, ZeroMemClass.coe_zero, sub_zero,
        add_zero]
    · change pairExt hb huf h f = f
      rw [pairExt_apply, pairProj_right hb huf, map_zero, ZeroMemClass.coe_zero, sub_zero,
        add_zero]
  exact ⟨⟨k, hk⟩, Subtype.ext (Units.ext (LinearMap.ext fun z =>
    Subtype.ext (pairExt_coe hb huf h z)))⟩

theorem pairRestrict_bijective (huf : b f u = 1) : Function.Bijective (pairRestrict b u f) :=
  ⟨pairRestrict_injective hb huf, pairRestrict_surjective hb huf⟩

theorem finrank_pairOrth [FiniteDimensional (ZMod 2) V] (hnd : b.Nondegenerate)
    (huf : b f u = 1) : finrank (ZMod 2) (pairOrth b u f) + 2 = finrank (ZMod 2) V :=
  hb.finrank_orthogonal_span_pair_add_two hnd huf

theorem card_pairStabilizer [FiniteDimensional (ZMod 2) V] (hnd : b.Nondegenerate)
    (huf : b f u = 1) (hV : finrank (ZMod 2) V = 6) : Nat.card (pairStabilizer b u f) = 720 := by
  have hE : finrank (ZMod 2) (pairOrth b u f) = 2 * 2 := by
    have := finrank_pairOrth hb hnd huf
    omega
  rw [Nat.card_congr (Equiv.ofBijective _ (pairRestrict_bijective hb huf)),
    Nat.card_congr (bilinIsometryEquivTauCeti _),
    card_isometryGroup 2 (b.restrict (pairOrth b u f)) (fun z => hb.self_eq_zero z)
      (hb.restrict_nondegenerate_orthogonal_span_pair huf hnd) hE, Nat.card_zmod]
  decide

theorem exists_pairStabilizer_apply_eq [FiniteDimensional (ZMod 2) V] (hnd : b.Nondegenerate)
    (huf : b f u = 1) {w w' : V} (hw : w ∈ pairOrth b u f) (hw' : w' ∈ pairOrth b u f)
    (hw0 : w ≠ 0) (hw0' : w' ≠ 0) :
    ∃ k ∈ pairStabilizer b u f,
      ((k : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) w = w' := by
  have hnd' := hb.restrict_nondegenerate_orthogonal_span_pair huf hnd
  have hpartner : ∀ {x : V} (hx : x ∈ pairOrth b u f), x ≠ 0 →
      ∃ y : pairOrth b u f, (b.restrict (pairOrth b u f)) y ⟨x, hx⟩ = 1 := by
    intro x hx hx0
    by_contra hcon
    push Not at hcon
    have h := hnd'.2 ⟨x, hx⟩ fun y => by
      rcases zmod_two_eq_zero_or_eq_one ((b.restrict (pairOrth b u f)) y ⟨x, hx⟩) with h0 | h1
      · exact h0
      · exact absurd h1 (hcon y)
    exact hx0 (congrArg Subtype.val h)
  obtain ⟨y, hy⟩ := hpartner hw hw0
  obtain ⟨y', hy'⟩ := hpartner hw' hw0'
  obtain ⟨g, hg, hgw, -⟩ := exists_isometry_apply_pair (B := b.restrict (pairOrth b u f))
    (fun z => hb.self_eq_zero z) hnd' hy hy'
  obtain ⟨k, hk⟩ := pairRestrict_surjective hb huf ((bilinIsometryEquivTauCeti _).symm ⟨g, hg⟩)
  refine ⟨k, k.2, ?_⟩
  have h1 := congrArg (fun x : bilinIsometryGroup (b.restrict (pairOrth b u f)) =>
    (((x : LinearMap.GeneralLinearGroup (ZMod 2) (pairOrth b u f)) :
      pairOrth b u f →ₗ[ZMod 2] pairOrth b u f) ⟨w, hw⟩ : V)) hk
  change (((k : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
    V →ₗ[ZMod 2] V) w = ((g ⟨w, hw⟩ : pairOrth b u f) : V) at h1
  rw [h1, hgw]

theorem exists_conj_pointElt_iff [FiniteDimensional (ZMod 2) V] (hnd : b.Nondegenerate)
    (huf : b f u = 1) {w w' : V} (hw : w ∈ pairOrth b u f) (hw' : w' ∈ pairOrth b u f)
    (c c' : ZMod 2) :
    (∃ k ∈ pairStabilizer b u f,
      k * pointElt hb (mem_pairOrth_left hw) c * k⁻¹ = pointElt hb (mem_pairOrth_left hw') c') ↔
      c = c' ∧ (w = 0 ↔ w' = 0) := by
  constructor
  · rintro ⟨k, hk, h⟩
    rw [conj_pointElt_of_mem_pairStabilizer hb hk hw] at h
    obtain ⟨h1, h2⟩ := pointMap_inj hb huf (apply_mem_pairOrth (mem_pairStabilizer.1 hk).1
      (mem_pairStabilizer.1 hk).2 hw) hw' (congrArg (fun x : bilinIsometryGroup b =>
        ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) h)
    refine ⟨h2, ?_⟩
    rw [← h1]
    constructor
    · rintro rfl
      exact map_zero _
    · intro h0
      have h3 := congrArg
        (((k⁻¹ : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) h0
      rwa [inv_apply_apply, map_zero] at h3
  · rintro ⟨rfl, h0⟩
    by_cases hw0 : w = 0
    · refine ⟨1, one_mem _, ?_⟩
      rw [one_mul, inv_one, mul_one]
      apply pointElt_ext
      rw [hw0, h0.1 hw0]
    · obtain ⟨k, hk, hkw⟩ := exists_pairStabilizer_apply_eq hb hnd huf hw hw' hw0
        fun h => hw0 (h0.2 h)
      refine ⟨k, hk, ?_⟩
      rw [conj_pointElt_of_mem_pairStabilizer hb hk hw]
      apply pointElt_ext
      rw [hkw]

theorem card_pointElt_ne_zero (huf : b f u = 1) [Finite (pairOrth b u f)] (c : ZMod 2) :
    Nat.card (Set.range fun w : {w : pairOrth b u f // w ≠ 0} =>
      pointElt hb (mem_pairOrth_left w.1.2) c) = Nat.card (pairOrth b u f) - 1 := by
  classical
  have hinj : Function.Injective fun w : {w : pairOrth b u f // w ≠ 0} =>
      pointElt hb (mem_pairOrth_left w.1.2) c := by
    intro w w' h
    exact Subtype.ext (Subtype.ext (pointMap_inj hb huf w.1.2 w'.1.2
      (congrArg (fun x : bilinIsometryGroup b =>
        ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) h)).1)
  have : Fintype (pairOrth b u f) := Fintype.ofFinite _
  rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq (0 : pairOrth b u f)

end Pair

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
