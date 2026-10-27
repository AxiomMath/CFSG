module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadicalRelativeUniqueness
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixRadicalLabels
public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveSplitting

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels
open LinearMap (BilinForm)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

abbrev ptSub {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) (z : G)
    (hb : b.IsAlt) (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) : Subgroup G :=
  pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ⊔ zpowers z

variable (e) in
@[expose] def ptCoord (i : Fin 3 ⊕ Fin 3) :
    ↥(pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) →ₗ[ZMod 2] ZMod 2 :=
  (e.coord i).comp (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))).subtype

theorem ptCoord_apply (i : Fin 3 ⊕ Fin 3) (w : 𝔼) : ptCoord e i w = e.repr w i :=
  rfl

variable (e) in
@[expose] def ptQuad : QuadraticForm (ZMod 2) ↥(pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) :=
  QuadraticMap.linMulLin (ptCoord e (Sum.inl 1)) (ptCoord e (Sum.inr 1)) +
    QuadraticMap.linMulLin (ptCoord e (Sum.inl 2)) (ptCoord e (Sum.inr 2))

theorem ptQuad_apply (w : 𝔼) :
    ptQuad e w = e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) +
      e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2) :=
  rfl

variable (he : IsSymplecticBasis b e)
include he

theorem repr_inl_zero (w : 𝔼) : e.repr w (Sum.inl 0) = 0 := by
  have h := (mem_pointSpan.1 ((pointSpan_eq_pairOrth he).symm ▸ w.2 : (w : V) ∈ pointSpan e)).1
  exact h

theorem repr_inr_zero (w : 𝔼) : e.repr w (Sum.inr 0) = 0 := by
  have h := (mem_pointSpan.1 ((pointSpan_eq_pairOrth he).symm ▸ w.2 : (w : V) ∈ pointSpan e)).2
  exact h

theorem form_pointSpan (w w' : 𝔼) :
    b w w' = e.repr w (Sum.inl 1) * e.repr w' (Sum.inr 1) +
      e.repr w (Sum.inl 2) * e.repr w' (Sum.inr 2) +
        (e.repr w (Sum.inr 1) * e.repr w' (Sum.inl 1) +
          e.repr w (Sum.inr 2) * e.repr w' (Sum.inl 2)) := by
  rw [form_eq_pairedSympForm he, pairedSympForm_three, repr_inl_zero he w, repr_inr_zero he w]
  ring

theorem polarBilin_ptQuad :
    QuadraticMap.polarBilin (ptQuad e) =
      b.restrict (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) := by
  ext w w'
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ptQuad_apply, ptQuad_apply,
    ptQuad_apply, LinearMap.BilinForm.restrict_apply]
  change _ = b w w'
  rw [form_pointSpan he]
  simp only [Submodule.coe_add, map_add, Finsupp.add_apply]
  ring

omit he in
theorem ptQuad_add (he : IsSymplecticBasis b e) (w w' : 𝔼) :
    ptQuad e (w + w') = ptQuad e w + ptQuad e w' + b w w' := by
  have h := congrArg (fun B : BilinForm (ZMod 2) 𝔼 => B w w') (polarBilin_ptQuad he)
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    LinearMap.BilinForm.restrict_apply] at h
  change ptQuad e (w + w') - ptQuad e w - ptQuad e w' = b w w' at h
  rw [← h]
  ring

variable (hb : b.IsAlt)

omit he in
@[expose] def ptElt (v : ↥(pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2) :
    bilinIsometryGroup b :=
  pointElt hb (mem_pairOrth_left v.1.2) (v.2 + ptQuad e v.1)

omit he in
theorem ptElt_eq (v : 𝔼 × ZMod 2) :
    ptElt hb v = pointElt hb (mem_pairOrth_left v.1.2) (v.2 + ptQuad e v.1) :=
  rfl

theorem ptElt_add (v v' : 𝔼 × ZMod 2) : ptElt hb (v + v') = ptElt hb v * ptElt hb v' := by
  rw [ptElt_eq, ptElt_eq, ptElt_eq, pointElt_mul]
  apply pointElt_ext
  congr 1
  simp only [Prod.snd_add, Prod.fst_add, ptQuad_add he]
  ring

omit he in
theorem ptElt_zero : ptElt hb (0 : 𝔼 × ZMod 2) = 1 := by
  rw [ptElt_eq]
  have h0 : ptQuad e (0 : 𝔼) = 0 := QuadraticMap.map_zero _
  simp only [Prod.snd_zero, Prod.fst_zero, h0, add_zero]
  exact pointElt_zero_zero hb _

@[expose] def ptHomV : Multiplicative (↥(pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2) →*
    bilinIsometryGroup b where
  toFun v := ptElt hb (Multiplicative.toAdd v)
  map_one' := ptElt_zero hb
  map_mul' v v' := ptElt_add he hb (Multiplicative.toAdd v) (Multiplicative.toAdd v')

theorem ptHomV_apply (v : 𝔼 × ZMod 2) : ptHomV he hb (Multiplicative.ofAdd v) = ptElt hb v :=
  rfl

theorem ptHomV_injective : Function.Injective (ptHomV he hb) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨⟨w, t⟩, rfl⟩ : ∃ y, Multiplicative.ofAdd y = x := ⟨Multiplicative.toAdd x, rfl⟩
  rw [ptHomV_apply, ptElt_eq, ← pointElt_zero_zero hb (mem_pairOrth_left (zero_mem 𝔼))] at hx
  have h := pointMap_inj hb (bilin_f_u he) w.2 (zero_mem 𝔼)
    (congrArg (fun g : bilinIsometryGroup b =>
      ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) hx)
  have hw : w = 0 := Subtype.ext h.1
  subst hw
  have h2 : t = 0 := by
    have h3 := h.2
    simpa using h3
  rw [h2]
  rfl

theorem range_ptHomV :
    (ptHomV he hb).range = pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  ext g
  rw [MonoidHom.mem_range, mem_pointRadical]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, (Multiplicative.toAdd v).1.2,
      (Multiplicative.toAdd v).2 + ptQuad e (Multiplicative.toAdd v).1, rfl⟩
  · rintro ⟨w, hw, c, rfl⟩
    refine ⟨Multiplicative.ofAdd (⟨w, hw⟩, c + ptQuad e ⟨w, hw⟩), ?_⟩
    rw [ptHomV_apply, ptElt_eq]
    apply pointElt_ext
    congr 1
    change c + ptQuad e ⟨w, hw⟩ + ptQuad e ⟨w, hw⟩ = c
    rw [add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

theorem conj_ptHomV (k : pairStabilizer b (e (Sum.inl 0)) (e (Sum.inr 0))) (v : 𝔼 × ZMod 2) :
    (k : bilinIsometryGroup b) * ptHomV he hb (Multiplicative.ofAdd v) *
        (k : bilinIsometryGroup b)⁻¹ =
      ptHomV he hb (Multiplicative.ofAdd (OddQuadraticFive.hV (polarBilin_ptQuad he)
        (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)) k) v)) := by
  set s := pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)) k with hs
  have h1 : (k : bilinIsometryGroup b) * ptHomV he hb (Multiplicative.ofAdd v) *
      (k : bilinIsometryGroup b)⁻¹ = pointElt hb (mem_pairOrth_left (apply_mem_pairOrth
        (mem_pairStabilizer.1 k.2).1 (mem_pairStabilizer.1 k.2).2 v.1.2)) (v.2 + ptQuad e v.1) :=
    conj_pointElt_of_mem_pairStabilizer hb k.2 v.1.2 _
  rw [h1, ptHomV_apply, ptElt_eq]
  apply pointElt_ext
  have h2 : (OddQuadraticFive.hV (polarBilin_ptQuad he) s v).2 + ptQuad e
      (OddQuadraticFive.hV (polarBilin_ptQuad he) s v).1 = v.2 + ptQuad e v.1 := by
    rw [OddQuadraticFive.hV_apply]
    change v.2 + ptQuad e v.1 + ptQuad e (OddQuadraticFive.sE s v.1) +
      ptQuad e (OddQuadraticFive.sE s v.1) = v.2 + ptQuad e v.1
    rw [add_assoc (v.2 + ptQuad e v.1), ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul,
      add_zero]
  rw [h2]
  rfl

section Group

variable {G : Type*} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hz : orderOf z = 2)

@[expose] def ptHom :
    Multiplicative ((↥(pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) × ZMod 2) × ZMod 2) →* G where
  toFun x := ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (Multiplicative.toAdd x).1)) : L) : G) *
    zPow z (Multiplicative.toAdd x).2
  map_one' := by
    rw [toAdd_one, Prod.fst_zero, Prod.snd_zero, ofAdd_zero, map_one, map_one, zPow_zero,
      mul_one]
    rfl
  map_mul' x y := by
    rw [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul, map_mul, zPow_add hz,
      Subgroup.coe_mul]
    have h := mul_comm_zPow hzC (φ.symm (ptHomV he hb (Multiplicative.ofAdd
      (Multiplicative.toAdd y).1))).2 (Multiplicative.toAdd x).2
    calc ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (Multiplicative.toAdd x).1)) : L) : G) *
          ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (Multiplicative.toAdd y).1)) : L) : G) *
          (zPow z (Multiplicative.toAdd x).2 * zPow z (Multiplicative.toAdd y).2) =
        ((φ.symm (ptHomV he hb (Multiplicative.ofAdd (Multiplicative.toAdd x).1)) : L) : G) *
          (((φ.symm (ptHomV he hb (Multiplicative.ofAdd (Multiplicative.toAdd y).1)) : L) : G) *
            zPow z (Multiplicative.toAdd x).2) * zPow z (Multiplicative.toAdd y).2 := by group
      _ = _ := by rw [h]; group

theorem ptHom_apply (v : 𝔼 × ZMod 2) (ε : ZMod 2) :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) * zPow z ε :=
  rfl

theorem ptHom_pt (v : 𝔼 × ZMod 2) :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) := by
  rw [ptHom_apply, zPow_zero, mul_one]

theorem ptHom_z : ptHom he hb φ hzC hz (Multiplicative.ofAdd (0, 1)) = z := by
  rw [ptHom_apply, ofAdd_zero, map_one, map_one, zPow_one, Subgroup.coe_one, one_mul]

theorem mem_ptA_iff {a : G} :
    a ∈ pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0))) ↔
      ∃ v : 𝔼 × ZMod 2, ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) = a := by
  rw [mem_pullSub]
  constructor
  · rintro ⟨ha, hP⟩
    rw [← range_ptHomV he hb] at hP
    obtain ⟨v, hv⟩ := hP
    refine ⟨Multiplicative.toAdd v, ?_⟩
    rw [ofAdd_toAdd, hv, MulEquiv.symm_apply_apply]
  · rintro ⟨v, rfl⟩
    refine ⟨(φ.symm _).2, ?_⟩
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, ← range_ptHomV he hb]
    exact ⟨_, rfl⟩

include hzC hz in
theorem mem_ptSub_iff {x : G} :
    x ∈ ptSub φ z hb e ↔ ∃ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) * zPow z ε = x := by
  constructor
  · intro hx
    obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_le_centralizer
      (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hx
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hz hs with rfl | rfl
    · exact ⟨v, 0, by rw [zPow_zero]⟩
    · exact ⟨v, 1, by rw [zPow_one]⟩
  · rintro ⟨v, ε, rfl⟩
    exact mul_mem (mem_sup_left ((mem_ptA_iff he hb φ).2 ⟨v, rfl⟩)) (mem_sup_right (zPow_mem z ε))

theorem range_ptHom : (ptHom he hb φ hzC hz).range = ptSub φ z hb e := by
  ext x
  rw [MonoidHom.mem_range, mem_ptSub_iff he hb φ hzC hz]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨v, ε, rfl⟩
    exact ⟨Multiplicative.ofAdd (v, ε), rfl⟩

theorem ptHom_injective (hinf : L ⊓ zpowers z = ⊥) : Function.Injective (ptHom he hb φ hzC hz) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨⟨v, ε⟩, rfl⟩ : ∃ y, Multiplicative.ofAdd y = x := ⟨Multiplicative.toAdd x, rfl⟩
  rw [ptHom_apply] at hx
  have hzε : zPow z ε ∈ L ⊓ zpowers z := by
    refine mem_inf.2 ⟨?_, zPow_mem z ε⟩
    have h1 : zPow z ε = ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G)⁻¹ :=
      eq_inv_of_mul_eq_one_right hx
    rw [h1]
    exact L.inv_mem (φ.symm _).2
  rw [hinf, mem_bot] at hzε
  rw [hzε, mul_one] at hx
  have h2 : φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) = 1 := Subtype.ext hx
  rw [MulEquiv.map_eq_one_iff, ← map_one (ptHomV he hb)] at h2
  have hv := ptHomV_injective he hb h2
  rw [(zPow_eq_one_iff hz).1 hzε]
  rw [← ofAdd_zero] at hv
  rw [Multiplicative.ofAdd.injective hv]
  rfl

@[expose] def ptLabel (hinf : L ⊓ zpowers z = ⊥) :
    ptSub φ z hb e ≃* Multiplicative ((𝔼 × ZMod 2) × ZMod 2) :=
  ((MonoidHom.ofInjective (ptHom_injective he hb φ hzC hz hinf)).trans
    (MulEquiv.subgroupCongr (range_ptHom he hb φ hzC hz))).symm

theorem coe_ptLabel_symm (hinf : L ⊓ zpowers z = ⊥)
    (x : Multiplicative ((𝔼 × ZMod 2) × ZMod 2)) :
    ((ptLabel he hb φ hzC hz hinf).symm x : G) = ptHom he hb φ hzC hz x :=
  rfl

@[expose] def ptLabelOf (hinf : L ⊓ zpowers z = ⊥) {M : Subgroup G} (hBM : ptSub φ z hb e ≤ M) :
    (ptSub φ z hb e).subgroupOf M ≃* Multiplicative ((𝔼 × ZMod 2) × ZMod 2) :=
  (subgroupOfEquivOfLe hBM).trans (ptLabel he hb φ hzC hz hinf)

theorem coe_ptLabelOf_symm (hinf : L ⊓ zpowers z = ⊥) {M : Subgroup G}
    (hBM : ptSub φ z hb e ≤ M) (x : Multiplicative ((𝔼 × ZMod 2) × ZMod 2)) :
    (((ptLabelOf he hb φ hzC hz hinf hBM).symm x : M) : G) = ptHom he hb φ hzC hz x :=
  rfl

@[expose] def ptLevi :
    bilinIsometryGroup (b.restrict (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)))) →* G :=
  L.subtype.comp (φ.symm.toMonoidHom.comp ((pairStabilizer b _ _).subtype.comp
    (MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
      (pairRestrict_bijective hb (bilin_f_u he))).symm.toMonoidHom))

theorem ptLevi_mem (s : bilinIsometryGroup (b.restrict 𝔼)) : ptLevi he hb φ s ∈ L :=
  (φ.symm _).2

theorem pairRestrict_ptLevi (s : bilinIsometryGroup (b.restrict 𝔼)) :
    pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0))
      ((MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
        (pairRestrict_bijective hb (bilin_f_u he))).symm s) = s :=
  (MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
    (pairRestrict_bijective hb (bilin_f_u he))).apply_symm_apply s

theorem ptLevi_conj_ptHomV (s : bilinIsometryGroup (b.restrict 𝔼)) (v : 𝔼 × ZMod 2) :
    ptLevi he hb φ s * ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) *
        (ptLevi he hb φ s)⁻¹ =
      ((φ.symm (ptHomV he hb (Multiplicative.ofAdd
        (OddQuadraticFive.hV (polarBilin_ptQuad he) s v))) : L) : G) := by
  set k := (MulEquiv.ofBijective (pairRestrict b (e (Sum.inl 0)) (e (Sum.inr 0)))
    (pairRestrict_bijective hb (bilin_f_u he))).symm s with hk
  have h1 := conj_ptHomV he hb k v
  rw [pairRestrict_ptLevi he hb s] at h1
  have h2 : ptLevi he hb φ s = ((φ.symm (k : bilinIsometryGroup b) : L) : G) := rfl
  rw [h2, ← h1, ← Subgroup.coe_inv, ← map_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
    ← map_mul, ← map_mul]

theorem ptLevi_conj_ptHom (s : bilinIsometryGroup (b.restrict 𝔼)) (v : 𝔼 × ZMod 2)
    (ε : ZMod 2) :
    ptLevi he hb φ s * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) *
        (ptLevi he hb φ s)⁻¹ =
      ptHom he hb φ hzC hz (Multiplicative.ofAdd
        (OddQuadraticFive.hV (polarBilin_ptQuad he) s v, ε)) := by
  have hzε : ptLevi he hb φ s * zPow z ε * (ptLevi he hb φ s)⁻¹ = zPow z ε := by
    rw [mul_inv_eq_iff_eq_mul, mul_comm_zPow hzC (ptLevi_mem he hb φ s) ε]
  rw [ptHom_apply, ptHom_apply, ← ptLevi_conj_ptHomV]
  calc ptLevi he hb φ s * (((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) *
        zPow z ε) * (ptLevi he hb φ s)⁻¹ =
      (ptLevi he hb φ s * ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) *
        (ptLevi he hb φ s)⁻¹) * (ptLevi he hb φ s * zPow z ε * (ptLevi he hb φ s)⁻¹) := by group
    _ = _ := by rw [hzε]

include hzC in
theorem ptLevi_mul_z (s : bilinIsometryGroup (b.restrict 𝔼)) :
    ptLevi he hb φ s * z = z * ptLevi he hb φ s :=
  mul_comm_z hzC (ptLevi_mem he hb φ s)

end Group

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
