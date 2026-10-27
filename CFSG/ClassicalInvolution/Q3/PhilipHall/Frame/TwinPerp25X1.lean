module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Nine
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf10U1
public import CFSG.ClassicalInvolution.Asc77.AscCX9Q

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Asc77.CX (eq_one_or_eq_of_mem_zpowers closure_pair_le
  mem_centralizer_pair_iff)


section Act

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def actW (hΩ : HypOmegaGen Ω) {w : G} (hw : IsPGroup 2 (Subgroup.zpowers w)) :
    ↥(Subgroup.centralizer ({w} : Set G)) →*
      MulAut (↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) :=
  CX.layerHom (TwinDisc.coreLayer Ω w) (Subgroup.centralizer ({w} : Set G)) fun _ hx =>
    TwinDisc.conjSub_coreLayer hΩ hw hx

theorem actW_apply (hΩ : HypOmegaGen Ω) {w : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (x : ↥(Subgroup.centralizer ({w} : Set G))) :
    actW hΩ hw x = C25Y.layerAut (TwinDisc.coreLayer Ω w)
      (TwinDisc.conjSub_coreLayer hΩ hw x.2) := rfl

theorem actW_self (hΩ : HypOmegaGen Ω) {w : G} (hw : IsPGroup 2 (Subgroup.zpowers w)) :
    actW hΩ hw ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = 1 := by
  ext y
  refine QuotientGroup.induction_on y fun y => ?_
  rw [actW_apply, C25Y.layerAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [C25Y.coe_conjOnSub]
  have hy := Subgroup.mem_centralizer_singleton_iff.mp
    (TwinDisc.coreLayer_le_centralizer (Ω := Ω) (c := w) y.2)
  rw [← hy, mul_inv_cancel_right]

theorem actW_eq_conj (hΩ : HypOmegaGen Ω) {w x : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hxY : x ∈ TwinDisc.coreLayer Ω w) :
    actW hΩ hw ⟨x, hx⟩ = MulAut.conj (QuotientGroup.mk ⟨x, hxY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) := by
  ext y
  refine QuotientGroup.induction_on y fun y => ?_
  rw [actW_apply, C25Y.layerAut_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem actW_mul_z (hΩ : HypOmegaGen Ω) {w x z : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (hz : z ∈ Subgroup.centralizer ({w} : Set G))
    (hzY : z ∈ TwinDisc.coreLayer Ω w) (hxz : x * z ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hΩ hw ⟨x * z, hxz⟩ = actW hΩ hw ⟨x, hx⟩ * MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) := by
  rw [← actW_eq_conj hΩ hw hz hzY, ← map_mul]
  rfl

theorem actW_mem_zpowers (hΩ : HypOmegaGen Ω) {w x e : G} (hw : IsPGroup 2 (Subgroup.zpowers w))
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) (he : e ∈ Subgroup.closure ({w, x} : Set G))
    (heC : e ∈ Subgroup.centralizer ({w} : Set G)) :
    actW hΩ hw ⟨e, heC⟩ ∈ Subgroup.zpowers (actW hΩ hw ⟨x, hx⟩) := by
  set P := (Subgroup.zpowers (actW hΩ hw ⟨x, hx⟩)).comap (actW hΩ hw) with hP
  have hle : Subgroup.closure ({w, x} : Set G) ≤
      P.map (Subgroup.centralizer ({w} : Set G)).subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h
    · refine ⟨⟨w, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_, h.symm⟩
      show actW hΩ hw ⟨w, _⟩ ∈ Subgroup.zpowers (actW hΩ hw ⟨x, hx⟩)
      rw [actW_self]
      exact one_mem _
    · exact ⟨⟨x, hx⟩, Subgroup.mem_zpowers _, h.symm⟩
  obtain ⟨e', he', hee'⟩ := hle he
  have he'eq : e' = ⟨e, heC⟩ := Subtype.ext hee'
  rw [he'eq] at he'
  exact he'

end Act

section Facts

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def fixOf {M : Type} [Group M] (L : Subgroup (MulAut M)) : Subgroup M where
  carrier := {x | ∀ β ∈ L, β x = x}
  one_mem' β _ := map_one β
  mul_mem' {a b} ha hb β hβ := by rw [map_mul, ha β hβ, hb β hβ]
  inv_mem' {a} ha β hβ := by rw [map_inv, ha β hβ]

@[expose] noncomputable def actOf (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw : w * w = 1) :
    ↥(Subgroup.centralizer ({w} : Set G)) →*
      MulAut (↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) :=
  actW hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hw)

structure LayerFacts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw : w * w = 1) : Prop where
  zY : z ∈ TwinDisc.coreLayer Ω w
  center : Subgroup.center
    (↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) = ⊥
  exp2 : ∀ x : G, x ∈ cA S R R' → ∀ hxw : x ∈ Subgroup.centralizer ({w} : Set G),
    actOf hyp hw ⟨x, hxw⟩ * actOf hyp hw ⟨x, hxw⟩ = 1
  card : Nat.card ↥(((cA S R R').subgroupOf (Subgroup.centralizer ({w} : Set G))).map
    (actOf hyp hw)) ≤ 4
  refl : ∀ x : G, x ∈ cA S R R' → ∀ hxw : x ∈ Subgroup.centralizer ({w} : Set G),
    actOf hyp hw ⟨x, hxw⟩ ≠ 1 →
    actOf hyp hw ⟨x, hxw⟩ ≠ MulAut.conj (QuotientGroup.mk ⟨z, zY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) →
    ∃ xb : ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w),
      actOf hyp hw ⟨x, hxw⟩ xb = xb ∧
        xb * QuotientGroup.mk ⟨z, zY⟩ * xb⁻¹ ≠ QuotientGroup.mk ⟨z, zY⟩ ∧
        (xb * QuotientGroup.mk ⟨z, zY⟩ * xb⁻¹) * QuotientGroup.mk ⟨z, zY⟩ =
          QuotientGroup.mk ⟨z, zY⟩ * (xb * QuotientGroup.mk ⟨z, zY⟩ * xb⁻¹)
  nonsolv : ∀ L : Subgroup (MulAut
      (↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w))),
    L ≤ ((cA S R R').subgroupOf (Subgroup.centralizer ({w} : Set G))).map (actOf hyp hw) →
    MulAut.conj (QuotientGroup.mk ⟨z, zY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) ∉ L →
    ¬ Group.IsSolvable ↥(fixOf L)

variable {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {w x : G} {hw : w * w = 1}

theorem actOf_apply (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw : w * w = 1)
    (x : ↥(Subgroup.centralizer ({w} : Set G))) :
    actOf hyp hw x = C25Y.layerAut (TwinDisc.coreLayer Ω w)
      (TwinDisc.conjSub_coreLayer hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hw) x.2) := rfl

theorem good_iff_actW (hLF : LayerFacts hyp hw) (hwA : w ∈ cA S R R') (hxA : x ∈ cA S R R')
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    z ∈ zStarOf (Subgroup.centralizer ({w, x} : Set G)) ↔
      actOf hyp hw ⟨x, hx⟩ = MulAut.conj (QuotientGroup.mk ⟨z, hLF.zY⟩ :
        ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw
  have hzY := hLF.zY
  have hβ2 := hLF.exp2 x hxA hx
  have hzw : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hzx : z ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS x hxA.1).symm
  constructor
  · intro hgood
    by_contra hβz
    set F := Subgroup.closure ({w, x} : Set G) with hF
    have hFA : F ≤ cA S R R' := closure_pair_le hwA hxA
    have hF2 : IsPGroup 2 F := S.isPGroup'.to_le (hFA.trans inf_le_left)
    have hFb : F ≤ Subgroup.centralizer ({w} : Set G) :=
      closure_pair_le (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hx
    have hFY : ∀ e ∈ F, conjSub e (TwinDisc.coreLayer Ω w) = TwinDisc.coreLayer Ω w :=
      fun e he => TwinDisc.conjSub_coreLayer hΩ hc2 (hFb he)
    have hzF : z ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact hzS g (hFA hg).1
    have hgoodF : z ∈ zStarOf (Subgroup.centralizer (F : Set G)) := by
      rw [hF, Subgroup.centralizer_closure]
      exact hgood
    have hpow : ∀ e (he : e ∈ F), actOf hyp hw ⟨e, hFb he⟩ = 1 ∨
        actOf hyp hw ⟨e, hFb he⟩ = actOf hyp hw ⟨x, hx⟩ := fun e he =>
      eq_one_or_eq_of_mem_zpowers hβ2 (actW_mem_zpowers hΩ hc2 hx he (hFb he))
    by_cases hβ1 : actOf hyp hw ⟨x, hx⟩ = 1
    · refine not_mem_zStarOf_of_layerAut_trivial hF2 hFY hzF hzY hz2 hz1 hLF.center ?_ hgoodF
      intro e he y
      have h1 : actOf hyp hw ⟨e, hFb he⟩ = 1 := by
        rcases hpow e he with h | h
        · exact h
        · rw [h, hβ1]
      have h2 := congrArg (fun φ => φ y) h1
      simpa [actOf_apply] using h2
    · obtain ⟨xb, hxbfix, hxbz, hxbc⟩ := hLF.refl x hxA hx hβ1 hβz
      refine not_mem_zStarOf_of_fix_of_normalizes hF2 hFY hzY hz2 (x := xb) ?_ hxbz hxbc hgoodF
      intro e he
      rcases hpow e he with h | h
      · have h2 := congrArg (fun φ => φ xb) h
        simpa [actOf_apply] using h2
      · have h2 := congrArg (fun φ => φ xb) h
        simp only [actOf_apply] at h2
        rw [h2]
        exact hxbfix
  · intro hβz
    refine mem_zStarOf_of_layerAut_eq_conj (d := x) (H := Subgroup.centralizer ({w, x} : Set G))
      (fun h hh => TwinDisc.conjSub_coreLayer hΩ hc2 (mem_centralizer_pair_iff.mp hh).1)
      (fun h hh => Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_pair_iff.mp hh).2)
      (mem_centralizer_pair_iff.mpr ⟨hzw, hzx⟩) (TwinDisc.conjSub_coreLayer hΩ hc2 hx) hzY
      hLF.center ?_
    intro y
    have h2 := congrArg (fun φ => φ y) hβz
    simpa [actOf_apply, MulAut.conj_apply] using h2

theorem not_good_and_good (hLF : LayerFacts hyp hw) (hwA : w ∈ cA S R R') (hxA : x ∈ cA S R R')
    (hx : x ∈ Subgroup.centralizer ({w} : Set G)) :
    ¬ (z ∈ zStarOf (Subgroup.centralizer ({w, x} : Set G)) ∧
      z ∈ zStarOf (Subgroup.centralizer ({w, x * z} : Set G))) := by
  rintro ⟨h₁, h₂⟩
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  have hzY := hLF.zY
  have hz : z ∈ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS w hwA.1).symm
  have hxz : x * z ∈ Subgroup.centralizer ({w} : Set G) := Subgroup.mul_mem _ hx hz
  have e₁ := (good_iff_actW hLF hwA hxA hx).mp h₁
  have e₂ := (good_iff_actW hLF hwA (Subgroup.mul_mem _ hxA hzA) hxz).mp h₂
  have e₂' : actW hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hw) ⟨x * z, hxz⟩ = _ := e₂
  rw [actW_mul_z _ _ hx hz hzY hxz] at e₂'
  change actOf hyp hw ⟨x, hx⟩ * _ = _ at e₂'
  rw [e₁] at e₂'
  have e₂ := e₂'
  have h1 : MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) = 1 := by
    set c := MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω w) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω w)) with hc
    calc c = c⁻¹ * (c * c) := by group
      _ = 1 := by rw [e₂, inv_mul_cancel]
  exact conj_ne_one_of_center_eq_bot hLF.center (mk_ne_one_of_involution hzY hz2 hz1) h1

end Facts

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
