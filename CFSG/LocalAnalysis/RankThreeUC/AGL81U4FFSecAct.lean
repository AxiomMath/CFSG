module

public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

theorem resHom_mem_stabSub_subgroupOf {X : Subgroup (MulAut V)} {Z' Z : Subgroup V}
    (hZ : X ≤ stabSub Z) (hZ' : X ≤ stabSub Z') (x : ↥X) :
    resHom Z ⟨(x : MulAut V), hZ x.2⟩ ∈ stabSub (Z'.subgroupOf Z) := by
  intro u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  exact hZ' x.2 (u : V)

@[expose] noncomputable def secAct (X : Subgroup (MulAut V)) {Z' Z : Subgroup V}
    (hZ : X ≤ stabSub Z) (hZ' : X ≤ stabSub Z') : ↥X →* MulAut (Sec Z Z') :=
  (quotHom (Z'.subgroupOf Z)).comp
    (((resHom Z).comp (Subgroup.inclusion hZ)).codRestrict (stabSub (Z'.subgroupOf Z))
      (fun x => resHom_mem_stabSub_subgroupOf hZ hZ' x))

theorem secAct_mk (X : Subgroup (MulAut V)) {Z' Z : Subgroup V} (hZ : X ≤ stabSub Z)
    (hZ' : X ≤ stabSub Z') (x : ↥X) (z : ↥Z) :
    secAct X hZ hZ' x (QuotientGroup.mk z) =
      QuotientGroup.mk ⟨(x : MulAut V) (z : V), (hZ x.2 (z : V)).2 z.2⟩ :=
  rfl

theorem range_secAct (X : Subgroup (MulAut V)) {Z' Z : Subgroup V} (hZ : X ≤ stabSub Z)
    (hZ' : X ≤ stabSub Z') : (secAct X hZ hZ').range = autSec X Z Z' := by
  ext φ
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_autQuot.2
      ⟨⟨resHom Z ⟨(x : MulAut V), hZ x.2⟩, resHom_mem_stabSub_subgroupOf hZ hZ' x⟩,
        mem_autSub.2 ⟨⟨(x : MulAut V), hZ x.2⟩, x.2, rfl⟩, rfl⟩
  · intro hφ
    have hφ' : φ ∈ autQuot (autSub X Z) (Z'.subgroupOf Z) := hφ
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.1 hφ'
    obtain ⟨h, hh, hgh⟩ := mem_autSub.1 hg
    refine ⟨⟨(h : MulAut V), hh⟩, ?_⟩
    have key : secAct X hZ hZ' ⟨(h : MulAut V), hh⟩ =
        quotHom (Z'.subgroupOf Z)
          ⟨resHom Z h, resHom_mem_stabSub_subgroupOf hZ hZ' ⟨(h : MulAut V), hh⟩⟩ :=
      rfl
    rw [key]
    exact congrArg (quotHom (Z'.subgroupOf Z)) (Subtype.ext hgh)

theorem secAct_eq_one_iff (X : Subgroup (MulAut V)) {Z' Z : Subgroup V} (hZ : X ≤ stabSub Z)
    (hZ' : X ≤ stabSub Z') (x : ↥X) :
    secAct X hZ hZ' x = 1 ↔ ∀ w ∈ Z, (x : MulAut V) w * w⁻¹ ∈ Z' := by
  constructor
  · intro h w hw
    have h1 : secAct X hZ hZ' x (QuotientGroup.mk (⟨w, hw⟩ : ↥Z)) =
        QuotientGroup.mk (⟨w, hw⟩ : ↥Z) :=
      DFunLike.congr_fun h _
    rw [secAct_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · intro h
    refine MulEquiv.ext fun φ => ?_
    induction φ using QuotientGroup.induction_on with
    | H z =>
      rw [secAct_mk, MulAut.one_apply, mk_eq_mk_iff, Subgroup.mem_subgroupOf]
      exact h z z.2

theorem ker_secAct (X : Subgroup (MulAut V)) {Z' Z : Subgroup V} (hZ'Z : Z' ≤ Z)
    (hZ : X ≤ stabSub Z) (hZ' : X ≤ stabSub Z') :
    (secAct X hZ hZ').ker = (X ⊓ centSec Z Z').subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, secAct_eq_one_iff X hZ hZ' x, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    mem_centSec]
  exact ⟨fun h => ⟨x.2, hZ x.2, h⟩, fun h => h.2.2⟩

end CFSG.LocalAnalysis.RankThreeUC
