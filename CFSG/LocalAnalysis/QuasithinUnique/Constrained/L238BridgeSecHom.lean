
module

public import CFSG.CGT.PushingUpLit.BHS.SecHom
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin

namespace Bridge

variable {V : Type} [CommGroup V]

theorem resHom_mem_stabSub_subgroupOf {W U' : Subgroup V} {g : MulAut V} (hW : g ∈ stabSub W)
    (hU : g ∈ stabSub U') : resHom W ⟨g, hW⟩ ∈ stabSub (U'.subgroupOf W) :=
  CFSG.CGT.PushingUpLit.BHS.resHom_mem_stabSub_subgroupOf' hW hU

@[expose] noncomputable def secHom (W U' : Subgroup V) :
    ↥(stabSub W ⊓ stabSub U') →* MulAut (Sec W U') :=
  (quotHom (U'.subgroupOf W)).comp
    (((resHom W).comp (Subgroup.inclusion (inf_le_left : stabSub W ⊓ stabSub U' ≤ stabSub W))).codRestrict
      (stabSub (U'.subgroupOf W)) (fun g => resHom_mem_stabSub_subgroupOf g.2.1 g.2.2))

theorem secHom_apply (W U' : Subgroup V) (g : ↥(stabSub W ⊓ stabSub U')) (w : ↥W) :
    secHom W U' g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨(g : MulAut V) (w : V), (g.2.1 (w : V)).2 w.2⟩ : ↥W) := rfl

theorem secHom_eq_one_iff {W U' : Subgroup V} (g : ↥(stabSub W ⊓ stabSub U')) :
    secHom W U' g = 1 ↔ (g : MulAut V) ∈ centSec W U' :=
  CFSG.CGT.PushingUpLit.BHS.secHom_eq_one_iff g

theorem mem_autSec_iff_secHom {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') {ψ : MulAut (Sec W U')} :
    ψ ∈ autSec X W U' ↔ ∃ g : ↥(stabSub W ⊓ stabSub U'), (g : MulAut V) ∈ X ∧ secHom W U' g = ψ :=
  CFSG.CGT.PushingUpLit.BHS.mem_autSec_iff_secHom hX

theorem secHom_mem_autSec {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') {g : ↥(stabSub W ⊓ stabSub U')} (hg : (g : MulAut V) ∈ X) :
    secHom W U' g ∈ autSec X W U' :=
  (mem_autSec_iff_secHom hX).2 ⟨g, hg, rfl⟩

@[expose] noncomputable def secRestrict {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') : ↥X →* ↥(autSec X W U') :=
  ((secHom W U').comp (Subgroup.inclusion hX)).codRestrict (autSec X W U')
    (fun x => secHom_mem_autSec hX (g := Subgroup.inclusion hX x) x.2)

theorem secRestrict_surjective {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') : Function.Surjective (secRestrict hX) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom hX).1 hψ
  exact ⟨⟨(g : MulAut V), hgX⟩, rfl⟩

theorem secRestrict_apply {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') (x : ↥X) :
    ((secRestrict hX x : ↥(autSec X W U')) : MulAut (Sec W U')) =
      secHom W U' (Subgroup.inclusion hX x) := rfl

theorem sec_sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (W U' : Subgroup V) (s : Sec W U') : s ^ 2 = 1 := by
  induction s using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow]
    have : (w ^ 2 : ↥W) = 1 := Subtype.ext (by simpa using hV (w : V))
    rw [this]
    rfl

theorem isElemAbelian2_autSec {A : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hA : IsElemAbelian2 A) (hAs : A ≤ stabSub W ⊓ stabSub U') :
    IsElemAbelian2 (autSec A W U') := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨g, hgA, rfl⟩ := (mem_autSec_iff_secHom hAs).1 ha
    obtain ⟨k, hkA, rfl⟩ := (mem_autSec_iff_secHom hAs).1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ hgA _ hkA)
  · obtain ⟨g, hgA, rfl⟩ := (mem_autSec_iff_secHom hAs).1 ha
    rw [← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (hA.2 _ hgA)
    rw [this, map_one]

theorem autSec_ne_bot {A : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hAs : A ≤ stabSub W ⊓ stabSub U') (hnt : ¬ A ≤ centSec W U') : autSec A W U' ≠ ⊥ := by
  intro h
  apply hnt
  intro a ha
  have h1 : secHom W U' ⟨a, hAs ha⟩ ∈ autSec A W U' := secHom_mem_autSec hAs (g := ⟨a, hAs ha⟩) ha
  rw [h, Subgroup.mem_bot] at h1
  exact (secHom_eq_one_iff ⟨a, hAs ha⟩).1 h1

end Bridge

end CFSG.QuasithinUnique
