module

public import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82.L13Aux

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem invariant_fixedSpace_self (L : Subgroup (GLV V)) : Invariant L (fixedSpace L) :=
  fun l hl v hv => by
    rw [hv l hl]
    exact hv

noncomputable abbrev tildeRep (L : Subgroup (GLV V)) : ↥L →* GLV (TildeV L) :=
  sectHom L (invariant_fixedSpace_self L) (invariant_commSpace_top L)

abbrev tildeMk (L : Subgroup (GLV V)) : ↥(commSpace L ⊤) →+ TildeV L :=
  ((fixedSpace L).comap (commSpace L ⊤).subtype).mkQ.toAddMonoidHom

theorem tildeRep_mk (L : Subgroup (GLV V)) (ℓ : ↥L) (w w' : ↥(commSpace L ⊤))
    (h : (w' : V) = (ℓ : GLV V) w) : tildeMk L w' = tildeRep L ℓ (tildeMk L w) := by
  have e : w' = ⟨(ℓ : GLV V) w, invariant_commSpace_top L _ ℓ.2 _ w.2⟩ := Subtype.ext h
  rw [e]
  exact (sectHom_mk L _ _ ℓ w).symm

theorem tildeMk_eq_zero_iff (L : Subgroup (GLV V)) (w : ↥(commSpace L ⊤)) :
    tildeMk L w = 0 ↔ (w : V) ∈ fixedSpace L :=
  Submodule.Quotient.mk_eq_zero _

theorem tildeMk_surjective (L : Subgroup (GLV V)) : Function.Surjective (tildeMk L) :=
  Submodule.mkQ_surjective _

theorem ker_tildeRep_le (L : Subgroup (GLV V)) : (tildeRep L).ker ≤ kT L := by
  intro ℓ hℓ w hw
  have h := tildeRep_mk L ℓ ⟨w, hw⟩ ⟨(ℓ : GLV V) w, invariant_commSpace_top L _ ℓ.2 _ hw⟩ rfl
  rw [MonoidHom.mem_ker.1 hℓ] at h
  have h0 : tildeMk L (⟨(ℓ : GLV V) w, invariant_commSpace_top L _ ℓ.2 _ hw⟩ - ⟨w, hw⟩) = 0 := by
    rw [map_sub, h, sub_eq_zero]
    rfl
  exact (tildeMk_eq_zero_iff L _).1 h0

theorem exists_surjective_range_ker {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : HasIrrTildeV L) {n : ℕ} (hn : 4 ≤ n) {α : ↥L →* alternatingGroup (Fin n)}
    (hα : Function.Surjective α) :
    ∃ α' : ↥(tildeRep L).range →* alternatingGroup (Fin n), Function.Surjective α' ∧
      α'.ker ≤ Subgroup.center ↥(tildeRep L).range := by
  have hle : (tildeRep L).rangeRestrict.ker ≤ α.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro z hz
    have hzc : z ∈ Subgroup.center ↥L := kT_le_center hq hirr (ker_tildeRep_le L hz)
    have hc : α z ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := hα g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hzc g']
    rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hc
    exact hc
  set α' := (tildeRep L).rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective _)
    ⟨α, hle⟩
  have hcomp : ∀ ℓ : ↥L, α' ((tildeRep L).rangeRestrict ℓ) = α ℓ := fun _ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hne : α.ker ≠ ⊤ := by
    haveI := alternatingGroup.nontrivial_of_three_le_card (α := Fin n) (by simp; omega)
    obtain ⟨g, hg⟩ := exists_ne (1 : alternatingGroup (Fin n))
    obtain ⟨ℓ, rfl⟩ := hα g
    intro htop
    exact hg (MonoidHom.mem_ker.1 (htop ▸ Subgroup.mem_top ℓ))
  have hkc : α.ker ≤ Subgroup.center ↥L :=
    (normal_eq_top_or_le_center hq (MonoidHom.normal_ker α)).resolve_left hne
  refine ⟨α', fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨ℓ, rfl⟩ := hα x
    exact ⟨_, hcomp ℓ⟩
  · obtain ⟨ℓ, rfl⟩ := MonoidHom.rangeRestrict_surjective (tildeRep L) y
    have hℓ : ℓ ∈ α.ker := by
      rw [MonoidHom.mem_ker, ← hcomp ℓ]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro y'
    obtain ⟨ℓ', rfl⟩ := MonoidHom.rangeRestrict_surjective (tildeRep L) y'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hkc hℓ) ℓ']

theorem exists_surjective_range {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : HasIrrTildeV L) {n : ℕ} (hn : 4 ≤ n) {α : ↥L →* alternatingGroup (Fin n)}
    (hα : Function.Surjective α) :
    ∃ α' : ↥(tildeRep L).range →* alternatingGroup (Fin n), Function.Surjective α' :=
  (exists_surjective_range_ker hq hirr hn hα).imp fun _ h => h.1

theorem range_perfect {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L) :
    ⁅(tildeRep L).range, (tildeRep L).range⁆ = (tildeRep L).range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  congr 1
  exact hq.1

theorem range_isIrr {L : Subgroup (GLV V)} (hirr : HasIrrTildeV L) :
    IsIrr (tildeRep L).range (⊤ : Submodule (ZMod 2) (TildeV L)) := by
  obtain ⟨hlt, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  set q := (fixedSpace L).comap (commSpace L ⊤).subtype
  have hnt : Nontrivial (TildeV L) := by
    obtain ⟨w, hwU, hwC⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Submodule.Quotient.mk (⟨w, hwU⟩ : ↥(commSpace L ⊤)), 0, fun h => hwC ?_⟩⟩
    exact ⟨(Submodule.Quotient.mk_eq_zero q).1 h, hwU⟩
  refine ⟨invariant_top _, bot_lt_top, fun J hJ _ _ => ?_⟩
  set J' : Submodule (ZMod 2) V := (J.comap q.mkQ).map (commSpace L ⊤).subtype
  have hJ'U : J' ≤ commSpace L ⊤ := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hCJ' : fixedSpace L ⊓ commSpace L ⊤ ≤ J' := by
    rintro c ⟨hcC, hcU⟩
    refine ⟨⟨c, hcU⟩, ?_, rfl⟩
    show Submodule.Quotient.mk (⟨c, hcU⟩ : ↥(commSpace L ⊤)) ∈ J
    rw [(Submodule.Quotient.mk_eq_zero q).2 hcC]
    exact J.zero_mem
  have hinv : Invariant L J' := by
    rintro l hl _ ⟨w, hw, rfl⟩
    have hw' : l (w : V) ∈ commSpace L ⊤ := invariant_commSpace_top L _ hl _ w.2
    refine ⟨⟨l w, hw'⟩, ?_, rfl⟩
    have h := tildeRep_mk L ⟨l, hl⟩ w ⟨l w, hw'⟩ rfl
    show tildeMk L ⟨l w, hw'⟩ ∈ J
    rw [h]
    exact hJ _ ⟨⟨l, hl⟩, rfl⟩ _ hw
  rcases hmin J' hinv hCJ' hJ'U with h | h
  · left
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective q x
    have hw : (w : V) ∈ J' := ⟨w, hx, rfl⟩
    rw [h] at hw
    exact (Submodule.mem_bot _).2 ((Submodule.Quotient.mk_eq_zero q).2 hw.1)
  · right
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective q x
    have hw : (w : V) ∈ J' := by
      rw [h]
      exact w.2
    obtain ⟨w', hw', e⟩ := hw
    rw [← Subtype.ext e]
    exact hw'

theorem finite_tildeV [Finite V] (L : Subgroup (GLV V)) : Finite (TildeV L) :=
  Finite.of_surjective _ (tildeMk_surjective L)

theorem faithfulTildeV_of_h1_range {L : Subgroup (GLV V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hirr : HasIrrTildeV L)
    (h1 : H1Zero ↥(tildeRep L).range (TildeV L) fun y a => (y : GLV (TildeV L)) a) :
    FaithfulTildeV L :=
  faithfulTildeV_of_h1 (tildeRep L).rangeRestrict (tildeMk L) (fun y a => (y : GLV (TildeV L)) a)
    (fun ℓ w w' h => tildeRep_mk L ℓ w w' h) (tildeMk_eq_zero_iff L) hq hirr
    (MonoidHom.rangeRestrict_surjective _) (tildeMk_surjective L) (fun _ => rfl)
    (fun y => map_zero (y : GLV (TildeV L))) h1

theorem faithfulTildeV_of_a7Four [Finite V] (hG21 : H1AltSevenFour) {L : Subgroup (GLV V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : HasIrrTildeV L) (hA : IsA7FourModule L) :
    FaithfulTildeV L := by
  obtain ⟨⟨α, hα⟩, hdim⟩ := hA
  haveI := finite_tildeV L
  exact faithfulTildeV_of_h1_range hq hirr
    (hG21 (TildeV L) hdim _ (exists_surjective_range hq hirr (by norm_num) hα))

theorem faithfulTildeV_of_a6Z3 [Finite V] (hG21 : H1ThreeAltSix) {L : Subgroup (GLV V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hirr : HasIrrTildeV L) (hA : IsA6Z3Module L) :
    FaithfulTildeV L := by
  obtain ⟨⟨α, hα⟩, hdim⟩ := hA
  haveI := finite_tildeV L
  exact faithfulTildeV_of_h1_range hq hirr
    (hG21 (TildeV L) hdim _ (range_perfect hq) (range_isIrr hirr)
      (exists_surjective_range_ker hq hirr (by norm_num) hα))

end CFSG.CGT.Foote82.L13Aux
