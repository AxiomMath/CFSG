module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCKind
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint
open CFSG.SeitzReduction.F4Pilot (OddSchurTrivial oddCoreLift HasBLift)

variable {N : Type} [Group N] [Finite N]

theorem eq_one_of_mem_oddCore_of_commute {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s) {c : N}
    (hcO : c ∈ oddCore N) (hcs : c * s = s * c) : c = 1 := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hcC : c ∈ centralizer ({s} : Set N) := mem_centralizer_singleton_iff.2 hcs
  rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hcC with h | h
  · have hz : (⟨c, h⟩ : Lb) ∈ center Lb :=
      CFSG.SeitzReduction.oddCore_subgroupOf_le_center hLq (mem_subgroupOf.2 hcO)
    rw [hLZ] at hz
    exact congrArg Subtype.val ((Subgroup.mem_bot).1 hz)
  · exfalso
    have hO : Odd (Nat.card (oddCore N)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
    obtain ⟨k, hk⟩ : Odd (orderOf c) := hO.of_dvd_nat ((oddCore N).orderOf_dvd_natCard hcO)
    have hcm : c ^ (2 * k + 1) = 1 := by rw [← hk, pow_orderOf_eq_one]
    have hsk : s ^ (2 * k + 1) = s := by
      rw [pow_succ, pow_mul, sq, hs2, one_pow, one_mul]
    have hpow : (c * s) ^ (2 * k + 1) = s := by
      rw [(Commute.mul_pow (show Commute c s from hcs) (2 * k + 1)), hcm, one_mul, hsk]
    have hsL : s ∈ Lb := hpow ▸ Lb.pow_mem h _
    have h1 := cKind_eq_one_of_mem_centralizer hLZ hsL (cKind_mem_centralizer hLs)
    rw [h1, orderOf_one] at hs
    exact absurd hs (by decide)

theorem isComponent_oddCoreLift_of_le_sup {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    {Kc : Subgroup (N ⧸ oddCore N)} (hKc : IsComponent Kc)
    (hsN : QuotientGroup.mk' (oddCore N) s ∈ normalizer (Kc : Set (N ⧸ oddCore N)))
    (hsC : QuotientGroup.mk' (oddCore N) s ∉ centralizer (Kc : Set (N ⧸ oddCore N))) :
    HasBLift Kc ∧ IsComponent (oddCoreLift Kc) ∧
      (oddCoreLift Kc).map (QuotientGroup.mk' (oddCore N)) = Kc ∧
      (oddCore N).subgroupOf (oddCoreLift Kc) ≤ center (oddCoreLift Kc) ∧
      s ∈ normalizer (oddCoreLift Kc : Set N) := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hC : ∀ c ∈ oddCore N, c * s = s * c → c ∈ center N := fun c hc hcs => by
    rw [eq_one_of_mem_oddCore_of_commute hs hLs hLq hLZ hCs hc hcs]
    exact one_mem _
  obtain ⟨h1, h2, h3, h4⟩ := F4Pilot.isComponent_oddCoreLift_of_le_center hs2 hKc hsN hsC hC
  exact ⟨h1, h2, h3, h4, F4Pilot.mem_normalizer_oddCoreLift Kc hsN⟩

theorem inf_oddCore_eq_bot_of_oddSchurTrivial {Kc : Subgroup (N ⧸ oddCore N)}
    (hKp : ⁅Kc, Kc⁆ = Kc) (hB : HasBLift Kc) (hschur : OddSchurTrivial Kc) :
    oddCoreLift Kc ⊓ oddCore N = ⊥ ∧ Nonempty (oddCoreLift Kc ≃* Kc) := by
  have hmap := F4Pilot.map_oddCoreLift hKp
  let f : oddCoreLift Kc →* Kc := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
    ((QuotientGroup.mk' (oddCore N)).subgroupMap (oddCoreLift Kc))
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hmap).surjective.comp
      ((QuotientGroup.mk' (oddCore N)).subgroupMap_surjective _)
  have hfx : ∀ x : oddCoreLift Kc,
      ((f x : Kc) : N ⧸ oddCore N) = QuotientGroup.mk' (oddCore N) (x : N) := fun x => rfl
  have hkerO : ∀ x : oddCoreLift Kc, x ∈ f.ker ↔ (x : N) ∈ oddCore N := by
    intro x
    rw [MonoidHom.mem_ker, Subtype.ext_iff, hfx, Subgroup.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hker : f.ker ≤ center (oddCoreLift Kc) := by
    intro x hx
    exact hB.inf_le_center (mem_subgroupOf.2 ((hkerO x).1 hx))
  have hodd : Odd (Nat.card f.ker) := by
    have hO : Odd (Nat.card (oddCore N)) := CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
    have hle : (f.ker).map (oddCoreLift Kc).subtype ≤ oddCore N := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hkerO x).1 hx
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (oddCoreLift Kc).subtype_injective] at hdvd
    exact hO.of_dvd_nat hdvd
  have hP : Group.IsPerfect (oddCoreLift Kc) :=
    isPerfect_iff.mpr (F4Pilot.commutator_oddCoreLift Kc)
  have hfinj := hschur (oddCoreLift Kc) hP f hf hker hodd
  refine ⟨?_, ⟨MulEquiv.ofBijective f ⟨hfinj, hf⟩⟩⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxO⟩ := Subgroup.mem_inf.1 hx
  have h1 : (⟨x, hxK⟩ : oddCoreLift Kc) ∈ f.ker := (hkerO _).2 hxO
  rw [(MonoidHom.ker_eq_bot_iff f).2 hfinj] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 h1))

theorem exists_lift_field_of_le_sup {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hschurF : ∀ (X : Type) [Group X], LieModel X .PSL 4 2 2 → OddSchurTrivial X)
    {Kc : Subgroup (N ⧸ oddCore N)} (hKc : IsComponent Kc)
    (hsN : QuotientGroup.mk' (oddCore N) s ∈ normalizer (Kc : Set (N ⧸ oddCore N)))
    (hsC : QuotientGroup.mk' (oddCore N) s ∉ centralizer (Kc : Set (N ⧸ oddCore N)))
    (hKm : LieModel Kc .PSL 4 2 (2 * 1)) :
    IsComponent (oddCoreLift Kc) ∧ oddCoreLift Kc ⊓ oddCore N = ⊥ ∧
      (oddCoreLift Kc).map (QuotientGroup.mk' (oddCore N)) = Kc ∧
      s ∈ normalizer (oddCoreLift Kc : Set N) ∧ Nonempty (oddCoreLift Kc ≃* Kc) ∧
      LieModel (oddCoreLift Kc) .PSL 4 2 2 := by
  obtain ⟨hB, hcomp, hmap, -, hN⟩ := isComponent_oddCoreLift_of_le_sup hs hLs hLq hLZ hCs hKc hsN hsC
  obtain ⟨hinf, ⟨φ⟩⟩ := inf_oddCore_eq_bot_of_oddSchurTrivial (isPerfect_iff.mp hKc.1.1) hB
    (hschurF Kc hKm)
  exact ⟨hcomp, hinf, hmap, hN, ⟨φ⟩, LieType.CurtisTits.lieModel_of_mulEquiv φ.symm hKm⟩

theorem exists_lift_swap_of_le_sup {s : N} (hs : orderOf s = 2) {Lb : Subgroup N}
    (hLs : Lb ≤ centralizer ({s} : Set N)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set N) ≤ Lb ⊔ zpowers s)
    (hschurL : OddSchurTrivial Lb) {Kc : Subgroup (N ⧸ oddCore N)} (hKc : IsComponent Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore N) s)).toMonoidHom⁆ = ⊥)
    (hKL : Nonempty (Kc ≃* Lb.map (QuotientGroup.mk' (oddCore N)))) :
    HasBLift (Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore N) s)).toMonoidHom) ∧
      IsComponent (oddCoreLift Kc) ∧ oddCoreLift Kc ⊓ oddCore N = ⊥ ∧
      (oddCoreLift Kc).map (QuotientGroup.mk' (oddCore N)) = Kc ∧
      Nonempty (oddCoreLift Kc ≃* Lb) ∧
      (oddCoreLift Kc).map (MulAut.conj s).toMonoidHom =
        oddCoreLift (Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore N) s)).toMonoidHom) := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hC : ∀ c ∈ oddCore N, c * s = s * c → c ∈ center N := fun c hc hcs => by
    rw [eq_one_of_mem_oddCore_of_commute hs hLs hLq hLZ hCs hc hcs]
    exact one_mem _
  have hKp : ⁅Kc, Kc⁆ = Kc := isPerfect_iff.mp hKc.1.1
  obtain ⟨hBsup, hB⟩ := F4Pilot.hasBLift_sup_conj_of_le_center hs2 hKp hcomm hC
  obtain ⟨ψ⟩ := hKL
  have φL := mapOddCoreMulEquivOfCenter hLq hLZ
  have hschurK : OddSchurTrivial Kc := hschurL.of_mulEquiv (φL.trans ψ.symm)
  obtain ⟨hinf, ⟨φ⟩⟩ := inf_oddCore_eq_bot_of_oddSchurTrivial hKp hB hschurK
  exact ⟨hBsup, hB.isComponent hKc, hinf, F4Pilot.map_oddCoreLift hKp,
    ⟨φ.trans (ψ.trans φL.symm)⟩, F4Pilot.map_conj_oddCoreLift Kc s⟩

end CFSG.SeitzReduction.LinearPilot
