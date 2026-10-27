module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.PerfectCover

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

omit [M.Normal] in
theorem commutator_subgroupOf_eq {P : Subgroup G} (hP : P ≤ M) (hPp : ⁅P, P⁆ = P) :
    ⁅P.subgroupOf M, P.subgroupOf M⁆ = P.subgroupOf M := by
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, map_subgroupOf_eq_of_le hP, hPp]

theorem map_subgroupOf_cqM {P : Subgroup G} (hP : P ≤ M) :
    (P.subgroupOf M).map (cqM M) = P.map (cq M) := by
  rw [← Subgroup.map_map, map_subgroupOf_eq_of_le hP]

theorem le_of_map_le_cq {P P' : Subgroup G} (hP : P ≤ M) (hP' : P' ≤ M) (hPp : ⁅P, P⁆ = P)
    (hPp' : ⁅P', P'⁆ = P') (h : P.map (cq M) ≤ P'.map (cq M)) : P ≤ P' := by
  have h1 := le_of_map_le_of_perfect (ker_cqM_le_center M) (commutator_subgroupOf_eq M hP hPp)
    (commutator_subgroupOf_eq M hP' hPp')
    (by rw [map_subgroupOf_cqM M hP, map_subgroupOf_cqM M hP']; exact h)
  intro x hx
  exact h1 (show (⟨x, hP hx⟩ : ↥M) ∈ P.subgroupOf M from hx)

theorem eq_of_map_eq_cq {P P' : Subgroup G} (hP : P ≤ M) (hP' : P' ≤ M) (hPp : ⁅P, P⁆ = P)
    (hPp' : ⁅P', P'⁆ = P') (h : P.map (cq M) = P'.map (cq M)) : P = P' :=
  le_antisymm (le_of_map_le_cq M hP hP' hPp hPp' h.le) (le_of_map_le_cq M hP' hP hPp' hPp h.ge)

@[expose] def lf (Q : Subgroup (CQ M)) : Subgroup G := (ccLift (cqM M) Q).map M.subtype

theorem lf_le (Q : Subgroup (CQ M)) : lf M Q ≤ M := Subgroup.map_subtype_le _

theorem lf_eq (Q : Subgroup (CQ M)) :
    lf M Q = ⁅Q.comap (cq M) ⊓ M, Q.comap (cq M) ⊓ M⁆ := by
  unfold lf ccLift
  rw [Subgroup.map_commutator]
  have h : (Q.comap (cqM M)).map M.subtype = Q.comap (cq M) ⊓ M :=
    Subgroup.subgroupOf_map_subtype (Q.comap (cq M)) M
  rw [h]

theorem map_lf {Q : Subgroup (CQ M)} (hQ : ⁅Q, Q⁆ = Q) (hQM : Q ≤ M.map (cq M)) :
    (lf M Q).map (cq M) = Q := by
  unfold lf
  rw [Subgroup.map_map]
  exact map_ccLift (cqM M) hQ (by rwa [range_cqM])

theorem commutator_lf {Q : Subgroup (CQ M)} (hQ : ⁅Q, Q⁆ = Q) (hQM : Q ≤ M.map (cq M)) :
    ⁅lf M Q, lf M Q⁆ = lf M Q := by
  unfold lf
  rw [← Subgroup.map_commutator,
    commutator_ccLift_eq (ker_cqM_le_center M) hQ (by rwa [range_cqM])]

theorem le_lf {P : Subgroup G} {Q : Subgroup (CQ M)} (hP : P ≤ M) (hPp : ⁅P, P⁆ = P)
    (hQ : ⁅Q, Q⁆ = Q) (hQM : Q ≤ M.map (cq M)) (h : P.map (cq M) ≤ Q) : P ≤ lf M Q :=
  le_of_map_le_cq M hP (lf_le M Q) hPp (commutator_lf M hQ hQM)
    (by rw [map_lf M hQ hQM]; exact h)

theorem ker_le_center_of_le {P : Subgroup G} (hP : P ≤ M) :
    (((cq M).comp P.subtype).ker) ≤ center ↥P := by
  intro x hx
  have hx' : (x : G) ∈ centralizer (M : Set G) := (cq_eq_one_iff M).1 hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (mem_centralizer_iff.1 hx' y (hP y.2))

@[expose] def cqOn (P : Subgroup G) : ↥P →* ↥(P.map (cq M)) :=
  ((cq M).comp P.subtype).codRestrict (P.map (cq M)) (fun x => ⟨x, x.2, rfl⟩)

theorem cqOn_surjective (P : Subgroup G) : Function.Surjective (cqOn M P) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_cqOn_le_center {P : Subgroup G} (hP : P ≤ M) : (cqOn M P).ker ≤ center ↥P := by
  intro x hx
  exact ker_le_center_of_le M hP (by
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx)

theorem isQuasisimple_map_cq {P : Subgroup G} (hP : P ≤ M) (hq : CFSG.IsQuasisimple ↥P) :
    CFSG.IsQuasisimple ↥(P.map (cq M)) :=
  isQuasisimple_of_cover hq (cqOn M P) (cqOn_surjective M P) (ker_cqOn_le_center M hP)

theorem isQuasisimple_of_map_cq {P : Subgroup G} (hP : P ≤ M) (hPp : ⁅P, P⁆ = P)
    (hq : CFSG.IsQuasisimple ↥(P.map (cq M))) : CFSG.IsQuasisimple ↥P :=
  isQuasisimple_of_perfect_cover (Subgroup.isPerfect_iff.2 hPp) hq (cqOn M P)
    (cqOn_surjective M P) (ker_cqOn_le_center M hP)

theorem le_centralizer_of_map_le {P : Subgroup G} (hP : P ≤ M) (hPp : ⁅P, P⁆ = P) {U : Subgroup G}
    (h : P.map (cq M) ≤ centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M))) :
    P ≤ centralizer (U : Set G) := by
  have hc : ⁅P, U⁆ ≤ centralizer (M : Set G) := by
    refine commutator_le.2 fun x hx u hu => ?_
    rw [← cq_eq_one_iff M, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (h ⟨x, hx, rfl⟩) _ ⟨u, hu, rfl⟩).symm
  have h2 : ⁅⁅P, U⁆, P⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅⁅P, U⁆, P⁆ ≤ ⁅centralizer (M : Set G), P⁆ := Subgroup.commutator_mono hc le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.centralizer_le hP)
  have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hPp
  have h3 := CFSG.LocalCores.perfect_double_commutator (P := P) (X := U) inferInstance h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3

theorem map_le_centralizer {P U : Subgroup G} (h : P ≤ centralizer (U : Set G)) :
    P.map (cq M) ≤ centralizer ((U.map (cq M) : Subgroup (CQ M)) : Set (CQ M)) := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (h hx) u hu]

end CFSG.EvenSporadicStandard.Induction.Junction
