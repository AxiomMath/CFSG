module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.RouteD.TWEB6Star
public import CFSG.ClassicalInvolution.RouteD.TWT9Twin
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)

set_option linter.unusedSectionVars false

theorem map_comm_of_comm {M N : Type} [Group M] [Group N] (π : M →* N) {A : Subgroup M} {x : M}
    (h : ∀ s ∈ A, x * s = s * x) : ∀ l ∈ A.map π, π x * l = l * π x := by
  rintro _ ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, h s hs]

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}



theorem twin_lift_td4 (c : TCtx p f .POmegaMinus 4 Ω K z) {M J' : Subgroup G} {w : G}
    (hMz : M ∈ centralizingMembers Ω {z}) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hwM : IsClassicalMember p f M w) (hwJ' : IsClassicalMember p f J' w)
    (e' : TwinElt M J' w) (hMJ' : M ≠ J')
    {RzM RJ' : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K}
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D)
    (hMR : locImg Ω z M = RzM.map c.d.ψ)
    (hRJ' : RJ' ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D)
    (hJ'R : locImg Ω z J' = RJ'.map c.d.ψ) :
    ∃ ĉ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
      (∀ hy : e'.a * e'.a' ∈ locLayer Ω z, c.d.ψ ĉ = locElt Ω z (e'.a * e'.a') hy) ∧
      spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ ∈
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) ∧
      spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ *
        spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ =
        1 ∧
      Module.finrank (GaloisField p f) (negSpace (spinAction (quadMinus 4 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ)) = 2 ∧
      ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K},
        (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → RN ≤ ⁅RN, RN⁆ →
        ∀ l ∈ RN.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)), spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) ĉ * l = l * spinAction (quadMinus 4 (GaloisField p f)
          (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ := by
  classical
  have hYM : M ≤ locLayer Ω z := le_centralizingLayer hMz
  have hYJ : J' ≤ locLayer Ω z := le_centralizingLayer hJ'z
  have hwY : w ∈ locLayer Ω z := hYM hwM.mem
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund c hMz hRzM hMR hwM
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund c hJ'z hRJ' hJ'R hwJ'
  have hlcongr : ∀ {y y' : G} (hy : y ∈ locLayer Ω z) (hy' : y' ∈ locLayer Ω z), y = y' →
      locElt Ω z y hy = locElt Ω z y' hy' := by
    intro y y' hy hy' h
    subst h
    rfl
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K}
      {y : (modelUniv .POmegaMinus 4 p f Fact.out).K}, (∀ k ∈ L, w * k = k * w) →
      locImg Ω z L = R.map c.d.ψ → R ≤ ⁅R, R⁆ → c.d.ψ y = locElt Ω z w hwY →
      ∀ s ∈ R, y * s = s * y := by
    intro L R y hzL hLR hRp hy
    refine commutes_of_commutator_mem_center hRp fun s hs => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hy]
    have hsL : c.d.ψ s ∈ locImg Ω z L := hLR ▸ Subgroup.mem_map_of_mem _ hs
    obtain ⟨k, hk, hks⟩ := hsL
    rw [← hks]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    show locMk Ω z ⟨w, hwY⟩ * locMk Ω z k = locMk Ω z k * locMk Ω z ⟨w, hwY⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hzL k (Subgroup.mem_subgroupOf.mp hk)
  have hr1 : r ≠ 1 := fun h => by
    have := hr.2
    rw [h, orderOf_one] at this
    omega
  have hr'1 : r' ≠ 1 := fun h => by
    have := hr'.2
    rw [h, orderOf_one] at this
    omega
  have hsame : r * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K :=
    c.d.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψr, hψr', mul_inv_cancel])
  have haM : locElt Ω z e'.a (hYM e'.mem_a) ∈ locImg Ω z M := locElt_mem_locImg hYM e'.mem_a
  rw [hMR] at haM
  obtain ⟨ã, hãR, hψã⟩ := haM
  have haJ : locElt Ω z e'.a' (hYJ e'.mem_a') ∈ locImg Ω z J' := locElt_mem_locImg hYJ e'.mem_a'
  rw [hJ'R] at haJ
  obtain ⟨ã', hã'R, hψã'⟩ := haJ
  have hsq : ã * ã * r⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã, hψr, locElt_mul,
        hlcongr _ hwY e'.mul_self_a, mul_inv_cancel])
  have hsq' : ã' * ã' * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã', hψr', locElt_mul,
        hlcongr _ hwY e'.mul_self_a', mul_inv_cancel])
  have hne_RJ : RzM ≠ RJ' := fun h =>
    hMJ' (c.eq_of_locImg_eq hMz hJ'z (by rw [hMR, hJ'R, h]))
  obtain ⟨FM, g', hFM, hFM', hg'eq, hg'O, hg'2, -, hg'dim, -, -⟩ :=
    TWT9.exists_twin_inv_four
    c.hp2 c.hq hRzM hRJ' hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hMR (c.hY.perfR _ hRzM) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJ'R (c.hY.perfR _ hRJ') hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  have hψu : c.d.ψ (ã * ã') = locElt Ω z (e'.a * e'.a')
      ((locLayer Ω z).mul_mem (hYM e'.mem_a) (hYJ e'.mem_a')) := by
    rw [map_mul, hψã, hψã', locElt_mul]
  refine ⟨ã * ã', fun hy => hψu, hg'eq ▸ hg'O, hg'eq ▸ hg'2, hg'eq ▸ hg'dim, ?_⟩
  intro N RN hNu hNR hRp
  have hcomm : ∀ s ∈ RN, ã * ã' * s = s * (ã * ã') := by
    refine commutes_of_commutator_mem_center hRp fun s hs => c.d.ker_le ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hψu]
    have hsL : c.d.ψ s ∈ locImg Ω z N := hNR ▸ Subgroup.mem_map_of_mem _ hs
    obtain ⟨k, hk, hks⟩ := hsL
    rw [← hks]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    show locMk Ω z ⟨e'.a * e'.a', _⟩ * locMk Ω z k = locMk Ω z k * locMk Ω z ⟨e'.a * e'.a', _⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hNu k (Subgroup.mem_subgroupOf.mp hk)).symm
  exact fun l hl => map_comm_of_comm (spinAction (quadMinus 4 (GaloisField p f)
    (minusCoeffs p f).1 (minusCoeffs p f).2)) hcomm l hl

end Group

end CFSG.ClassicalInvolution.RouteD.TWU
