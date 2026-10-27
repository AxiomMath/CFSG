module

public import CFSG.ClassicalInvolution.RouteD.TWT8Model
public import CFSG.ClassicalInvolution.RouteD.TWT9Twin
public import CFSG.ClassicalInvolution.RouteD.TWT8V
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalInvolution.RouteD.TWT8 (BridgeOmega)
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)

set_option linter.unusedSectionVars false

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem unip_data_td4 (c : TCtx p f .POmegaMinus 4 Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    {J : Subgroup G} (hJz : J ∈ centralizingMembers Ω {z})
    {RJ : Subgroup (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRJ : RJ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr p f)))
    (hJR : locImg Ω z J = RJ.map c.d.ψ) (hJt : conjSub t J = J) {x : G} (hxJ : x ∈ J)
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxinv : t * x * t⁻¹ = x⁻¹)
    {α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
      spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) :
    (∀ y ∈ RJ, α y ∈ RJ) ∧ ∃ x₀ ∈ RJ, x₀ ≠ 1 ∧ x₀ ^ p = 1 ∧ α x₀ = x₀⁻¹ := by
  classical
  have hΩ := c.hΩ
  let θ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →*
      locQuot Ω z := c.d.ψ
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) := c.d.ker_le
  have hαθ' : ∀ y, θ (α y) = locAut hΩ.conjInvariant htz (θ y) := hαθ
  have hJR' : locImg Ω z J = RJ.map θ := hJR
  have hstab : ∀ y ∈ RJ, locAut hΩ.conjInvariant htz (θ y) ∈ RJ.map θ := by
    intro y hy
    have h1 : θ y ∈ locImg Ω z J := by
      rw [hJR']
      exact ⟨y, hy, rfl⟩
    have h2 : locAut hΩ.conjInvariant htz (θ y) ∈
        (locImg Ω z J).map (locAut hΩ.conjInvariant htz).toMonoidHom := ⟨_, h1, rfl⟩
    rw [locAut_locImg hΩ.conjInvariant htz, hJt, hJR'] at h2
    exact h2
  have hperf : ⁅RJ, RJ⁆ = RJ := le_antisymm
    (Subgroup.commutator_le.mpr fun a ha b hb =>
      RJ.mul_mem (RJ.mul_mem (RJ.mul_mem ha hb) (RJ.inv_mem ha)) (RJ.inv_mem hb))
    (c.hY.perfR _ hRJ)
  have hαRJ : ∀ y ∈ RJ, α y ∈ RJ :=
    TWE.B4.mem_of_stable θ hker α (locAut hΩ.conjInvariant htz) hαθ' hperf hstab
  refine ⟨hαRJ, ?_⟩
  have hxL : x ∈ locLayer Ω z := le_centralizingLayer hJz hxJ
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2), r₀ ∈ RJ ∧ θ r₀ = locMk Ω z ⟨x, hxL⟩ := by
    have : locMk Ω z ⟨x, hxL⟩ ∈ RJ.map θ := by
      rw [← hJR']
      exact ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hxJ, rfl⟩
    obtain ⟨r, hr, hrx⟩ := this
    exact ⟨r, hr, hrx⟩
  have hψx1 : θ r₀ ≠ 1 := by
    rw [hr₀x]
    intro h
    have h1 : locMk Ω z ⟨x, hxL⟩ = locMk Ω z 1 := by rw [h, map_one]
    have := Exotic.locMk_inj_of_member c.hex hJz (b := 1) hxJ (one_mem _) h1
    exact hx1 (by simpa using congrArg Subtype.val this)
  have hr₀1 : r₀ ≠ 1 := fun h => hψx1 (by rw [h, map_one])
  have hr₀p : r₀ ^ p = 1 := by
    have h1 : θ (r₀ ^ p) = 1 := by
      rw [map_pow, hr₀x, ← map_pow]
      have : (⟨x, hxL⟩ : ↥(locLayer Ω z)) ^ p = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    exact c.hY.central RJ hRJ (r₀ ^ p) (pow_mem hr₀ p) (hker (MonoidHom.mem_ker.mpr h1))
  refine ⟨r₀, hr₀, hr₀1, hr₀p, ?_⟩
  have hψα : θ (α r₀) = θ r₀⁻¹ := by
    rw [hαθ', map_inv, hr₀x, ← map_inv]
    show locMk Ω z (layerAut hΩ.conjInvariant htz ⟨x, hxL⟩) = _
    congr 1
    apply Subtype.ext
    simpa [coe_layerAut] using hxinv
  have hk : r₀ * α r₀ ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, hψα, map_inv, mul_inv_cancel])
  have hkR : r₀ * α r₀ ∈ RJ := RJ.mul_mem hr₀ (hαRJ r₀ hr₀)
  exact eq_inv_of_mul_eq_one_right (c.hY.central RJ hRJ _ hkR hk)

theorem twin_datum_td4 (c : TCtx p f .POmegaMinus 4 Ω K z) {M J' : Subgroup G} {w : G}
    (hMz : M ∈ centralizingMembers Ω {z}) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hwM : IsClassicalMember p f M w) (hwJ' : IsClassicalMember p f J' w)
    (e' : TwinElt M J' w) (hMJ' : M ≠ J')
    {RzM RJ' : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K}
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D)
    (hMR : locImg Ω z M = RzM.map c.d.ψ)
    (hRJ' : RJ' ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p f Fact.out).D)
    (hJ'R : locImg Ω z J' = RJ'.map c.d.ψ) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (quadMinus 4 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2))
      (g' : Vm 4 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 4 (GaloisField p f)),
      RzM.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = FM.La.range ∧
      RJ'.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = FM.swap.La.range ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField p f) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      (¬ IsSquare (-1 : GaloisField p f) → ∀ y ∈ FM.span, g' y = y → y ≠ 0 →
        quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2 y ≠ 0) ∧
      ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaMinus 4 p f Fact.out).K},
        (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → RN ≤ ⁅RN, RN⁆ →
        ∀ l ∈ RN.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)), g' * l = l * g' := by
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
  obtain ⟨FM, g', hFM, hFM', hg'eq, hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an⟩ :=
    TWT9.exists_twin_inv_four
    c.hp2 c.hq hRzM hRJ' hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hMR (c.hY.perfR _ hRzM) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJ'R (c.hY.perfR _ hRJ') hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  refine ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an, ?_⟩
  intro N RN hNu hNR hRp
  have hψu : c.d.ψ (ã * ã') = locElt Ω z (e'.a * e'.a')
      ((locLayer Ω z).mul_mem (hYM e'.mem_a) (hYJ e'.mem_a')) := by
    rw [map_mul, hψã, hψã', locElt_mul]
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
  rintro _ ⟨s, hs, rfl⟩
  rw [hg'eq, ← map_mul, ← map_mul]
  exact congrArg (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2)) (hcomm s hs)

end Group

end CFSG.ClassicalInvolution.RouteD.TWT9
