module

public import CFSG.ClassicalInvolution.Q3.Q3TY16
public import CFSG.ClassicalInvolution.RouteD.TWT9Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Base

variable {K : Type} [Group K]

theorem mem_of_stable3 {X : Type} [Group X] (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K)
    (hcop : ∀ z ∈ θ.ker, ¬ 3 ∣ orderOf z) (α : K ≃* K) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {R : Subgroup K} (hR : Pow3 R)
    (hstab : ∀ y ∈ R, σ (θ y) ∈ R.map θ) : ∀ y ∈ R, α y ∈ R := by
  have hle : R.map α.toMonoidHom ≤ R := by
    refine le_of_map_le_of_pow3 θ hker hcop (hR.map α.toMonoidHom) ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show θ (α y) ∈ R.map θ
    rw [hαθ]
    exact hstab y hy
  intro y hy
  exact hle ⟨y, hy, rfl⟩

theorem commutes_of_commutator_mem_center3 (hcop : ∀ z ∈ Subgroup.center K, ¬ 3 ∣ orderOf z)
    {R : Subgroup K} (hR : Pow3 R) {x : K} (hx : ∀ r ∈ R, ⁅x, r⁆ ∈ Subgroup.center K) :
    ∀ r ∈ R, x * r = r * x := by
  have conjEq : ∀ r ∈ R, x * r * x⁻¹ = r * ⁅x, r⁆ := fun r hr => by
    rw [Subgroup.mem_center_iff.mp (hx r hr) r, commutatorElement_def]
    group
  have hle : ⁅R, R⁆ ≤ Subgroup.centralizer ({x} : Set K) := by
    refine Subgroup.commutator_le.mpr fun r₁ hr₁ r₂ hr₂ =>
      Subgroup.mem_centralizer_singleton_iff.mpr ?_
    symm
    calc x * ⁅r₁, r₂⁆ = (x * ⁅r₁, r₂⁆ * x⁻¹) * x := by group
      _ = ⁅x * r₁ * x⁻¹, x * r₂ * x⁻¹⁆ * x := by rw [conjugate_commutatorElement]
      _ = ⁅r₁ * ⁅x, r₁⁆, r₂ * ⁅x, r₂⁆⁆ * x := by rw [conjEq r₁ hr₁, conjEq r₂ hr₂]
      _ = ⁅r₁, r₂⁆ * x := by
        rw [CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_left _ _ _
            (hx r₁ hr₁),
          CFSG.ComponentClassification.CentralExtensions.commutator_mul_center_right _ _ _
            (hx r₂ hr₂)]
  intro r hr
  have hkc : ⁅x, r⁆ ∈ Subgroup.center K := hx r hr
  have h3 : r ^ 3 * x = x * r ^ 3 :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle (hR r hr))
  have e1 : x * r ^ 3 * x⁻¹ = (r * ⁅x, r⁆) ^ 3 := by
    have : x * r ^ 3 * x⁻¹ = (x * r * x⁻¹) ^ 3 := by simp
    rw [this, conjEq r hr]
  have hcomm : Commute r ⁅x, r⁆ := Subgroup.mem_center_iff.mp hkc r
  have e2 : x * r ^ 3 * x⁻¹ = r ^ 3 := by rw [← h3]; group
  have hk3 : ⁅x, r⁆ ^ 3 = 1 := by
    have : r ^ 3 * ⁅x, r⁆ ^ 3 = r ^ 3 := by rw [← hcomm.mul_pow, ← e1, e2]
    exact mul_eq_left.mp this
  have hk1 : ⁅x, r⁆ = 1 := by
    by_contra hne
    have h3' : orderOf ⁅x, r⁆ = 3 := orderOf_eq_prime hk3 hne
    exact hcop _ hkc (by rw [h3'])
  have := conjEq r hr
  rw [hk1, mul_one] at this
  exact (mul_inv_eq_iff_eq_mul.mp this)

end Base

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}



theorem exists_involution_of_fund3 {tY : StatedLieTag} {nY : ℕ} {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} {N : Subgroup G} {x : G} (cx : TCtx3 tY nY Ω N x) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x})
    {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) {w : G} (hw : IsClassicalMember3 L w) :
    ∃ r, InvOf R r ∧ cx.d.ψ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map cx.d.ψ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (cx.d.ψ r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : cx.d.ψ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (cx.d.ψ r)
      rwa [h2, pow_two] at this
    exact cx.hY.central R hR (r * r) (R.mul_mem hrR hrR) (cx.d.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem unip_data_td4_3 (c : TCtx3 .POmegaMinus 4 Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    {J : Subgroup G} (hJz : J ∈ centralizingMembers Ω {z})
    {RJ : Subgroup (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hRJ : RJ ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)))
    (hJR : locImg Ω z J = RJ.map c.d.ψ) (hJt : conjSub t J = J) {x : G} (hxJ : x ∈ J)
    (hx1 : x ≠ 1) (hxp : x ^ 3 = 1) (hxinv : t * x * t⁻¹ = x⁻¹)
    {α : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ≃*
      spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) :
    (∀ y ∈ RJ, α y ∈ RJ) ∧ ∃ x₀ ∈ RJ, x₀ ≠ 1 ∧ x₀ ^ 3 = 1 ∧ α x₀ = x₀⁻¹ := by
  classical
  have hΩ := c.hΩ
  let θ : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →*
      locQuot Ω z := c.d.ψ
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := c.d.ker_le
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
  have hαRJ : ∀ y ∈ RJ, α y ∈ RJ :=
    mem_of_stable3 θ hker c.ker_cop α (locAut hΩ.conjInvariant htz) hαθ' (c.hY.pow3 _ hRJ) hstab
  refine ⟨hαRJ, ?_⟩
  have hxL : x ∈ locLayer Ω z := le_centralizingLayer hJz hxJ
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2), r₀ ∈ RJ ∧ θ r₀ = locMk Ω z ⟨x, hxL⟩ := by
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
  have hr₀p : r₀ ^ 3 = 1 := by
    have h1 : θ (r₀ ^ 3) = 1 := by
      rw [map_pow, hr₀x, ← map_pow]
      have : (⟨x, hxL⟩ : ↥(locLayer Ω z)) ^ 3 = 1 := Subtype.ext (by simpa using hxp)
      rw [this, map_one]
    exact c.hY.central RJ hRJ (r₀ ^ 3) (pow_mem hr₀ 3) (hker (MonoidHom.mem_ker.mpr h1))
  refine ⟨r₀, hr₀, hr₀1, hr₀p, ?_⟩
  have hψα : θ (α r₀) = θ r₀⁻¹ := by
    rw [hαθ', map_inv, hr₀x, ← map_inv]
    show locMk Ω z (layerAut hΩ.conjInvariant htz ⟨x, hxL⟩) = _
    congr 1
    apply Subtype.ext
    simpa [coe_layerAut] using hxinv
  have hk : r₀ * α r₀ ∈ Subgroup.center (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, hψα, map_inv, mul_inv_cancel])
  have hkR : r₀ * α r₀ ∈ RJ := RJ.mul_mem hr₀ (hαRJ r₀ hr₀)
  exact eq_inv_of_mul_eq_one_right (c.hY.central RJ hRJ _ hkR hk)


theorem twin_datum_td4_3 (c : TCtx3 .POmegaMinus 4 Ω K z) {M J' : Subgroup G} {w : G}
    (hMz : M ∈ centralizingMembers Ω {z}) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hwM : IsClassicalMember3 M w) (hwJ' : IsClassicalMember3 J' w)
    (e' : TwinElt M J' w) (hMJ' : M ≠ J')
    {RzM RJ' : Subgroup (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K}
    (hRzM : RzM ∈
      fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).D)
    (hMR : locImg Ω z M = RzM.map c.d.ψ)
    (hRJ' : RJ' ∈
      fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).D)
    (hJ'R : locImg Ω z J' = RJ'.map c.d.ψ) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (quadMinus 4 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
      (g' : Vm 4 (GaloisField 3 1) ≃ₗ[GaloisField 3 1] Vm 4 (GaloisField 3 1)),
      RzM.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = FM.La.range ∧
      RJ'.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = FM.swap.La.range ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField 3 1) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      (¬ IsSquare (-1 : GaloisField 3 1) → ∀ y ∈ FM.span, g' y = y → y ≠ 0 →
        quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2 y ≠ 0) ∧
      ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K},
        (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → Pow3 RN →
        ∀ l ∈ RN.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2)), g' * l = l * g' := by
  classical
  have hYM : M ≤ locLayer Ω z := le_centralizingLayer hMz
  have hYJ : J' ≤ locLayer Ω z := le_centralizingLayer hJ'z
  have hwY : w ∈ locLayer Ω z := hYM hwM.mem
  obtain ⟨r, hr, hψr⟩ := exists_involution_of_fund3 c hMz hRzM hMR hwM
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund3 c hJ'z hRJ' hJ'R hwJ'
  have hlcongr : ∀ {y y' : G} (hy : y ∈ locLayer Ω z) (hy' : y' ∈ locLayer Ω z), y = y' →
      locElt Ω z y hy = locElt Ω z y' hy' := by
    intro y y' hy hy' h
    subst h
    rfl
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K}
      {y : (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K}, (∀ k ∈ L, w * k = k * w) →
      locImg Ω z L = R.map c.d.ψ → Pow3 R → c.d.ψ y = locElt Ω z w hwY →
      ∀ s ∈ R, y * s = s * y := by
    intro L R y hzL hLR hRp hy
    refine commutes_of_commutator_mem_center3 c.hY.cop hRp fun s hs => c.d.ker_le ?_
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
  have hsame : r * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K :=
    c.d.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψr, hψr', mul_inv_cancel])
  have haM : locElt Ω z e'.a (hYM e'.mem_a) ∈ locImg Ω z M := locElt_mem_locImg hYM e'.mem_a
  rw [hMR] at haM
  obtain ⟨ã, hãR, hψã⟩ := haM
  have haJ : locElt Ω z e'.a' (hYJ e'.mem_a') ∈ locImg Ω z J' := locElt_mem_locImg hYJ e'.mem_a'
  rw [hJ'R] at haJ
  obtain ⟨ã', hã'R, hψã'⟩ := haJ
  have hsq : ã * ã * r⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã, hψr, locElt_mul,
        hlcongr _ hwY e'.mul_self_a, mul_inv_cancel])
  have hsq' : ã' * ã' * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaMinus 4 3 1 Nat.prime_three).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã', hψr', locElt_mul,
        hlcongr _ hwY e'.mul_self_a', mul_inv_cancel])
  have hne_RJ : RzM ≠ RJ' := fun h =>
    hMJ' (c.eq_of_locImg_eq hMz hJ'z (by rw [hMR, hJ'R, h]))
  obtain ⟨FM, g', hFM, hFM', hg'eq, hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an⟩ :=
    exists_twin_inv_four3
    hRzM hRJ' hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hMR (c.hY.pow3 _ hRzM) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJ'R (c.hY.pow3 _ hRJ') hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  refine ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an, ?_⟩
  intro N RN hNu hNR hRp
  have hψu : c.d.ψ (ã * ã') = locElt Ω z (e'.a * e'.a')
      ((locLayer Ω z).mul_mem (hYM e'.mem_a) (hYJ e'.mem_a')) := by
    rw [map_mul, hψã, hψã', locElt_mul]
  have hcomm : ∀ s ∈ RN, ã * ã' * s = s * (ã * ã') := by
    refine commutes_of_commutator_mem_center3 c.hY.cop hRp fun s hs => c.d.ker_le ?_
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
  exact congrArg (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
    (minusCoeffs 3 1).2)) (hcomm s hs)


end Group

end CFSG.ClassicalInvolution.Q3.Q3TY
