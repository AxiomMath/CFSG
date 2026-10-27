module

public import CFSG.ClassicalInvolution.Q3.Q3TWY11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Asc77.T7H CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.RouteD.TWE.B4 CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Twin

theorem exists_twin_inv_odd3 {m : ℕ} (hm : 3 ≤ m)
    {R R' : Subgroup (spinGroup (quadOdd m 𝔽₃))}
    (hR : R ∈ fundamentalSubgroups .POmegaOdd (oddDatum m 𝔽₃))
    (hR' : R' ∈ fundamentalSubgroups .POmegaOdd (oddDatum m 𝔽₃)) (hne : R ≠ R')
    {x x' a a' : spinGroup (quadOdd m 𝔽₃)} (hx : x ∈ R)
    (hcx : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx' : x' ∈ R') (hcx' : ∀ r ∈ R', x' * r = r * x')
    (hx'1 : x' ≠ 1) (hsame : x * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd m 𝔽₃)))
    (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center (spinGroup (quadOdd m 𝔽₃)))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center (spinGroup (quadOdd m 𝔽₃))) :
    ∃ (FM : OFrame (quadOdd m 𝔽₃))
      (g' J₁ : (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃)),
      R.map (spinAction (quadOdd m 𝔽₃)) = FM.La.range ∧
      R'.map (spinAction (quadOdd m 𝔽₃)) = FM.swap.La.range ∧
      g' = spinAction (quadOdd m 𝔽₃) (a * a') ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd m 𝔽₃) y w = 0) → g' y = y) ∧
      Module.finrank 𝔽₃ (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      J₁ = spinAction (quadOdd m 𝔽₃) a ∧
      J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) ∧
      (∀ y ∈ FM.span, J₁ y ∈ FM.span) ∧ (∀ y ∈ FM.span, J₁ (J₁ y) = -y) ∧
      (∀ y, g' (J₁ y) = J₁ (g' y)) := by
  classical
  have hadm : StatedLieAdmissible .POmegaOdd m 3 1 := ⟨Nat.prime_three, le_rfl, hm, by norm_num⟩
  have cq := centralQuot3_odd (m := m) hm
  have : Group.IsPerfect (spinGroup (quadOdd m 𝔽₃)) :=
    isPerfect_spinGroup_quadOdd two_ne_zero_gf3 hm
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hdimV : Module.finrank 𝔽₃ (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) = 2 * m + 1 :=
    Gaps.finrank_odd 3 1 m
  have hY := yData3_odd hm hadm
  obtain ⟨F₁, A, A', hF₁, hF₁', hθx, hθx', hθa, hθa', hAA, hA'A'⟩ := exists_twin_frame3 odd_gf3
    (range_spinAction_quadOdd h2 hm) (centerScalar_quadOdd h2 hm) (by omega)
    (fun F₁ F₂ h => ModelFacts.TG3.hproj_odd F₁ F₂ h) (cq.map_inj hR hR') (cq.map_mem R hR)
    (cq.map_mem R' hR') (hY.central R hR) (hY.central R' hR') hne hx hcx hx1 hx' hcx' hx'1 hsame
    ha ha' hsq hsq'
  have hθu : spinAction (quadOdd m 𝔽₃) (a * a') = twinInv F₁ A A' := by
    rw [map_mul, hθa, hθa']
    rfl
  have hdet : LinearEquiv.det (twinInv F₁ A A') = 1 := by
    rw [← hθu]
    exact det_spinAction_eq_one _
  have hii : twinInv F₁ A A' * twinInv F₁ A A' = 1 :=
    LinearEquiv.ext fun v => twinInv_twinInv F₁ hAA hA'A' v
  have hAA' : A * A = -1 := Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_mul] using hAA)
  refine ⟨F₁, twinInv F₁ A A', F₁.La A, hF₁, hF₁', hθu.symm, twinInv_mem_orthogonalGroup F₁ A A',
    hii, ?_, finrank_minusSp_twinInv h2 F₁ hAA hA'A' hdet, ?_, hθa.symm,
    F₁.La_mem_orthogonalGroup A, fun y hy => ?_, ?_, ?_⟩
  · intro y hy
    exact twinInv_perp F₁ A A' ((Frame.mem_perp_iff_forall_incl F₁).mpr fun Y => hy _ ⟨Y, rfl⟩)
  · intro y hy
    have : y ∈ eigIn (twinInv F₁ A A') (-1) F₁.span := by
      rw [← minusSp_twinInv_eq h2 F₁]
      exact hy
    exact (mem_eigIn_iff.mp this).1
  · obtain ⟨X, rfl⟩ := hy
    rw [Frame.La_apply_incl]
    exact ⟨_, rfl⟩
  · intro y hy
    have h1 : F₁.La A (F₁.La A y) = F₁.La (-1) y := by
      rw [← LinearEquiv.mul_apply, ← map_mul, hAA']
    rw [h1]
    have hy' : y ∈ negSpace (F₁.La (-1)) := by rw [negSpace_La_neg_one h2]; exact hy
    exact mem_negSpace_iff'.mp hy'
  · intro y
    show F₁.La A (F₁.swap.La A' (F₁.La A y)) = F₁.La A (F₁.La A (F₁.swap.La A' y))
    have := LinearEquiv.congr_fun (F₁.La_comm_La_swap A A') y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
    rw [← this]

end Twin

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem unip_data_odd3 {m : ℕ} (c : TCtx3 .POmegaOdd m Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    {J : Subgroup G} (hJz : J ∈ centralizingMembers Ω {z})
    {RJ : Subgroup (spinGroup (quadOdd m 𝔽₃))}
    (hRJ : RJ ∈ fundamentalSubgroups .POmegaOdd (oddDatum m 𝔽₃))
    (hJR : locImg Ω z J = RJ.map c.d.ψ) (hJt : conjSub t J = J) {x : G} (hxJ : x ∈ J)
    (hx1 : x ≠ 1) (hxp : x ^ 3 = 1) (hxinv : t * x * t⁻¹ = x⁻¹)
    {α : spinGroup (quadOdd m 𝔽₃) ≃* spinGroup (quadOdd m 𝔽₃)}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) :
    (∀ y ∈ RJ, α y ∈ RJ) ∧ ∃ x₀ ∈ RJ, x₀ ≠ 1 ∧ x₀ ^ 3 = 1 ∧ α x₀ = x₀⁻¹ := by
  classical
  have hΩ := c.hΩ
  let θ : spinGroup (quadOdd m 𝔽₃) →* locQuot Ω z := c.d.ψ
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd m 𝔽₃)) := c.d.ker_le
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
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ : spinGroup (quadOdd m 𝔽₃), r₀ ∈ RJ ∧
      θ r₀ = locMk Ω z ⟨x, hxL⟩ := by
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
  have hk : r₀ * α r₀ ∈ Subgroup.center (spinGroup (quadOdd m 𝔽₃)) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, hψα, map_inv, mul_inv_cancel])
  have hkR : r₀ * α r₀ ∈ RJ := RJ.mul_mem hr₀ (hαRJ r₀ hr₀)
  exact eq_inv_of_mul_eq_one_right (c.hY.central RJ hRJ _ hkR hk)

theorem twin_datum_odd3 {m : ℕ} (hm : 3 ≤ m) (c : TCtx3 .POmegaOdd m Ω K z)
    {M J' : Subgroup G} {w : G}
    (hMz : M ∈ centralizingMembers Ω {z}) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hwM : IsClassicalMember3 M w) (hwJ' : IsClassicalMember3 J' w)
    (e' : TwinElt M J' w) (hMJ' : M ≠ J')
    {RzM RJ' : Subgroup (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K}
    (hRzM : RzM ∈
      fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D)
    (hMR : locImg Ω z M = RzM.map c.d.ψ)
    (hRJ' : RJ' ∈
      fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D)
    (hJ'R : locImg Ω z J' = RJ'.map c.d.ψ) :
    ∃ (FM : OFrame (quadOdd m 𝔽₃))
      (g' J₁ : (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃) ≃ₗ[𝔽₃] (Fin m ⊕ Fin m ⊕ Unit → 𝔽₃)),
      RzM.map (spinAction (quadOdd m 𝔽₃)) = FM.La.range ∧
      RJ'.map (spinAction (quadOdd m 𝔽₃)) = FM.swap.La.range ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd m 𝔽₃) y w = 0) → g' y = y) ∧
      Module.finrank 𝔽₃ (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      J₁ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd m 𝔽₃) ∧
      (∀ y ∈ FM.span, J₁ y ∈ FM.span) ∧ (∀ y ∈ FM.span, J₁ (J₁ y) = -y) ∧
      (∀ y, g' (J₁ y) = J₁ (g' y)) ∧
      ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K},
        (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → Pow3 RN →
        ∀ l ∈ RN.map (spinAction (quadOdd m 𝔽₃)), g' * l = l * g' := by
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
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K}
      {y : (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K}, (∀ k ∈ L, w * k = k * w) →
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
  have hsame : r * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K :=
    c.d.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψr, hψr', mul_inv_cancel])
  have haM : locElt Ω z e'.a (hYM e'.mem_a) ∈ locImg Ω z M := locElt_mem_locImg hYM e'.mem_a
  rw [hMR] at haM
  obtain ⟨ã, hãR, hψã⟩ := haM
  have haJ : locElt Ω z e'.a' (hYJ e'.mem_a') ∈ locImg Ω z J' := locElt_mem_locImg hYJ e'.mem_a'
  rw [hJ'R] at haJ
  obtain ⟨ã', hã'R, hψã'⟩ := haJ
  have hsq : ã * ã * r⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã, hψr, locElt_mul,
        hlcongr _ hwY e'.mul_self_a, mul_inv_cancel])
  have hsq' : ã' * ã' * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã', hψr', locElt_mul,
        hlcongr _ hwY e'.mul_self_a', mul_inv_cancel])
  have hne_RJ : RzM ≠ RJ' := fun h =>
    hMJ' (c.eq_of_locImg_eq hMz hJ'z (by rw [hMR, hJ'R, h]))
  obtain ⟨FM, g', J₁, hFM, hFM', hg'eq, hg'O, hg'2, hg'fix, hg'dim, hg'le, -, hJ₁O, hJ₁span,
    hJ₁sq, hJ₁comm⟩ := exists_twin_inv_odd3 hm
    hRzM hRJ' hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hMR (c.hY.pow3 _ hRzM) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJ'R (c.hY.pow3 _ hRJ') hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  refine ⟨FM, g', J₁, hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hJ₁O, hJ₁span, hJ₁sq, hJ₁comm,
    ?_⟩
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
  exact congrArg (spinAction (quadOdd m 𝔽₃)) (hcomm s hs)

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
