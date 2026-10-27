module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Twin
public import CFSG.ClassicalInvolution.RouteD.TWEB4Rec
public import CFSG.ClassicalInvolution.RouteD.TWEB4Class
public import CFSG.ClassicalInvolution.RouteD.TWEB6Scalar
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourLift
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)

set_option linter.unusedSectionVars false

section Stable

variable {G X : Type} [Group G] [Group X]

theorem commutator_mul_center_left {a b c : G} (hc : c ∈ Subgroup.center G) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h : c * b * c⁻¹ = b := mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp hc b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * b * (a * c)⁻¹ * b⁻¹ = a * (c * b * c⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem commutator_mul_center_right {a b c : G} (hc : c ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h : c * a⁻¹ * c⁻¹ = a⁻¹ :=
    mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_center_iff.mp hc a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹ * c⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem mem_of_stable (θ : G →* X) (hker : θ.ker ≤ Subgroup.center G) (α : G ≃* G) (σ : X ≃* X)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {R : Subgroup G} (hR : ⁅R, R⁆ = R)
    (hstab : ∀ y ∈ R, σ (θ y) ∈ R.map θ) : ∀ y ∈ R, α y ∈ R := by
  have hdecomp : ∀ y ∈ R, ∃ r ∈ R, ∃ c ∈ Subgroup.center G, α y = r * c := by
    intro y hy
    obtain ⟨r, hr, hθr⟩ := hstab y hy
    refine ⟨r, hr, r⁻¹ * α y, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθr, hαθ, inv_mul_cancel]
  have hle : R.map α.toMonoidHom ≤ R := by
    have h1 : R.map α.toMonoidHom = ⁅R.map α.toMonoidHom, R.map α.toMonoidHom⁆ := by
      rw [← Subgroup.map_commutator, hR]
    rw [h1]
    refine Subgroup.commutator_le.mpr ?_
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    obtain ⟨r₁, hr₁, c₁, hc₁, h₁⟩ := hdecomp y₁ hy₁
    obtain ⟨r₂, hr₂, c₂, hc₂, h₂⟩ := hdecomp y₂ hy₂
    have e₁ : α.toMonoidHom y₁ = r₁ * c₁ := h₁
    have e₂ : α.toMonoidHom y₂ = r₂ * c₂ := h₂
    rw [e₁, e₂, commutator_mul_center_left hc₁, commutator_mul_center_right hc₂]
    exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₂) (R.inv_mem hr₁)) (R.inv_mem hr₂)
  intro y hy
  exact hle ⟨y, hy, rfl⟩

end Stable

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


local macro "b4_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem exists_layer_leaf (c : TCtx p f .POmegaOdd 4 Ω K z) {M : Subgroup G}
    (nd : DNodes p f 4 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) :
    ∃ b : Fin 4, 2 ≤ b.val ∧ nd.J b ∈ centralizingMembers Ω {z} ∧ nd.J b ≠ K ∧
      ¬ locImg Ω z (nd.J b) ≤ c.d.Q₁ := by
  have hΩ := c.hΩ
  have hKJ : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by b4_idx)) (by b4_idx)
  have hJz : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hJK : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ≠ K := fun a h ha => by
    rw [← h0]
    exact (nd.ne_J hΩ (fin_ne_of_val_ne (by b4_idx))).symm
  by_cases hQ2 : locImg Ω z (nd.J ⟨2, by omega⟩) ≤ c.d.Q₁
  · refine ⟨⟨3, by omega⟩, by norm_num, hJz 3 (by omega) (by omega), hJK 3 (by omega) (by omega),
      fun hQ3 => ?_⟩
    have := c.eq_of_locImg_le_Q₁ (hJz 2 (by omega) (by omega)) (hJz 3 (by omega) (by omega))
      hQ2 hQ3
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by b4_idx)) this
  · exact ⟨⟨2, by omega⟩, by norm_num, hJz 2 (by omega) (by omega), hJK 2 (by omega) (by omega),
      hQ2⟩

theorem unip_data_b4 (c : TCtx p f .POmegaOdd 4 Ω K z) {t : G} (htz : t * z * t⁻¹ = z)
    {J : Subgroup G} (hJz : J ∈ centralizingMembers Ω {z})
    {RJ : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))}
    (hRJ : RJ ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f)))
    (hJR : locImg Ω z J = RJ.map c.d.ψ) (hJt : conjSub t J = J) {x : G} (hxJ : x ∈ J)
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxinv : t * x * t⁻¹ = x⁻¹)
    {α : spinGroup (quadOdd 4 (GaloisField p f)) ≃* spinGroup (quadOdd 4 (GaloisField p f))}
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) :
    (∀ y ∈ RJ, α y ∈ RJ) ∧ ∃ x₀ ∈ RJ, x₀ ≠ 1 ∧ x₀ ^ p = 1 ∧ α x₀ = x₀⁻¹ := by
  classical
  have hΩ := c.hΩ
  let θ : spinGroup (quadOdd 4 (GaloisField p f)) →* locQuot Ω z := c.d.ψ
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd 4 (GaloisField p f))) := c.d.ker_le
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
    mem_of_stable θ hker α (locAut hΩ.conjInvariant htz) hαθ' hperf hstab
  refine ⟨hαRJ, ?_⟩
  have hxL : x ∈ locLayer Ω z := le_centralizingLayer hJz hxJ
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ : spinGroup (quadOdd 4 (GaloisField p f)), r₀ ∈ RJ ∧
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
  have hk : r₀ * α r₀ ∈ Subgroup.center (spinGroup (quadOdd 4 (GaloisField p f))) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, hψα, map_inv, mul_inv_cancel])
  have hkR : r₀ * α r₀ ∈ RJ := RJ.mul_mem hr₀ (hαRJ r₀ hr₀)
  exact eq_inv_of_mul_eq_one_right (c.hY.central RJ hRJ _ hkR hk)

theorem twin_datum_b4 (c : TCtx p f .POmegaOdd 4 Ω K z) {M J' : Subgroup G} {w : G}
    (hMz : M ∈ centralizingMembers Ω {z}) (hJ'z : J' ∈ centralizingMembers Ω {z})
    (hwM : IsClassicalMember p f M w) (hwJ' : IsClassicalMember p f J' w)
    (e' : TwinElt M J' w) (hMJ' : M ≠ J')
    {RzM RJ' : Subgroup (modelUniv .POmegaOdd 4 p f Fact.out).K}
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 4 p f Fact.out).D)
    (hMR : locImg Ω z M = RzM.map c.d.ψ)
    (hRJ' : RJ' ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 4 p f Fact.out).D)
    (hJ'R : locImg Ω z J' = RJ'.map c.d.ψ) :
    ∃ (FM : CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame (quadOdd 4 (GaloisField p f)))
      (g' : (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f) ≃ₗ[GaloisField p f]
        (Fin 4 ⊕ Fin 4 ⊕ Unit → GaloisField p f)),
      RzM.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.La.range ∧
      RJ'.map (spinAction (quadOdd 4 (GaloisField p f))) = FM.swap.La.range ∧
      g' ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 4 (GaloisField p f)) ∧ g' * g' = 1 ∧
      (∀ y, (∀ w ∈ FM.span, polar (quadOdd 4 (GaloisField p f)) y w = 0) → g' y = y) ∧
      Module.finrank (GaloisField p f) (negSpace g') = 2 ∧ negSpace g' ≤ FM.span ∧
      ∀ {N : Subgroup G} {RN : Subgroup (modelUniv .POmegaOdd 4 p f Fact.out).K},
        (∀ n ∈ N, n * e'.u = e'.u * n) → locImg Ω z N = RN.map c.d.ψ → RN ≤ ⁅RN, RN⁆ →
        ∀ l ∈ RN.map (spinAction (quadOdd 4 (GaloisField p f))), g' * l = l * g' := by
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
  have hcentral : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaOdd 4 p f Fact.out).K}
      {y : (modelUniv .POmegaOdd 4 p f Fact.out).K}, (∀ k ∈ L, w * k = k * w) →
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
  have hsame : r * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 4 p f Fact.out).K :=
    c.d.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψr, hψr', mul_inv_cancel])
  have haM : locElt Ω z e'.a (hYM e'.mem_a) ∈ locImg Ω z M := locElt_mem_locImg hYM e'.mem_a
  rw [hMR] at haM
  obtain ⟨ã, hãR, hψã⟩ := haM
  have haJ : locElt Ω z e'.a' (hYJ e'.mem_a') ∈ locImg Ω z J' := locElt_mem_locImg hYJ e'.mem_a'
  rw [hJ'R] at haJ
  obtain ⟨ã', hã'R, hψã'⟩ := haJ
  have hsq : ã * ã * r⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 4 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã, hψr, locElt_mul,
        hlcongr _ hwY e'.mul_self_a, mul_inv_cancel])
  have hsq' : ã' * ã' * r'⁻¹ ∈ Subgroup.center (modelUniv .POmegaOdd 4 p f Fact.out).K :=
    c.d.ker_le (by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hψã', hψr', locElt_mul,
        hlcongr _ hwY e'.mul_self_a', mul_inv_cancel])
  have hne_RJ : RzM ≠ RJ' := fun h =>
    hMJ' (c.eq_of_locImg_eq hMz hJ'z (by rw [hMR, hJ'R, h]))
  obtain ⟨FM, g', hFM, hFM', hg'eq, hg'O, hg'2, hg'fix, hg'dim, hg'le⟩ := exists_twin_inv_four
    c.hp2 c.hq hRzM hRJ' hne_RJ hr.1
    (hcentral hwM.isCentralInvolution.central hMR (c.hY.perfR _ hRzM) hψr) hr1 hr'.1
    (hcentral hwJ'.isCentralInvolution.central hJ'R (c.hY.perfR _ hRJ') hψr') hr'1 hsame hãR hã'R
    hsq hsq'
  refine ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, ?_⟩
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
  exact congrArg (spinAction (quadOdd 4 (GaloisField p f))) (hcomm s hs)

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.B4
