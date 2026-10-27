module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X18
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X14
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf6Trans

public section


set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped MatrixGroups

section Centralizer

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_normalizer_of_commute {H : Subgroup Y} {x : Y} (h : ∀ y ∈ H, x * y = y * x) :
    x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : x * g * x⁻¹ = g := by rw [h g hg]; group
    rw [this]
    exact hg
  · intro hg
    have h1 : x * (x * g * x⁻¹) = (x * g * x⁻¹) * x := h _ hg
    have e : x⁻¹ * (x * g * x⁻¹) * x = x * g * x⁻¹ := by
      calc x⁻¹ * (x * g * x⁻¹) * x = x⁻¹ * ((x * g * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * g * x⁻¹)) := by rw [h1]
        _ = x * g * x⁻¹ := by group
    have e2 : x⁻¹ * (x * g * x⁻¹) * x = g := by group
    rw [← e2, e]
    exact hg

theorem twin_centralizer {Φ₀ : Set (Subgroup Y)} (hΩ : HypOmegaGen Φ₀)
    (hconj₀ : ∀ J ∈ Φ₀, ∀ y : Y, conjSub y J ∈ Φ₀)
    (hconjL : ∀ J ∈ liftFam Φ₀, ∀ y : Y, conjSub y J ∈ liftFam Φ₀)
    {Q Q' : Subgroup Y} (hQ : Q ∈ Φ₀) (hQ' : Q' ∈ Φ₀) (hne : Q ≠ Q') (hp2 : IsPGroup 2 Q)
    {A A' : Subgroup Y} (hA : A ∈ liftFam Φ₀) (hA' : A' ∈ liftFam Φ₀) (hQA : Q ≤ A)
    (hQA' : Q' ≤ A') (hcomm : ∀ q ∈ Q, ∀ q' ∈ Q', q * q' = q' * q)
    (eA : ↥A ≃* SL(2, ZMod 3)) (eA' : ↥A' ≃* SL(2, ZMod 3))
    (hQ4 : ∀ a ∈ A, a ^ 4 = 1 → a ∈ Q) (hQ4' : ∀ a ∈ A', a ^ 4 = 1 → a ∈ Q')
    (nbQ' : ∀ J ∈ Φ₀, J ∈ omegaNbr Φ₀ Q' → J = Q) :
    (∀ a ∈ A, ∀ q' ∈ Q', a * q' = q' * a) ∧
      ∀ c : Y, (∀ q' ∈ Q', c * q' = q' * c) →
        (∀ a ∈ A, c * a * c⁻¹ ∈ A) ∧ (∀ a ∈ A', c * a = a * c) := by
  classical
  have hnormA : ∀ c : Y, (∀ q ∈ Q, c * q = q * c) → conjSub c A = A := by
    intro c hc
    refine liftFam_eq_of_le hΩ (hconjL A hA c) hA hQ ?_ hQA
    intro q hq
    have : q = c * q * c⁻¹ := by rw [hc q hq]; group
    rw [this]
    exact conj_mem_conjSub (hQA hq)
  have hnormA' : ∀ c : Y, (∀ q' ∈ Q', c * q' = q' * c) → conjSub c A' = A' := by
    intro c hc
    refine liftFam_eq_of_le hΩ (hconjL A' hA' c) hA' hQ' ?_ hQA'
    intro q hq
    have : q = c * q * c⁻¹ := by rw [hc q hq]; group
    rw [this]
    exact conj_mem_conjSub (hQA' hq)
  have hcentA' : ∀ c : Y, (∀ q' ∈ Q', c * q' = q' * c) → ∀ a ∈ A', c * a = a * c := by
    intro c hc
    have hA'c := hnormA' c hc
    have hfix := fix_of_fix_sylow eA' hQ4' (MulAut.conj c)
      (fun a ha => by
        have : c * a * c⁻¹ ∈ conjSub c A' := conj_mem_conjSub ha
        rw [hA'c] at this
        exact this)
      (fun q hq => by
        rw [MulAut.conj_apply, hc q hq]
        group)
    intro a ha
    have := hfix a ha
    rw [MulAut.conj_apply] at this
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = a * c := by rw [this]
  have hCA : ∀ a ∈ A, ∀ q' ∈ Q', a * q' = q' * a := by
    intro a ha q' hq'
    have hq'c : ∀ q ∈ Q, q' * q = q * q' := fun q hq => (hcomm q hq q' hq').symm
    have hAc := hnormA q' hq'c
    have hfix := fix_of_fix_sylow eA hQ4 (MulAut.conj q')
      (fun a ha => by
        have : q' * a * q'⁻¹ ∈ conjSub q' A := conj_mem_conjSub ha
        rw [hAc] at this
        exact this)
      (fun q hq => by
        rw [MulAut.conj_apply, hq'c q hq]
        group)
    have := hfix a ha
    rw [MulAut.conj_apply] at this
    calc a * q' = (q' * a * q'⁻¹) * q' := by rw [this]
      _ = q' * a := by group
  refine ⟨hCA, fun c hc => ⟨?_, hcentA' c hc⟩⟩
  have hcinv : ∀ y ∈ Q', c⁻¹ * y * c = y := fun y hy => by
    rw [mul_assoc, ← hc y hy, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcQ' : conjSub c Q' = Q' := by
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro h
      have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      have e2 : c * (c⁻¹ * x * c) * c⁻¹ = c⁻¹ * x * c := by
        rw [hc _ h]
        group
      rw [e, e2]
      exact h
    · intro h
      rw [hcinv x h]
      exact h
  have hM₀ : conjSub c Q ∈ Φ₀ := hconj₀ Q hQ c
  have hMQ : conjSub c Q = Q := by
    apply nbQ' _ hM₀
    refine ⟨hM₀, ?_, conjSub c Q, ?_, le_rfl, ?_⟩
    · intro h
      apply hne
      have h1 := congrArg (conjSub c⁻¹) h
      rw [conjSub_inv_conjSub] at h1
      rw [h1]
      calc conjSub c⁻¹ Q' = conjSub c⁻¹ (conjSub c Q') := by rw [hcQ']
        _ = Q' := conjSub_inv_conjSub c Q'
    · have h2 : IsPGroup 2 ↥(conjSub c Q) :=
        hp2.of_surjective ((MulAut.conj c).toMonoidHom.subgroupMap Q)
          (MonoidHom.subgroupMap_surjective _ _)
      exact mem_RSet_of_isSylow2In hM₀ ⟨le_rfl, h2, fun V hV _ hMV => le_antisymm hV hMV⟩
    · rintro _ ⟨q, hq, rfl⟩
      apply mem_normalizer_of_commute
      intro h hh
      show c * q * c⁻¹ * h = h * (c * q * c⁻¹)
      have h1 : c⁻¹ * h = h * c⁻¹ := by
        have := hcinv h hh
        calc c⁻¹ * h = c⁻¹ * h * c * c⁻¹ := by group
          _ = h * c⁻¹ := by rw [this]
      calc c * q * c⁻¹ * h = c * q * (c⁻¹ * h) := by group
        _ = c * q * (h * c⁻¹) := by rw [h1]
        _ = c * (q * h) * c⁻¹ := by group
        _ = c * (h * q) * c⁻¹ := by rw [hcomm q hq h hh]
        _ = (c * h) * q * c⁻¹ := by group
        _ = (h * c) * q * c⁻¹ := by rw [hc h hh]
        _ = h * (c * q * c⁻¹) := by group
  have hcA : conjSub c A = A := by
    refine liftFam_eq_of_le hΩ (hconjL A hA c) hA hQ ?_ hQA
    rw [← hMQ]
    exact conjSub_mono hQA |>.trans' (by rw [hMQ])
  intro a ha
  have : c * a * c⁻¹ ∈ conjSub c A := conj_mem_conjSub ha
  rw [hcA] at this
  exact this

end Centralizer


section Sec

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem R_centralizes {w : G} (hwA : w ∈ cA S R R') {r : G} (hr : r ∈ R ⊔ R') :
    r ∈ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hwA.2) r hr)

theorem R_mem_hull (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') {r : G} (hr : r ∈ R) :
    (⟨r, R_centralizes hwA (Subgroup.mem_sup_left hr)⟩ : ↥(Subgroup.centralizer ({w} : Set G))) ∈
      TwinDisc.coreHull Ω w := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨hKtq, -, -, -, -, -⟩ := layer_twins_tq hyp hwA
  have hRK : IsSylow2In R K :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.stand.mem hyp.hR.1 hyp.hR.2.1
  obtain ⟨huC, huY, -⟩ := layer_mem_secImg hΩ hc2 hKtq hRK
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_left hx)) hr
  exact huY

theorem R'_mem_hull (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') {r : G} (hr : r ∈ R') :
    (⟨r, R_centralizes hwA (Subgroup.mem_sup_right hr)⟩ : ↥(Subgroup.centralizer ({w} : Set G))) ∈
      TwinDisc.coreHull Ω w := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨-, hK'tq, -, -, -, -⟩ := layer_twins_tq hyp hwA
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.hK'.1 hyp.hR'.1 hyp.hR'.2.1
  obtain ⟨huC, huY, -⟩ := layer_mem_secImg hΩ hc2 hK'tq hR'K'
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_right hx)) hr
  exact huY

@[expose] noncomputable def eSec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : ↥R → SecQ Ω w := fun r =>
  QuotientGroup.mk (⟨⟨r, R_centralizes hwA (Subgroup.mem_sup_left r.2)⟩,
    R_mem_hull hyp hw2 hwA r.2⟩ : ↥(TwinDisc.coreHull Ω w))

@[expose] noncomputable def eSec' (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : ↥R' → SecQ Ω w := fun r =>
  QuotientGroup.mk (⟨⟨r, R_centralizes hwA (Subgroup.mem_sup_right r.2)⟩,
    R'_mem_hull hyp hw2 hwA r.2⟩ : ↥(TwinDisc.coreHull Ω w))


theorem z_centralizes (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hwA : w ∈ cA S R R') :
    z ∈ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS w hwA.1).symm

theorem z_mem_hull (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') :
    (⟨z, z_centralizes hyp hwA⟩ : ↥(Subgroup.centralizer ({w} : Set G))) ∈ TwinDisc.coreHull Ω w := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨hKtq, -, hz, -, -, -⟩ := layer_twins_tq hyp hwA
  obtain ⟨htC, htY, -⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hKtq hz
  exact htY

@[expose] noncomputable def zSec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') : SecQ Ω w :=
  QuotientGroup.mk (⟨⟨z, z_centralizes hyp hwA⟩, z_mem_hull hyp hw2 hwA⟩ : ↥(TwinDisc.coreHull Ω w))

end Sec

section Main

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem eSec_mem (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') (r : ↥R) : eSec hyp hw2 hwA r ∈ TwinDisc.secImg Ω w K := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨hKtq, -, -, -, -, -⟩ := layer_twins_tq hyp hwA
  have hRK : IsSylow2In R K :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.stand.mem hyp.hR.1 hyp.hR.2.1
  obtain ⟨huC, huY, hmem⟩ := layer_mem_secImg hΩ hc2 hKtq hRK
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_left hx)) r.2
  exact hmem

theorem eSec'_mem (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hwA : w ∈ cA S R R') (r : ↥R') : eSec' hyp hw2 hwA r ∈ TwinDisc.secImg Ω w K' := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨-, hK'tq, -, -, -, -⟩ := layer_twins_tq hyp hwA
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.hK'.1 hyp.hR'.1 hyp.hR'.2.1
  obtain ⟨huC, huY, hmem⟩ := layer_mem_secImg hΩ hc2 hK'tq hR'K'
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_right hx)) r.2
  exact hmem

theorem exists_eSec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwA : w ∈ cA S R R') (hno : SecNoExitAt Ω w) {a : SecQ Ω w}
    (ha : a ∈ TwinDisc.secImg Ω w K) : ∃ r : ↥R, a = eSec hyp hw2 hwA r := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨hKtq, -, -, -, -, -⟩ := layer_twins_tq hyp hwA
  obtain ⟨hp2, -, -⟩ := secImg_q8 hyp hw2 hw1 hno hKtq
  have hRK : IsSylow2In R K :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.stand.mem hyp.hR.1 hyp.hR.2.1
  have heq := TwinPerpV3.secImgR_eq_secImg hc2 hKtq hRK
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_left hx)) hp2
  rw [← heq] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  exact ⟨⟨((y : ↥(Subgroup.centralizer ({w} : Set G))) : G),
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)⟩, rfl⟩

theorem exists_eSec' (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwA : w ∈ cA S R R') (hno : SecNoExitAt Ω w) {a : SecQ Ω w}
    (ha : a ∈ TwinDisc.secImg Ω w K') : ∃ r : ↥R', a = eSec' hyp hw2 hwA r := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  obtain ⟨-, hK'tq, -, -, -, -⟩ := layer_twins_tq hyp hwA
  obtain ⟨hp2, -, -⟩ := secImg_q8 hyp hw2 hw1 hno hK'tq
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hyp.std.1.hK'.1 hyp.hR'.1 hyp.hR'.2.1
  have heq := TwinPerpV3.secImgR_eq_secImg hc2 hK'tq hR'K'
    (fun x hx => R_centralizes hwA (Subgroup.mem_sup_right hx)) hp2
  rw [← heq] at ha
  obtain ⟨y, hy, rfl⟩ := ha
  exact ⟨⟨((y : ↥(Subgroup.centralizer ({w} : Set G))) : G),
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hy)⟩, rfl⟩

end Main

section TwinLiftSec

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem twinLiftSec (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {w : G} (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwA : w ∈ cA S R R') (hno : SecNoExitAt Ω w) (h6 : LayerLie Ω w 6) :
    Nonempty (TwinLift (eSec hyp hw2 hwA) (eSec' hyp hw2 hwA) (zSec hyp hw2 hwA) (actImg hyp hw2)) := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_sq_eq_one hw2
  have hS := layer_q8Section hyp hw2
  have hΩΦ : HypOmegaGen (TwinDisc.secFam Ω w) := TwinDisc.hypOmegaGen_secFam hΩ hc2
  obtain ⟨hKtq, hK'tq, hz, hz', hperp₁, hperp₂⟩ := layer_twins_tq hyp hwA
  obtain ⟨htC, htY, hu₁C, hu₁Y, hu₂C, hu₂Y, A, A', htw, hAK, hAK'⟩ :=
    EndL.layer_twinData hyp hw2 hw1 hwA hno
  obtain ⟨D, hD1, i, hi⟩ := h6
  have hπ : (!piSign 3 1) = true := by decide
  have hi' : ∃ i : Fin D.card, IsOrthTag 6 (!piSign 3 1) (D.tag i) (D.rank i) :=
    ⟨i, by rw [hπ]; exact hi⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj₀ : ∀ J ∈ TwinDisc.secFam Ω w, ∀ y : SecQ Ω w, conjSub y J ∈ TwinDisc.secFam Ω w :=
    fun J hJ y => hΩΦ.conjInvariant y J hJ
  have hconj : ∀ J ∈ liftFam (TwinDisc.secFam Ω w), ∀ y : SecQ Ω w,
      conjSub y J ∈ liftFam (TwinDisc.secFam Ω w) :=
    fun J hJ y => conjInvariant_liftFam hΩΦ.conjInvariant y J hJ
  have hLT := CFSG.ClassicalInvolution.Asc77.CX.layer6Twin_proved 3 1 _ _ D A A' _ _ _ hD1 hi' htw
  obtain ⟨eA⟩ := nonempty_equiv_of_mem_liftFam htw.hA hLT.2.1
  obtain ⟨eA'⟩ := nonempty_equiv_of_mem_liftFam htw.hA' hLT.2.2.1
  obtain ⟨hp2K, hc8, h4⟩ := secImg_q8 hyp hw2 hw1 hno hKtq
  obtain ⟨hp2K', hc8', h4'⟩ := secImg_q8 hyp hw2 hw1 hno hK'tq
  have hQ4 := mem_of_pow_four_eq_one eA hAK h4 hc8
  have hQ4' := mem_of_pow_four_eq_one eA' hAK' h4' hc8'
  have hne : TwinDisc.secImg Ω w K ≠ TwinDisc.secImg Ω w K' :=
    TwinPerpV3.secImg_ne_of_twin hΩ hc2 hKtq hK'tq hyp.std.1.hne.symm hz hz'
  have hcommR : Commutes R R' := by
    obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
    exact h.hcomm
  have hcomm : ∀ q ∈ TwinDisc.secImg Ω w K, ∀ q' ∈ TwinDisc.secImg Ω w K', q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨r, rfl⟩ := exists_eSec hyp hw2 hw1 hwA hno hq
    obtain ⟨r', rfl⟩ := exists_eSec' hyp hw2 hw1 hwA hno hq'
    show QuotientGroup.mk _ * QuotientGroup.mk _ = QuotientGroup.mk _ * QuotientGroup.mk _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hcommR r.1 r.2 r'.1 r'.2
  have nbQ' : ∀ J ∈ TwinDisc.secFam Ω w,
      J ∈ omegaNbr (TwinDisc.secFam Ω w) (TwinDisc.secImg Ω w K') → J = TwinDisc.secImg Ω w K := by
    intro J hJ hn
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hJ
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK'tq hJ₁ hperp₂ hn
  have nbQ : ∀ J ∈ TwinDisc.secFam Ω w,
      J ∈ omegaNbr (TwinDisc.secFam Ω w) (TwinDisc.secImg Ω w K) → J = TwinDisc.secImg Ω w K' := by
    intro J hJ hn
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hJ
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hKtq hJ₁ hperp₁ hn
  obtain ⟨hCA, hC⟩ := twin_centralizer hΩΦ hconj₀ hconj (TwinDisc.secImg_mem_secFam hKtq)
    (TwinDisc.secImg_mem_secFam hK'tq) hne hp2K htw.hA htw.hA' hAK hAK' hcomm eA eA' hQ4 hQ4' nbQ'
  obtain ⟨hCA', hC'⟩ := twin_centralizer hΩΦ hconj₀ hconj (TwinDisc.secImg_mem_secFam hK'tq)
    (TwinDisc.secImg_mem_secFam hKtq) hne.symm hp2K' htw.hA' htw.hA hAK' hAK
    (fun q hq q' hq' => (hcomm q' hq' q hq).symm) eA' eA hQ4' hQ4 nbQ
  refine ⟨{
    Φ := liftFam (TwinDisc.secFam Ω w)
    A := A
    A' := A'
    z' := _
    a₀ := _
    b₀ := _
    hz := rfl
    om6 := ⟨⟨D, hD1, hi'⟩, htw, hconj⟩
    eA := eA
    eA' := eA'
    he := fun r => hAK (eSec_mem hyp hw2 hwA r)
    he' := fun r => hAK' (eSec'_mem hyp hw2 hwA r)
    hQ := fun a ha h => exists_eSec hyp hw2 hw1 hwA hno (hQ4 a ha h)
    hQ' := fun a ha h => exists_eSec' hyp hw2 hw1 hwA hno (hQ4' a ha h)
    hCA := fun a ha r => hCA a ha _ (eSec'_mem hyp hw2 hwA r)
    hCA' := fun a ha r => hCA' a ha _ (eSec_mem hyp hw2 hwA r)
    hC := fun c hc => hC c (fun q' hq' => by
      obtain ⟨r, rfl⟩ := exists_eSec' hyp hw2 hw1 hwA hno hq'
      exact hc r)
    hC' := fun c hc => hC' c (fun q hq => by
      obtain ⟨r, rfl⟩ := exists_eSec hyp hw2 hw1 hwA hno hq
      exact hc r)
    hfix := ?_ }⟩
  rintro _ ⟨⟨x, hxb⟩, hx, rfl⟩
  exact secAct_fix_lifts hyp hw2 hw1 hwA hno hAK hAK' htw.hA htw.hA' eA eA'
    (Subgroup.mem_subgroupOf.mp hx) hxb

end TwinLiftSec

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
