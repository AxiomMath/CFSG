module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAb

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem sylowVec_mem_rootV_five_sup_R1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Fin 12 → K}
    (hx : ∀ n ∈ ({0, 1, 2, 3, 5, 9} : Finset (Fin 12)), x n = 0) :
    sylowVec a K x ∈ rootV K a .i5 ⊔ R1 K a := by
  rw [sylowVec_eq_prod_rootElt hK, hx 0 (by decide), hx 1 (by decide), hx 2 (by decide),
    hx 3 (by decide), hx 5 (by decide), hx 9 (by decide)]
  simp only [rootElt_zero, one_mul, mul_one]
  have hR : ∀ k : Idx, k.isR1 = true → ∀ c, rootElt K a k c ∈ rootV K a .i5 ⊔ R1 K a :=
    fun k hk c => mem_sup_right (rootElt_mem_R1 hk c)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hR .i8 rfl _) (hR .i11 rfl _))
    (mem_sup_left (rootElt_mem_rootV _ _))) (hR .i12 rfl _)) (hR .i9 rfl _)) (hR .i10 rfl _)

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

@[expose] def rb (z : G) (k : Idx) : h.K := h.r1c ⁅z, h.elt (rootElt h.K h.a k 1)⁆ .i12

theorem exists_coords_R {r : G} (hr : r ∈ h.R) : ∃ x : Fin 12 → h.K,
    (x 0 = 0 → x 3 = 0 → x 5 = 0 → x 9 = 0 → r ∈ h.V .i5 ⊔ h.R₁) ∧ ∀ u : Idx → h.K,
      h.r1c ⁅r, h.elt (r1Elt h.K h.a u)⁆ .i12 = x 0 * u .i11 + x 3 * u .i10 + x 5 * u .i9 +
        x 9 * u .i8 := by
  obtain ⟨g, hg, hgΓ, rfl⟩ := (h.mem_pull_iff_elt).1 hr
  obtain ⟨x, hx1, hx2, rfl⟩ := exists_sylowVec_of_mem_radR h.card_K hg
  refine ⟨x, fun h0 h3 h5 h9 => ?_, fun u => ?_⟩
  · have hm := sylowVec_mem_rootV_five_sup_R1 h.card_K (x := x) (by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    have := (h.elt_mem_pull hgΓ).2 hm
    rwa [h.pull_sup (rootV_le_reeGamma h.card_K _) h.R1_le_reeGamma] at this
  · have hu : r1Elt h.K h.a u ∈ F4.reeGamma h.K h.a := h.R1_le_reeGamma (r1Elt_mem u)
    rw [← h.elt_commutator hgΓ hu, comm_sylowVec_r1Elt h.card_K hx1 hx2,
      h.r1c_elt_rootElt rfl _ rfl, Pi.single_eq_same]

theorem elt_rootElt_eq_r1Elt {k : Idx} (hk : k.isR1 = true) (c : h.K) :
    h.elt (rootElt h.K h.a k c) = h.elt (r1Elt h.K h.a (Pi.single k c)) := by
  rw [rootElt_eq_r1Elt hk]

theorem r1c_comm_r1Elt_eq_of_mem_R {r : G} (hr : r ∈ h.R) (u : Idx → h.K) :
    h.r1c ⁅r, h.elt (r1Elt h.K h.a u)⁆ .i12 = h.rb r .i11 * u .i11 + h.rb r .i10 * u .i10 +
      h.rb r .i9 * u .i9 + h.rb r .i8 * u .i8 := by
  obtain ⟨x, -, hx⟩ := h.exists_coords_R hr
  have hrb : ∀ k : Idx, k.isR1 = true → h.rb r k = x 0 * (Pi.single k 1 : Idx → h.K) .i11 +
      x 3 * (Pi.single k 1 : Idx → h.K) .i10 + x 5 * (Pi.single k 1 : Idx → h.K) .i9 +
        x 9 * (Pi.single k 1 : Idx → h.K) .i8 := fun k hk => by
    rw [rb, h.elt_rootElt_eq_r1Elt hk, hx]
  rw [hx, hrb .i11 rfl, hrb .i10 rfl, hrb .i9 rfl, hrb .i8 rfl]
  simp [Pi.single_apply]

theorem mem_V5_sup_R₁_of_rb {r : G} (hr : r ∈ h.R) (h11 : h.rb r .i11 = 0)
    (h10 : h.rb r .i10 = 0) (h9 : h.rb r .i9 = 0) (h8 : h.rb r .i8 = 0) :
    r ∈ h.V .i5 ⊔ h.R₁ := by
  obtain ⟨x, hdec, hx⟩ := h.exists_coords_R hr
  have hrb : ∀ k : Idx, k.isR1 = true → h.rb r k = x 0 * (Pi.single k 1 : Idx → h.K) .i11 +
      x 3 * (Pi.single k 1 : Idx → h.K) .i10 + x 5 * (Pi.single k 1 : Idx → h.K) .i9 +
        x 9 * (Pi.single k 1 : Idx → h.K) .i8 := fun k hk => by
    rw [rb, h.elt_rootElt_eq_r1Elt hk, hx]
  refine hdec ?_ ?_ ?_ ?_
  · rw [hrb .i11 rfl] at h11; simpa [Pi.single_apply] using h11
  · rw [hrb .i10 rfl] at h10; simpa [Pi.single_apply] using h10
  · rw [hrb .i9 rfl] at h9; simpa [Pi.single_apply] using h9
  · rw [hrb .i8 rfl] at h8; simpa [Pi.single_apply] using h8

theorem r_conj_elt_rootElt {i : Idx} (hi1 : i ≠ .i1) (hi2 : i ≠ .i2) (c : h.K) :
    h.r * h.elt (rootElt h.K h.a i c) * h.r⁻¹ = h.elt (rootElt h.K h.a i.rPerm c) := by
  rw [← h.elt_weylR, ← h.elt_conj' weylR_mem_reeGamma
    (rootV_le_reeGamma h.card_K i (rootElt_mem_rootV _ _)), weylR_conj_rootElt hi1 hi2]

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem exists_R_comm_eq {z : G} (hz : z ∈ d.RA1) :
    ∃ r ∈ h.R, ∀ y ∈ h.R₁, ⁅z, y⁆ = ⁅r, y⁆ := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1 hz
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [commutatorElement_mul_left_eq,
    commutatorElement_eq_one_iff_mul_comm.2 (d.A1_comm ha (d.R₁_le_A1 hy)), mul_one,
    mul_inv_cancel, one_mul]

theorem comm_RA1_R₁_mem_V12 {z y : G} (hz : z ∈ d.RA1) (hy : y ∈ h.R₁) : ⁅z, y⁆ ∈ h.V .i12 := by
  obtain ⟨r, hr, e⟩ := d.exists_R_comm_eq hz
  rw [e y hy, ← h.commutator_R_R₁]
  exact commutator_mem_commutator hr hy

theorem r1c_comm_r1Elt_eq {z : G} (hz : z ∈ d.RA1) (u : Idx → h.K) :
    h.r1c ⁅z, h.elt (r1Elt h.K h.a u)⁆ .i12 = h.rb z .i11 * u .i11 + h.rb z .i10 * u .i10 +
      h.rb z .i9 * u .i9 + h.rb z .i8 * u .i8 := by
  obtain ⟨r, hr, e⟩ := d.exists_R_comm_eq hz
  have hR1 : ∀ u : Idx → h.K, h.elt (r1Elt h.K h.a u) ∈ h.R₁ := fun u =>
    (h.elt_mem_pull (h.R1_le_reeGamma (r1Elt_mem u))).2 (r1Elt_mem u)
  have hrb : ∀ k : Idx, k.isR1 = true → h.rb z k = h.rb r k := fun k hk => by
    rw [Setup.rb, Setup.rb, e _ (h.elt_rootElt_mem_R₁ hk 1)]
  rw [e _ (hR1 u), h.r1c_comm_r1Elt_eq_of_mem_R hr, hrb .i11 rfl, hrb .i10 rfl, hrb .i9 rfl,
    hrb .i8 rfl]

theorem mem_V5_sup_A1_of_rb {z : G} (hz : z ∈ d.RA1) (h11 : h.rb z .i11 = 0)
    (h10 : h.rb z .i10 = 0) (h9 : h.rb z .i9 = 0) (h8 : h.rb z .i8 = 0) :
    z ∈ h.V .i5 ⊔ d.A1 := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1 hz
  have hrb : ∀ k : Idx, k.isR1 = true → h.rb (r * a) k = h.rb r k := fun k hk => by
    obtain ⟨r', -, e⟩ := d.exists_R_comm_eq hz
    simp only [Setup.rb]
    rw [commutatorElement_mul_left_eq,
      commutatorElement_eq_one_iff_mul_comm.2 (d.A1_comm ha (d.R₁_le_A1
        (h.elt_rootElt_mem_R₁ hk 1))), mul_one, mul_inv_cancel, one_mul]
  rw [hrb .i11 rfl] at h11
  rw [hrb .i10 rfl] at h10
  rw [hrb .i9 rfl] at h9
  rw [hrb .i8 rfl] at h8
  have hr' := h.mem_V5_sup_R₁_of_rb hr h11 h10 h9 h8
  exact mul_mem ((sup_le_sup_left d.R₁_le_A1 _) hr') (mem_sup_right ha)

theorem rb_mul {z z' : G} (hz : z ∈ d.RA1) (hz' : z' ∈ d.RA1) {k : Idx} (hk : k.isR1 = true) :
    h.rb (z * z') k = h.rb z k + h.rb z' k := by
  have hy := h.elt_rootElt_mem_R₁ hk 1
  have h1 := d.comm_RA1_R₁_mem_V12 hz hy
  have h2 := d.comm_RA1_R₁_mem_V12 hz' hy
  have hzc : z ∈ centralizer (h.V .i12 : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 d.V12_le_W12) (d.RA1_le_A hz).2.1
  simp only [Setup.rb]
  rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hzc _ h2, mul_inv_cancel_right,
    h.r1c_mul (h.V12_le_R₁ h2) (h.V12_le_R₁ h1) rfl, add_comm]

theorem rb_eq_zero_of_mem_A1 {z : G} (hz : z ∈ d.A1) {k : Idx} (hk : k.isR1 = true) :
    h.rb z k = 0 := by
  simp only [Setup.rb]
  rw [commutatorElement_eq_one_iff_mul_comm.2 (d.A1_comm hz (d.R₁_le_A1
    (h.elt_rootElt_mem_R₁ hk 1))), h.r1c_one rfl]

theorem rb_conj_A {x z : G} (hx : x ∈ d.A) (hz : z ∈ d.RA1) {k : Idx} (hk : k.isR1 = true) :
    h.rb (x * z * x⁻¹) k = h.rb z k := by
  have e : x * z * x⁻¹ = ⁅x, z⁆ * z := by simp only [commutatorElement_def]; group
  rw [e, d.rb_mul (d.A1_le_RA1 (d.comm_A_RA1_mem hx hz)) hz hk,
    d.rb_eq_zero_of_mem_A1 (d.comm_A_RA1_mem hx hz) hk, zero_add]

theorem rb_torus_ten {z : G} (hz : z ∈ d.RA1) (t : h.Kˣ × h.Kˣ) :
    h.rb (h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹) .i10 =
      (rootChar h.K h.a .i4 t : h.K) * h.rb z .i10 := by
  have hτΓ := h.torusPair_mem_reeGamma t
  have hτinv : (h.elt (torusPair h.a t))⁻¹ = h.elt (torusPair h.a t⁻¹) := by
    rw [← h.elt_inv' hτΓ, map_inv]
  have hconj : (h.elt (torusPair h.a t))⁻¹ * h.elt (rootElt h.K h.a .i10 1) *
      (h.elt (torusPair h.a t))⁻¹⁻¹ =
        h.elt (rootElt h.K h.a .i10 ((rootChar h.K h.a .i10 t⁻¹ : h.K) * 1)) := by
    rw [hτinv]
    exact h.elt_torusPair_conj_rootElt t⁻¹ .i10 1
  have e : ⁅h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹,
      h.elt (rootElt h.K h.a .i10 1)⁆ = h.elt (torusPair h.a t) *
        ⁅z, (h.elt (torusPair h.a t))⁻¹ * h.elt (rootElt h.K h.a .i10 1) *
          (h.elt (torusPair h.a t))⁻¹⁻¹⁆ * (h.elt (torusPair h.a t))⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hc := d.comm_RA1_R₁_mem_V12 hz (h.elt_rootElt_mem_R₁ (k := .i10) rfl
    ((rootChar h.K h.a .i10 t⁻¹ : h.K) * 1))
  have hpair : h.r1c ⁅z, h.elt (rootElt h.K h.a .i10 ((rootChar h.K h.a .i10 t⁻¹ : h.K) * 1))⁆
      .i12 = h.rb z .i10 * ((rootChar h.K h.a .i10 t⁻¹ : h.K) * 1) := by
    rw [h.elt_rootElt_eq_r1Elt rfl, d.r1c_comm_r1Elt_eq hz]
    simp [Pi.single_apply]
  have hne : (rootChar h.K h.a .i10 t : h.K) ≠ 0 := Units.ne_zero _
  show h.r1c ⁅h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹,
    h.elt (rootElt h.K h.a .i10 1)⁆ .i12 = _
  rw [e, hconj, h.r1c_torus (h.V12_le_R₁ hc) t rfl, hpair, h.rootChar_twelve_eq t, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

theorem rb_conj_r {z : G} (hz : z ∈ d.RA1) {k : Idx} (hk : k.isR1 = true) (hk12 : k ≠ .i12) :
    h.rb (h.r * z * h.r⁻¹) k = h.rb z k.rPerm := by
  have hk1 : k ≠ .i1 := by rintro rfl; exact absurd hk (by decide)
  have hk2 : k ≠ .i2 := by rintro rfl; exact absurd hk (by decide)
  have hrc : ∀ v ∈ h.V .i12, h.r * v * h.r⁻¹ = v := by
    have hle : h.V .i12 ≤ centralizer ({h.r} : Set G) := h.V_le_of_forall_elt_mem fun c =>
      mem_centralizer_singleton_iff.2 (by
        have := h.r_conj_elt_rootElt (i := .i12) (by decide) (by decide) c
        calc h.elt (rootElt h.K h.a .i12 c) * h.r =
            h.r * h.elt (rootElt h.K h.a .i12 c) * h.r⁻¹ * h.r := by rw [this]; rfl
          _ = h.r * h.elt (rootElt h.K h.a .i12 c) := by group)
    intro v hv
    rw [(mem_centralizer_singleton_iff.1 (hle hv)).symm, mul_inv_cancel_right]
  have e : ⁅h.r * z * h.r⁻¹, h.elt (rootElt h.K h.a k 1)⁆ =
      h.r * ⁅z, h.r * h.elt (rootElt h.K h.a k 1) * h.r⁻¹⁆ * h.r⁻¹ := by
    have hr := h.r_inv
    simp only [commutatorElement_def]
    calc h.r * z * h.r⁻¹ * h.elt (rootElt h.K h.a k 1) * (h.r * z * h.r⁻¹)⁻¹ *
          (h.elt (rootElt h.K h.a k 1))⁻¹ =
        h.r * (z * (h.r⁻¹ * h.elt (rootElt h.K h.a k 1) * h.r) * z⁻¹ *
          (h.r⁻¹ * h.elt (rootElt h.K h.a k 1) * h.r)⁻¹) * h.r⁻¹ := by group
      _ = _ := by rw [hr]
  have hc : ⁅z, h.r * h.elt (rootElt h.K h.a k 1) * h.r⁻¹⁆ ∈ h.V .i12 := by
    rw [h.r_conj_elt_rootElt hk1 hk2]
    exact d.comm_RA1_R₁_mem_V12 hz (h.elt_rootElt_mem_R₁ (by
      revert hk hk12; cases k <;> decide) 1)
  simp only [Setup.rb]
  rw [e, hrc _ hc, h.r_conj_elt_rootElt hk1 hk2]

theorem rb_conj_one_ten {z : G} (hz : z ∈ d.RA1) (c : h.K) :
    h.rb ((h.elt (rootElt h.K h.a .i1 c))⁻¹ * z * h.elt (rootElt h.K h.a .i1 c)) .i10 =
      h.rb z .i10 + c * h.rb z .i11 := by
  set v := h.elt (rootElt h.K h.a .i1 c) with hv
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have hvP : v ∈ h.P := h.V_le_P .i1 (h.elt_rootElt_mem_V .i1 c)
  have hconj : v * h.elt (rootElt h.K h.a .i10 1) * v⁻¹ =
      h.elt (r1Elt h.K h.a (Pi.single .i11 c + Pi.single .i10 1)) := by
    have e1 : v * h.elt (rootElt h.K h.a .i10 1) * v⁻¹ =
        ⁅v, h.elt (rootElt h.K h.a .i10 1)⁆ * h.elt (rootElt h.K h.a .i10 1) := by
      simp only [commutatorElement_def]; group
    have e2 : r1Elt h.K h.a (Pi.single .i11 c + Pi.single .i10 1) =
        rootElt h.K h.a .i11 c * rootElt h.K h.a .i10 1 := by
      simp only [r1Elt, Pi.add_apply, Pi.single_apply]
      simp [rootElt_zero]
    rw [e1, hv, ← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_1_10 h.card_K, mul_one, e2,
      h.elt_mul' (hΓ _ _) (hΓ _ _)]
  have e : ⁅v⁻¹ * z * v, h.elt (rootElt h.K h.a .i10 1)⁆ =
      v⁻¹ * ⁅z, v * h.elt (rootElt h.K h.a .i10 1) * v⁻¹⁆ * v := by
    simp only [commutatorElement_def]
    group
  have hR1 : h.elt (r1Elt h.K h.a (Pi.single .i11 c + Pi.single .i10 1)) ∈ h.R₁ :=
    (h.elt_mem_pull (h.R1_le_reeGamma (r1Elt_mem _))).2 (r1Elt_mem _)
  have hc := d.comm_RA1_R₁_mem_V12 hz hR1
  have hvc : v⁻¹ * ⁅z, h.elt (r1Elt h.K h.a (Pi.single .i11 c + Pi.single .i10 1))⁆ * v =
      ⁅z, h.elt (r1Elt h.K h.a (Pi.single .i11 c + Pi.single .i10 1))⁆ := by
    rw [mul_assoc, mem_centralizer_iff.1 (h.P_le_centralizer_V12 hvP) _ hc,
      inv_mul_cancel_left]
  simp only [Setup.rb]
  rw [e, hconj, hvc, d.r1c_comm_r1Elt_eq hz]
  simp only [Pi.add_apply, Pi.single_apply]
  simp only [Setup.rb]
  simp
  ring

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
