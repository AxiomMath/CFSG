module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAg

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem rootChar_twelve_eq_three (t : h.Kˣ × h.Kˣ) :
    rootChar h.K h.a .i12 t = rootChar h.K h.a .i3 t * rootChar h.K h.a .i11 t := by
  obtain ⟨u, v⟩ := t
  obtain ⟨-, -, ⟨e30, e31⟩, -, -, -, -, -, -, -, ⟨e110, e111⟩, ⟨e120, e121⟩⟩ :=
    torusExp_leadRoot (2 ^ h.a : ℤ)
  simp only [rootChar, CFSG.LieType.Ree.LargeReeCover.torusWeight_apply, e30, e31, e110, e111,
    e120, e121]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 2 <;> ring

theorem rootChar_twelve_eq_six (t : h.Kˣ × h.Kˣ) :
    rootChar h.K h.a .i12 t = rootChar h.K h.a .i6 t * rootChar h.K h.a .i9 t := by
  obtain ⟨u, v⟩ := t
  obtain ⟨-, -, -, -, -, ⟨e60, e61⟩, -, -, ⟨e90, e91⟩, -, -, ⟨e120, e121⟩⟩ :=
    torusExp_leadRoot (2 ^ h.a : ℤ)
  simp only [rootChar, CFSG.LieType.Ree.LargeReeCover.torusWeight_apply, e60, e61, e90, e91,
    e120, e121]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 2 <;> ring

theorem rootChar_twelve_eq_seven (t : h.Kˣ × h.Kˣ) :
    rootChar h.K h.a .i12 t = rootChar h.K h.a .i7 t * rootChar h.K h.a .i8 t := by
  obtain ⟨u, v⟩ := t
  obtain ⟨-, -, -, -, -, -, ⟨e70, e71⟩, ⟨e80, e81⟩, -, -, -, ⟨e120, e121⟩⟩ :=
    torusExp_leadRoot (2 ^ h.a : ℤ)
  simp only [rootChar, CFSG.LieType.Ree.LargeReeCover.torusWeight_apply, e70, e71, e80, e81,
    e120, e121]
  rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add]
  congr 2 <;> ring

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem r1c_comm_rootElt_eq {z : G} (hz : z ∈ d.RA1) {k : Idx}
    (hk : k ∈ ({.i8, .i9, .i10, .i11} : Finset Idx)) (c : h.K) :
    h.r1c ⁅z, h.elt (rootElt h.K h.a k c)⁆ .i12 = h.rb z k * c := by
  have hk1 : k.isR1 = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> rfl
  rw [h.elt_rootElt_eq_r1Elt hk1, d.r1c_comm_r1Elt_eq hz]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem rb_torus {z : G} (hz : z ∈ d.RA1) (t : h.Kˣ × h.Kˣ) {j k : Idx}
    (hk : k ∈ ({.i8, .i9, .i10, .i11} : Finset Idx))
    (hjk : rootChar h.K h.a .i12 t = rootChar h.K h.a j t * rootChar h.K h.a k t) :
    h.rb (h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹) k =
      (rootChar h.K h.a j t : h.K) * h.rb z k := by
  have hk1 : k.isR1 = true := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> rfl
  have hτΓ := h.torusPair_mem_reeGamma t
  have hτinv : (h.elt (torusPair h.a t))⁻¹ = h.elt (torusPair h.a t⁻¹) := by
    rw [← h.elt_inv' hτΓ, map_inv]
  have hconj : (h.elt (torusPair h.a t))⁻¹ * h.elt (rootElt h.K h.a k 1) *
      (h.elt (torusPair h.a t))⁻¹⁻¹ =
        h.elt (rootElt h.K h.a k ((rootChar h.K h.a k t⁻¹ : h.K) * 1)) := by
    rw [hτinv]
    exact h.elt_torusPair_conj_rootElt t⁻¹ k 1
  have e : ⁅h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹,
      h.elt (rootElt h.K h.a k 1)⁆ = h.elt (torusPair h.a t) *
        ⁅z, (h.elt (torusPair h.a t))⁻¹ * h.elt (rootElt h.K h.a k 1) *
          (h.elt (torusPair h.a t))⁻¹⁻¹⁆ * (h.elt (torusPair h.a t))⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hc := d.comm_RA1_R₁_mem_V12 hz (h.elt_rootElt_mem_R₁ hk1
    ((rootChar h.K h.a k t⁻¹ : h.K) * 1))
  have hpair := d.r1c_comm_rootElt_eq hz hk ((rootChar h.K h.a k t⁻¹ : h.K) * 1)
  have hne : (rootChar h.K h.a k t : h.K) ≠ 0 := Units.ne_zero _
  show h.r1c ⁅h.elt (torusPair h.a t) * z * (h.elt (torusPair h.a t))⁻¹,
    h.elt (rootElt h.K h.a k 1)⁆ .i12 = _
  rw [e, hconj, h.r1c_torus (h.V12_le_R₁ hc) t rfl, hpair, hjk, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

theorem mem_V5_sup_A1_of_mem_W {w : G} (hw : w ∈ d.W) (hwR : w ∈ d.RA1) :
    w ∈ h.V .i5 ⊔ d.A1 := by
  have hfix : ∀ t : h.Kˣ × h.Kˣ, rootChar h.K h.a .i5 t = 1 →
      h.elt (torusPair h.a t) * w * (h.elt (torusPair h.a t))⁻¹ = w := fun t ht => by
    have hτ : h.elt (torusPair h.a t) ∈ h.Ht .i5 :=
      (h.elt_torusPair_mem_Ht_iff t).2 ((mem_torusHi_iff h.card_K .i5 t).2 ht)
    rw [mem_centralizer_iff.1 (d.W_le_CH hw) _ hτ, mul_inv_cancel_right]
  have hrow : ∀ {j k : Idx}, k ∈ ({.i8, .i9, .i10, .i11} : Finset Idx) →
      (∀ t, rootChar h.K h.a .i12 t = rootChar h.K h.a j t * rootChar h.K h.a k t) →
      Idx.brace .i5 j ≠ 0 → h.rb w k = 0 := fun hk hjk hj =>
    eq_zero_of_forall_rootChar_mul_eq h.one_le_a h.card_K (i := .i5) rfl hj fun t ht => by
      rw [← d.rb_torus hwR t hk (hjk t), hfix t ht]
  exact d.mem_V5_sup_A1_of_rb hwR (hrow (j := .i3) (by decide) h.rootChar_twelve_eq_three
    (by decide)) (hrow (j := .i4) (by decide) h.rootChar_twelve_eq (by decide))
    (hrow (j := .i6) (by decide) h.rootChar_twelve_eq_six (by decide))
    (hrow (j := .i7) (by decide) h.rootChar_twelve_eq_seven (by decide))

theorem mul_self_mem_of_mem_RA1 {z : G} (hz : z ∈ d.RA1) : z * z ∈ h.V .i5 ⊔ d.A1 := by
  have h2 : ∀ k : Idx, k.isR1 = true → h.rb (z * z) k = 0 := fun k hk => by
    rw [d.rb_mul hz hz hk, CharTwo.add_self_eq_zero]
  exact d.mem_V5_sup_A1_of_rb (mul_mem hz hz) (h2 _ rfl) (h2 _ rfl) (h2 _ rfl) (h2 _ rfl)

@[expose] def sqA : Subgroup G where
  carrier := {x | x ∈ d.A ∧ x * x ∈ h.V .i5 ⊔ d.A1}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    have e : x * y * (x * y) = x * x * ⁅x⁻¹, y⁆ * (y * y) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (mul_mem hx.2 (d.comm_mem_V5_sup_A1 (inv_mem hx.1) hy.1)) hy.2⟩
  one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    rw [← mul_inv_rev]
    exact inv_mem hx.2⟩

theorem mul_self_mem_V5_sup_A1 {x : G} (hx : x ∈ d.A) : x * x ∈ h.V .i5 ⊔ d.A1 := by
  have hrJ := h.r_mem_J
  have hA1 : ∀ {y : G}, y ∈ d.A1 → y ∈ h.V .i5 ⊔ d.A1 := fun hy => mem_sup_right hy
  have h6 : ∀ c : h.K, ∃ y ∈ d.A, y ∈ d.W6 ∧
      ⁅y, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i6 c) ∈ d.A1 := fun c => by
    obtain ⟨y, hyA, hyH, hy⟩ := d.exists_A_CH_comm_t (i := .i6)
      (h.V_le_R (by decide) (h.elt_rootElt_mem_V .i6 c))
      (h.V_le_CH (by decide) (Or.inl rfl) (h.elt_rootElt_mem_V .i6 c))
    exact ⟨y, hyA, d.A_inf_CH6_le_W6 ⟨hyA, hyH⟩, hy⟩
  have hle := d.A_le_of_lifts (M := d.sqA) (fun _ hy => hy.1)
    (fun z hz => ⟨d.RA1_le_A hz, d.mul_self_mem_of_mem_RA1 hz⟩) fun k hk c => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    ·
      obtain ⟨w, hwW, hwt⟩ := d.exists_W7_comm_t (h.elt_rootElt_mem_V .i7 c)
      have hl := d.conj_J_lift_mem hrJ (show ⁅w, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i7 c) ∈ d.A1 by
        rw [hwt, inv_mul_cancel]; exact one_mem _)
      rw [h.r_conj_elt_rootElt (by decide) (by decide)] at hl
      refine ⟨h.r * w * h.r⁻¹, ⟨d.conj_J_mem_A hrJ (d.W7_le_A hwW), ?_⟩, hl⟩
      rw [show h.r * w * h.r⁻¹ * (h.r * w * h.r⁻¹) = h.r * (w * w) * h.r⁻¹ by group,
        d.B3_mul_self (d.W7_le_B3 hwW), mul_one, mul_inv_cancel]
      exact one_mem _
    ·
      obtain ⟨y, hyA, hyW, hy⟩ := h6 c
      have hl := d.conj_J_lift_mem hrJ hy
      rw [h.r_conj_elt_rootElt (by decide) (by decide)] at hl
      refine ⟨h.r * y * h.r⁻¹, ⟨d.conj_J_mem_A hrJ hyA, ?_⟩, hl⟩
      rw [show h.r * y * h.r⁻¹ * (h.r * y * h.r⁻¹) = h.r * (y * y) * h.r⁻¹ by group]
      exact hA1 (d.conj_J_mem_A1 hrJ (d.W11_le_A1 (d.W6_mul_self_mem_W11 hyW)))
    ·
      obtain ⟨y, hyA, hyH, hy⟩ := d.exists_A_CH_comm_t (i := .i5)
        (h.V_le_R (by decide) (h.elt_rootElt_mem_V .i5 c))
        (h.V_le_CH (by decide) (Or.inl rfl) (h.elt_rootElt_mem_V .i5 c))
      refine ⟨y, ⟨hyA, hA1 (d.W12_le_A1 ?_)⟩, hy⟩
      exact d.bender.mul_self_mem y (d.A_inf_CH5_le_W ⟨hyA, hyH⟩)
    ·
      obtain ⟨y, hyA, hyW, hy⟩ := h6 c
      exact ⟨y, ⟨hyA, hA1 (d.W11_le_A1 (d.W6_mul_self_mem_W11 hyW))⟩, hy⟩
    ·
      obtain ⟨w, hwW, hwt⟩ := d.exists_W7_comm_t (h.elt_rootElt_mem_V .i7 c)
      refine ⟨w, ⟨d.W7_le_A hwW, ?_⟩, by rw [hwt, inv_mul_cancel]; exact one_mem _⟩
      rw [d.B3_mul_self (d.W7_le_B3 hwW)]
      exact one_mem _
  exact (hle hx).2

theorem exists_mul_of_mem_A1_sup_W {z : G} (hz : z ∈ d.A1 ⊔ d.W) :
    ∃ a ∈ d.A1, ∃ w ∈ d.W, z = a * w := by
  have hz' : z ∈ ((d.A1 ⊔ d.W : Subgroup G) : Set G) := hz
  rw [coe_mul_of_right_le_normalizer_left d.A1 d.W fun x hx => (d.W_le_A hx).1,
    Set.mem_mul] at hz'
  obtain ⟨a, ha, w, hw, rfl⟩ := hz'
  exact ⟨a, ha, w, hw, rfl⟩

theorem A1_sup_W_le_A : d.A1 ⊔ d.W ≤ d.A := sup_le d.A1_le_A d.W_le_A

theorem V5_sup_A1_le_A1_sup_W : h.V .i5 ⊔ d.A1 ≤ d.A1 ⊔ d.W :=
  sup_le (d.bender.le.trans le_sup_right) le_sup_left

theorem mem_V5_sup_A1_of_mem_A1_sup_W {z : G} (hz : z ∈ d.A1 ⊔ d.W) (hzR : z ∈ d.RA1) :
    z ∈ h.V .i5 ⊔ d.A1 := by
  obtain ⟨a, ha, w, hw, rfl⟩ := d.exists_mul_of_mem_A1_sup_W hz
  have hwR : w ∈ d.RA1 := by
    have := mul_mem (inv_mem (d.A1_le_RA1 ha)) hzR
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_right ha) (d.mem_V5_sup_A1_of_mem_W hw hwR)

theorem t_mem_normalizer_A1_sup_W : h.t ∈ normalizer ((d.A1 ⊔ d.W : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    (mem_inf.2 ⟨d.J_le_normalizer_A1 h.t_mem_J, d.bender.mem_normalizer⟩)

theorem freeSeries_A : FreeSeries h.t ![⊥, d.A1, d.A1 ⊔ d.W, d.A] where
  bot := rfl
  le_succ := by
    intro i
    fin_cases i
    · exact bot_le
    · exact le_sup_left
    · exact d.A1_sup_W_le_A
  le_normalizer := by
    intro i
    fin_cases i
    · change d.A1 ≤ normalizer ((⊥ : Subgroup G) : Set G)
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    · exact fun x hx => (d.A1_sup_W_le_A hx).1
    · change d.A ≤ normalizer ((d.A1 ⊔ d.W : Subgroup G) : Set G)
      intro x hx
      refine mem_normalizer_of_conj_mem (fun z hz => ?_) fun z hz => ?_
      · have e : x * z * x⁻¹ = ⁅x, z⁆ * z := by simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (d.V5_sup_A1_le_A1_sup_W (d.comm_mem_V5_sup_A1 hx (d.A1_sup_W_le_A hz)))
          hz
      · have e : x⁻¹ * z * x = ⁅x⁻¹, z⁆ * z := by simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem (d.V5_sup_A1_le_A1_sup_W
          (d.comm_mem_V5_sup_A1 (inv_mem hx) (d.A1_sup_W_le_A hz))) hz
  mem_normalizer := by
    intro i
    fin_cases i
    · change h.t ∈ normalizer ((⊥ : Subgroup G) : Set G)
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top _
    · exact d.J_le_normalizer_A1 h.t_mem_J
    · exact d.t_mem_normalizer_A1_sup_W
    · exact d.J_le_normalizer_A h.t_mem_J
  mul_self_mem := by
    intro i
    fin_cases i
    · intro x hx
      change x * x ∈ (⊥ : Subgroup G)
      rw [d.A1_mul_self hx]
      exact one_mem _
    · intro z hz
      change z * z ∈ d.A1
      obtain ⟨a, ha, w, hw, rfl⟩ := d.exists_mul_of_mem_A1_sup_W hz
      have e : a * w * (a * w) = a * (w * a * w⁻¹) * (w * w) := by group
      rw [e]
      exact mul_mem (mul_mem ha ((mem_normalizer_iff.1 (d.W_le_A hw).1 a).1 ha))
        (d.W12_le_A1 (d.bender.mul_self_mem w hw))
    · intro x hx
      exact d.V5_sup_A1_le_A1_sup_W (d.mul_self_mem_V5_sup_A1 hx)
  exists_commutator := by
    intro i
    fin_cases i
    · intro x hx hxt
      change x ∈ d.A1 at hx
      change h.t⁻¹ * x⁻¹ * h.t * x ∈ (⊥ : Subgroup G) at hxt
      change ∃ y ∈ d.A1, x⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ (⊥ : Subgroup G)
      rw [mem_bot] at hxt
      have hxc : ⁅x, h.t⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        calc x * h.t = x * (h.t * (h.t⁻¹ * x⁻¹ * h.t * x)) := by rw [hxt, mul_one]
          _ = h.t * x := by group
      obtain ⟨b, hb, hbt⟩ := d.exists_A1_comm_t (d.mem_R₁_of_mem_A1 hx hxc)
      refine ⟨b⁻¹, inv_mem hb, ?_⟩
      rw [mem_bot, show b⁻¹⁻¹ * (h.t⁻¹ * b⁻¹ * h.t) = ⁅b, h.t⁆ by
        rw [commutatorElement_def, inv_inv, h.t_inv]; group, hbt, inv_mul_cancel]
    · intro z hz hzt
      change z ∈ d.A1 ⊔ d.W at hz
      change h.t⁻¹ * z⁻¹ * h.t * z ∈ d.A1 at hzt
      change ∃ y ∈ d.A1 ⊔ d.W, z⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ d.A1
      obtain ⟨a, ha, w, hw, rfl⟩ := d.exists_mul_of_mem_A1_sup_W hz
      have htA1 := d.J_le_normalizer_A1 h.t_mem_J
      have hconjt : ∀ y ∈ d.A1, h.t⁻¹ * y * h.t ∈ d.A1 := fun y hy => by
        have := (mem_normalizer_iff.1 (inv_mem htA1) y).1 hy
        rwa [inv_inv] at this
      have hwN := (d.W_le_A hw).1
      have hwt : w⁻¹ * (h.t⁻¹ * w * h.t) ∈ zIn d.W := by
        have hA : w⁻¹ * (h.t⁻¹ * w * h.t) ∈ d.A1 := by
          have e : w⁻¹ * (h.t⁻¹ * w * h.t) = (w⁻¹ * (h.t⁻¹ * a⁻¹ * h.t * a) * w⁻¹⁻¹) *
              (h.t⁻¹ * (a * w)⁻¹ * h.t * (a * w))⁻¹ := by group
          rw [e]
          exact mul_mem ((mem_normalizer_iff.1 (inv_mem hwN) _).1
            (mul_mem (hconjt _ (inv_mem ha)) ha)) (inv_mem hzt)
        have hW : w⁻¹ * (h.t⁻¹ * w * h.t) ∈ d.W :=
          mul_mem (inv_mem hw) (d.bender.conj_mem w hw)
        show w⁻¹ * (h.t⁻¹ * w * h.t) ∈ d.W12
        rw [← d.WA_five_eq]
        exact ⟨hA, d.W_le_CH hW⟩
      obtain ⟨v, hv, u, hu, rfl⟩ := exists_mul_of_mem_sup_zIn d.bender.le
        (d.bender.mem_of_comm w hw hwt)
      obtain ⟨y, hy, hvy⟩ := d.bender.exists_comm_mod v hv
      refine ⟨y, mem_sup_right hy, ?_⟩
      have e : (a * (v * u))⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) =
          ((v * u)⁻¹ * a⁻¹ * (v * u)) * (u⁻¹ * (v⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)))) := by group
      rw [e]
      refine mul_mem ?_ (d.W12_le_A1 ?_)
      · have := (mem_normalizer_iff.1 (inv_mem hwN) _).1 (inv_mem ha)
        simpa [mul_assoc] using this
      · exact mul_mem (inv_mem hu) hvy
    · intro x hx hxt
      change x ∈ d.A at hx
      change h.t⁻¹ * x⁻¹ * h.t * x ∈ d.A1 ⊔ d.W at hxt
      change ∃ y ∈ d.A, x⁻¹ * (y⁻¹ * (h.t⁻¹ * y * h.t)) ∈ d.A1 ⊔ d.W
      have hx1 : ⁅x⁻¹, h.t⁆ ∈ h.V .i5 ⊔ d.A1 := by
        refine d.mem_V5_sup_A1_of_mem_A1_sup_W ?_ (inv_mem hx).2.2.2.2
        have e : ⁅x⁻¹, h.t⁆ = h.t * (h.t⁻¹ * x⁻¹ * h.t * x) * h.t⁻¹ := by
          rw [commutatorElement_def]; group
        rw [e]
        exact (mem_normalizer_iff.1 d.t_mem_normalizer_A1_sup_W _).1 hxt
      have hx1' : ⁅x⁻¹, h.t⁆ ∈ ((h.V .i5 ⊔ d.A1 : Subgroup G) : Set G) := hx1
      rw [coe_mul_of_left_le_normalizer_right (h.V .i5) d.A1 fun v hv =>
        d.R_le_normalizer_A1 (h.V_le_R (by decide) hv), Set.mem_mul] at hx1'
      obtain ⟨v, hv, a, ha, hva⟩ := hx1'
      obtain ⟨c, hcA, hcH, hc⟩ := d.exists_A_CH_comm_t (i := .i5) (h.V_le_R (by decide) hv)
        (h.V_le_CH (by decide) (Or.inl rfl) hv)
      have hcW : c ∈ d.W := d.A_inf_CH5_le_W ⟨hcA, hcH⟩
      have hxc : (x * c)⁻¹ ∈ d.RA1 := by
        rw [mul_inv_rev]
        refine d.inv_mul_mem_RA1_of_comm hcA (inv_mem hx) ?_
        rw [← hva, ← mul_assoc]
        exact mul_mem hc ha
      obtain ⟨r, hr, b, hb, hrb⟩ := d.exists_mul_of_mem_RA1 (inv_mem hxc)
      rw [inv_inv] at hrb
      obtain ⟨y', hy'A, hy'⟩ := d.exists_A_comm_t hr
      refine ⟨y'⁻¹, inv_mem hy'A, ?_⟩
      have hx' : x = r * b * c⁻¹ := by rw [← hrb]; group
      have e : x⁻¹ * (y'⁻¹⁻¹ * (h.t⁻¹ * y'⁻¹ * h.t)) =
          c * (b⁻¹ * (⁅y', h.t⁆⁻¹ * r)⁻¹) := by
        have ht : h.t⁻¹ = h.t := h.t_inv
        rw [hx', commutatorElement_def]
        calc (r * b * c⁻¹)⁻¹ * (y'⁻¹⁻¹ * (h.t⁻¹ * y'⁻¹ * h.t)) =
            c * (b⁻¹ * (r⁻¹ * (y' * h.t⁻¹ * y'⁻¹ * h.t))) := by group
          _ = c * (b⁻¹ * (r⁻¹ * (y' * h.t * y'⁻¹ * h.t⁻¹))) := by rw [ht]
          _ = _ := by group
      rw [e]
      exact mul_mem (mem_sup_right hcW) (mem_sup_left (mul_mem (inv_mem hb) (inv_mem hy')))

theorem miyamoto_1_3_A :
    {x | (∃ y ∈ d.A, x = h.t * y) ∧ orderOf x = 2} = {x | ∃ y ∈ d.A, x = y⁻¹ * h.t * y} ∧
      sectionCentralizer (zpowers h.t ⊔ d.A) d.A =
        d.A ⊔ (normalizer (d.A : Set G) ⊓ centralizer ({h.t} : Set G)) :=
  miyamoto_lemma_1_3 h.ht d.freeSeries_A

theorem normalizer_A_inf_C_le_J : normalizer (d.A : Set G) ⊓ h.C ≤ h.J := by
  intro x hx
  obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨hxC, ?_⟩
  have hxt : x * h.t = h.t * x := mem_centralizer_singleton_iff.1 hxC
  have key : ∀ {y : G}, y ∈ normalizer (d.A : Set G) → y * h.t = h.t * y → ∀ r ∈ h.R,
      y * r * y⁻¹ ∈ h.R := by
    intro y hyA hyt r hr
    refine d.mem_R_of_mem_A_of_comm ((mem_normalizer_iff.1 hyA r).1 (d.R_le_A hr)) ?_
    have hyt' : y * h.t * y⁻¹ = h.t := by rw [hyt, mul_inv_cancel_right]
    have hrt : ⁅r, h.t⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R_le_L hr))
    have e : ⁅y * r * y⁻¹, h.t⁆ = y * ⁅r, h.t⁆ * y⁻¹ := by
      conv_lhs => rw [← hyt']
      simp only [commutatorElement_def]; group
    rw [e, hrt, mul_one, mul_inv_cancel]
  refine mem_normalizer_of_conj_mem (key hxA hxt) fun r hr => ?_
  have hxt' : x⁻¹ * h.t = h.t * x⁻¹ := (Commute.inv_left (show Commute x h.t from hxt)).eq
  have := key (inv_mem hxA) hxt' r hr
  rwa [inv_inv] at this

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
