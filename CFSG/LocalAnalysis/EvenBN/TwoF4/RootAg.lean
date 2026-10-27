module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAf
public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootAe

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

instance normal_A1_RA1 : (d.A1.subgroupOf d.RA1).Normal :=
  normal_subgroupOf_of_le_normalizer fun _ hx => (d.RA1_le_A hx).1

theorem mk_eq_mk_iff (u v : d.RA1) :
    (QuotientGroup.mk u : d.RA1 ⧸ d.A1.subgroupOf d.RA1) = QuotientGroup.mk v ↔
      (u : G)⁻¹ * v ∈ d.A1 := by
  rw [QuotientGroup.eq, mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

@[expose] def kappa : d.A →* d.RA1 ⧸ d.A1.subgroupOf d.RA1 where
  toFun x := QuotientGroup.mk (⟨⁅(x : G), h.t⁆, x.2.2.2.2.2⟩ : d.RA1)
  map_one' := by
    rw [← QuotientGroup.mk_one, d.mk_eq_mk_iff]
    simp only [OneMemClass.coe_one, commutatorElement_one_left, inv_one, mul_one]
    exact one_mem _
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul, d.mk_eq_mk_iff]
    simp only [Subgroup.coe_mul]
    set u := ⁅(x : G) * y, h.t⁆ with hu
    have h1 := d.comm_t_mul_mem x.2 y.2
    rw [← hu] at h1
    have huN : u⁻¹ ∈ normalizer (d.A1 : Set G) :=
      (d.RA1_le_A (inv_mem (mul_mem x.2 y.2).2.2.2.2)).1
    have e : u⁻¹ * (⁅(x : G), h.t⁆ * ⁅(y : G), h.t⁆) =
        u⁻¹ * (u * (⁅(x : G), h.t⁆ * ⁅(y : G), h.t⁆)⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 huN _).1 (inv_mem h1)

theorem kappa_apply (x : d.A) :
    d.kappa x = QuotientGroup.mk (⟨⁅(x : G), h.t⁆, x.2.2.2.2.2⟩ : d.RA1) := rfl

theorem kappa_eq_iff (x y : d.A) :
    d.kappa x = d.kappa y ↔ ⁅(x : G), h.t⁆⁻¹ * ⁅(y : G), h.t⁆ ∈ d.A1 := by
  rw [kappa_apply, kappa_apply, d.mk_eq_mk_iff]

theorem kappa_eq_one_iff (x : d.A) : d.kappa x = 1 ↔ (x : G) ∈ d.RA1 := by
  rw [kappa_apply, ← QuotientGroup.mk_one, d.mk_eq_mk_iff]
  simp only [OneMemClass.coe_one, mul_one]
  exact ⟨fun hx => d.mem_RA1_of_comm_mem_A1 x.2 (by simpa using inv_mem hx),
    fun hx => inv_mem (d.comm_t_mem_A1_of_mem_RA1 hx)⟩

theorem quot_mul_comm (p q : d.RA1 ⧸ d.A1.subgroupOf d.RA1) : p * q = q * p := by
  induction p using QuotientGroup.induction_on with | H u => ?_
  induction q using QuotientGroup.induction_on with | H v => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, d.mk_eq_mk_iff]
  have := d.comm_RA1_RA1_mem (inv_mem v.2) (inv_mem u.2)
  convert this using 1
  simp only [Subgroup.coe_mul, commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]

theorem comm_mem_RA1 {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) : ⁅x, y⁆ ∈ d.RA1 := by
  have h1 : d.kappa ⁅(⟨x, hx⟩ : d.A), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, d.quot_mul_comm]
  have := (d.kappa_eq_one_iff _).1 h1
  simpa [commutatorElement_def] using this

theorem inv_mul_mem_RA1_of_comm {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A)
    (hxy : ⁅x, h.t⁆⁻¹ * ⁅y, h.t⁆ ∈ d.A1) : x⁻¹ * y ∈ d.RA1 := by
  have h1 : d.kappa ((⟨x, hx⟩ : d.A)⁻¹ * ⟨y, hy⟩) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one, d.kappa_eq_iff]
    exact hxy
  simpa using (d.kappa_eq_one_iff _).1 h1

theorem comm_inv_mul_mem_of_lifts {x y v w : G} (hxv : ⁅x, h.t⁆⁻¹ * v ∈ d.A1)
    (hvw : v⁻¹ * w ∈ d.A1) (hyw : ⁅y, h.t⁆⁻¹ * w ∈ d.A1) : ⁅x, h.t⁆⁻¹ * ⁅y, h.t⁆ ∈ d.A1 := by
  have e : ⁅x, h.t⁆⁻¹ * ⁅y, h.t⁆ = (⁅x, h.t⁆⁻¹ * v) * (v⁻¹ * w) * (⁅y, h.t⁆⁻¹ * w)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxv hvw) (inv_mem hyw)

theorem comm_mul_lift_mem {x x' v v' : G} (hx : x ∈ d.A) (hx' : x' ∈ d.A) (hv : v ∈ d.RA1)
    (hv' : v' ∈ d.RA1) (hxv : ⁅x, h.t⁆⁻¹ * v ∈ d.A1) (hxv' : ⁅x', h.t⁆⁻¹ * v' ∈ d.A1) :
    ⁅x * x', h.t⁆⁻¹ * (v * v') ∈ d.A1 := by
  have h1 : d.kappa (⟨x, hx⟩ * ⟨x', hx'⟩) =
      QuotientGroup.mk (⟨v, hv⟩ * ⟨v', hv'⟩ : d.RA1) := by
    rw [map_mul, QuotientGroup.mk_mul, kappa_apply, kappa_apply]
    congr 1
    · exact (d.mk_eq_mk_iff _ _).2 hxv
    · exact (d.mk_eq_mk_iff _ _).2 hxv'
  rw [kappa_apply, d.mk_eq_mk_iff] at h1
  simpa using h1

theorem conj_J_lift_mem {j x v : G} (hj : j ∈ h.J) (hxv : ⁅x, h.t⁆⁻¹ * v ∈ d.A1) :
    ⁅j * x * j⁻¹, h.t⁆⁻¹ * (j * v * j⁻¹) ∈ d.A1 := by
  have hjt : j * h.t = h.t * j := mem_centralizer_singleton_iff.1 (mem_inf.1 hj).1
  have hjt' : j * h.t * j⁻¹ = h.t := by rw [hjt, mul_inv_cancel_right]
  have e : ⁅j * x * j⁻¹, h.t⁆⁻¹ * (j * v * j⁻¹) = j * (⁅x, h.t⁆⁻¹ * v) * j⁻¹ := by
    simp only [commutatorElement_def]
    conv_lhs => rw [← hjt']
    group
  rw [e]
  exact (mem_normalizer_iff.1 (d.J_le_normalizer_A1 hj) _).1 hxv

@[expose] def imOf (M : Subgroup G) (hM : M ≤ d.A) : Subgroup G where
  carrier := {v | ∃ x ∈ M, ⁅x, h.t⁆⁻¹ * v ∈ d.A1}
  mul_mem' := fun {v v'} hv hv' => by
    obtain ⟨x, hx, hα⟩ := hv
    obtain ⟨x', hx', hα'⟩ := hv'
    refine ⟨x * x', mul_mem hx hx', ?_⟩
    set u := ⁅x, h.t⁆ with hu
    set w := ⁅x', h.t⁆ with hw
    set ε := ⁅x * x', h.t⁆ * (u * w)⁻¹ with hε
    have hεA : ε ∈ d.A1 := d.comm_t_mul_mem (hM hx) (hM hx')
    have huN : u ∈ normalizer (d.A1 : Set G) := (d.RA1_le_A (hM hx).2.2.2.2).1
    have hwN : w⁻¹ ∈ normalizer (d.A1 : Set G) := (d.RA1_le_A (inv_mem (hM hx').2.2.2.2)).1
    have e : ⁅x * x', h.t⁆⁻¹ * (v * v') =
        (w⁻¹ * (u⁻¹ * ε⁻¹ * u * (u⁻¹ * v)) * w⁻¹⁻¹) * (w⁻¹ * v') := by
      rw [hε]; group
    rw [e]
    refine mul_mem ((mem_normalizer_iff.1 hwN _).1 (mul_mem ?_ hα)) hα'
    have := (mem_normalizer_iff.1 (inv_mem huN) _).1 (inv_mem hεA)
    simpa [mul_assoc] using this
  one_mem' := ⟨1, one_mem _, by rw [commutatorElement_one_left, inv_one, one_mul]; exact one_mem _⟩
  inv_mem' := fun {v} hv => by
    obtain ⟨x, hx, hα⟩ := hv
    refine ⟨x⁻¹, inv_mem hx, ?_⟩
    set u := ⁅x, h.t⁆ with hu
    have huR : u ∈ d.RA1 := (hM hx).2.2.2.2
    have hδ : ⁅x⁻¹, u⁻¹⁆ ∈ d.A1 := d.comm_A_RA1_mem (inv_mem (hM hx)) (inv_mem huR)
    have e : ⁅x⁻¹, h.t⁆⁻¹ * v⁻¹ = u * ((⁅x⁻¹, u⁻¹⁆)⁻¹ * (u⁻¹ * v)⁻¹) * u⁻¹ := by
      rw [hu]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (d.RA1_le_A huR).1 _).1 (mul_mem (inv_mem hδ) (inv_mem hα))

theorem A_le_of_lifts {M : Subgroup G} (hMA : M ≤ d.A) (hRM : d.RA1 ≤ M)
    (hl : ∀ k ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx), ∀ c : h.K,
      ∃ x ∈ M, ⁅x, h.t⁆⁻¹ * h.elt (rootElt h.K h.a k c) ∈ d.A1) : d.A ≤ M := by
  have hR : h.R ≤ d.imOf M hMA := by
    refine h.pull_rootJoin_le fun k hk => h.V_le_of_forall_elt_mem fun c => ?_
    have h1 : ∀ k : Idx, k.isR1 = true → h.elt (rootElt h.K h.a k c) ∈ d.imOf M hMA :=
      fun k hk => ⟨1, one_mem _, by
        rw [commutatorElement_one_left, inv_one, one_mul]
        exact d.R₁_le_A1 (h.elt_rootElt_mem_R₁ hk c)⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hl .i3 (by decide) c
    · exact hl .i4 (by decide) c
    · exact hl .i5 (by decide) c
    · exact hl .i6 (by decide) c
    · exact hl .i7 (by decide) c
    · exact h1 .i9 rfl
    · exact h1 .i10 rfl
  intro x hx
  obtain ⟨r, hr, a, ha, hxt⟩ := d.exists_mul_of_mem_RA1 hx.2.2.2.2
  obtain ⟨m, hm, hmr⟩ := hR hr
  have hmx : m⁻¹ * x ∈ d.RA1 := by
    refine d.inv_mul_mem_RA1_of_comm (hMA hm) hx ?_
    rw [hxt, ← mul_assoc]
    exact mul_mem hmr ha
  have e : x = m * (m⁻¹ * x) := by group
  rw [e]
  exact mul_mem hm (hRM hmx)

theorem rb_comm_mul_left {x x' y : G} (hx : x ∈ d.A) (hx' : x' ∈ d.A) (hy : y ∈ d.A) {k : Idx}
    (hk : k.isR1 = true) : h.rb ⁅x * x', y⁆ k = h.rb ⁅x, y⁆ k + h.rb ⁅x', y⁆ k := by
  rw [commutatorElement_mul_left_eq,
    d.rb_mul (d.conj_A_mem_RA1 hx (d.comm_mem_RA1 hx' hy)) (d.comm_mem_RA1 hx hy) hk,
    d.rb_conj_A hx (d.comm_mem_RA1 hx' hy) hk, add_comm]

theorem rb_comm_mul_right {x y y' : G} (hx : x ∈ d.A) (hy : y ∈ d.A) (hy' : y' ∈ d.A) {k : Idx}
    (hk : k.isR1 = true) : h.rb ⁅x, y * y'⁆ k = h.rb ⁅x, y⁆ k + h.rb ⁅x, y'⁆ k := by
  rw [commutatorElement_mul_right_eq,
    d.rb_mul (d.comm_mem_RA1 hx hy) (d.conj_A_mem_RA1 hy (d.comm_mem_RA1 hx hy')) hk,
    d.rb_conj_A hy (d.comm_mem_RA1 hx hy') hk]

theorem rb_comm_eq_zero_left {x y : G} (hx : x ∈ d.RA1) (hy : y ∈ d.A) {k : Idx}
    (hk : k.isR1 = true) : h.rb ⁅x, y⁆ k = 0 := by
  rw [← commutatorElement_inv]
  exact d.rb_eq_zero_of_mem_A1 (inv_mem (d.comm_A_RA1_mem hy hx)) hk

theorem rb_comm_eq_zero_right {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.RA1) {k : Idx}
    (hk : k.isR1 = true) : h.rb ⁅x, y⁆ k = 0 :=
  d.rb_eq_zero_of_mem_A1 (d.comm_A_RA1_mem hx hy) hk

theorem rb_comm_swap {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) {k : Idx} (hk : k.isR1 = true) :
    h.rb ⁅y, x⁆ k = - h.rb ⁅x, y⁆ k := by
  have h1 := d.rb_mul (d.comm_mem_RA1 hx hy) (d.comm_mem_RA1 hy hx) hk
  rw [← commutatorElement_inv x y, mul_inv_cancel, d.rb_eq_zero_of_mem_A1 (one_mem _) hk] at h1
  rw [← commutatorElement_inv x y]
  linear_combination (-1 : h.K) * h1

theorem rb_comm_congr_left {x x' y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) (hxx : x⁻¹ * x' ∈ d.RA1)
    {k : Idx} (hk : k.isR1 = true) : h.rb ⁅x', y⁆ k = h.rb ⁅x, y⁆ k := by
  have e : x' = x * (x⁻¹ * x') := by group
  calc h.rb ⁅x', y⁆ k = h.rb ⁅x * (x⁻¹ * x'), y⁆ k := by rw [← e]
    _ = h.rb ⁅x, y⁆ k := by
      rw [d.rb_comm_mul_left hx (d.RA1_le_A hxx) hy hk, d.rb_comm_eq_zero_left hxx hy hk, add_zero]

theorem rb_comm_congr_right {x y y' : G} (hx : x ∈ d.A) (hy : y ∈ d.A) (hyy : y⁻¹ * y' ∈ d.RA1)
    {k : Idx} (hk : k.isR1 = true) : h.rb ⁅x, y'⁆ k = h.rb ⁅x, y⁆ k := by
  have e : y' = y * (y⁻¹ * y') := by group
  calc h.rb ⁅x, y'⁆ k = h.rb ⁅x, y * (y⁻¹ * y')⁆ k := by rw [← e]
    _ = h.rb ⁅x, y⁆ k := by
      rw [d.rb_comm_mul_right hx hy (d.RA1_le_A hyy) hk, d.rb_comm_eq_zero_right hx hyy hk,
        add_zero]

theorem rb_comm_eq_of_lifts {x y x' y' v w v' w' : G} (hx : x ∈ d.A) (hy : y ∈ d.A)
    (hx' : x' ∈ d.A) (hy' : y' ∈ d.A) (hxv : ⁅x, h.t⁆⁻¹ * v ∈ d.A1) (hvv : v⁻¹ * v' ∈ d.A1)
    (hx'v : ⁅x', h.t⁆⁻¹ * v' ∈ d.A1) (hyw : ⁅y, h.t⁆⁻¹ * w ∈ d.A1) (hww : w⁻¹ * w' ∈ d.A1)
    (hy'w : ⁅y', h.t⁆⁻¹ * w' ∈ d.A1) {k : Idx} (hk : k.isR1 = true) :
    h.rb ⁅x, y⁆ k = h.rb ⁅x', y'⁆ k := by
  have h1 := d.inv_mul_mem_RA1_of_comm hx hx' (d.comm_inv_mul_mem_of_lifts hxv hvv hx'v)
  have h2 := d.inv_mul_mem_RA1_of_comm hy hy' (d.comm_inv_mul_mem_of_lifts hyw hww hy'w)
  rw [← d.rb_comm_congr_left hx hy h1 hk, ← d.rb_comm_congr_right hx' hy h2 hk]

theorem rb_comm_eq_of_lifts' {x y x' y' v w : G} (hx : x ∈ d.A) (hy : y ∈ d.A)
    (hx' : x' ∈ d.A) (hy' : y' ∈ d.A) (hxv : ⁅x, h.t⁆⁻¹ * v ∈ d.A1)
    (hx'v : ⁅x', h.t⁆⁻¹ * v ∈ d.A1) (hyw : ⁅y, h.t⁆⁻¹ * w ∈ d.A1)
    (hy'w : ⁅y', h.t⁆⁻¹ * w ∈ d.A1) {k : Idx} (hk : k.isR1 = true) :
    h.rb ⁅x, y⁆ k = h.rb ⁅x', y'⁆ k :=
  d.rb_comm_eq_of_lifts hx hy hx' hy' hxv (by rw [inv_mul_cancel]; exact one_mem _) hx'v hyw
    (by rw [inv_mul_cancel]; exact one_mem _) hy'w hk

theorem rb_comm_torus {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) (t : h.Kˣ × h.Kˣ) :
    h.rb ⁅h.elt (torusPair h.a t) * x * (h.elt (torusPair h.a t))⁻¹,
      h.elt (torusPair h.a t) * y * (h.elt (torusPair h.a t))⁻¹⁆ .i10 =
      (rootChar h.K h.a .i4 t : h.K) * h.rb ⁅x, y⁆ .i10 := by
  rw [← conjugate_commutatorElement]
  exact d.rb_torus_ten (d.comm_mem_RA1 hx hy) t

theorem rb_comm_conj_r {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) {k : Idx} (hk : k.isR1 = true)
    (hk12 : k ≠ .i12) :
    h.rb ⁅h.r * x * h.r⁻¹, h.r * y * h.r⁻¹⁆ k = h.rb ⁅x, y⁆ k.rPerm := by
  rw [← conjugate_commutatorElement]
  exact d.rb_conj_r (d.comm_mem_RA1 hx hy) hk hk12

theorem rb_comm_conj_one {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) (c : h.K) :
    h.rb ⁅(h.elt (rootElt h.K h.a .i1 c))⁻¹ * x * h.elt (rootElt h.K h.a .i1 c),
      (h.elt (rootElt h.K h.a .i1 c))⁻¹ * y * h.elt (rootElt h.K h.a .i1 c)⁆ .i10 =
      h.rb ⁅x, y⁆ .i10 + c * h.rb ⁅x, y⁆ .i11 := by
  have e := conjugate_commutatorElement x y (h.elt (rootElt h.K h.a .i1 c))⁻¹
  rw [inv_inv] at e
  rw [← e]
  exact d.rb_conj_one_ten (d.comm_mem_RA1 hx hy) c

open Classical in
@[expose] def liftR (v : G) : G := if hv : v ∈ h.R then (d.exists_A_comm_t hv).choose else 1

theorem liftR_spec {v : G} (hv : v ∈ h.R) : d.liftR v ∈ d.A ∧ ⁅d.liftR v, h.t⁆⁻¹ * v ∈ d.A1 := by
  unfold liftR
  split
  · exact (d.exists_A_comm_t ‹_›).choose_spec
  · contradiction

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.elt_rootElt_mem_R_of_row (h : Setup G)
    {k : Idx} (hk : k ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx)) (c : h.K) :
    h.elt (rootElt h.K h.a k c) ∈ h.R :=
  h.V_le_R (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp) (h.elt_rootElt_mem_V _ c)

theorem rootElt_add_mem {k : Idx} (hk : k ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (c c' : h.K) :
    (h.elt (rootElt h.K h.a k c) * h.elt (rootElt h.K h.a k c'))⁻¹ *
      h.elt (rootElt h.K h.a k (c + c')) ∈ d.A1 := by
  have hΓ : ∀ l c, rootElt h.K h.a l c ∈ F4.reeGamma h.K h.a := fun l c =>
    rootV_le_reeGamma h.card_K l (rootElt_mem_rootV _ _)
  have hlin : ∀ {l : Idx}, l.isSz = false → ∀ c c' : h.K,
      (h.elt (rootElt h.K h.a l c) * h.elt (rootElt h.K h.a l c'))⁻¹ *
        h.elt (rootElt h.K h.a l (c + c')) ∈ d.A1 := fun hl c c' => by
    rw [rootElt_add h.card_K hl, h.elt_mul' (hΓ _ _) (hΓ _ _), inv_mul_cancel]
    exact one_mem _
  have hsz : ∀ {l : Idx}, l.isSz = true → l.center.isR1 = true → ∀ c c' : h.K,
      (h.elt (rootElt h.K h.a l c) * h.elt (rootElt h.K h.a l c'))⁻¹ *
        h.elt (rootElt h.K h.a l (c + c')) ∈ d.A1 := fun hl hlc c c' => by
    rw [h.elt_rootElt_mul_of_isSz hl, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem (d.R₁_le_A1 (h.elt_rootElt_mem_R₁ hlc _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · exact hlin rfl c c'
  · exact hsz rfl rfl c c'
  · exact hsz rfl rfl c c'
  · exact hsz rfl rfl c c'
  · exact hlin rfl c c'

theorem pair_eq_zero_of_brace {a b : Idx} (ha : a ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (hb : b ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (hab : Idx.brace b a ≠ Idx.brace b .i4) (c e : h.K) :
    h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a c)), d.liftR (h.elt (rootElt h.K h.a b e))⁆ .i10 =
      0 := by
  set y := d.liftR (h.elt (rootElt h.K h.a b e)) with hydef
  obtain ⟨hyA, hy⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row hb e)
  have hb0 : b.isCenter = false := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rfl
  refine miyamoto_2_1 (K := h.K) (a := h.a) h.one_le_a h.card_K hb0 hab
    (φ := fun c => h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a c)), y⁆ .i10) (fun c c' => ?_)
    (fun t ht c => ?_) c
  · obtain ⟨h1A, h1⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row ha c)
    obtain ⟨h2A, h2⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row ha c')
    obtain ⟨h3A, h3⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row ha (c + c'))
    have hprod := d.comm_mul_lift_mem h1A h2A (d.R_le_RA1 (h.elt_rootElt_mem_R_of_row ha c))
      (d.R_le_RA1 (h.elt_rootElt_mem_R_of_row ha c')) h1 h2
    show h.rb ⁅d.liftR _, y⁆ .i10 = h.rb ⁅d.liftR _, y⁆ .i10 + h.rb ⁅d.liftR _, y⁆ .i10
    rw [← d.rb_comm_mul_left h1A h2A hyA rfl]
    exact d.rb_comm_eq_of_lifts h3A hyA (mul_mem h1A h2A) hyA h3
      (by simpa [mul_assoc] using inv_mem (d.rootElt_add_mem ha c c')) hprod hy
      (by simp) hy rfl
  · set τ := h.elt (torusPair h.a t) with hτ
    have hτJ : τ ∈ h.J := h.H_le_J (h.elt_torusPair_mem_H t)
    obtain ⟨h1A, h1⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row ha c)
    obtain ⟨h2A, h2⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row ha
      ((rootChar h.K h.a a t : h.K) * c))
    have hτ1 := d.conj_J_lift_mem hτJ h1
    rw [hτ, h.elt_torusPair_conj_rootElt t a c, ← hτ] at hτ1
    have hτy := d.conj_J_lift_mem hτJ hy
    rw [hτ, h.elt_torusPair_conj_rootElt t b e, (mem_torusHi_iff h.card_K b t).1 ht, Units.val_one,
      one_mul, ← hτ] at hτy
    show h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a ((rootChar h.K h.a a t : h.K) * c))), y⁆ .i10 =
      (rootChar h.K h.a .i4 t : h.K) * h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a c)), y⁆ .i10
    rw [d.rb_comm_eq_of_lifts' h2A hyA (d.conj_J_mem_A hτJ h1A) (d.conj_J_mem_A hτJ hyA) h2
      hτ1 hy hτy rfl, hτ]
    exact d.rb_comm_torus h1A hyA t

theorem pair_eq_zero_of_brace' {a b : Idx} (ha : a ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (hb : b ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (hab : Idx.brace a b ≠ Idx.brace a .i4) (c e : h.K) :
    h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a c)), d.liftR (h.elt (rootElt h.K h.a b e))⁆ .i10 =
      0 := by
  rw [d.rb_comm_swap (d.liftR_spec (h.elt_rootElt_mem_R_of_row hb e)).1
    (d.liftR_spec (h.elt_rootElt_mem_R_of_row ha c)).1 rfl,
    d.pair_eq_zero_of_brace hb ha hab e c, neg_zero]

theorem pair_four_four (c e : h.K) :
    h.rb ⁅d.liftR (h.elt (rootElt h.K h.a .i4 c)), d.liftR (h.elt (rootElt h.K h.a .i4 e))⁆ .i10 =
      0 := by
  have hlift : ∀ c : h.K, ∃ x ∈ d.A, x ∈ d.W6 ∧
      ⁅x, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i6 c) ∈ d.A1 := fun c => by
    obtain ⟨x, hxA, hxH, hx⟩ := d.exists_A_CH_comm_t (i := .i6)
      (h.V_le_R (by decide) (h.elt_rootElt_mem_V .i6 c))
      (h.V_le_CH (by decide) (Or.inl rfl) (h.elt_rootElt_mem_V .i6 c))
    exact ⟨x, hxA, d.A_inf_CH6_le_W6 ⟨hxA, hxH⟩, hx⟩
  obtain ⟨x, hxA, hxW, hx⟩ := hlift c
  obtain ⟨y, hyA, hyW, hy⟩ := hlift e
  have hrJ := h.r_mem_J
  have hx' : ⁅h.r * x * h.r⁻¹, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i4 c) ∈ d.A1 := by
    have := d.conj_J_lift_mem hrJ hx
    rwa [h.r_conj_elt_rootElt (by decide) (by decide)] at this
  have hy' : ⁅h.r * y * h.r⁻¹, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i4 e) ∈ d.A1 := by
    have := d.conj_J_lift_mem hrJ hy
    rwa [h.r_conj_elt_rootElt (by decide) (by decide)] at this
  obtain ⟨h1A, h1⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i4) (by decide) c)
  obtain ⟨h2A, h2⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i4) (by decide) e)
  rw [d.rb_comm_eq_of_lifts' h1A h2A (d.conj_J_mem_A hrJ hxA) (d.conj_J_mem_A hrJ hyA) h1
    hx' h2 hy' rfl, d.rb_comm_conj_r hxA hyA rfl (by decide)]
  exact d.rb_eq_zero_of_mem_A1 (d.W11_le_A1 (d.comm_W6_mem_W11 hxW hyW)) rfl

theorem pair_five_seven (c e : h.K) :
    h.rb ⁅d.liftR (h.elt (rootElt h.K h.a .i5 c)), d.liftR (h.elt (rootElt h.K h.a .i7 e))⁆ .i10 =
      0 := by
  obtain ⟨x, hxA, hxH, hx⟩ := d.exists_A_CH_comm_t (i := .i5)
    (h.V_le_R (by decide) (h.elt_rootElt_mem_V .i5 c))
    (h.V_le_CH (by decide) (Or.inl rfl) (h.elt_rootElt_mem_V .i5 c))
  have hxW : x ∈ d.W := d.A_inf_CH5_le_W ⟨hxA, hxH⟩
  obtain ⟨w, hwW, hwt⟩ := d.exists_W7_comm_t (h.elt_rootElt_mem_V .i7 e)
  obtain ⟨h1A, h1⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i5) (by decide) c)
  obtain ⟨h2A, h2⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i7) (by decide) e)
  rw [d.rb_comm_eq_of_lifts' h1A h2A hxA (d.W7_le_A hwW) h1 hx h2
    (show ⁅w, h.t⁆⁻¹ * h.elt (rootElt h.K h.a .i7 e) ∈ d.A1 by
      rw [hwt, inv_mul_cancel]; exact one_mem _) rfl]
  exact d.rb_eq_zero_of_mem_A1
    (d.B1_le_A1 (d.comm_B4_B3_mem_B1 (d.W_le_B4 hxW) (d.W7_le_B3 hwW))) rfl

theorem pair_eq_zero {a b : Idx} (ha : a ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx))
    (hb : b ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx)) (c e : h.K) :
    h.rb ⁅d.liftR (h.elt (rootElt h.K h.a a c)), d.liftR (h.elt (rootElt h.K h.a b e))⁆ .i10 =
      0 := by
  by_cases h44 : a = .i4 ∧ b = .i4
  · obtain ⟨rfl, rfl⟩ := h44
    exact d.pair_four_four c e
  by_cases h57 : a = .i5 ∧ b = .i7
  · obtain ⟨rfl, rfl⟩ := h57
    exact d.pair_five_seven c e
  by_cases h75 : a = .i7 ∧ b = .i5
  · obtain ⟨rfl, rfl⟩ := h75
    rw [d.rb_comm_swap (d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i5) (by decide) e)).1
      (d.liftR_spec (h.elt_rootElt_mem_R_of_row (k := .i7) (by decide) c)).1 rfl,
      d.pair_five_seven e c, neg_zero]
  have key : Idx.brace b a ≠ Idx.brace b .i4 ∨ Idx.brace a b ≠ Idx.brace a .i4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      simp_all <;> decide
  rcases key with hk | hk
  · exact d.pair_eq_zero_of_brace ha hb hk c e
  · exact d.pair_eq_zero_of_brace' ha hb hk c e

@[expose] def pairKer (x : G) (hx : x ∈ d.A) : Subgroup G where
  carrier := {y | y ∈ d.A ∧ h.rb ⁅x, y⁆ .i10 = 0}
  mul_mem' := fun {y y'} hy hy' => ⟨mul_mem hy.1 hy'.1, by
    rw [d.rb_comm_mul_right hx hy.1 hy'.1 rfl, hy.2, hy'.2, add_zero]⟩
  one_mem' := ⟨one_mem _, by
    rw [commutatorElement_one_right]
    exact d.rb_eq_zero_of_mem_A1 (one_mem _) rfl⟩
  inv_mem' := fun {y} hy => ⟨inv_mem hy.1, by
    have := d.rb_comm_mul_right hx hy.1 (inv_mem hy.1) (k := .i10) rfl
    rw [mul_inv_cancel, commutatorElement_one_right, d.rb_eq_zero_of_mem_A1 (one_mem _) rfl,
      hy.2, zero_add] at this
    exact this.symm⟩

@[expose] def pairRad : Subgroup G where
  carrier := {x | x ∈ d.A ∧ ∀ y ∈ d.A, h.rb ⁅x, y⁆ .i10 = 0}
  mul_mem' := fun {x x'} hx hx' => ⟨mul_mem hx.1 hx'.1, fun y hy => by
    rw [d.rb_comm_mul_left hx.1 hx'.1 hy rfl, hx.2 y hy, hx'.2 y hy, add_zero]⟩
  one_mem' := ⟨one_mem _, fun y _ => by
    rw [commutatorElement_one_left]
    exact d.rb_eq_zero_of_mem_A1 (one_mem _) rfl⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun y hy => by
    have := d.rb_comm_mul_left hx.1 (inv_mem hx.1) hy (k := .i10) rfl
    rw [mul_inv_cancel, commutatorElement_one_left, d.rb_eq_zero_of_mem_A1 (one_mem _) rfl,
      hx.2 y hy, zero_add] at this
    exact this.symm⟩

theorem rb_comm_ten_eq_zero {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) : h.rb ⁅x, y⁆ .i10 = 0 := by
  have hlift : ∀ k ∈ ({.i3, .i4, .i5, .i6, .i7} : Finset Idx), ∀ c : h.K,
      ∀ y ∈ d.A, h.rb ⁅d.liftR (h.elt (rootElt h.K h.a k c)), y⁆ .i10 = 0 := by
    intro k hk c y hy
    obtain ⟨hxA, -⟩ := d.liftR_spec (h.elt_rootElt_mem_R_of_row hk c)
    have hle := d.A_le_of_lifts (M := d.pairKer _ hxA) (fun _ hz => hz.1)
      (fun z hz => ⟨d.RA1_le_A hz, d.rb_comm_eq_zero_right hxA hz rfl⟩)
      (fun b hb e => ⟨d.liftR (h.elt (rootElt h.K h.a b e)),
        ⟨(d.liftR_spec (h.elt_rootElt_mem_R_of_row hb e)).1, d.pair_eq_zero hk hb c e⟩,
        (d.liftR_spec (h.elt_rootElt_mem_R_of_row hb e)).2⟩)
    exact (hle hy).2
  have hle := d.A_le_of_lifts (M := d.pairRad) (fun _ hz => hz.1)
    (fun z hz => ⟨d.RA1_le_A hz, fun y hy => d.rb_comm_eq_zero_left hz hy rfl⟩)
    (fun k hk c => ⟨d.liftR (h.elt (rootElt h.K h.a k c)),
      ⟨(d.liftR_spec (h.elt_rootElt_mem_R_of_row hk c)).1, hlift k hk c⟩,
      (d.liftR_spec (h.elt_rootElt_mem_R_of_row hk c)).2⟩)
  exact (hle hx).2 y hy

theorem comm_mem_V5_sup_A1 {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) :
    ⁅x, y⁆ ∈ h.V .i5 ⊔ d.A1 := by
  have hrJ := h.r_mem_J
  have h1J : (h.elt (rootElt h.K h.a .i1 1))⁻¹ ∈ h.J :=
    inv_mem (h.N1_le_J (h.V_le_N .i1 (h.elt_rootElt_mem_V .i1 1)))
  have hconj1 : ∀ {z : G}, z ∈ d.A →
      (h.elt (rootElt h.K h.a .i1 1))⁻¹ * z * h.elt (rootElt h.K h.a .i1 1) ∈ d.A := fun hz => by
    have := d.conj_J_mem_A h1J hz
    rwa [inv_inv] at this
  have h11 : ∀ {x y : G}, x ∈ d.A → y ∈ d.A → h.rb ⁅x, y⁆ .i11 = 0 := fun hx hy => by
    have := d.rb_comm_conj_one hx hy 1
    rw [d.rb_comm_ten_eq_zero (hconj1 hx) (hconj1 hy), d.rb_comm_ten_eq_zero hx hy, zero_add,
      one_mul] at this
    exact this.symm
  have h9 : h.rb ⁅x, y⁆ .i9 = 0 := by
    have := d.rb_comm_conj_r hx hy (k := .i10) rfl (by decide)
    rw [d.rb_comm_ten_eq_zero (d.conj_J_mem_A hrJ hx) (d.conj_J_mem_A hrJ hy)] at this
    exact this.symm
  have h8 : h.rb ⁅x, y⁆ .i8 = 0 := by
    have := d.rb_comm_conj_r hx hy (k := .i11) rfl (by decide)
    rw [h11 (d.conj_J_mem_A hrJ hx) (d.conj_J_mem_A hrJ hy)] at this
    exact this.symm
  exact d.mem_V5_sup_A1_of_rb (d.comm_mem_RA1 hx hy) (h11 hx hy) (d.rb_comm_ten_eq_zero hx hy) h9
    h8

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
