module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4c

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

@[expose] def RA1 : Subgroup G := h.R ⊔ d.A1

theorem R_le_RA1 : h.R ≤ d.RA1 := le_sup_left

theorem A1_le_RA1 : d.A1 ≤ d.RA1 := le_sup_right

theorem R_le_normalizer_A1 : h.R ≤ normalizer (d.A1 : Set G) :=
  h.R_le_J.trans d.J_le_normalizer_A1

theorem exists_mul_of_mem_RA1 {z : G} (hz : z ∈ d.RA1) : ∃ r ∈ h.R, ∃ a ∈ d.A1, z = r * a := by
  have hz' : z ∈ ((h.R ⊔ d.A1 : Subgroup G) : Set G) := hz
  rw [coe_mul_of_left_le_normalizer_right _ _ d.R_le_normalizer_A1, Set.mem_mul] at hz'
  obtain ⟨r, hr, a, ha, rfl⟩ := hz'
  exact ⟨r, hr, a, ha, rfl⟩

theorem conj_mem_RA1 {x : G} (hxN : x ∈ normalizer (d.A1 : Set G))
    (hxR : ∀ r ∈ h.R, ⁅x, r⁆ ∈ d.A1) {z : G} (hz : z ∈ d.RA1) : x * z * x⁻¹ ∈ d.RA1 := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1 hz
  have e : x * (r * a) * x⁻¹ = ⁅x, r⁆ * r * (x * a * x⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (mul_mem (d.A1_le_RA1 (hxR r hr)) (d.R_le_RA1 hr))
    (d.A1_le_RA1 ((mem_normalizer_iff.1 hxN a).1 ha))

theorem J_le_normalizer_RA1 : h.J ≤ normalizer (d.RA1 : Set G) := by
  have key : ∀ {j : G}, j ∈ h.J → ∀ z ∈ d.RA1, j * z * j⁻¹ ∈ d.RA1 := by
    intro j hj z hz
    have hle : d.RA1 ≤ d.RA1.comap (MulAut.conj j).toMonoidHom :=
      sup_le (fun r hr => d.R_le_RA1 ((mem_normalizer_iff.1 (mem_inf.1 hj).2 r).1 hr))
        (fun a ha => d.A1_le_RA1 ((mem_normalizer_iff.1 (d.J_le_normalizer_A1 hj) a).1 ha))
    exact hle hz
  intro j hj
  refine mem_normalizer_of_conj_mem (key hj) fun z hz => ?_
  have := key (inv_mem hj) z hz
  rwa [inv_inv] at this

@[expose] def A : Subgroup G where
  carrier := {x | x ∈ normalizer (d.A1 : Set G) ∧ x ∈ centralizer (d.W12 : Set G) ∧
    (∀ r ∈ h.R, ⁅x, r⁆ ∈ d.A1) ∧ (∀ a ∈ d.A1, ⁅x, a⁆ ∈ d.W12) ∧ ⁅x, h.t⁆ ∈ d.RA1}
  mul_mem' := fun {x y} hx hy => by
    refine ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, fun r hr => ?_, fun a ha => ?_, ?_⟩
    · rw [commutatorElement_mul_left_eq]
      exact mul_mem ((mem_normalizer_iff.1 hx.1 _).1 (hy.2.2.1 r hr)) (hx.2.2.1 r hr)
    · rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hx.2.1 _ (hy.2.2.2.1 a ha),
        mul_inv_cancel_right]
      exact mul_mem (hy.2.2.2.1 a ha) (hx.2.2.2.1 a ha)
    · rw [commutatorElement_mul_left_eq]
      exact mul_mem (d.conj_mem_RA1 hx.1 hx.2.2.1 hy.2.2.2.2) hx.2.2.2.2
  one_mem' := ⟨one_mem _, one_mem _, fun r _ => by rw [commutatorElement_one_left]; exact one_mem _,
    fun a _ => by rw [commutatorElement_one_left]; exact one_mem _,
    by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => by
    have e : ∀ y : G, ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := fun y => by
      simp only [commutatorElement_def]
      group
    have hR : ∀ r ∈ h.R, ⁅x⁻¹, r⁆ ∈ d.A1 := fun r hr => by
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem hx.1) _).1 (inv_mem (hx.2.2.1 r hr))
    refine ⟨inv_mem hx.1, inv_mem hx.2.1, hR, fun a ha => ?_, ?_⟩
    · rw [e, ← mem_centralizer_iff.1 (inv_mem hx.2.1) _ (inv_mem (hx.2.2.2.1 a ha)),
        mul_inv_cancel_right]
      exact inv_mem (hx.2.2.2.1 a ha)
    · rw [e]
      exact d.conj_mem_RA1 (inv_mem hx.1) hR (inv_mem hx.2.2.2.2)

theorem conj_A_mem_RA1 {x z : G} (hx : x ∈ d.A) (hz : z ∈ d.RA1) : x * z * x⁻¹ ∈ d.RA1 :=
  d.conj_mem_RA1 hx.1 hx.2.2.1 hz

theorem comm_A_RA1_mem {x z : G} (hx : x ∈ d.A) (hz : z ∈ d.RA1) : ⁅x, z⁆ ∈ d.A1 := by
  obtain ⟨r, hr, a, ha, rfl⟩ := d.exists_mul_of_mem_RA1 hz
  rw [commutatorElement_mul_right_eq]
  exact mul_mem (hx.2.2.1 r hr) ((mem_normalizer_iff.1 (d.R_le_normalizer_A1 hr) _).1
    (d.W12_le_A1 (hx.2.2.2.1 a ha)))

theorem conj_J_mem_A {j x : G} (hj : j ∈ h.J) (hx : x ∈ d.A) : j * x * j⁻¹ ∈ d.A := by
  have hjA := d.J_le_normalizer_A1 hj
  have hjW := d.J_le_normalizer_W12 hj
  have hjR : j ∈ normalizer (h.R : Set G) := (mem_inf.1 hj).2
  have hjt : j * h.t = h.t * j := mem_centralizer_singleton_iff.1 (mem_inf.1 hj).1
  have e : ∀ y : G, ⁅j * x * j⁻¹, y⁆ = j * ⁅x, j⁻¹ * y * j⁻¹⁻¹⁆ * j⁻¹ := fun y => by
    simp only [commutatorElement_def]
    group
  have hconj : ∀ {M : Subgroup G}, j ∈ normalizer (M : Set G) → ∀ y ∈ M, j⁻¹ * y * j⁻¹⁻¹ ∈ M :=
    fun hM y hy => (mem_normalizer_iff.1 (inv_mem hM) y).1 hy
  refine ⟨mul_mem (mul_mem hjA hx.1) (inv_mem hjA), ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
  · exact (mem_normalizer_iff.1 (mem_normalizer_centralizer hjW) x).1 hx.2.1
  · rw [e]
    exact (mem_normalizer_iff.1 hjA _).1 (hx.2.2.1 _ (hconj hjR r hr))
  · rw [e]
    exact (mem_normalizer_iff.1 hjW _).1 (hx.2.2.2.1 _ (hconj hjA a ha))
  · rw [e, show j⁻¹ * h.t * j⁻¹⁻¹ = h.t by rw [inv_inv, mul_assoc, ← hjt, inv_mul_cancel_left]]
    exact (mem_normalizer_iff.1 (d.J_le_normalizer_RA1 hj) _).1 hx.2.2.2.2

theorem J_le_normalizer_A : h.J ≤ normalizer (d.A : Set G) := fun j hj =>
  mem_normalizer_of_conj_mem (fun x hx => d.conj_J_mem_A hj hx) fun x hx => by
    have := d.conj_J_mem_A (inv_mem hj) hx
    rwa [inv_inv] at this

theorem A1_le_A : d.A1 ≤ d.A := fun x hx => by
  refine ⟨le_normalizer hx, hx.2.1, fun r hr => ?_, fun a ha => ?_,
    d.A1_le_RA1 (d.R₁_le_A1 hx.2.2)⟩
  · rw [← commutatorElement_inv]
    exact inv_mem (d.W12_le_A1 (d.commutator_R_A1_le (commutator_mem_commutator hr hx)))
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (d.A1_comm hx ha)]
    exact one_mem _

theorem R_le_A : h.R ≤ d.A := fun r hr => by
  refine ⟨d.R_le_normalizer_A1 hr, mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 (d.W12_le_centralizer_R hz) r hr).symm, fun r' hr' => ?_,
    fun a ha => d.commutator_R_A1_le (commutator_mem_commutator hr ha), ?_⟩
  · have := commutator_mem_commutator hr hr'
    rw [h.commutator_R_R] at this
    exact d.R₁_le_A1 this
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.R_le_L hr))]
    exact one_mem _

theorem RA1_le_A : d.RA1 ≤ d.A := sup_le d.R_le_A d.A1_le_A

theorem comm_RA1_RA1_mem {z z' : G} (hz : z ∈ d.RA1) (hz' : z' ∈ d.RA1) : ⁅z, z'⁆ ∈ d.A1 :=
  d.comm_A_RA1_mem (d.RA1_le_A hz) hz'

theorem t_not_mem_A : h.t ∉ d.A := by
  intro ht
  obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := .i10) (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) (h.elt_rootElt_mem_V .i10 1)
  have h1 := ht.2.2.2.1 w hw.1
  rw [← commutatorElement_inv, hwt] at h1
  have h2 := inv_mem h1
  rw [inv_inv] at h2
  have h3 := d.mem_V12_of_commute h2 (h.mul_t_comm (h.pull_le_L _ (h.elt_rootElt_mem_V .i10 1)))
  have h0 := h.r1c_eq_zero_of_mem_V12 h3 (k := .i10) rfl (by decide)
  rw [h.r1c_elt_rootElt rfl 1 rfl, Pi.single_eq_same] at h0
  exact one_ne_zero h0

theorem comm_t_mul_mem {x y : G} (hx : x ∈ d.A) (hy : y ∈ d.A) :
    ⁅x * y, h.t⁆ * (⁅x, h.t⁆ * ⁅y, h.t⁆)⁻¹ ∈ d.A1 := by
  have e : ⁅x * y, h.t⁆ * (⁅x, h.t⁆ * ⁅y, h.t⁆)⁻¹ =
      ⁅x, ⁅y, h.t⁆⁆ * ⁅⁅y, h.t⁆, ⁅x, h.t⁆⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (d.comm_A_RA1_mem hx hy.2.2.2.2) (d.comm_RA1_RA1_mem hy.2.2.2.2 hx.2.2.2.2)

theorem mem_RA1_of_comm_mem_A1 {x : G} (hx : x ∈ d.A) (hxt : ⁅x, h.t⁆ ∈ d.A1) :
    x ∈ d.RA1 := by
  have ht : h.t⁻¹ = h.t := h.t_inv
  have htt : h.t * ⁅x, h.t⁆ * h.t⁻¹ = ⁅x, h.t⁆⁻¹ := by
    calc h.t * ⁅x, h.t⁆ * h.t⁻¹ = h.t * x * h.t * x⁻¹ * (h.t⁻¹ * h.t⁻¹) := by
          rw [commutatorElement_def]; group
      _ = h.t * x * h.t * x⁻¹ := by rw [ht, h.t_mul_t, mul_one]
      _ = ⁅x, h.t⁆⁻¹ := by
          rw [commutatorElement_def]
          simp only [mul_inv_rev, inv_inv, ht, mul_assoc]
  have hR1 : ⁅x, h.t⁆ ∈ h.R₁ := by
    refine d.mem_R₁_of_mem_A1 hxt ?_
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h1 : h.t * ⁅x, h.t⁆ * h.t⁻¹ = ⁅x, h.t⁆ := by
      rw [htt]
      exact inv_eq_of_mul_eq_one_left (d.A1_mul_self hxt)
    calc ⁅x, h.t⁆ * h.t = h.t * ⁅x, h.t⁆ * h.t⁻¹ * h.t := by rw [h1]
      _ = h.t * ⁅x, h.t⁆ := by group
  obtain ⟨b, hb, hbt⟩ := d.exists_A1_comm_t hR1
  set c := b⁻¹ * x with hc
  have hcA : c ∈ d.A := mul_mem (inv_mem (d.A1_le_A hb)) hx
  have hct : c ∈ h.C := by
    refine mem_centralizer_singleton_iff.2 ?_
    have e1 : ⁅c, h.t⁆ = 1 := by
      rw [hc, commutatorElement_mul_left_eq, d.comm_t_inv_A1 hb, hbt, inv_inv,
        d.A1_comm (inv_mem hb) hxt]
      group
    exact commutatorElement_eq_one_iff_mul_comm.1 e1
  have hcE : c ∈ h.CE := mem_inf.2 ⟨hct, centralizer_le
    (SetLike.coe_subset_coe.2 d.V12_le_W12) hcA.2.1⟩
  have hm1 : ∀ {r m : G}, r ∈ h.R → m ∈ h.N .i1 → (∀ y ∈ h.R₁, ⁅r * m, y⁆ ∈ d.W12) → m = 1 := by
    intro r m hr hm hrm
    refine h.eq_one_of_mem_N1_of_comm_mem_V12 hm fun y hy => ?_
    have hry : ⁅r, y⁆ ∈ h.V .i12 := by
      rw [← h.commutator_R_R₁]
      exact commutator_mem_commutator hr hy
    have hmy : ⁅m, y⁆ ∈ d.W12 := by
      have e : ⁅m, y⁆ = r⁻¹ * (⁅r * m, y⁆ * ⁅r, y⁆⁻¹) * r := by
        rw [commutatorElement_mul_left_eq]
        group
      have hz : ⁅r * m, y⁆ * ⁅r, y⁆⁻¹ ∈ d.W12 :=
        mul_mem (hrm y hy) (inv_mem (d.V12_le_W12 hry))
      rw [e, mem_centralizer_iff.1 (d.W12_le_centralizer_R hz) r⁻¹ (inv_mem hr),
        inv_mul_cancel_right]
      exact hz
    have hmyL : ⁅m, y⁆ ∈ h.L := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (h.N_le_L _ hm) (h.pull_le_L _ hy))
        (inv_mem (h.N_le_L _ hm))) (inv_mem (h.pull_le_L _ hy))
    exact d.mem_V12_of_commute hmy (h.mul_t_comm hmyL)
  have hx' : x = b * c := by rw [hc]; group
  obtain ⟨r, hr, m, hm, hcm | hcm⟩ := h.exists_of_mem_CE hcE
  · have hm' : m = 1 := hm1 hr hm fun y hy => by
      rw [← hcm]
      exact hcA.2.2.2.1 y (d.R₁_le_A1 hy)
    rw [hm', mul_one] at hcm
    rw [hx', hcm]
    exact mul_mem (d.A1_le_RA1 hb) (d.R_le_RA1 hr)
  · have hm' : m = 1 := hm1 hr hm fun y hy => by
      have e : ⁅r * m, y⁆ = ⁅c, y⁆ := by
        rw [hcm, commutatorElement_mul_left_eq (r * m) h.t y,
          commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hy)).symm]
        group
      rw [e]
      exact hcA.2.2.2.1 y (d.R₁_le_A1 hy)
    rw [hm', mul_one] at hcm
    refine absurd ?_ d.t_not_mem_A
    have e : h.t = r⁻¹ * c := by rw [hcm]; group
    rw [e]
    exact mul_mem (inv_mem (d.R_le_A hr)) hcA

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
