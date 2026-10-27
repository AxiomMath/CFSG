module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB4b

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

@[expose] def Q4 : Subgroup G := h.S₄ ⊔ d.B2

theorem S₄_le_Q4 : h.S₄ ≤ d.Q4 := le_sup_left

theorem B2_le_Q4 : d.B2 ≤ d.Q4 := le_sup_right

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.S₄_le_Kp (h : Setup G) : h.S₄ ≤ h.Kp :=
  h.S₂_le_S₃_le_S₄_le_S.2.2.1.trans
    (h.S₂_le_S₃_le_S₄_le_S.2.2.2.1.trans h.S₂_le_S₃_le_S₄_le_S.2.2.2.2)

theorem Q4_le_normalizer_B2 : d.Q4 ≤ normalizer (d.B2 : Set G) :=
  sup_le (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2) le_normalizer

theorem comm_mem_B2_of_mem_normalizer {x b : G} (hx : x ∈ normalizer (d.B2 : Set G))
    (hb : b ∈ d.B2) : ⁅x, b⁆ ∈ d.B2 := by
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 hx b).1 hb) (inv_mem hb)

theorem comm_Q4_mem_B2 {x : G} (hxN : x ∈ normalizer (d.B2 : Set G))
    (hxS : ∀ v ∈ h.S₄, ⁅x, v⁆ ∈ d.B2) {q : G} (hq : q ∈ d.Q4) : ⁅x, q⁆ ∈ d.B2 := by
  have hle : d.Q4 ≤ commRightIn x d.B2 :=
    sup_le (fun v hv => mem_commRightIn.2 ⟨d.Q4_le_normalizer_B2 (d.S₄_le_Q4 hv), hxS v hv⟩)
      (fun b hb => mem_commRightIn.2 ⟨le_normalizer hb, d.comm_mem_B2_of_mem_normalizer hxN hb⟩)
  exact (mem_commRightIn.1 (hle hq)).2

theorem comm_Q4_Q4_mem {q q' : G} (hq : q ∈ d.Q4) (hq' : q' ∈ d.Q4) : ⁅q, q'⁆ ∈ d.B2 := by
  have hle : d.Q4 ≤ commLeftIn q' d.B2 := by
    refine sup_le (fun v hv => mem_commLeftIn.2 ⟨d.Q4_le_normalizer_B2 (d.S₄_le_Q4 hv), ?_⟩)
      (fun b hb => mem_commLeftIn.2 ⟨le_normalizer hb, ?_⟩)
    · exact d.comm_Q4_mem_B2 (d.Q4_le_normalizer_B2 (d.S₄_le_Q4 hv))
        (fun w hw => d.S₂_le_B2 (h.comm_S₄_S₄_mem hv hw)) hq'
    · rw [← commutatorElement_inv]
      exact inv_mem (d.comm_mem_B2_of_mem_normalizer (d.Q4_le_normalizer_B2 hq') hb)
  exact (mem_commLeftIn.1 (hle hq)).2

theorem comm_t_mem_B2_of_mem_Q4 {q : G} (hq : q ∈ d.Q4) : ⁅q, h.t⁆ ∈ d.B2 := by
  have htK : h.t ∈ h.Kp := h.P_sup_Tsyl_le_J_Kp.2 (mem_sup_right h.t_mem_Tsyl)
  have hle : d.Q4 ≤ commLeftIn h.t d.B2 := by
    refine sup_le (fun v hv => mem_commLeftIn.2 ⟨d.Q4_le_normalizer_B2 (d.S₄_le_Q4 hv), ?_⟩)
      (fun b hb => mem_commLeftIn.2 ⟨le_normalizer hb, ?_⟩)
    · rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hv))]
      exact one_mem _
    · rw [← commutatorElement_inv]
      exact inv_mem (d.comm_mem_B2_of_mem_normalizer (d.Kp_le_normalizer_B2 htK) hb)
  exact (mem_commLeftIn.1 (hle hq)).2

theorem isPGroup_B2 : IsPGroup 2 d.B2 := fun g =>
  ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (d.B2_mul_self g.2)⟩

theorem isPGroup_Q4 : IsPGroup 2 d.Q4 :=
  (h.isPGroup_P.to_le (h.S₂_le_S₃_le_S₄_le_S.2.2.1.trans
    h.S₂_le_S₃_le_S₄_le_S.2.2.2.1)).to_sup_of_normal_right' d.isPGroup_B2
    (h.S₄_le_Kp.trans d.Kp_le_normalizer_B2)

theorem conj_mem_Q4 {x : G} (hxN : x ∈ normalizer (d.B2 : Set G))
    (hxS : ∀ v ∈ h.S₄, ⁅x, v⁆ ∈ d.B2) {q : G} (hq : q ∈ d.Q4) : x * q * x⁻¹ ∈ d.Q4 := by
  have e : x * q * x⁻¹ = ⁅x, q⁆ * q := by simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (d.B2_le_Q4 (d.comm_Q4_mem_B2 hxN hxS hq)) hq

@[expose] def B4 : Subgroup G where
  carrier := {x | x ∈ normalizer (d.B2 : Set G) ∧ x ∈ centralizer (h.S₂ : Set G) ∧
    (∀ v ∈ h.S₄, ⁅x, v⁆ ∈ d.B2) ∧ (∀ b ∈ d.B2, ⁅x, b⁆ ∈ h.S₁) ∧ ⁅x, h.t⁆ ∈ d.Q4}
  mul_mem' := fun {x y} hx hy => by
    have hS12 : h.S₁ ≤ h.S₂ := h.S₁_le_S₂_le_S₃_le_S₄_le_S.1
    refine ⟨mul_mem hx.1 hy.1, mul_mem hx.2.1 hy.2.1, fun v hv => ?_, fun b hb => ?_, ?_⟩
    · rw [commutatorElement_mul_left_eq]
      exact mul_mem ((mem_normalizer_iff.1 hx.1 _).1 (hy.2.2.1 v hv)) (hx.2.2.1 v hv)
    · rw [commutatorElement_mul_left_eq, ← mem_centralizer_iff.1 hx.2.1 _
        (hS12 (hy.2.2.2.1 b hb)), mul_inv_cancel_right]
      exact mul_mem (hy.2.2.2.1 b hb) (hx.2.2.2.1 b hb)
    · rw [commutatorElement_mul_left_eq]
      exact mul_mem (d.conj_mem_Q4 hx.1 hx.2.2.1 hy.2.2.2.2) hx.2.2.2.2
  one_mem' := ⟨one_mem _, one_mem _, fun v _ => by rw [commutatorElement_one_left]; exact one_mem _,
    fun b _ => by rw [commutatorElement_one_left]; exact one_mem _,
    by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := fun {x} hx => by
    have hS12 : h.S₁ ≤ h.S₂ := h.S₁_le_S₂_le_S₃_le_S₄_le_S.1
    have e : ∀ y : G, ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x⁻¹⁻¹ := fun y => by
      simp only [commutatorElement_def]
      group
    have hS : ∀ v ∈ h.S₄, ⁅x⁻¹, v⁆ ∈ d.B2 := fun v hv => by
      rw [e]
      exact (mem_normalizer_iff.1 (inv_mem hx.1) _).1 (inv_mem (hx.2.2.1 v hv))
    refine ⟨inv_mem hx.1, inv_mem hx.2.1, hS, fun b hb => ?_, ?_⟩
    · have h1 := hS12 (inv_mem (hx.2.2.2.1 b hb))
      rw [e, ← mem_centralizer_iff.1 (inv_mem hx.2.1) _ h1, mul_inv_cancel_right]
      exact inv_mem (hx.2.2.2.1 b hb)
    · rw [e]
      exact d.conj_mem_Q4 (inv_mem hx.1) hS (inv_mem hx.2.2.2.2)

theorem comm_B4_Q4_mem {x q : G} (hx : x ∈ d.B4) (hq : q ∈ d.Q4) : ⁅x, q⁆ ∈ d.B2 :=
  d.comm_Q4_mem_B2 hx.1 hx.2.2.1 hq

theorem conj_B4_mem_Q4 {x q : G} (hx : x ∈ d.B4) (hq : q ∈ d.Q4) : x * q * x⁻¹ ∈ d.Q4 :=
  d.conj_mem_Q4 hx.1 hx.2.2.1 hq

theorem conj_Kp_mem_B4 {k x : G} (hk : k ∈ h.Kp) (hx : x ∈ d.B4) : k * x * k⁻¹ ∈ d.B4 := by
  obtain ⟨hN2, hN3, hN4⟩ := h.Kp_le_normalizer_S₂_S₃_S₄
  have hNB := d.Kp_le_normalizer_B2 hk
  have hN1 := h.Kp_le_normalizer_S₁ hk
  have hkt : k * h.t = h.t * k := mem_centralizer_singleton_iff.1 hk.1
  have e : ∀ y : G, ⁅k * x * k⁻¹, y⁆ = k * ⁅x, k⁻¹ * y * k⁻¹⁻¹⁆ * k⁻¹ := fun y => by
    simp only [commutatorElement_def]
    group
  have hconj : ∀ {M : Subgroup G}, k ∈ normalizer (M : Set G) → ∀ y ∈ M, k⁻¹ * y * k⁻¹⁻¹ ∈ M :=
    fun hM y hy => (mem_normalizer_iff.1 (inv_mem hM) y).1 hy
  refine ⟨mul_mem (mul_mem hNB hx.1) (inv_mem hNB), ?_, fun v hv => ?_, fun b hb => ?_, ?_⟩
  · have := mem_normalizer_centralizer (hN2 hk)
    exact (mem_normalizer_iff.1 this x).1 hx.2.1
  · rw [e]
    exact (mem_normalizer_iff.1 hNB _).1 (hx.2.2.1 _ (hconj (hN4 hk) v hv))
  · rw [e]
    exact (mem_normalizer_iff.1 hN1 _).1 (hx.2.2.2.1 _ (hconj hNB b hb))
  · rw [e, show k⁻¹ * h.t * k⁻¹⁻¹ = h.t by rw [inv_inv, mul_assoc, ← hkt, inv_mul_cancel_left]]
    have hQ : k * ⁅x, h.t⁆ * k⁻¹ ∈ d.Q4 := by
      have hle : d.Q4 ≤ d.Q4.comap (MulAut.conj k).toMonoidHom :=
        sup_le (fun v hv => d.S₄_le_Q4 ((mem_normalizer_iff.1 (hN4 hk) v).1 hv))
          (fun b hb => d.B2_le_Q4 ((mem_normalizer_iff.1 hNB b).1 hb))
      exact hle hx.2.2.2.2
    exact hQ

theorem Kp_le_normalizer_B4 : h.Kp ≤ normalizer (d.B4 : Set G) := fun k hk =>
  mem_normalizer_of_conj_mem (fun x hx => d.conj_Kp_mem_B4 hk hx) fun x hx => by
    have := d.conj_Kp_mem_B4 (inv_mem hk) hx
    rwa [inv_inv] at this

theorem _root_.CFSG.LocalAnalysis.EvenBN.TwoF4.Setup.R₁_le_S₄_V12_le_S₁ (h : Setup G) :
    h.R₁ ≤ h.S₄ ∧ h.V .i12 ≤ h.S₁ :=
  ⟨h.pull_mono (rootJoin_mono (by decide)), h.pull_mono (rootV_le_rootJoin (by decide))⟩

theorem A1_le_B4 : d.A1 ≤ d.B4 := fun _ hx =>
  ⟨d.A1_le_normalizer_B2 hx,
    centralizer_le (SetLike.coe_subset_coe.2 h.S₂_le_R₁) (d.A1_le_centralizer_R₁ hx),
    fun _ hv => d.comm_A1_S₄_mem hx hv,
    fun _ hb => h.R₁_le_S₄_V12_le_S₁.2 (d.comm_A1_mem_V12 hx (d.B2_le_A1 hb)),
    d.S₄_le_Q4 (h.R₁_le_S₄_V12_le_S₁.1 hx.2.2)⟩

theorem Q4_le_B4 : d.Q4 ≤ d.B4 := by
  have hS1 : ∀ {x : G}, x ∈ d.B2 → ∀ v ∈ h.S₄, ⁅v, x⁆ = 1 := fun hx v hv =>
    commutatorElement_eq_one_iff_mul_comm.2
      (mem_centralizer_iff.1 (d.B2_le_centralizer_S₄ hx) v hv)
  refine sup_le (fun v hv => ⟨d.Q4_le_normalizer_B2 (d.S₄_le_Q4 hv), mem_centralizer_iff.2
      fun u hu => (mem_centralizer_iff.1 (h.S₂_le_centralizer_S₄ hu) v hv).symm,
    fun w hw => d.S₂_le_B2 (h.comm_S₄_S₄_mem hv hw), fun b hb => by
      rw [hS1 hb v hv]; exact one_mem _, by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (h.mul_t_comm (h.pull_le_L _ hv))]
      exact one_mem _⟩) fun b hb => d.A1_le_B4 (d.B2_le_A1 hb)

theorem t_not_mem_B4 : h.t ∉ d.B4 := by
  intro ht
  obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := .i10) (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) (h.elt_rootElt_mem_V .i10 1)
  have h1 := ht.2.2.2.1 w (mem_sup_left hw)
  rw [← commutatorElement_inv, hwt] at h1
  have h2 := inv_mem h1
  rw [inv_inv] at h2
  have hS1 : ∀ l ∈ ({.i11, .i12} : Finset Idx), l.isR1 = true := by decide
  have h2' : h.elt (rootElt h.K h.a .i10 1) ∈ h.pull (rootJoin h.K h.a {.i11, .i12}) := h2
  have h0 := h.r1c_eq_zero_of_mem hS1 h2' (k := .i10) rfl (by decide)
  rw [h.r1c_elt_rootElt rfl 1 rfl, Pi.single_eq_same] at h0
  exact one_ne_zero h0

theorem mem_Q4_of_comm_mem_B2 {x : G} (hx : x ∈ d.B4) (hxt : ⁅x, h.t⁆ ∈ d.B2) : x ∈ d.Q4 := by
  obtain ⟨b, hb, hc⟩ := d.exists_B2_mul_mem_C hxt
  have hcB : b⁻¹ * x ∈ d.B4 := mul_mem (inv_mem (d.Q4_le_B4 (d.B2_le_Q4 hb))) hx
  have hcS := h.C_inf_centralizer_S₂_le (mem_inf.2 ⟨hc, hcB.2.1⟩)
  obtain ⟨m, hm, hme | hme⟩ := h.exists_mul_of_mem_sup_zpowers_t (h.pull_le_L _) hcS
  · have e : x = b * (b⁻¹ * x) := by group
    rw [e, hme]
    exact mul_mem (d.B2_le_Q4 hb) (d.S₄_le_Q4 hm)
  · refine absurd ?_ d.t_not_mem_B4
    have e : h.t = m⁻¹ * (b⁻¹ * x) := by rw [hme]; group
    rw [e]
    exact mul_mem (inv_mem (d.Q4_le_B4 (d.S₄_le_Q4 hm))) hcB

theorem inv_mul_mem_Q4_of_comm {x y : G} (hx : x ∈ d.B4) (hy : y ∈ d.B4)
    (hxy : ⁅x, h.t⁆⁻¹ * ⁅y, h.t⁆ ∈ d.B2) : x⁻¹ * y ∈ d.Q4 := by
  refine d.mem_Q4_of_comm_mem_B2 (mul_mem (inv_mem hx) hy) ?_
  have e : ⁅x⁻¹ * y, h.t⁆ =
      x⁻¹ * (⁅x, h.t⁆ * (⁅x, h.t⁆⁻¹ * ⁅y, h.t⁆) * ⁅x, h.t⁆⁻¹) * x⁻¹⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine (mem_normalizer_iff.1 (inv_mem hx.1) _).1 ?_
  exact (mem_normalizer_iff.1 (d.Q4_le_normalizer_B2 hx.2.2.2.2) _).1 hxy

theorem comm_pow_mem {x : G} (hx : x ∈ d.B4) (k : ℕ) :
    ⁅x ^ k, h.t⁆ * (⁅x, h.t⁆ ^ k)⁻¹ ∈ d.B2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ⁅x ^ (k + 1), h.t⁆ * (⁅x, h.t⁆ ^ (k + 1))⁻¹ =
        (x * (⁅x ^ k, h.t⁆ * (⁅x, h.t⁆ ^ k)⁻¹) * x⁻¹) * ⁅x, ⁅x, h.t⁆ ^ k⁆ := by
      rw [pow_succ' x k, commutatorElement_mul_left_eq, pow_succ]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((mem_normalizer_iff.1 hx.1 _).1 ih)
      (d.comm_B4_Q4_mem hx (pow_mem hx.2.2.2.2 k))

theorem isPGroup_B4 : IsPGroup 2 d.B4 := by
  intro x
  obtain ⟨m, hm⟩ := d.isPGroup_Q4 ⟨_, (x.2 : (x : G) ∈ d.B4).2.2.2.2⟩
  have hm' : ⁅(x : G), h.t⁆ ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 := d.comm_pow_mem x.2 (2 ^ m)
  rw [hm', inv_one, mul_one] at h1
  have hQ := d.mem_Q4_of_comm_mem_B2 (pow_mem x.2 _) h1
  obtain ⟨m', hm''⟩ := d.isPGroup_Q4 ⟨_, hQ⟩
  refine ⟨m + m', Subtype.ext ?_⟩
  have := congrArg Subtype.val hm''
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
  rw [pow_add, pow_mul, this]

@[expose] def imB4 : Subgroup G where
  carrier := {v | ∃ x ∈ d.B4, ∃ b ∈ d.B2, v = ⁅x, h.t⁆ * b}
  mul_mem' := fun {v v'} hv hv' => by
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    obtain ⟨x', hx', b', hb', rfl⟩ := hv'
    set a := ⁅x, h.t⁆ with ha
    set a' := ⁅x', h.t⁆ with ha'
    have haQ : a ∈ d.Q4 := hx.2.2.2.2
    have haQ' : a' ∈ d.Q4 := hx'.2.2.2.2
    set β := ⁅x, a'⁆ with hβ
    have hβB : β ∈ d.B2 := d.comm_B4_Q4_mem hx haQ'
    refine ⟨x * x', mul_mem hx hx', ⁅a⁻¹, a'⁻¹⁆ * ((a * a')⁻¹ * β⁻¹ * (a * a')⁻¹⁻¹) *
      (a'⁻¹ * b * a'⁻¹⁻¹) * b', ?_, ?_⟩
    · have hN := d.Q4_le_normalizer_B2
      exact mul_mem (mul_mem (mul_mem (d.comm_Q4_Q4_mem (inv_mem haQ) (inv_mem haQ'))
        ((mem_normalizer_iff.1 (hN (inv_mem (mul_mem haQ haQ'))) _).1 (inv_mem hβB)))
        ((mem_normalizer_iff.1 (hN (inv_mem haQ')) _).1 hb)) hb'
    · rw [commutatorElement_mul_left_eq]
      simp only [hβ, ha, ha', commutatorElement_def]
      group
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [commutatorElement_one_left, one_mul]⟩
  inv_mem' := fun {v} hv => by
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    set a := ⁅x, h.t⁆ with ha
    have haQ : a ∈ d.Q4 := hx.2.2.2.2
    set γ := ⁅x⁻¹, a⁻¹⁆ with hγ
    have hγB : γ ∈ d.B2 := d.comm_B4_Q4_mem (inv_mem hx) (inv_mem haQ)
    refine ⟨x⁻¹, inv_mem hx, a * (γ⁻¹ * b⁻¹) * a⁻¹, ?_, ?_⟩
    · exact (mem_normalizer_iff.1 (d.Q4_le_normalizer_B2 haQ) _).1
        (mul_mem (inv_mem hγB) (inv_mem hb))
    · simp only [hγ, ha, commutatorElement_def]
      group

theorem Kp_le_normalizer_imB4 : h.Kp ≤ normalizer (d.imB4 : Set G) := by
  have key : ∀ {k : G}, k ∈ h.Kp → ∀ v ∈ d.imB4, k * v * k⁻¹ ∈ d.imB4 := by
    intro k hk v hv
    obtain ⟨x, hx, b, hb, rfl⟩ := hv
    have hkt : k * h.t = h.t * k := mem_centralizer_singleton_iff.1 hk.1
    refine ⟨k * x * k⁻¹, d.conj_Kp_mem_B4 hk hx, k * b * k⁻¹,
      (mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 hk) b).1 hb, ?_⟩
    have hkt' : k * h.t * k⁻¹ = h.t := by rw [hkt, mul_inv_cancel_right]
    simp only [commutatorElement_def]
    conv_rhs => rw [← hkt']
    group
  intro k hk
  refine mem_normalizer_of_conj_mem (key hk) fun v hv => ?_
  have := key (inv_mem hk) v hv
  rwa [inv_inv] at this

theorem S₄_le_imB4 : h.S₄ ≤ d.imB4 := by
  have hV : ∀ {i k : Idx}, i.isCenter = false → k = i ∨ k = i.center →
      k ∈ ({.i8, .i9, .i10, .i11, .i12} : Finset Idx) → h.V k ≤ d.imB4 := by
    intro i k hi hk hkR v hv
    obtain ⟨w, hw, hwt⟩ := d.exists_WA_comm_t (i := i) (h.V_le_R₁ hkR) (h.V_le_CH hi hk) hv
    exact ⟨w, d.A1_le_B4 hw.1, 1, one_mem _, by rw [mul_one, hwt]⟩
  refine h.S₄_le_of_V8_V9 (fun v hv => ?_) (hV (i := .i4) rfl (Or.inr rfl) (by decide))
    (hV (i := .i9) rfl (Or.inl rfl) (by decide)) (fun c => ?_) ?_ ?_
  · obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t hv
    exact ⟨b, d.Q4_le_B4 (d.B2_le_Q4 hb), 1, one_mem _, by rw [mul_one, hbt]⟩
  · exact d.Kp_le_normalizer_imB4 (h.elt_rootElt_three_mem_Kp c)
  · exact d.Kp_le_normalizer_imB4 h.s_mem_Kp
  · exact fun b hb => d.Kp_le_normalizer_imB4 (h.H_le_Kp hb)

theorem exists_B4_comm_t {v : G} (hv : v ∈ h.S₄) : ∃ x ∈ d.B4, ∃ b ∈ d.B2, v = ⁅x, h.t⁆ * b :=
  d.S₄_le_imB4 hv

theorem B3_le_B4 : d.B3 ≤ d.B4 := by
  rw [d.B3_eq]
  refine sup_le (sup_le (fun y hy => ?_) fun y hy => d.A1_le_B4 hy.1) fun y hy =>
    d.A1_le_B4 (d.B2_le_A1 hy)
  have hz := d.A1_le_B4 ((d.mem_W7_iff).1 hy).1
  have := d.conj_Kp_mem_B4 (inv_mem h.s_mem_Kp) hz
  rwa [show h.s⁻¹ * (h.s * y * h.s⁻¹) * h.s⁻¹⁻¹ = y by group] at this

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
