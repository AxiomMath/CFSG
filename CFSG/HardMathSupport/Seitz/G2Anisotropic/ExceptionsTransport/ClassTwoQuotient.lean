module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

variable {G : Type*} [Group G]

structure ClassTwo (Q Z : Subgroup G) : Prop where
  le : Z ≤ Q
  central : ∀ q ∈ Q, ∀ z ∈ Z, q * z = z * q
  comm : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' * q⁻¹ * q'⁻¹ ∈ Z

namespace ClassTwo

variable {Q Z : Subgroup G}

instance normal [h : Fact (ClassTwo Q Z)] : (Z.subgroupOf Q).Normal where
  conj_mem := fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := h.out.central g g.2 n hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this, mul_inv_cancel_right]
    exact hn

end ClassTwo

abbrev V (Q Z : Subgroup G) : Type _ := Additive (Q ⧸ Z.subgroupOf Q)

namespace ClassTwo

variable {Q Z : Subgroup G}

theorem quot_mul_comm [h : Fact (ClassTwo Q Z)] (a b : Q ⧸ Z.subgroupOf Q) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have := h.out.comm (b⁻¹ : Q) (b⁻¹.2) (a⁻¹ : Q) (a⁻¹.2)
  simpa [mul_assoc] using this

instance [h : Fact (ClassTwo Q Z)] : AddCommGroup (V Q Z) :=
  { (inferInstance : AddGroup (V Q Z)) with
    add_comm := fun a b => quot_mul_comm (Q := Q) (Z := Z) (Additive.toMul a) (Additive.toMul b) }

section Maps

variable [Fact (ClassTwo Q Z)]

@[expose] def cls (q : Q) : V Q Z := Additive.ofMul (QuotientGroup.mk q)

theorem cls_mul (q q' : Q) : cls (Z := Z) (q * q') = cls q + cls q' := rfl

theorem cls_one : cls (Z := Z) (1 : Q) = 0 := rfl

omit [Fact (ClassTwo Q Z)] in
theorem cls_eq_iff (q q' : Q) : cls (Z := Z) q = cls q' ↔ ((q⁻¹ * q' : Q) : G) ∈ Z := by
  unfold cls
  rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf]

@[expose] def conjQ (g : G) (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : Q →* Q where
  toFun q := ⟨g * q * g⁻¹, hg q q.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[expose] def conjV (g : G) (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hgz : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z) :
    V Q Z →+ V Q Z :=
  MonoidHom.toAdditive (QuotientGroup.map (Z.subgroupOf Q) (Z.subgroupOf Q) (conjQ g hg)
    (fun n hn => by
      rw [Subgroup.mem_subgroupOf] at hn
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hgz _ hn))

theorem conjV_cls (g : G) (hg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hgz : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (q : Q) : conjV g hg hgz (cls q) = cls (conjQ g hg q) := rfl

end Maps

end ClassTwo

theorem norm_fixed {Q Z : Subgroup G} (h : ClassTwo Q Z) {g : G} (hg3 : g ^ 3 = 1)
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) (hgZ : ∀ z ∈ Z, g * z * g⁻¹ = z)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1 → z = 1) {q : G} (hq : q ∈ Q) :
    let y₁ := g * q * g⁻¹
    let y₂ := g * y₁ * g⁻¹
    q * y₁ * y₂ ∈ Q ∧ g * (q * y₁ * y₂) * g⁻¹ = q * y₁ * y₂ := by
  intro y₁ y₂
  have hy₁ : y₁ ∈ Q := hgQ q hq
  have hy₂ : y₂ ∈ Q := hgQ y₁ hy₁
  have hu : q * y₁ * y₂ ∈ Q := Q.mul_mem (Q.mul_mem hq hy₁) hy₂
  refine ⟨hu, ?_⟩
  set u := q * y₁ * y₂ with hu_def
  have hg3' : g * g * g = 1 := by simpa [pow_succ, mul_assoc] using hg3
  have hy₃ : g * y₂ * g⁻¹ = q := by
    simp only [y₂, y₁]
    calc g * (g * (g * q * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * q * (g * g * g)⁻¹ := by group
      _ = q := by rw [hg3']; simp
  have hgu : g * u * g⁻¹ = y₁ * y₂ * q := by
    have : g * u * g⁻¹ = (g * q * g⁻¹) * (g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) := by
      simp only [hu_def]; group
    rw [this, hy₃]
  set c := u⁻¹ * (g * u * g⁻¹) with hc_def
  have hcZ : c ∈ Z := by
    have := h.comm (y₁ * y₂)⁻¹ (Q.inv_mem (Q.mul_mem hy₁ hy₂)) q⁻¹ (Q.inv_mem hq)
    have e : c = (y₁ * y₂)⁻¹ * q⁻¹ * ((y₁ * y₂)⁻¹)⁻¹ * (q⁻¹)⁻¹ := by
      rw [hc_def, hgu]; simp only [hu_def]; group
    rw [e]; exact this
  have gc : g * c * g⁻¹ = c := hgZ c hcZ
  have k1 : g * u * g⁻¹ = u * c := by rw [hc_def]; group
  have k2 : g * (u * c) * g⁻¹ = u * c * c := by
    calc g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
      _ = u * c * c := by rw [k1, gc]
  have k3 : g * (u * c * c) * g⁻¹ = u * c * c * c := by
    calc g * (u * c * c) * g⁻¹ = (g * (u * c) * g⁻¹) * (g * c * g⁻¹) := by group
      _ = u * c * c * c := by rw [k2, gc]
  have k4 : g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ = u * c * c * c := by rw [k1, k2, k3]
  have k5 : g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ = u := by
    calc g * (g * (g * u * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * u * (g * g * g)⁻¹ := by group
      _ = u := by rw [hg3']; simp
  have hc3 : c ^ 3 = 1 := by
    have h6 : u * (c * c * c) = u * 1 := by
      calc u * (c * c * c) = u * c * c * c := by group
        _ = u := by rw [← k4, k5]
        _ = u * 1 := by rw [mul_one]
    have h7 := mul_left_cancel h6
    calc c ^ 3 = c * c * c := by rw [pow_succ, sq]
      _ = 1 := h7
  have hc1 : c = 1 := hZ3 c hcZ hc3
  rw [k1, hc1, mul_one]

theorem conj_eq_of_mul_comm {x z : G} (h : x * z = z * x) : x * z * x⁻¹ = z := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem central_closure {S : Set G} {Z : Subgroup G} (hS : ∀ s ∈ S, ∀ z ∈ Z, s * z = z * s) :
    ∀ q ∈ Subgroup.closure S, ∀ z ∈ Z, q * z = z * q := by
  intro q hq z hz
  have : Commute q z := by
    induction hq using Subgroup.closure_induction with
    | mem x hx => exact hS x hx z hz
    | one => exact Commute.one_left z
    | mul x y _ _ hx hy => exact hx.mul_left hy
    | inv x _ hx => exact hx.inv_left
  exact this.eq

theorem comm_mem_closure {S : Set G} {Z : Subgroup G} (hS : ∀ s ∈ S, ∀ z ∈ Z, s * z = z * s)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' * s⁻¹ * s'⁻¹ ∈ Z) :
    ∀ q ∈ Subgroup.closure S, ∀ q' ∈ Subgroup.closure S, q * q' * q⁻¹ * q'⁻¹ ∈ Z := by
  have hc := central_closure hS
  have hconj : ∀ x ∈ Subgroup.closure S, ∀ z ∈ Z, x * z * x⁻¹ = z :=
    fun x hx z hz => conj_eq_of_mul_comm (hc x hx z hz)
  have hconj' : ∀ x ∈ Subgroup.closure S, ∀ z ∈ Z, x⁻¹ * z * x = z := fun x hx z hz => by
    have := hconj x⁻¹ (Subgroup.inv_mem _ hx) z hz
    simpa using this
  have hinv : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ Z → b * a * b⁻¹ * a⁻¹ ∈ Z := fun a b h => by
    have := Z.inv_mem h
    convert this using 1
    group
  have h1 : ∀ s ∈ S, ∀ q' ∈ Subgroup.closure S, s * q' * s⁻¹ * q'⁻¹ ∈ Z := by
    intro s hs q' hq'
    induction hq' using Subgroup.closure_induction with
    | mem x hx => exact hcomm s hs x hx
    | one => simp
    | mul x y hx hy hxZ hyZ =>
      have e : s * (x * y) * s⁻¹ * (x * y)⁻¹ =
          (s * x * s⁻¹ * x⁻¹) * (x * (s * y * s⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e, hconj x hx _ hyZ]
      exact Z.mul_mem hxZ hyZ
    | inv x hx hxZ =>
      have e : s * x⁻¹ * s⁻¹ * x⁻¹⁻¹ = x⁻¹ * (x * s * x⁻¹ * s⁻¹) * x := by group
      rw [e, hconj' x hx _ (hinv _ _ hxZ)]
      exact hinv _ _ hxZ
  intro q hq q' hq'
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx q' hq'
  | one => simp
  | mul x y hxm hym hxZ hyZ =>
    have e : x * y * q' * (x * y)⁻¹ * q'⁻¹ =
        (x * (y * q' * y⁻¹ * q'⁻¹) * x⁻¹) * (x * q' * x⁻¹ * q'⁻¹) := by group
    rw [e, hconj x hxm _ hyZ]
    exact Z.mul_mem hyZ hxZ
  | inv x hxm hxZ =>
    have e : x⁻¹ * q' * x⁻¹⁻¹ * q'⁻¹ = x⁻¹ * (q' * x * q'⁻¹ * x⁻¹) * x := by group
    rw [e, hconj' x hxm _ (hinv _ _ hxZ)]
    exact hinv _ _ hxZ

theorem conj_mem_closure {S : Set G} {g : G} (h : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    ∀ q ∈ Subgroup.closure S, g * q * g⁻¹ ∈ Subgroup.closure S := by
  intro q hq
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [e]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ hx

theorem conj_eq_comm_mul (g h : G) : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
