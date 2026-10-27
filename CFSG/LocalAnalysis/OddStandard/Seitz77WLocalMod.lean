module

public import CFSG.LocalAnalysis.OddStandard.Seitz77WLocalQuot

public section

namespace CFSG.OddStandard.Seitz77

open CFSG.ComponentClassification.PSL3Four CFSG.Open Subgroup
open scoped commutatorElement

namespace Config25

variable {Q : Type} [Group Q] [Finite Q] {V : Subgroup Q} {t : Q} (c : Config25 Q V t)

section Identities

variable [V.Normal]

include c

omit [V.Normal] in
theorem V_conj {v : Q} (hv : v ∈ V) (y : Q) : y * v * y⁻¹ = v := by
  rw [← c.V_comm hv y, mul_assoc, mul_inv_cancel, mul_one]

theorem comm_symm (x y : Q) : ⁅x, y⁆ = ⁅y, x⁆ :=
  calc ⁅x, y⁆ = ⁅x, y⁆⁻¹ := (c.V_inv (c.comm_mem_V x y)).symm
    _ = ⁅y, x⁆ := commutatorElement_inv x y

theorem comm_mul_right (x y z : Q) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, c.V_conj (c.comm_mem_V x z) y]

theorem comm_mul_left (x y z : Q) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have e : ⁅x * y, z⁆ = (x * ⁅y, z⁆ * x⁻¹) * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, c.V_conj (c.comm_mem_V y z) x]
  exact (c.V_comm (c.comm_mem_V x z) _).symm

omit [V.Normal] in
theorem comm_V_right {v : Q} (hv : v ∈ V) (x : Q) : ⁅x, v⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (c.V_comm hv x).symm

omit [V.Normal] in
theorem comm_V_left {v : Q} (hv : v ∈ V) (x : Q) : ⁅v, x⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (c.V_comm hv x)

theorem sq_mul (x y : Q) : (x * y) * (x * y) = (x * x) * (y * y) * ⁅x, y⁆ := by
  have hw := c.comm_mem_V y x
  have e : (x * y) * (x * y) = x * (⁅y, x⁆ * (x * y)) * y := by
    simp only [commutatorElement_def]; group
  rw [c.comm_symm x y]
  calc (x * y) * (x * y) = x * (⁅y, x⁆ * (x * y)) * y := e
    _ = (x * ⁅y, x⁆) * (x * y) * y := by group
    _ = (⁅y, x⁆ * x) * (x * y) * y := by rw [← c.V_comm hw x]
    _ = ⁅y, x⁆ * ((x * x) * (y * y)) := by group
    _ = ((x * x) * (y * y)) * ⁅y, x⁆ := c.V_comm hw _

omit [V.Normal] in
theorem sq_mul_V (x : Q) {v : Q} (hv : v ∈ V) : (x * v) * (x * v) = x * x := by
  calc (x * v) * (x * v) = x * (v * x) * v := by group
    _ = x * (x * v) * v := by rw [c.V_comm hv x]
    _ = (x * x) * (v * v) := by group
    _ = x * x := by rw [c.V_sq hv, mul_one]

theorem comm_mul_V_right (x y : Q) {v : Q} (hv : v ∈ V) : ⁅x, y * v⁆ = ⁅x, y⁆ := by
  rw [c.comm_mul_right, c.comm_V_right hv, mul_one]

theorem comm_mul_V_left (x y : Q) {v : Q} (hv : v ∈ V) : ⁅x * v, y⁆ = ⁅x, y⁆ := by
  rw [c.comm_mul_left, c.comm_V_left hv, mul_one]

end Identities

@[expose] def M (_c : Config25 Q V t) : Type := Additive (Q ⧸ V)

instance instAddCommGroupM [V.Normal] : AddCommGroup c.M :=
  @Additive.addCommGroup (Q ⧸ V) { (inferInstance : Group (Q ⧸ V)) with mul_comm := c.mk_comm }

@[expose] def cls (x : Q) : c.M := Additive.ofMul (QuotientGroup.mk x : Q ⧸ V)

section Mk

variable [V.Normal]

theorem cls_mul (x y : Q) : c.cls (x * y) = c.cls x + c.cls y := rfl

theorem cls_one : c.cls 1 = 0 := rfl

omit [V.Normal] in
theorem cls_surj (m : c.M) : ∃ x, c.cls x = m := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (show Additive (Q ⧸ V) from m))
  exact ⟨x, by rw [cls, hx]; rfl⟩

theorem cls_eq_zero_iff (x : Q) : c.cls x = 0 ↔ x ∈ V := by
  rw [← QuotientGroup.eq_one_iff x]
  exact Iff.rfl

end Mk

include c in
@[expose] def descend {β : Type*} (f : Q → β) (hf : ∀ x v, v ∈ V → f (x * v) = f x) : c.M → β :=
  fun m => Quotient.liftOn' (Additive.toMul (show Additive (Q ⧸ V) from m)) f (fun a b hab => by
    have h : a⁻¹ * b ∈ V := (QuotientGroup.leftRel_apply).mp hab
    have e : b = a * (a⁻¹ * b) := by group
    rw [e, hf a _ h])

include c in
@[expose] def descend₂ {β : Type*} (f : Q → Q → β) (h1 : ∀ x y v, v ∈ V → f (x * v) y = f x y)
    (h2 : ∀ x y v, v ∈ V → f x (y * v) = f x y) : c.M → c.M → β :=
  fun m m' => Quotient.liftOn₂' (Additive.toMul (show Additive (Q ⧸ V) from m))
    (Additive.toMul (show Additive (Q ⧸ V) from m')) f (fun a b a' b' ha hb => by
      have ha' : a⁻¹ * a' ∈ V := (QuotientGroup.leftRel_apply).mp ha
      have hb' : b⁻¹ * b' ∈ V := (QuotientGroup.leftRel_apply).mp hb
      have ea : a' = a * (a⁻¹ * a') := by group
      have eb : b' = b * (b⁻¹ * b') := by group
      rw [ea, eb, h1 a _ _ ha', h2 a b _ hb'])

section Maps

variable [V.Normal]

theorem M_two (m : c.M) : m + m = 0 := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [← c.cls_mul, c.cls_eq_zero_iff]
  exact c.sq_mem_V x

@[expose] noncomputable def πfun : c.M → F4V :=
  c.descend (fun x => c.coord ⁅t, x⁆) (fun x v hv => by rw [c.comm_mul_V_right t x hv])

theorem πfun_cls (x : Q) : c.πfun (c.cls x) = c.coord ⁅t, x⁆ := rfl

@[expose] noncomputable def π : c.M →+ F4V :=
  AddMonoidHom.mk' c.πfun (by
    intro a b
    obtain ⟨x, rfl⟩ := c.cls_surj a
    obtain ⟨y, rfl⟩ := c.cls_surj b
    rw [← c.cls_mul, c.πfun_cls, c.πfun_cls, c.πfun_cls, c.comm_mul_right,
      c.coord_mul (c.comm_mem x) (c.comm_mem y)])

theorem π_cls (x : Q) : c.π (c.cls x) = c.coord ⁅t, x⁆ := rfl

@[expose] noncomputable def Bfun : c.M → c.M → F4V :=
  c.descend₂ (fun x y => c.coord ⁅x, y⁆) (fun x y v hv => by rw [c.comm_mul_V_left x y hv])
    (fun x y v hv => by rw [c.comm_mul_V_right x y hv])

theorem Bfun_cls (x y : Q) : c.Bfun (c.cls x) (c.cls y) = c.coord ⁅x, y⁆ := rfl

theorem Bfun_add_right (m a b : c.M) : c.Bfun m (a + b) = c.Bfun m a + c.Bfun m b := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  obtain ⟨y, rfl⟩ := c.cls_surj a
  obtain ⟨z, rfl⟩ := c.cls_surj b
  rw [← c.cls_mul, c.Bfun_cls, c.Bfun_cls, c.Bfun_cls, c.comm_mul_right,
    c.coord_mul (c.comm_mem_V x y) (c.comm_mem_V x z)]

theorem Bfun_add_left (a b m : c.M) : c.Bfun (a + b) m = c.Bfun a m + c.Bfun b m := by
  obtain ⟨x, rfl⟩ := c.cls_surj a
  obtain ⟨y, rfl⟩ := c.cls_surj b
  obtain ⟨z, rfl⟩ := c.cls_surj m
  rw [← c.cls_mul, c.Bfun_cls, c.Bfun_cls, c.Bfun_cls, c.comm_mul_left,
    c.coord_mul (c.comm_mem_V x z) (c.comm_mem_V y z)]

@[expose] noncomputable def B : c.M →+ c.M →+ F4V :=
  AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (c.Bfun m) (c.Bfun_add_right m)) (by
    intro a b
    refine AddMonoidHom.ext (fun m => ?_)
    exact c.Bfun_add_left a b m)

theorem B_cls (x y : Q) : c.B (c.cls x) (c.cls y) = c.coord ⁅x, y⁆ := rfl

@[expose] noncomputable def qm : c.M → F4V :=
  c.descend (fun x => c.coord (x * x)) (fun x v hv => by rw [c.sq_mul_V x hv])

omit [V.Normal] in
theorem qm_cls (x : Q) : c.qm (c.cls x) = c.coord (x * x) := rfl

end Maps

section Action

variable [V.Normal] {c} {φ : MulAut Q} {f : F4V → F4V}

@[expose] def gM (h : c.Acts φ f) : c.M ≃+ c.M := h.quot.toAdditive

theorem gM_cls (h : c.Acts φ f) (x : Q) : gM h (c.cls x) = c.cls (φ x) := h.quot_mk x

theorem π_gM (h : c.Acts φ f) (m : c.M) : c.π (gM h m) = f (c.π m) := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [gM_cls, π_cls, π_cls, show ⁅t, φ x⁆ = φ ⁅t, x⁆ by rw [map_commutatorElement, h.fix]]
  exact h.coord_apply (c.comm_mem x)

theorem B_gM (h : c.Acts φ f) (m m' : c.M) : c.B (gM h m) (gM h m') = f (c.B m m') := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  obtain ⟨y, rfl⟩ := c.cls_surj m'
  rw [gM_cls, gM_cls, B_cls, B_cls, ← map_commutatorElement]
  exact h.coord_apply (c.comm_mem_V x y)

theorem q_gM (h : c.Acts φ f) (m : c.M) : c.qm (gM h m) = f (c.qm m) := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [gM_cls, qm_cls, qm_cls, ← map_mul]
  exact h.coord_apply (c.sq_mem_V x)

theorem gM_m₀ (h : c.Acts φ f) : gM h (c.cls t) = c.cls t := by
  rw [gM_cls, h.fix]

end Action

section Fields

variable [V.Normal]

theorem π_surj : Function.Surjective c.π := by
  intro v
  obtain ⟨x, hx⟩ := c.delta_surjective (Multiplicative.ofAdd v)
  rw [c.delta_eq_ofAdd_coord] at hx
  exact ⟨c.cls x, by rw [π_cls]; exact Multiplicative.ofAdd.injective hx⟩

theorem π_m₀ : c.π (c.cls t) = 0 := by
  rw [π_cls, commutatorElement_self, c.coord_one]

theorem π_ker (m : c.M) (hm : c.π m = 0) : m = 0 ∨ m = c.cls t := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [π_cls, c.coord_eq_zero_iff (c.comm_mem x)] at hm
  have h1 : c.delta x = 1 := by
    rw [c.delta_apply]
    have : (⟨⁅t, x⁆, c.comm_mem x⟩ : V) = 1 := Subtype.ext hm
    rw [this, map_one]
  rcases c.mem_sup_iff.mp ((c.delta_eq_one_iff x).mp h1) with h | ⟨v, hv, rfl⟩
  · left; exact (c.cls_eq_zero_iff x).mpr h
  · right; rw [c.cls_mul, (c.cls_eq_zero_iff v).mpr hv, zero_add]

theorem m₀_ne : c.cls t ≠ 0 := fun h => c.t_not_mem ((c.cls_eq_zero_iff t).mp h)

theorem B_symm (m m' : c.M) : c.B m m' = c.B m' m := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  obtain ⟨y, rfl⟩ := c.cls_surj m'
  rw [B_cls, B_cls, c.comm_symm x y]

theorem B_alt (m : c.M) : c.B m m = 0 := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [B_cls, commutatorElement_self, c.coord_one]

theorem q_add (m m' : c.M) : c.qm (m + m') = c.qm m + c.qm m' + c.B m m' := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  obtain ⟨y, rfl⟩ := c.cls_surj m'
  rw [← c.cls_mul, qm_cls, qm_cls, qm_cls, B_cls, c.sq_mul,
    c.coord_mul (V.mul_mem (c.sq_mem_V x) (c.sq_mem_V y)) (c.comm_mem_V x y),
    c.coord_mul (c.sq_mem_V x) (c.sq_mem_V y)]

omit [V.Normal] in
theorem q_m₀ : c.qm (c.cls t) = 0 := by
  rw [qm_cls, c.t_sq, c.coord_one]

theorem B_m₀ (m : c.M) : c.B m (c.cls t) = c.π m := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [B_cls, π_cls, c.comm_symm x t]

theorem gU_add (γ γ' : F4) (m : c.M) :
    gM (c.acts_up (γ + γ')) m = gM (c.acts_up γ) (gM (c.acts_up γ') m) := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [gM_cls, gM_cls, gM_cls, ofAdd_add, map_mul, MulAut.mul_apply]

theorem gL_add (γ γ' : F4) (m : c.M) :
    gM (c.acts_low (γ + γ')) m = gM (c.acts_low γ) (gM (c.acts_low γ') m) := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [gM_cls, gM_cls, gM_cls, ofAdd_add, map_mul, MulAut.mul_apply]

theorem gT_cube (m : c.M) : gM c.acts_tor (gM c.acts_tor (gM c.acts_tor m)) = m := by
  obtain ⟨x, rfl⟩ := c.cls_surj m
  rw [gM_cls, gM_cls, gM_cls]
  have h := congrArg (fun φ : MulAut Q => φ x) c.αTor_cube
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
  rw [h]

@[expose] noncomputable def modData : ModData c.M where
  two := c.M_two
  π := c.π
  m₀ := c.cls t
  B := c.B
  q := c.qm
  gU := fun γ => gM (c.acts_up γ)
  gL := fun γ => gM (c.acts_low γ)
  gT := gM c.acts_tor
  π_surj := c.π_surj
  π_m₀ := c.π_m₀
  π_ker := c.π_ker
  m₀_ne := c.m₀_ne
  B_symm := c.B_symm
  B_alt := c.B_alt
  q_add := c.q_add
  q_m₀ := c.q_m₀
  B_m₀ := c.B_m₀
  gU_add := c.gU_add
  gL_add := c.gL_add
  gT_cube := c.gT_cube
  gU_m₀ := fun γ => gM_m₀ (c.acts_up γ)
  gL_m₀ := fun γ => gM_m₀ (c.acts_low γ)
  gT_m₀ := gM_m₀ c.acts_tor
  π_U := fun γ m => π_gM (c.acts_up γ) m
  π_L := fun γ m => π_gM (c.acts_low γ) m
  π_T := fun m => π_gM c.acts_tor m
  B_U := fun γ m m' => B_gM (c.acts_up γ) m m'
  B_L := fun γ m m' => B_gM (c.acts_low γ) m m'
  B_T := fun m m' => B_gM c.acts_tor m m'
  q_U := fun γ m => q_gM (c.acts_up γ) m
  q_L := fun γ m => q_gM (c.acts_low γ) m
  q_T := fun m => q_gM c.acts_tor m

end Fields

end Config25

end CFSG.OddStandard.Seitz77
