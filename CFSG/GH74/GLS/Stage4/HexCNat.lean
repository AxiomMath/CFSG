module

public import CFSG.GH74.GLS.Stage4.HexCSL2

public noncomputable section

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section ConjAdd

variable {G : Type*} [Group G]

@[expose] def conjAdd (V : Subgroup G) (g : G) (hg : ∀ v ∈ V, g * v * g⁻¹ ∈ V) :
    Additive ↥V →+ Additive ↥V where
  toFun x := Additive.ofMul (⟨g * (x.toMul : G) * g⁻¹, hg _ x.toMul.2⟩ : ↥V)
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [mul_assoc]

theorem conjAdd_toMul (V : Subgroup G) (g : G) (hg : ∀ v ∈ V, g * v * g⁻¹ ∈ V)
    (x : Additive ↥V) : ((conjAdd V g hg x).toMul : G) = g * (x.toMul : G) * g⁻¹ := rfl

end ConjAdd

section NatPair

variable {F : Type*} [Field F] {G : Type*} [Group G]

structure NatPair (φ : SL2 F →* G) (A B : Subgroup G) : Prop where
  commA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a
  commB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b
  commAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  uA : ∀ c, ∀ a ∈ A, φ (sl2U c) * a * (φ (sl2U c))⁻¹ = a
  lB : ∀ c, ∀ b ∈ B, φ (sl2L c) * b * (φ (sl2L c))⁻¹ = b
  uB : ∀ c, ∀ b ∈ B, φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹ ∈ A
  lA : ∀ c, ∀ a ∈ A, φ (sl2L c) * a * (φ (sl2L c))⁻¹ * a⁻¹ ∈ B
  ndU : ∀ b ∈ B, φ (sl2U 1) * b * (φ (sl2U 1))⁻¹ = b → b = 1
  ndL : ∀ a ∈ A, φ (sl2L 1) * a * (φ (sl2L 1))⁻¹ = a → a = 1

namespace NatPair

variable {φ : SL2 F →* G} {A B : Subgroup G} (h : NatPair φ A B)

@[expose] def prodSub : Subgroup G where
  carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← h.commAB a' ha' b hb]
      _ = a * a' * (b * b') := by group
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact (h.commAB _ (A.inv_mem ha) _ (B.inv_mem hb)).symm

theorem comm_prodSub : ∀ x ∈ h.prodSub, ∀ y ∈ h.prodSub, x * y = y * x := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩
  have e1 : a * b * (a' * b') = a * a' * (b * b') := by
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← h.commAB a' ha' b hb]
      _ = a * a' * (b * b') := by group
  have e2 : a' * b' * (a * b) = a' * a * (b' * b) := by
    calc a' * b' * (a * b) = a' * (b' * a) * b := by group
      _ = a' * (a * b') * b := by rw [← h.commAB a ha b' hb']
      _ = a' * a * (b' * b) := by group
  rw [e1, e2, h.commA a ha a' ha', h.commB b hb b' hb']

theorem conj_U_mem (c : F) : ∀ v ∈ h.prodSub, φ (sl2U c) * v * (φ (sl2U c))⁻¹ ∈ h.prodSub := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine ⟨a * (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹), A.mul_mem ha (h.uB c b hb), b, hb, ?_⟩
  have h1 := h.uA c a ha
  calc φ (sl2U c) * (a * b) * (φ (sl2U c))⁻¹
      = (φ (sl2U c) * a * (φ (sl2U c))⁻¹) * (φ (sl2U c) * b * (φ (sl2U c))⁻¹) := by group
    _ = a * (φ (sl2U c) * b * (φ (sl2U c))⁻¹) := by rw [h1]
    _ = a * (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) * b := by group

theorem conj_L_mem (c : F) : ∀ v ∈ h.prodSub, φ (sl2L c) * v * (φ (sl2L c))⁻¹ ∈ h.prodSub := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hβ := h.lA c a ha
  refine ⟨a, ha, (φ (sl2L c) * a * (φ (sl2L c))⁻¹ * a⁻¹) * b, B.mul_mem hβ hb, ?_⟩
  have h1 := h.lB c b hb
  have h2 := h.commAB a ha _ hβ
  calc φ (sl2L c) * (a * b) * (φ (sl2L c))⁻¹
      = (φ (sl2L c) * a * (φ (sl2L c))⁻¹) * (φ (sl2L c) * b * (φ (sl2L c))⁻¹) := by group
    _ = (φ (sl2L c) * a * (φ (sl2L c))⁻¹) * b := by rw [h1]
    _ = ((φ (sl2L c) * a * (φ (sl2L c))⁻¹ * a⁻¹) * a) * b := by group
    _ = (a * (φ (sl2L c) * a * (φ (sl2L c))⁻¹ * a⁻¹)) * b := by rw [← h2]
    _ = a * ((φ (sl2L c) * a * (φ (sl2L c))⁻¹ * a⁻¹) * b) := by group

include h in
open scoped IsMulCommutative in
theorem key (t : Fˣ) {b : G} (hb : b ∈ B) :
    φ (sl2D t) * b * (φ (sl2D t))⁻¹ ∈ B ∧
      ⁅φ (sl2U (t : F)), φ (sl2D t) * b * (φ (sl2D t))⁻¹⁆ = ⁅φ (sl2U 1), b⁆ := by
  classical
  have : IsMulCommutative ↥h.prodSub :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (h.comm_prodSub x x.2 y y.2)
  have hU : ∀ c, ∀ v ∈ h.prodSub, φ (sl2U c) * v * (φ (sl2U c))⁻¹ ∈ h.prodSub := h.conj_U_mem
  have hL : ∀ c, ∀ v ∈ h.prodSub, φ (sl2L c) * v * (φ (sl2L c))⁻¹ ∈ h.prodSub := h.conj_L_mem
  have hW : ∀ c : F, ∀ v ∈ h.prodSub,
      φ (sl2Wc c) * v * (φ (sl2Wc c))⁻¹ ∈ h.prodSub := by
    intro c v hv
    have h1 := hU c _ (hL (-c⁻¹) _ (hU c v hv))
    have e : φ (sl2Wc c) * v * (φ (sl2Wc c))⁻¹ =
        φ (sl2U c) * (φ (sl2L (-c⁻¹)) * (φ (sl2U c) * v * (φ (sl2U c))⁻¹) *
          (φ (sl2L (-c⁻¹)))⁻¹) * (φ (sl2U c))⁻¹ := by
      simp only [sl2Wc, map_mul]; group
    rw [e]; exact h1
  have hD : ∀ v ∈ h.prodSub, φ (sl2D t) * v * (φ (sl2D t))⁻¹ ∈ h.prodSub := by
    intro v hv
    have h1 := hW (t : F) _ (hW (-1) v hv)
    have e : φ (sl2D t) * v * (φ (sl2D t))⁻¹ =
        φ (sl2Wc (t : F)) * (φ (sl2Wc (-1)) * v * (φ (sl2Wc (-1)))⁻¹) * (φ (sl2Wc (t : F)))⁻¹ := by
      rw [sl2D_eq_sl2Wc t, map_mul]; group
    rw [e]; exact h1
  let u : F → Additive ↥h.prodSub →+ Additive ↥h.prodSub := fun c => conjAdd _ (φ (sl2U c)) (hU c)
  let l : F → Additive ↥h.prodSub →+ Additive ↥h.prodSub := fun c => conjAdd _ (φ (sl2L c)) (hL c)
  let A' : AddSubgroup (Additive ↥h.prodSub) :=
    { carrier := {x | (x.toMul : G) ∈ A}
      add_mem' := fun {x y} hx hy => A.mul_mem hx hy
      zero_mem' := A.one_mem
      neg_mem' := fun {x} hx => A.inv_mem hx }
  let B' : AddSubgroup (Additive ↥h.prodSub) :=
    { carrier := {x | (x.toMul : G) ∈ B}
      add_mem' := fun {x y} hx hy => B.mul_mem hx hy
      zero_mem' := B.one_mem
      neg_mem' := fun {x} hx => B.inv_mem hx }
  have hdata : NatModData A' B' u l := by
    have hrel1 : ∀ c : F, c ≠ 0 → φ (sl2U 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) =
        (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2L (-(c⁻¹ * c⁻¹))) := by
      intro c hc
      have := congrArg φ (sl2U_one_mul_sl2Wc hc)
      simpa only [sl2Wc, map_mul] using this
    have hrel2 : ∀ c : F, c ≠ 0 → φ (sl2L 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) =
        (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2U (-(c * c))) := by
      intro c hc
      have := congrArg φ (sl2L_one_mul_sl2Wc hc)
      simpa only [sl2Wc, map_mul] using this
    refine
      { u_zero := fun x => ?_
        u_add := fun c d x => ?_
        uw := fun c hc x => ?_
        lw := fun c hc x => ?_
        uA := fun c a ha => ?_
        lB := fun c b hb => ?_
        uB := fun c b hb => ?_
        lA := fun c a ha => ?_
        ndU := fun b hb hfix => ?_
        ndL := fun a ha hfix => ?_ }
    · apply Additive.toMul.injective
      apply Subtype.ext
      simp [u, conjAdd_toMul, sl2U_zero]
    · apply Additive.toMul.injective
      apply Subtype.ext
      simp only [u, conjAdd_toMul, sl2U_add, map_mul]
      group
    · apply Additive.toMul.injective
      apply Subtype.ext
      simp only [wmap, u, l, conjAdd_toMul]
      calc φ (sl2U 1) * (φ (sl2U c) * (φ (sl2L (-c⁻¹)) * (φ (sl2U c) * (x.toMul : G) *
              (φ (sl2U c))⁻¹) * (φ (sl2L (-c⁻¹)))⁻¹) * (φ (sl2U c))⁻¹) * (φ (sl2U 1))⁻¹
          = (φ (sl2U 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c))) * (x.toMul : G) *
              (φ (sl2U 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)))⁻¹ := by group
        _ = ((φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2L (-(c⁻¹ * c⁻¹)))) *
              (x.toMul : G) *
              ((φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2L (-(c⁻¹ * c⁻¹))))⁻¹ := by
            rw [hrel1 c hc]
        _ = φ (sl2U c) * (φ (sl2L (-c⁻¹)) * (φ (sl2U c) * (φ (sl2L (-(c⁻¹ * c⁻¹))) *
              (x.toMul : G) * (φ (sl2L (-(c⁻¹ * c⁻¹))))⁻¹) * (φ (sl2U c))⁻¹) *
              (φ (sl2L (-c⁻¹)))⁻¹) * (φ (sl2U c))⁻¹ := by group
    · apply Additive.toMul.injective
      apply Subtype.ext
      simp only [wmap, u, l, conjAdd_toMul]
      calc φ (sl2L 1) * (φ (sl2U c) * (φ (sl2L (-c⁻¹)) * (φ (sl2U c) * (x.toMul : G) *
              (φ (sl2U c))⁻¹) * (φ (sl2L (-c⁻¹)))⁻¹) * (φ (sl2U c))⁻¹) * (φ (sl2L 1))⁻¹
          = (φ (sl2L 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c))) * (x.toMul : G) *
              (φ (sl2L 1) * (φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)))⁻¹ := by group
        _ = ((φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2U (-(c * c)))) *
              (x.toMul : G) *
              ((φ (sl2U c) * φ (sl2L (-c⁻¹)) * φ (sl2U c)) * φ (sl2U (-(c * c))))⁻¹ := by
            rw [hrel2 c hc]
        _ = φ (sl2U c) * (φ (sl2L (-c⁻¹)) * (φ (sl2U c) * (φ (sl2U (-(c * c))) *
              (x.toMul : G) * (φ (sl2U (-(c * c))))⁻¹) * (φ (sl2U c))⁻¹) *
              (φ (sl2L (-c⁻¹)))⁻¹) * (φ (sl2U c))⁻¹ := by group
    · apply Additive.toMul.injective
      apply Subtype.ext
      exact h.uA c _ ha
    · apply Additive.toMul.injective
      apply Subtype.ext
      exact h.lB c _ hb
    · show ((u c b - b).toMul : G) ∈ A
      have e : ((u c b - b).toMul : G) =
          φ (sl2U c) * (b.toMul : G) * (φ (sl2U c))⁻¹ * (b.toMul : G)⁻¹ := by
        simp [u, conjAdd_toMul, div_eq_mul_inv]
      rw [e]
      exact h.uB c _ hb
    · show ((l c a - a).toMul : G) ∈ B
      have e : ((l c a - a).toMul : G) =
          φ (sl2L c) * (a.toMul : G) * (φ (sl2L c))⁻¹ * (a.toMul : G)⁻¹ := by
        simp [l, conjAdd_toMul, div_eq_mul_inv]
      rw [e]
      exact h.lA c _ ha
    · have h1 : φ (sl2U 1) * (b.toMul : G) * (φ (sl2U 1))⁻¹ = (b.toMul : G) := by
        have := congrArg (fun x : Additive ↥h.prodSub => ((x.toMul : ↥h.prodSub) : G)) hfix
        simpa [u, conjAdd_toMul] using this
      have h2 := h.ndU _ hb h1
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa using h2
    · have h1 : φ (sl2L 1) * (a.toMul : G) * (φ (sl2L 1))⁻¹ = (a.toMul : G) := by
        have := congrArg (fun x : Additive ↥h.prodSub => ((x.toMul : ↥h.prodSub) : G)) hfix
        simpa [l, conjAdd_toMul] using this
      have h2 := h.ndL _ ha h1
      apply Additive.toMul.injective
      apply Subtype.ext
      simpa using h2
  have hbV : b ∈ h.prodSub := ⟨1, A.one_mem, b, hb, by simp⟩
  let b' : Additive ↥h.prodSub := Additive.ofMul ⟨b, hbV⟩
  have hb' : b' ∈ B' := hb
  let d : Additive ↥h.prodSub →+ Additive ↥h.prodSub := conjAdd _ (φ (sl2D t)) hD
  have hd : ∀ x, d x = wmap u l (t : F) (wmap u l (-1) x) := by
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [wmap, d, u, l, conjAdd_toMul]
    rw [sl2D_eq_sl2Wc t]
    simp only [sl2Wc, map_mul]
    group
  obtain ⟨h1, h2⟩ := hdata.key t.ne_zero d hd hb'
  refine ⟨?_, ?_⟩
  · exact h1
  · have h3 := congrArg (fun x : Additive ↥h.prodSub => ((x.toMul : ↥h.prodSub) : G)) h2
    have e1 : ((u (t : F) (d b') - d b').toMul : G) =
        φ (sl2U (t : F)) * (φ (sl2D t) * b * (φ (sl2D t))⁻¹) * (φ (sl2U (t : F)))⁻¹ *
          (φ (sl2D t) * b * (φ (sl2D t))⁻¹)⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
      rfl
    have e2 : ((u 1 b' - b').toMul : G) = φ (sl2U 1) * b * (φ (sl2U 1))⁻¹ * b⁻¹ := by
      rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv]
      rfl
    rw [e1, e2] at h3
    simpa only [commutatorElement_def] using h3

include h in
theorem comm_mul_right (c : F) {b b' : G} (hb : b ∈ B) (hb' : b' ∈ B) :
    ⁅φ (sl2U c), b * b'⁆ = ⁅φ (sl2U c), b⁆ * ⁅φ (sl2U c), b'⁆ := by
  have h1 : ⁅φ (sl2U c), b'⁆ ∈ A := by
    simpa [commutatorElement_def] using h.uB c b' hb'
  have h2 := h.commAB _ h1 b hb
  simp only [commutatorElement_def] at h2 ⊢
  calc φ (sl2U c) * (b * b') * (φ (sl2U c))⁻¹ * (b * b')⁻¹
      = (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) *
          (b * (φ (sl2U c) * b' * (φ (sl2U c))⁻¹ * b'⁻¹) * b⁻¹) := by group
    _ = (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) *
          (φ (sl2U c) * b' * (φ (sl2U c))⁻¹ * b'⁻¹) := by
        rw [← h2]; group

include h in
theorem comm_mul_left (c d : F) {b : G} (hb : b ∈ B) :
    ⁅φ (sl2U (c + d)), b⁆ = ⁅φ (sl2U c), b⁆ * ⁅φ (sl2U d), b⁆ := by
  have h1 : ⁅φ (sl2U d), b⁆ ∈ A := by
    simpa [commutatorElement_def] using h.uB d b hb
  have h2 := h.uA c _ h1
  have h3 : ⁅φ (sl2U c), b⁆ ∈ A := by
    simpa [commutatorElement_def] using h.uB c b hb
  have h4 := h.commA _ h3 _ h1
  simp only [commutatorElement_def] at h2 h4 ⊢
  rw [sl2U_add, map_mul]
  calc φ (sl2U c) * φ (sl2U d) * b * (φ (sl2U c) * φ (sl2U d))⁻¹ * b⁻¹
      = φ (sl2U c) * (φ (sl2U d) * b * (φ (sl2U d))⁻¹ * b⁻¹) * (φ (sl2U c))⁻¹ *
          (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) := by group
    _ = (φ (sl2U d) * b * (φ (sl2U d))⁻¹ * b⁻¹) *
          (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) := by rw [h2]
    _ = (φ (sl2U c) * b * (φ (sl2U c))⁻¹ * b⁻¹) *
          (φ (sl2U d) * b * (φ (sl2U d))⁻¹ * b⁻¹) := h4.symm

end NatPair

end NatPair

end CFSG.GH74.GLS.Stage4.Hex
