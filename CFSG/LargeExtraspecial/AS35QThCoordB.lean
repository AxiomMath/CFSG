module

public import CFSG.LargeExtraspecial.AS35QThCoordA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open QuadraticMap CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure CoordHyp (q : QuadraticForm (ZMod 2) V) (a b ζ : V →ₗ[ZMod 2] V) : Prop where
  qζ : ∀ v, q (ζ v) = q v
  qa : ∀ v, q (a v) = q v
  ζa : ∀ v, ζ (a v) = a (ζ v)
  ζb : ∀ v, ζ (b v) = b (ζ v)
  ab : ∀ v, a (b v) = ζ (b (a v))
  a3 : ∀ v, a (a (a v)) = v
  b3 : ∀ v, b (b (b v)) = v
  ζ2 : ∀ v, ζ (ζ v) + ζ v + v = 0
  nd : ∀ v, (∀ w, polar q v w = 0) → v = 0

namespace CoordHyp

variable {q : QuadraticForm (ZMod 2) V} {a b ζ : V →ₗ[ZMod 2] V} (h : CoordHyp q a b ζ)
include h

theorem b_injective : Function.Injective b := fun x y hxy => by
  rw [← h.b3 x, ← h.b3 y, hxy]

theorem b_E0 {u : V} (hu : a u = u) : a (b u) = ζ (b u) := by rw [h.ab, hu]

theorem b_E1 {u : V} (hu : a u = ζ u) : a (b u) = ζ (ζ (b u)) := by
  rw [h.ab, hu, ← h.ζb]

theorem b_E2 {u : V} (hu : a u = ζ (ζ u)) : a (b u) = b u := by
  rw [h.ab, hu, ← h.ζb, ← h.ζb, zeta_cube h.ζ2]

theorem act_E0 (c : K) {u : V} (hu : a u = u) : a (act ζ c u) = act ζ c u := by
  rw [act_comm (f := a) (fun v => h.ζa v), hu]

theorem act_E1 (c : K) {u : V} (hu : a u = ζ u) : a (act ζ c u) = ζ (act ζ c u) := by
  rw [act_comm (f := a) (fun v => h.ζa v), hu, act_comm (f := ζ) (fun v => rfl)]

theorem act_E2 (c : K) {u : V} (hu : a u = ζ (ζ u)) :
    a (act ζ c u) = ζ (ζ (act ζ c u)) := by
  rw [act_comm (f := a) (fun v => h.ζa v), hu, act_comm (f := ζ) (fun v => rfl),
    act_comm (f := ζ) (fun v => rfl)]

theorem zeta_E0 {u : V} (hu : a u = u) : a (ζ u) = ζ u := by rw [← h.ζa, hu]

theorem zeta_E1 {u : V} (hu : a u = ζ u) : a (ζ u) = ζ (ζ u) := by rw [← h.ζa, hu]

theorem zeta_E2 {u : V} (hu : a u = ζ (ζ u)) : a (ζ u) = ζ (ζ (ζ u)) := by rw [← h.ζa, hu]

theorem eq_zero_of_E {u₀ u₁ u₂ : V} (h0 : a u₀ = u₀) (h1 : a u₁ = ζ u₁)
    (h2 : a u₂ = ζ (ζ u₂)) (hs : u₀ + u₁ + u₂ = 0) : u₀ = 0 ∧ u₁ = 0 ∧ u₂ = 0 := by
  have ha : u₀ + ζ u₁ + ζ (ζ u₂) = 0 := by
    have := congrArg a hs
    rwa [map_add, map_add, h0, h1, h2, map_zero] at this
  have haa : u₀ + ζ (ζ u₁) + ζ u₂ = 0 := by
    have := congrArg a ha
    rw [map_add, map_add, h0, ← h.ζa, h1, ← h.ζa, ← h.ζa, h2, map_zero,
      zeta_cube h.ζ2 (ζ u₂)] at this
    exact this
  have hu₀ : u₀ = 0 := by
    have e1 := h.ζ2 u₁
    have e2 := h.ζ2 u₂
    have e : (u₀ + u₁ + u₂) + (u₀ + ζ u₁ + ζ (ζ u₂)) + (u₀ + ζ (ζ u₁) + ζ u₂) =
        (u₀ + u₀) + u₀ + (ζ (ζ u₁) + ζ u₁ + u₁) + (ζ (ζ u₂) + ζ u₂ + u₂) := by abel
    rw [hs, ha, haa, e1, e2, add_self_V u₀] at e
    simpa using e.symm
  subst hu₀
  rw [zero_add] at hs ha
  have hu₂ : u₁ = u₂ := eq_of_add_eq_zero_V hs
  subst hu₂
  have hz : u₁ = 0 := by
    have e1 := h.ζ2 u₁
    rw [add_comm (ζ (ζ u₁)) (ζ u₁), ha, zero_add] at e1
    exact e1
  exact ⟨rfl, hz, hz⟩

theorem polar_E0_E1 {u w : V} (hu : a u = u) (hw : a w = ζ w) : polar q u w = 0 := by
  refine polar_eq_zero_of_shift h.ζ2 ?_
  have hw' : a (ζ w) = ζ (ζ w) := by rw [← h.ζa, hw]
  rw [← polar_map_map q h.qa u (ζ w), hu, hw']

theorem polar_E0_E2 {u w : V} (hu : a u = u) (hw : a w = ζ (ζ w)) : polar q u w = 0 := by
  refine polar_eq_zero_of_shift2 h.ζ2 ?_ ?_
  · rw [← polar_map_map q h.qa u w, hu, hw]
  · have hw' : a (ζ w) = ζ (ζ (ζ w)) := by rw [← h.ζa, hw]
    rw [← polar_map_map q h.qa u (ζ w), hu, hw', zeta_cube h.ζ2]

theorem polar_E1_E2 {u w : V} (hu : a u = ζ u) (hw : a w = ζ (ζ w)) : polar q u w = 0 := by
  refine polar_eq_zero_of_shift h.ζ2 ?_
  have hw' : a (ζ w) = ζ (ζ (ζ w)) := by rw [← h.ζa, hw]
  rw [← polar_map_map q h.qa u (ζ w), hu, hw', polar_map_map q h.qζ]

omit h in
theorem polar_act_act_of_orth {u w : V} (h00 : polar q u w = 0) (h01 : polar q u (ζ w) = 0)
    (h10 : polar q (ζ u) w = 0) (h11 : polar q (ζ u) (ζ w) = 0) (c c' : K) :
    polar q (act ζ c u) (act ζ c' w) = 0 := by
  simp only [act, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, h00, h01,
    h10, h11, smul_zero, add_zero]

omit h in
theorem polar_act_act_self {v : V} (hv : polar q v (ζ v) = 1) (c c' : K) :
    polar q (act ζ c v) (act ζ c' v) = tr2 (frob c * c') := by
  have h00 : polar q v v = 0 := polar_self_zmod q v
  have h11 : polar q (ζ v) (ζ v) = 0 := polar_self_zmod q (ζ v)
  have h10 : polar q (ζ v) v = 1 := by rw [polar_comm]; exact hv
  have key : ∀ c c' : K, polar q (act ζ c v) (act ζ c' v) =
      tr2 (frob ω * c) * tr2 c' + tr2 c * tr2 (frob ω * c') := by
    intro c c'
    simp only [act, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, h00, hv,
      h10, h11, smul_eq_mul]
    ring
  rw [key]
  rcases K_cases c with rfl | rfl | rfl | rfl <;> rcases K_cases c' with rfl | rfl | rfl | rfl <;>
    simp only [map_zero, map_one, frob_frob, mul_zero, zero_mul, mul_one, one_mul,
      omega_mul_omega, frob_omega_mul_frob_omega, frob_omega_mul_omega, omega_mul_frob_omega,
      tr2_zero, tr2_one, tr2_omega, tr2_frob_omega] <;> decide

@[expose] noncomputable def lam (ζ : V →ₗ[ZMod 2] V) (v₁ v₂ v₃ : V) (x : Fin 3 → K) : V :=
  act ζ (x 0) v₁ + act ζ (x 1) v₂ + act ζ (x 2) v₃

omit h in
theorem lam_add (v₁ v₂ v₃ : V) (x y : Fin 3 → K) :
    lam ζ v₁ v₂ v₃ (x + y) = lam ζ v₁ v₂ v₃ x + lam ζ v₁ v₂ v₃ y := by
  simp only [lam, Pi.add_apply, act_add_left]
  abel

theorem lam_omega (v₁ v₂ v₃ : V) (x : Fin 3 → K) :
    lam ζ v₁ v₂ v₃ (ω • x) = ζ (lam ζ v₁ v₂ v₃ x) := by
  simp only [lam, Pi.smul_apply, smul_eq_mul, act_omega_mul h.ζ2, map_add]

theorem exists_coords [Finite V] (hcard : Nat.card V = 64) :
    ∃ l : (Fin 3 → K) → V, (∀ x y, l (x + y) = l x + l y) ∧ Function.Bijective l ∧
      (∀ x, l (ω • x) = ζ (l x)) ∧ (∀ x y, polar q (l x) (l y) = tr2 (herm frob x y)) := by
  classical
  have hV : ∃ w : V, w ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nat.card V = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨0⟩⟩
    omega
  obtain ⟨w, hw⟩ := hV
  have hv₁ : ∃ v₁ : V, v₁ ≠ 0 ∧ a v₁ = v₁ := by
    set p₀ := w + a w + a (a w)
    set p₁ := w + ζ (ζ (a w)) + ζ (a (a w))
    set p₂ := w + ζ (a w) + ζ (ζ (a (a w)))
    have h0 : a p₀ = p₀ := by
      simp only [p₀, map_add, h.a3]
      abel
    have h1 : a p₁ = ζ p₁ := by
      simp only [p₁, map_add, ← h.ζa, h.a3, zeta_cube h.ζ2]
      abel
    have h2 : a p₂ = ζ (ζ p₂) := by
      simp only [p₂, map_add, ← h.ζa, h.a3, zeta_cube h.ζ2]
      abel
    have hsum : p₀ + p₁ + p₂ = w := by
      have e1 := h.ζ2 (a w)
      have e2 := h.ζ2 (a (a w))
      calc p₀ + p₁ + p₂ = (w + w) + w + (ζ (ζ (a w)) + ζ (a w) + a w) +
          (ζ (ζ (a (a w))) + ζ (a (a w)) + a (a w)) := by simp only [p₀, p₁, p₂]; abel
        _ = w := by rw [e1, e2, add_self_V]; abel
    by_cases hp₀ : p₀ = 0
    · by_cases hp₂ : p₂ = 0
      · have hp₁ : p₁ ≠ 0 := by
          intro hp₁
          apply hw
          rw [← hsum, hp₀, hp₁, hp₂, add_zero, add_zero]
        refine ⟨b (b p₁), fun h' => hp₁ (h.b_injective (h.b_injective (by rw [h', map_zero,
          map_zero]))), h.b_E2 (h.b_E1 h1)⟩
      · exact ⟨b p₂, fun h' => hp₂ (h.b_injective (by rw [h', map_zero])), h.b_E2 h2⟩
    · exact ⟨p₀, hp₀, h0⟩
  obtain ⟨v₁, hv₁0, hv₁a⟩ := hv₁
  set v₂ := b v₁ with hv₂def
  set v₃ := b v₂ with hv₃def
  have hv₂a : a v₂ = ζ v₂ := h.b_E0 hv₁a
  have hv₃a : a v₃ = ζ (ζ v₃) := h.b_E1 hv₂a
  have hv₂0 : v₂ ≠ 0 := fun h' => hv₁0 (h.b_injective (by rw [← hv₂def, h', map_zero]))
  have hv₃0 : v₃ ≠ 0 := fun h' => hv₂0 (h.b_injective (by rw [← hv₃def, h', map_zero]))
  set l := lam ζ v₁ v₂ v₃ with hl
  have hinj : Function.Injective l := by
    intro x y hxy
    have h0 : l (x + y) = 0 := by rw [hl, lam_add, ← hl, hxy, add_self_V]
    obtain ⟨z0, z1, z2⟩ := h.eq_zero_of_E (h.act_E0 ((x + y) 0) hv₁a)
      (h.act_E1 ((x + y) 1) hv₂a) (h.act_E2 ((x + y) 2) hv₃a) h0
    have hxy0 : x + y = 0 := by
      funext i
      fin_cases i
      · exact (act_eq_zero h.ζ2 z0).resolve_right hv₁0
      · exact (act_eq_zero h.ζ2 z1).resolve_right hv₂0
      · exact (act_eq_zero h.ζ2 z2).resolve_right hv₃0
    exact eq_of_add_eq_zero_V hxy0
  have hbij : Function.Bijective l := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [hcard, Nat.card_fun, card_K, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have o12 : ∀ c c' : K, polar q (act ζ c v₁) (act ζ c' v₂) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E0_E1 hv₁a hv₂a) (h.polar_E0_E1 hv₁a (h.zeta_E1 hv₂a))
      (h.polar_E0_E1 (h.zeta_E0 hv₁a) hv₂a)
      (h.polar_E0_E1 (h.zeta_E0 hv₁a) (h.zeta_E1 hv₂a)) c c'
  have o13 : ∀ c c' : K, polar q (act ζ c v₁) (act ζ c' v₃) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E0_E2 hv₁a hv₃a) (h.polar_E0_E2 hv₁a (h.zeta_E2 hv₃a))
      (h.polar_E0_E2 (h.zeta_E0 hv₁a) hv₃a)
      (h.polar_E0_E2 (h.zeta_E0 hv₁a) (h.zeta_E2 hv₃a)) c c'
  have o23 : ∀ c c' : K, polar q (act ζ c v₂) (act ζ c' v₃) = 0 := fun c c' =>
    polar_act_act_of_orth (h.polar_E1_E2 hv₂a hv₃a) (h.polar_E1_E2 hv₂a (h.zeta_E2 hv₃a))
      (h.polar_E1_E2 (h.zeta_E1 hv₂a) hv₃a)
      (h.polar_E1_E2 (h.zeta_E1 hv₂a) (h.zeta_E2 hv₃a)) c c'
  have polar_self_act : ∀ (v : V), polar q v (ζ v) = 0 → ∀ c : K, polar q v (act ζ c v) = 0 := by
    intro v hv c
    simp only [act, polar_add_right, polar_smul_right, polar_self_zmod, hv, smul_zero, add_zero]
  have hlx : ∀ x : Fin 3 → K, l x = act ζ (x 0) v₁ + act ζ (x 1) v₂ + act ζ (x 2) v₃ :=
    fun x => rfl
  have p1 : polar q v₁ (ζ v₁) = 1 := by
    rcases zmod2_cases (polar q v₁ (ζ v₁)) with h0 | h1
    · exfalso
      refine hv₁0 (h.nd v₁ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e2 := o12 1 (x 1)
      have e3 := o13 1 (x 2)
      rw [act_one] at e2 e3
      rw [hlx, polar_add_right, polar_add_right, polar_self_act v₁ h0, e2, e3, add_zero,
        add_zero]
    · exact h1
  have p2 : polar q v₂ (ζ v₂) = 1 := by
    rcases zmod2_cases (polar q v₂ (ζ v₂)) with h0 | h1
    · exfalso
      refine hv₂0 (h.nd v₂ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e1 := o12 (x 0) 1
      have e3 := o23 1 (x 2)
      rw [act_one] at e1 e3
      rw [hlx, polar_add_right, polar_add_right, polar_comm, e1, polar_self_act v₂ h0, e3,
        add_zero, add_zero]
    · exact h1
  have p3 : polar q v₃ (ζ v₃) = 1 := by
    rcases zmod2_cases (polar q v₃ (ζ v₃)) with h0 | h1
    · exfalso
      refine hv₃0 (h.nd v₃ fun w => ?_)
      obtain ⟨x, rfl⟩ := hbij.2 w
      have e1 := o13 (x 0) 1
      have e2 := o23 (x 1) 1
      rw [act_one] at e1 e2
      rw [hlx, polar_add_right, polar_add_right, polar_comm, e1, polar_comm, e2,
        polar_self_act v₃ h0, add_zero, zero_add]
    · exact h1
  refine ⟨l, lam_add v₁ v₂ v₃, hbij, h.lam_omega v₁ v₂ v₃, fun x y => ?_⟩
  rw [hlx, hlx, herm_def, Fin.sum_univ_three, tr2_add, tr2_add]
  simp only [polar_add_left, polar_add_right]
  rw [polar_act_act_self p1, polar_act_act_self p2, polar_act_act_self p3, o12, o13, o23,
    polar_comm q (act ζ (x 1) v₂) (act ζ (y 0) v₁), o12, polar_comm q (act ζ (x 2) v₃),
    o13, polar_comm q (act ζ (x 2) v₃) (act ζ (y 1) v₂), o23]
  ring

end CoordHyp

end CFSG.LargeExtraspecial.AS35QTh
