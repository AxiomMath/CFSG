module

public import CFSG.CGT.PushingUpLit.BHS.FourFourC
public import CFSG.CGT.PushingUpLit.BHS.FourFourB
public import CFSG.CGT.PushingUpLit.BHS.FourOne

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V]

structure IsTransv (x : MulAut V) (u : V) : Prop where
  sq : x * x = 1
  ne_one : x ≠ 1
  ne : u ≠ 1
  step : ∀ v : V, x v = v ∨ x v = v * u

namespace IsTransv

variable {x y : MulAut V} {u w : V}

theorem exists_move (h : IsTransv x u) : ∃ v : V, x v = v * u := by
  by_contra hcon
  push Not at hcon
  apply h.ne_one
  refine MulEquiv.ext fun v => ?_
  rcases h.step v with h1 | h1
  · rw [h1]; rfl
  · exact absurd h1 (hcon v)

theorem apply_centre (hV : ∀ v : V, v ^ 2 = 1) (h : IsTransv x u) : x u = u := by
  rcases h.step u with h1 | h1
  · exact h1
  · exfalso
    have hu : u * u = 1 := by rw [← pow_two]; exact hV u
    rw [hu] at h1
    apply h.ne
    have : x u = x 1 := by rw [h1, map_one]
    exact x.injective this

theorem centre_unique (h : IsTransv x u) (h' : IsTransv x w) : u = w := by
  obtain ⟨v, hv⟩ := h.exists_move
  obtain ⟨v', hv'⟩ := h'.exists_move
  rcases h'.step v with h1 | h1
  · exfalso
    rw [h1] at hv
    exact h.ne (by simpa using hv.symm)
  · rw [hv] at h1
    exact mul_left_cancel h1

theorem conj (g : MulAut V) (h : IsTransv x u) : IsTransv (g * x * g⁻¹) (g u) where
  sq := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  ne_one := by
    intro h1
    apply h.ne_one
    have : g⁻¹ * (g * x * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
    simpa [mul_assoc] using this
  ne := fun h1 => h.ne (g.injective (by rw [h1, map_one]))
  step := fun v => by
    have hgv : (g * x * g⁻¹) v = g (x (g⁻¹ v)) := rfl
    rcases h.step (g⁻¹ v) with h1 | h1
    · left
      rw [hgv, h1]
      simp
    · right
      rw [hgv, h1, map_mul]
      simp

theorem step_div (h : IsTransv x u) (v : V) : x v * v⁻¹ = 1 ∨ x v * v⁻¹ = u := by
  rcases h.step v with h1 | h1
  · left; rw [h1]; simp
  · right; rw [h1]; simp

theorem comm_iff (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w) :
    x * y = y * x ↔ x w = w ∧ y u = u := by
  constructor
  · intro hxy
    have hx1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx.sq
    have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy.sq
    have e1 : x * y * x⁻¹ = y := by rw [hxy, mul_assoc, mul_inv_cancel, mul_one]
    have e2 : y * x * y⁻¹ = x := by rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨?_, ?_⟩
    · have := hy.conj x
      rw [e1] at this
      exact (hy.centre_unique this).symm
    · have := hx.conj y
      rw [e2] at this
      exact (hx.centre_unique this).symm
  · rintro ⟨hxw, hyu⟩
    refine MulEquiv.ext fun v => ?_
    have hu2 : u * u = 1 := by rw [← pow_two]; exact hV u
    have hw2 : w * w = 1 := by rw [← pow_two]; exact hV w
    show x (y v) = y (x v)
    rcases hx.step v with h1 | h1 <;> rcases hy.step v with h2 | h2
    · rw [h2, h1, h2]
    · rw [h1, h2, map_mul, hxw]
      rw [h1]
    · rw [h1, h2, h1, map_mul, hyu]
      rw [h2]
    · rw [h1, h2, map_mul, map_mul, hxw, hyu, h1, h2]
      comm_group

@[expose] def fixer (u : V) : Subgroup (MulAut V) where
  carrier := {g | g u = u}
  one_mem' := rfl
  mul_mem' := fun {a b} ha hb => by
    show a (b u) = u
    rw [show b u = u from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    show a⁻¹ u = u
    have : a u = u := ha
    calc a⁻¹ u = a⁻¹ (a u) := by rw [this]
      _ = u := by simp

theorem rel_of_conj (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hnc : x * y ≠ y * x) {g : MulAut V} (hg : g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y)
    (hgxy : y = g * x * g⁻¹) : x w = w * u ∧ y u = u * w ∧ u ≠ w := by
  have hxw : x w ≠ w ∨ y u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hnc ((hx.comm_iff hV hy).2 hcon)
  have hgu : g u = w := by
    have := hx.conj g
    rw [← hgxy] at this
    exact (hy.centre_unique this).symm
  have hxu : x u = u := hx.apply_centre hV
  have hyw : y w = w := hy.apply_centre hV
  have hyu' : y u ≠ u := by
    intro hyu
    have hxw' : x w ≠ w := hxw.resolve_right (not_not.2 hyu)
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ fixer u :=
      sup_le (Subgroup.zpowers_le.2 hxu) (Subgroup.zpowers_le.2 hyu)
    have hgu' : g u = u := hle hg
    have huw : u = w := hgu'.symm.trans hgu
    exact hxw' (by rw [← huw]; exact hxu)
  have hxw' : x w ≠ w := by
    intro hxw0
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ fixer w :=
      sup_le (Subgroup.zpowers_le.2 hxw0) (Subgroup.zpowers_le.2 hyw)
    have hginv : g⁻¹ ∈ fixer w := (fixer w).inv_mem (hle hg)
    have huw : u = w := by
      calc u = g⁻¹ (g u) := by simp
        _ = g⁻¹ w := by rw [hgu]
        _ = w := hginv
    exact hyu' (by rw [huw]; exact hyw)
  have e1 : x w = w * u := (hx.step w).resolve_left hxw'
  have e2 : y u = u * w := (hy.step u).resolve_left hyu'
  refine ⟨e1, e2, fun huw => hxw' ?_⟩
  rw [← huw]
  exact hxu

theorem braid (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) : x * y * x = y * x * y := by
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hV u
  have hw2 : w * w = 1 := by rw [← pow_two]; exact hV w
  have hu3 : ∀ z : V, u * (u * z) = z := fun z => by rw [← mul_assoc, hu2, one_mul]
  have hw3 : ∀ z : V, w * (w * z) = z := fun z => by rw [← mul_assoc, hw2, one_mul]
  have hxu : x u = u := hx.apply_centre hV
  have hyw : y w = w := hy.apply_centre hV
  refine MulEquiv.ext fun v => ?_
  show x (y (x v)) = y (x (y v))
  rcases hx.step v with h1 | h1 <;> rcases hy.step v with h2 | h2 <;>
    simp only [h1, h2, map_mul, hxw, hxu, hyu, hyw] <;>
    simp only [mul_comm, mul_left_comm, hu3, hw3, hw2, mul_one]

theorem pow_three (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w) : (x * y) ^ 3 = 1 := by
  have hb := braid hV hx hy hxw hyu
  calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (y * x * y) * (y * x * y) := by rw [hb]
    _ = y * (x * (y * y) * x) * y := by simp only [mul_assoc]
    _ = 1 := by rw [hy.sq, mul_one, hx.sq, mul_one, hy.sq]

end IsTransv

section Link

variable {V : Type} [CommGroup V] [Finite V]

theorem eq_one_or_of_mem_zpowers {G : Type*} [Group G] {u z : G} (hu : u * u = 1)
    (hz : z ∈ Subgroup.zpowers u) : z = 1 ∨ z = u := by
  obtain ⟨k, rfl⟩ := hz
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  show u ^ k = 1 ∨ u ^ k = u
  have hk : 2 * (k / 2) + k % 2 = k := by omega
  rw [← hk, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem eq_zpowers_of_card_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : Nat.card H = 2) {a : G} (ha : a ∈ H) (ha1 : a ≠ 1) : H = Subgroup.zpowers a := by
  have hord : orderOf a = 2 := by
    have h1 : orderOf a ∣ 2 := by
      rw [← hH]
      have := orderOf_dvd_natCard (⟨a, ha⟩ : H)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.1 h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd h h2
    · exact h
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 ha) ?_
  rw [Nat.card_zpowers, hord, hH]

omit [Finite V] in
theorem forall_comm_zpowers_iff (x y : MulAut V) :
    (∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a) ↔ x * y = y * x := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x) y (Subgroup.mem_zpowers y)
  · intro h a ha b hb
    obtain ⟨k, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := hb
    exact ((Commute.zpow_zpow (show Commute x y from h) k l)).eq

omit [Finite V] in
theorem conjSub_zpowers (g x : MulAut V) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}

theorem exists_transv_of_card_two (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1)
    {A : Subgroup (MulAut V)} (hA : A ∈ D) (hcard : Nat.card A = 2) :
    ∃ (x : MulAut V) (u : V), IsTransv x u ∧ x ∈ P ∧ A = Subgroup.zpowers x ∧
      commV A = Subgroup.zpowers u := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (h.ne_bot A hA)
  have ha1' : a ≠ 1 := fun e => ha1 (Subtype.ext e)
  have hAx : A = Subgroup.zpowers a := eq_zpowers_of_card_two hcard ha ha1'
  have ha2 : a * a = 1 := by rw [← pow_two]; exact (h.elemAb A hA).2 a ha
  have hcomm : Nat.card (commV A) = 2 := by
    have h1 := card_commV_zpowers_mul a
    have h2 := h.card_eq A hA
    rw [← hAx] at h1
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    have : Nat.card (commV A) * Nat.card (fixV A) = Nat.card A * Nat.card (fixV A) := by
      rw [h1, h2]
    have := Nat.eq_of_mul_eq_mul_right hpos this
    rw [this, hcard]
  obtain ⟨⟨u, hu⟩, hu1⟩ : ∃ u : ↥(commV A), u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card (commV A) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun p q => (hcon p).trans (hcon q).symm⟩, ⟨1⟩⟩
    omega
  have hu1' : u ≠ 1 := fun e => hu1 (Subtype.ext e)
  have hcu : commV A = Subgroup.zpowers u := eq_zpowers_of_card_two hcomm hu hu1'
  have hu2 : u * u = 1 := by rw [← pow_two]; exact hV u
  refine ⟨a, u, ⟨ha2, ha1', hu1', fun v => ?_⟩, h.le A hA ha, hAx, hcu⟩
  have hmem : a v * v⁻¹ ∈ commV A :=
    Subgroup.subset_closure ⟨a, ha, v, rfl⟩
  rw [hcu] at hmem
  rcases eq_one_or_of_mem_zpowers hu2 hmem with h1 | h1
  · left
    calc a v = a v * v⁻¹ * v := by simp
      _ = v := by rw [h1, one_mul]
  · right
    calc a v = a v * v⁻¹ * v := by simp
      _ = u * v := by rw [h1]
      _ = v * u := mul_comm _ _

theorem Hyp41.rel_of_noncomm (h : Hyp41 P D) (hV : ∀ v : V, v ^ 2 = 1) {A B : Subgroup (MulAut V)}
    (hA : A ∈ D) (hB : B ∈ D) {x y : MulAut V} {u w : V} (hx : IsTransv x u) (hy : IsTransv y w)
    (hAx : A = Subgroup.zpowers x) (hBy : B = Subgroup.zpowers y) (hnc : x * y ≠ y * x) :
    x w = w * u ∧ y u = u * w ∧ u ≠ w := by
  rcases h.four_eight_conj hA hB with hc | ⟨g, hg, hBg⟩
  · exfalso
    apply hnc
    rw [hAx, hBy] at hc
    exact (forall_comm_zpowers_iff x y).1 hc
  · have hyB : y ∈ B := by rw [hBy]; exact Subgroup.mem_zpowers y
    rw [hBg] at hyB
    obtain ⟨a, haA, hay⟩ := hyB
    have haA' : a ∈ Subgroup.zpowers x := by rw [← hAx]; exact haA
    have hx2 : x * x = 1 := hx.sq
    have hax : a = x := by
      rcases eq_one_or_of_mem_zpowers hx2 haA' with h1 | h1
      · exfalso
        apply hy.ne_one
        rw [← hay, h1]
        simp
      · exact h1
    have hgxy : y = g * x * g⁻¹ := by
      rw [← hay, hax]
      rfl
    refine IsTransv.rel_of_conj hV hx hy hnc ?_ hgxy
    rw [← hAx, ← hBy]
    exact hg

omit [Finite V] in
theorem gen_ne_of_ne {A B : Subgroup (MulAut V)} {x y : MulAut V} (hAx : A = Subgroup.zpowers x)
    (hBy : B = Subgroup.zpowers y) (hAB : A ≠ B) : x ≠ y := by
  intro hxy
  apply hAB
  rw [hAx, hBy, hxy]

end Link

end CFSG.CGT.PushingUpLit.BHS
