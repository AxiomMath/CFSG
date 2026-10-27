module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

open Subgroup SemidirectProduct

variable (A : Type*) [Group A]

@[expose] def swapEquiv : MulAut (A × A) := MulEquiv.prodComm

theorem swapEquiv_mul_self : swapEquiv A * swapEquiv A = 1 := by
  ext ⟨a, b⟩ <;> rfl

@[expose] def swapHom : Multiplicative (ZMod 2) →* MulAut (A × A) where
  toFun x := if Multiplicative.toAdd x = 0 then 1 else swapEquiv A
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨a, rfl⟩ : ∃ a : ZMod 2, Multiplicative.ofAdd a = x := ⟨x.toAdd, rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : ZMod 2, Multiplicative.ofAdd b = y := ⟨y.toAdd, rfl⟩
    fin_cases a <;> fin_cases b <;> simp [swapEquiv_mul_self] <;> rfl

theorem swapHom_one' : swapHom A (Multiplicative.ofAdd 1) = swapEquiv A := by
  simp [swapHom]

abbrev Wr2 := (A × A) ⋊[swapHom A] Multiplicative (ZMod 2)

variable {A}

@[expose] def tau : Wr2 A := inr (Multiplicative.ofAdd 1)

@[expose] def base (a b : A) : Wr2 A := inl (a, b)

theorem zmod2_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod 2, Multiplicative.ofAdd a = x := ⟨x.toAdd, rfl⟩
  fin_cases a
  · left; rfl
  · right; rfl

theorem tau_mul_tau : (tau : Wr2 A) * tau = 1 := by
  unfold tau
  rw [← map_mul]
  have : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
    rw [← ofAdd_add]; decide
  rw [this, map_one]

theorem tau_inv : (tau : Wr2 A)⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_tau

theorem base_mul_base (a b c d : A) : base a b * base c d = base (a * c) (b * d) := by
  unfold base; rw [← map_mul]; rfl

theorem base_one : base (1 : A) 1 = 1 := by unfold base; exact map_one _

theorem base_inv (a b : A) : (base a b)⁻¹ = base a⁻¹ b⁻¹ := by
  unfold base; rw [← map_inv]; rfl

theorem tau_mul_base (a b : A) : tau * base a b = base b a * tau := by
  have h := inl_aut (φ := swapHom A) (Multiplicative.ofAdd 1) (a, b)
  rw [swapHom_one', map_inv] at h
  have e : swapEquiv A (a, b) = (b, a) := rfl
  rw [e] at h
  have h' : base b a = tau * base a b * tau⁻¹ := by
    unfold base tau
    exact h
  rw [tau_inv] at h'
  rw [h', mul_assoc (tau * base a b) tau tau, tau_mul_tau, mul_one]

theorem base_injective {a b c d : A} : base a b = base c d ↔ a = c ∧ b = d := by
  unfold base
  rw [inl_injective.eq_iff, Prod.mk.injEq]

@[expose] def swapChar : Wr2 A →* Multiplicative (ZMod 2) := rightHom

@[simp] theorem swapChar_base (a b : A) : swapChar (base a b) = 1 := rightHom_inl _

@[simp] theorem swapChar_tau : swapChar (tau : Wr2 A) = Multiplicative.ofAdd 1 := rightHom_inr _

theorem base_mul_tau_inj {a b c d : A} : base a b * tau = base c d * tau ↔ a = c ∧ b = d := by
  rw [mul_left_inj, base_injective]

theorem base_ne_base_mul_tau (a b c d : A) : base a b ≠ base c d * tau := by
  intro h
  have h' := congrArg swapChar h
  rw [map_mul, swapChar_base, swapChar_base, swapChar_tau, one_mul] at h'
  exact absurd h' (by decide)

theorem eq_base_or_eq_base_mul_tau (w : Wr2 A) :
    (∃ a b, w = base a b) ∨ ∃ a b, w = base a b * tau := by
  obtain ⟨⟨a, b⟩, g⟩ := w
  rcases zmod2_cases g with rfl | rfl
  · left
    refine ⟨a, b, ?_⟩
    rw [mk_eq_inl_mul_inr, map_one, mul_one]; rfl
  · right
    exact ⟨a, b, mk_eq_inl_mul_inr _ _⟩

theorem base_mul_tau_sq (a b : A) :
    (base a b * tau) * (base a b * tau) = base (a * b) (b * a) := by
  rw [mul_assoc, ← mul_assoc tau, tau_mul_base, mul_assoc (base b a) tau tau,
    tau_mul_tau, mul_one, base_mul_base]

@[expose] def baseSubgroup : Subgroup (Wr2 A) := (inl : A × A →* Wr2 A).range

theorem swapChar_ker : (swapChar : Wr2 A →* Multiplicative (ZMod 2)).ker = baseSubgroup := by
  ext w
  rw [MonoidHom.mem_ker]
  constructor
  · intro hw
    rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact ⟨(a, b), rfl⟩
    · rw [map_mul, swapChar_base, swapChar_tau, one_mul] at hw
      exact absurd hw (by decide)
  · rintro ⟨x, rfl⟩
    exact swapChar_base x.1 x.2

theorem mem_baseSubgroup_iff (w : Wr2 A) : w ∈ (baseSubgroup : Subgroup (Wr2 A)) ↔ swapChar w = 1 := by
  rw [← swapChar_ker]; rfl

instance : (baseSubgroup : Subgroup (Wr2 A)).Normal := by
  rw [← swapChar_ker]; infer_instance

theorem card_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod 2

theorem conj_base_base (c d a b : A) :
    base c d * base a b * (base c d)⁻¹ = base (c * a * c⁻¹) (d * b * d⁻¹) := by
  rw [base_inv, base_mul_base, base_mul_base]

theorem conj_base_base_mul_tau (x y a b : A) :
    base x y * (base a b * tau) * (base x y)⁻¹ = base (x * a * y⁻¹) (y * b * x⁻¹) * tau := by
  rw [base_inv, mul_assoc, mul_assoc, tau_mul_base, ← mul_assoc (base a b), ← mul_assoc,
    base_mul_base, base_mul_base]
  simp only [mul_assoc]

theorem conj_base_tau (c d : A) :
    base c d * tau * (base c d)⁻¹ = base (c * d⁻¹) (d * c⁻¹) * tau := by
  have h := conj_base_base_mul_tau c d 1 1
  rw [base_one, one_mul] at h
  simpa using h

theorem not_isConj_base_tau (a b c d : A) : ¬ IsConj (base a b) (base c d * tau) := by
  intro h
  have h' := isConj_iff_eq.mp ((swapChar : Wr2 A →* Multiplicative (ZMod 2)).map_isConj h)
  rw [map_mul, swapChar_base, swapChar_base, swapChar_tau, one_mul] at h'
  exact absurd h' (by decide)

theorem eq_top_of_tau_mem_of_base_mem {H : Subgroup (Wr2 A)} (ht : tau ∈ H)
    (hb : ∀ a : A, base a 1 ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro w _
  have hb1 : ∀ b : A, base 1 b ∈ H := by
    intro b
    have : base 1 b = tau * base b 1 * tau⁻¹ := by
      rw [tau_mul_base, tau_inv, mul_assoc, tau_mul_tau, mul_one]
    rw [this]
    exact H.mul_mem (H.mul_mem ht (hb b)) (H.inv_mem ht)
  have hbase : ∀ a b : A, base a b ∈ H := by
    intro a b
    have : base a b = base a 1 * base 1 b := by rw [base_mul_base, mul_one, one_mul]
    rw [this]
    exact H.mul_mem (hb a) (hb1 b)
  rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · exact hbase a b
  · exact H.mul_mem (hbase a b) ht

theorem card_ker_swapChar_restrict (H : Subgroup (Wr2 A)) :
    Nat.card (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2)).ker
      = Nat.card {p : A × A // base p.1 p.2 ∈ H} := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective
    (fun p => (⟨⟨base p.1.1 p.1.2, p.2⟩, by simp [MonoidHom.mem_ker]⟩ :
      (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2)).ker)) ⟨?_, ?_⟩
  · intro p q hpq
    have h := congrArg (fun x => (x.1 : Wr2 A)) hpq
    simp only at h
    exact Subtype.ext (Prod.ext (base_injective.mp h).1 (base_injective.mp h).2)
  · rintro ⟨⟨w, hwH⟩, hk⟩
    have hk' : swapChar w = 1 := by simpa [MonoidHom.mem_ker] using hk
    rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
    · exact ⟨⟨(a, b), hwH⟩, rfl⟩
    · rw [map_mul, swapChar_base, swapChar_tau, one_mul] at hk'
      exact absurd hk' (by decide)

theorem card_subgroup_of_exists (H : Subgroup (Wr2 A)) (h : ∃ x ∈ H, swapChar x ≠ 1) :
    Nat.card H = 2 * Nat.card {p : A × A // base p.1 p.2 ∈ H} := by
  rw [← card_ker_swapChar_restrict, ← Subgroup.card_ker_mul_card_range
    (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2)), mul_comm]
  congr 1
  have : (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2)).range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hxH, hx⟩ := h
    rcases zmod2_cases y with rfl | rfl
    · exact one_mem _
    · rcases zmod2_cases (swapChar x) with h1 | h1
      · exact absurd h1 hx
      · exact ⟨⟨x, hxH⟩, h1⟩
  rw [this, Subgroup.card_top, card_multiplicative_zmod_two]

theorem card_subgroup_of_forall (H : Subgroup (Wr2 A)) (h : ∀ x ∈ H, swapChar x = 1) :
    Nat.card H = Nat.card {p : A × A // base p.1 p.2 ∈ H} := by
  rw [← card_ker_swapChar_restrict, ← Subgroup.card_ker_mul_card_range
    (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2))]
  have : (swapChar.comp H.subtype : H →* Multiplicative (ZMod 2)).range = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨x, rfl⟩
    exact h x.1 x.2
  rw [this, Subgroup.card_bot, mul_one]

theorem card_wr2 [Finite A] : Nat.card (Wr2 A) = 2 * Nat.card A ^ 2 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd : Wr2 A ≃ (A × A) × Multiplicative (ZMod 2)),
    Nat.card_prod, Nat.card_prod, card_multiplicative_zmod_two]
  ring

theorem swapChar_base_mul_tau (a b : A) : swapChar (base a b * tau) = Multiplicative.ofAdd 1 := by
  rw [map_mul, swapChar_base, swapChar_tau, one_mul]

theorem swapChar_base_mul_tau_ne_one (a b : A) : swapChar (base a b * tau) ≠ 1 := by
  rw [swapChar_base_mul_tau]; decide

theorem mem_centralizer_tau_iff (c d : A) :
    base c d ∈ Subgroup.centralizer ({tau} : Set (Wr2 A)) ↔ c = d := by
  rw [mem_centralizer_singleton_iff, tau_mul_base, base_mul_tau_inj]
  exact ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩

theorem mem_centralizer_base_mul_tau_iff (c d a b : A) :
    base c d ∈ Subgroup.centralizer ({base a b * tau} : Set (Wr2 A)) ↔
      c * a * d⁻¹ = a ∧ d * b * c⁻¹ = b := by
  rw [mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul, conj_base_base_mul_tau,
    base_mul_tau_inj]

theorem mem_centralizer_base_iff (c d a b : A) :
    base c d ∈ Subgroup.centralizer ({base a b} : Set (Wr2 A)) ↔ c * a = a * c ∧ d * b = b * d := by
  rw [mem_centralizer_singleton_iff, base_mul_base, base_mul_base, base_injective]

theorem base_mul_tau_mem_centralizer_base_iff (c d a b : A) :
    base c d * tau ∈ Subgroup.centralizer ({base a b} : Set (Wr2 A)) ↔
      c * b = a * c ∧ d * a = b * d := by
  rw [mem_centralizer_singleton_iff, mul_assoc, tau_mul_base, ← mul_assoc, ← mul_assoc,
    base_mul_base, base_mul_base, base_mul_tau_inj]

theorem card_centralizer_tau [Finite A] :
    Nat.card (Subgroup.centralizer ({tau} : Set (Wr2 A))) = 2 * Nat.card A := by
  rw [card_subgroup_of_exists _ ⟨tau, mem_centralizer_singleton_iff.mpr rfl, by simp⟩]
  congr 1
  symm
  apply Nat.card_congr
  exact
    { toFun := fun a => ⟨(a, a), (mem_centralizer_tau_iff a a).mpr rfl⟩
      invFun := fun p => p.1.1
      left_inv := fun _ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl ((mem_centralizer_tau_iff _ _).mp p.2)) }

theorem card_centralizer_base_mul_tau [Finite A] (a b : A) :
    Nat.card (Subgroup.centralizer ({base a b * tau} : Set (Wr2 A)))
      = 2 * Nat.card (Subgroup.centralizer ({a * b} : Set A)) := by
  rw [card_subgroup_of_exists _ ⟨base a b * tau, mem_centralizer_singleton_iff.mpr rfl,
    swapChar_base_mul_tau_ne_one a b⟩]
  congr 1
  symm
  apply Nat.card_congr
  exact
    { toFun := fun c => ⟨(c.1, a⁻¹ * c.1 * a), (mem_centralizer_base_mul_tau_iff _ _ _ _).mpr (by
        have hc : c.1 * (a * b) = a * b * c.1 := mem_centralizer_singleton_iff.mp c.2
        have hc' : c.1 * a * b = a * b * c.1 := by simpa [mul_assoc] using hc
        refine ⟨by group, ?_⟩
        calc a⁻¹ * c.1 * a * b * c.1⁻¹ = a⁻¹ * (c.1 * a * b) * c.1⁻¹ := by group
          _ = b := by rw [hc']; group)⟩
      invFun := fun p => ⟨p.1.1, by
        obtain ⟨h1, h2⟩ := (mem_centralizer_base_mul_tau_iff _ _ _ _).mp p.2
        rw [mul_inv_eq_iff_eq_mul] at h1 h2
        rw [mem_centralizer_singleton_iff]
        calc p.1.1 * (a * b) = (p.1.1 * a) * b := by rw [mul_assoc]
          _ = a * (p.1.2 * b) := by rw [h1, mul_assoc]
          _ = a * b * p.1.1 := by rw [h2, mul_assoc]⟩
      left_inv := fun c => Subtype.ext rfl
      right_inv := fun p => by
        obtain ⟨h1, -⟩ := (mem_centralizer_base_mul_tau_iff _ _ _ _).mp p.2
        rw [mul_inv_eq_iff_eq_mul] at h1
        refine Subtype.ext (Prod.ext rfl ?_)
        show a⁻¹ * p.1.1 * a = p.1.2
        rw [mul_assoc, h1, inv_mul_cancel_left] }

theorem card_base_centralizer_base [Finite A] (a b : A) :
    Nat.card {p : A × A // base p.1 p.2 ∈ Subgroup.centralizer ({base a b} : Set (Wr2 A))}
      = Nat.card (Subgroup.centralizer ({a} : Set A)) *
        Nat.card (Subgroup.centralizer ({b} : Set A)) := by
  rw [← Nat.card_prod]
  symm
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨(x.1.1, x.2.1), (mem_centralizer_base_iff _ _ _ _).mpr
        ⟨mem_centralizer_singleton_iff.mp x.1.2, mem_centralizer_singleton_iff.mp x.2.2⟩⟩
      invFun := fun p =>
        ((⟨p.1.1, mem_centralizer_singleton_iff.mpr ((mem_centralizer_base_iff _ _ _ _).mp p.2).1⟩,
          ⟨p.1.2, mem_centralizer_singleton_iff.mpr ((mem_centralizer_base_iff _ _ _ _).mp p.2).2⟩) :
          Subgroup.centralizer ({a} : Set A) × Subgroup.centralizer ({b} : Set A))
      left_inv := fun x => rfl
      right_inv := fun p => rfl }

theorem card_centralizer_base_of_not_isConj [Finite A] {a b : A} (h : ¬ IsConj a b) :
    Nat.card (Subgroup.centralizer ({base a b} : Set (Wr2 A)))
      = Nat.card (Subgroup.centralizer ({a} : Set A)) *
        Nat.card (Subgroup.centralizer ({b} : Set A)) := by
  rw [card_subgroup_of_forall, card_base_centralizer_base]
  intro x hx
  rcases eq_base_or_eq_base_mul_tau x with ⟨c, d, rfl⟩ | ⟨c, d, rfl⟩
  · exact swapChar_base c d
  · exfalso
    obtain ⟨h1, -⟩ := (base_mul_tau_mem_centralizer_base_iff _ _ _ _).mp hx
    apply h
    rw [isConj_iff]
    refine ⟨c⁻¹, ?_⟩
    calc c⁻¹ * a * c⁻¹⁻¹ = c⁻¹ * (a * c) := by group
      _ = c⁻¹ * (c * b) := by rw [h1]
      _ = b := by group

theorem card_centralizer_base_of_isConj [Finite A] {a b : A} (h : IsConj a b) :
    Nat.card (Subgroup.centralizer ({base a b} : Set (Wr2 A)))
      = 2 * Nat.card (Subgroup.centralizer ({a} : Set A)) *
        Nat.card (Subgroup.centralizer ({b} : Set A)) := by
  obtain ⟨z, hz⟩ := isConj_iff.mp h
  have hmem : base z⁻¹ z * tau ∈ Subgroup.centralizer ({base a b} : Set (Wr2 A)) := by
    rw [base_mul_tau_mem_centralizer_base_iff]
    constructor
    · rw [← hz]; group
    · rw [← hz]; group
  rw [card_subgroup_of_exists _ ⟨_, hmem, swapChar_base_mul_tau_ne_one _ _⟩,
    card_base_centralizer_base, mul_assoc]

theorem card_centralizer_base_self [Finite A] (c : A) :
    Nat.card (Subgroup.centralizer ({base c c} : Set (Wr2 A)))
      = 2 * Nat.card (Subgroup.centralizer ({c} : Set A)) ^ 2 := by
  rw [card_centralizer_base_of_isConj (IsConj.refl c)]
  ring

theorem base_mem_centralizer_base_self (c : A) :
    base c 1 ∈ Subgroup.centralizer ({base c c} : Set (Wr2 A)) := by
  rw [mem_centralizer_base_iff]
  simp

section Functoriality

variable {B : Type*} [Group B]

theorem map_swap_compat (f : A →* B) (g : Multiplicative (ZMod 2)) :
    (f.prodMap f).comp (swapHom A g).toMonoidHom
      = (swapHom B (MonoidHom.id _ g)).toMonoidHom.comp (f.prodMap f) := by
  rcases zmod2_cases g with rfl | rfl
  · ext ⟨a, b⟩ <;> simp
  · rw [MonoidHom.id_apply, swapHom_one', swapHom_one']
    ext ⟨a, b⟩ <;> rfl

@[expose] def mapHom (f : A →* B) : Wr2 A →* Wr2 B :=
  SemidirectProduct.map (f.prodMap f) (MonoidHom.id _) (map_swap_compat f)

theorem mapHom_base (f : A →* B) (a b : A) : mapHom f (base a b) = base (f a) (f b) := by
  simp [mapHom, base]

theorem mapHom_tau (f : A →* B) : mapHom f tau = tau := by
  simp [mapHom, tau]

@[expose] def mapEquiv (f : A ≃* B) : Wr2 A ≃* Wr2 B :=
  MonoidHom.toMulEquiv (mapHom f.toMonoidHom) (mapHom f.symm.toMonoidHom)
    (by
      refine MonoidHom.ext fun w => ?_
      rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;>
        simp [mapHom_base, mapHom_tau])
    (by
      refine MonoidHom.ext fun w => ?_
      rcases eq_base_or_eq_base_mul_tau w with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩ <;>
        simp [mapHom_base, mapHom_tau])

theorem mapEquiv_base (f : A ≃* B) (a b : A) : mapEquiv f (base a b) = base (f a) (f b) :=
  mapHom_base f.toMonoidHom a b

theorem mapEquiv_tau (f : A ≃* B) : mapEquiv f (tau : Wr2 A) = tau :=
  mapHom_tau f.toMonoidHom

end Functoriality

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Wreath
