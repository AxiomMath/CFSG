module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup

variable {X : Type*} [Group X]

theorem isElementaryAbelian_of_sq_eq_one {Y : Type*} [Group Y] (A : Subgroup Y)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hs : ∀ a ∈ A, a * a = 1) :
    IsElementaryAbelian 2 A := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

structure CentralLift (Z E : Subgroup X) (r : ℕ) : Prop where
  central : Z ≤ center X
  le : Z ≤ E
  sq_mem : ∀ e ∈ E, e * e ∈ Z
  comm_mem : ∀ e ∈ E, ∀ f ∈ E, e * f * e⁻¹ * f⁻¹ ∈ Z
  bound : ∀ A : Subgroup X, A ≤ Z → (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ r

namespace CentralLift

variable {Z E : Subgroup X} {r : ℕ}

theorem commute_of_mem (h : CentralLift Z E r) {z : X} (hz : z ∈ Z) (g : X) : g * z = z * g :=
  Subgroup.mem_center_iff.1 (h.central hz) g

@[expose] def commHom (h : CentralLift Z E r) {D : Subgroup X} (hD : D ≤ E) {x : X} (hx : x ∈ E) :
    ↥D →* X where
  toFun d := (d : X) * x * (d : X)⁻¹ * x⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hca := h.comm_mem _ (hD a.2) x hx
    have hcb := h.comm_mem _ (hD b.2) x hx
    have e : ((a * b : ↥D) : X) * x * ((a * b : ↥D) : X)⁻¹ * x⁻¹ =
        ((a : X) * ((b : X) * x * (b : X)⁻¹ * x⁻¹) * (a : X)⁻¹) *
          ((a : X) * x * (a : X)⁻¹ * x⁻¹) := by
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    have hc := h.commute_of_mem hcb (a : X)
    rw [e, show (a : X) * ((b : X) * x * (b : X)⁻¹ * x⁻¹) * (a : X)⁻¹ =
        (b : X) * x * (b : X)⁻¹ * x⁻¹ by
      calc (a : X) * ((b : X) * x * (b : X)⁻¹ * x⁻¹) * (a : X)⁻¹
          = ((b : X) * x * (b : X)⁻¹ * x⁻¹) * (a : X) * (a : X)⁻¹ := by rw [hc]
        _ = (b : X) * x * (b : X)⁻¹ * x⁻¹ := mul_inv_cancel_right _ _]
    exact h.commute_of_mem hca _

theorem commHom_apply (h : CentralLift Z E r) {D : Subgroup X} (hD : D ≤ E) {x : X} (hx : x ∈ E)
    (d : ↥D) : commHom h hD hx d = (d : X) * x * (d : X)⁻¹ * x⁻¹ := rfl

theorem card_le_mul_card_inf_centralizer [Finite X] (h : CentralLift Z E r) {D : Subgroup X}
    (hD : D ≤ E) {x : X} (hx : x ∈ E) :
    Nat.card D ≤ 2 ^ r * Nat.card ↥(D ⊓ centralizer ({x} : Set X)) := by
  let φ := commHom h hD hx
  have hker : φ.ker = (D ⊓ centralizer ({x} : Set X)).subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_centralizer_singleton_iff, commHom_apply]
    refine ⟨fun e => ⟨d.2, ?_⟩, fun e => ?_⟩
    · rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at e
      exact e
    · calc (d : X) * x * (d : X)⁻¹ * x⁻¹ = x * (d : X) * (d : X)⁻¹ * x⁻¹ := by rw [e.2]
        _ = 1 := by group
  have hrange : Nat.card φ.range ≤ 2 ^ r := by
    apply h.bound
    · rintro _ ⟨d, rfl⟩
      exact h.comm_mem _ (hD d.2) x hx
    · rintro _ ⟨d, rfl⟩
      rw [← map_mul]
      have hdd := h.sq_mem _ (hD d.2)
      have hc := h.commute_of_mem hdd x
      show ((d * d : ↥D) : X) * x * ((d * d : ↥D) : X)⁻¹ * x⁻¹ = 1
      rw [Subgroup.coe_mul, ← hc, mul_inv_cancel_right, mul_inv_cancel]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at h1
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  calc Nat.card D = _ := h1.symm
    _ ≤ Nat.card ↥(D ⊓ centralizer ({x} : Set X)) * 2 ^ r := Nat.mul_le_mul_left _ hrange
    _ = _ := mul_comm _ _

theorem exists_extension [Finite X] (h : CentralLift Z E r) {W : Subgroup X} (hWE : W ≤ E)
    (hZW : Z ≤ W) {x : X} (hxE : x ∈ E) (hxc : ∀ w ∈ W, w * x = x * w) (hxW : x ∉ W) :
    ∃ W' : Subgroup X, W ≤ W' ∧ W' ≤ E ∧ x ∈ W' ∧ Nat.card W' = 2 * Nat.card W ∧
      (∀ y : X, (∀ w ∈ W, y * w = w * y) → y * x = x * y → ∀ w' ∈ W', y * w' = w' * y) ∧
      ((∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → ∀ a ∈ W', ∀ b ∈ W', a * b = b * a) := by
  have hx2 : x * x ∈ W := hZW (h.sq_mem x hxE)
  have hxi : ∀ w ∈ W, x⁻¹ * w = w * x⁻¹ := fun w hw => by
    calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * w) * x⁻¹ := by rw [hxc w hw]
      _ = w * x⁻¹ := by group
  let W' : Subgroup X :=
    { carrier := {y | y ∈ W ∨ x⁻¹ * y ∈ W}
      mul_mem' := by
        rintro y₁ y₂ (h₁ | h₁) (h₂ | h₂)
        · exact Or.inl (W.mul_mem h₁ h₂)
        · refine Or.inr ?_
          have : x⁻¹ * (y₁ * y₂) = y₁ * (x⁻¹ * y₂) := by rw [← mul_assoc, hxi y₁ h₁, mul_assoc]
          rw [this]
          exact W.mul_mem h₁ h₂
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact W.mul_mem h₁ h₂
        · refine Or.inl ?_
          obtain ⟨w₁, hw₁, rfl⟩ : ∃ w₁ ∈ W, y₁ = x * w₁ := ⟨x⁻¹ * y₁, h₁, by group⟩
          obtain ⟨w₂, hw₂, rfl⟩ : ∃ w₂ ∈ W, y₂ = x * w₂ := ⟨x⁻¹ * y₂, h₂, by group⟩
          have : x * w₁ * (x * w₂) = (x * x) * (w₁ * w₂) := by
            calc x * w₁ * (x * w₂) = x * (w₁ * x) * w₂ := by group
              _ = x * (x * w₁) * w₂ := by rw [hxc w₁ hw₁]
              _ = (x * x) * (w₁ * w₂) := by group
          rw [this]
          exact W.mul_mem hx2 (W.mul_mem hw₁ hw₂)
      one_mem' := Or.inl W.one_mem
      inv_mem' := by
        rintro y (h₁ | h₁)
        · exact Or.inl (W.inv_mem h₁)
        · refine Or.inr ?_
          obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, y = x * w := ⟨x⁻¹ * y, h₁, by group⟩
          have : x⁻¹ * (x * w)⁻¹ = w⁻¹ * (x * x)⁻¹ := by
            calc x⁻¹ * (x * w)⁻¹ = x⁻¹ * w⁻¹ * x⁻¹ := by group
              _ = w⁻¹ * x⁻¹ * x⁻¹ := by rw [hxi w⁻¹ (W.inv_mem hw)]
              _ = w⁻¹ * (x * x)⁻¹ := by group
          rw [this]
          exact W.mul_mem (W.inv_mem hw) (W.inv_mem hx2) }
  have hWW' : W ≤ W' := fun y hy => Or.inl hy
  have hxW' : x ∈ W' := Or.inr (by simp)
  have hW'E : W' ≤ E := by
    intro y hy
    rcases hy with hy | hy
    · exact hWE hy
    · have : y = x * (x⁻¹ * y) := by group
      rw [this]
      exact E.mul_mem hxE (hWE hy)
  have hle2 : Nat.card W' ≤ 2 * Nat.card W := by
    classical
    let f : ↥W' → ↥W × Bool := fun y =>
      if hy : (y : X) ∈ W then (⟨y, hy⟩, false) else (⟨x⁻¹ * y, y.2.resolve_left hy⟩, true)
    have hf : Function.Injective f := by
      intro y₁ y₂ hy
      by_cases h₁ : (y₁ : X) ∈ W <;> by_cases h₂ : (y₂ : X) ∈ W
      · simp only [f, h₁, h₂, dite_true] at hy
        exact Subtype.ext (by simpa using congrArg (fun p => (p.1 : X)) hy)
      · simp [f, h₁, h₂] at hy
      · simp [f, h₁, h₂] at hy
      · simp only [f, h₁, h₂, dite_false, Prod.mk.injEq, and_true] at hy
        apply Subtype.ext
        have := congrArg Subtype.val hy
        simpa using this
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at this
    simpa [mul_comm] using this
  have hcard : Nat.card W' = 2 * Nat.card W := by
    have hpos : 0 < Nat.card W := Nat.card_pos
    have hle : Nat.card W ≤ Nat.card W' := Subgroup.card_le_of_le hWW'
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hWW'
    have hne : Nat.card W ≠ Nat.card W' := fun e => by
      have : Finite W' := inferInstance
      have := Subgroup.eq_of_le_of_card_ge hWW' e.ge
      exact hxW (this ▸ hxW')
    rw [hm] at hle hle2 hne
    have h1 : m ≤ 2 := by nlinarith
    have h0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp at hle
        omega
      · exact h0
    have h2 : m ≠ 1 := fun e => hne (by rw [e, mul_one])
    have : m = 2 := by omega
    rw [hm, this, mul_comm]
  refine ⟨W', hWW', hW'E, hxW', hcard, ?_, ?_⟩
  · intro y hyW hyx w' hw'
    rcases hw' with hw' | hw'
    · exact hyW w' hw'
    · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, w' = x * w := ⟨x⁻¹ * w', hw', by group⟩
      calc y * (x * w) = (y * x) * w := by group
        _ = (x * y) * w := by rw [hyx]
        _ = x * (y * w) := by group
        _ = x * (w * y) := by rw [hyW w hw]
        _ = x * w * y := by group
  · intro hab a ha b hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hab a ha b hb
    · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, b = x * w := ⟨x⁻¹ * b, hb, by group⟩
      calc a * (x * w) = (a * x) * w := by group
        _ = (x * a) * w := by rw [hxc a ha]
        _ = x * (a * w) := by group
        _ = x * (w * a) := by rw [hab a ha w hw]
        _ = x * w * a := by group
    · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, a = x * w := ⟨x⁻¹ * a, ha, by group⟩
      calc x * w * b = x * (w * b) := by group
        _ = x * (b * w) := by rw [hab w hw b hb]
        _ = (x * b) * w := by group
        _ = (b * x) * w := by rw [hxc b hb]
        _ = b * (x * w) := by group
    · obtain ⟨w₁, hw₁, rfl⟩ : ∃ w ∈ W, a = x * w := ⟨x⁻¹ * a, ha, by group⟩
      obtain ⟨w₂, hw₂, rfl⟩ : ∃ w ∈ W, b = x * w := ⟨x⁻¹ * b, hb, by group⟩
      calc x * w₁ * (x * w₂) = x * (w₁ * x) * w₂ := by group
        _ = x * (x * w₁) * w₂ := by rw [hxc w₁ hw₁]
        _ = x * x * (w₁ * w₂) := by group
        _ = x * x * (w₂ * w₁) := by rw [hab w₁ hw₁ w₂ hw₂]
        _ = x * (x * w₂) * w₁ := by group
        _ = x * (w₂ * x) * w₁ := by rw [hxc w₂ hw₂]
        _ = x * w₂ * (x * w₁) := by group

theorem exists_abelian_chain [Finite X] (h : CentralLift Z E r) {n : ℕ}
    (hn : 2 ^ n * Nat.card Z ≤ Nat.card E) :
    ∀ t : ℕ, (∀ k < t, k * (r + 1) < n) →
      ∃ W : Subgroup X, W ≤ E ∧ Z ≤ W ∧ (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) ∧
        Nat.card W = 2 ^ t * Nat.card Z ∧
        Nat.card E ≤ 2 ^ (r * t) * Nat.card ↥(E ⊓ centralizer (W : Set X)) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨Z, h.le, le_rfl, fun a ha b hb => h.commute_of_mem hb a, by simp, ?_⟩
    have hEc : E ≤ E ⊓ centralizer (Z : Set X) := by
      refine le_inf le_rfl fun e _ => ?_
      rw [mem_centralizer_iff]
      intro z hz
      exact (h.commute_of_mem hz e).symm
    simpa using Subgroup.card_le_of_le hEc
  | succ t ih =>
    intro hT
    obtain ⟨W, hWE, hZW, hWab, hWcard, hWc⟩ := ih fun k hk => hT k (by omega)
    set C : Subgroup X := E ⊓ centralizer (W : Set X) with hC
    have hWC : W ≤ C := by
      refine le_inf hWE fun w hw => ?_
      rw [mem_centralizer_iff]
      intro v hv
      exact (hWab v hv w hw)
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hlt : Nat.card W < Nat.card C := by
      have h1 : 2 ^ (r * t + t) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num)
        (by have := hT t (by omega); nlinarith)
      have h2 : 2 ^ (r * t) * (2 ^ t * Nat.card Z) < 2 ^ (r * t) * Nat.card C := by
        calc 2 ^ (r * t) * (2 ^ t * Nat.card Z) = 2 ^ (r * t + t) * Nat.card Z := by ring
          _ < 2 ^ n * Nat.card Z := Nat.mul_lt_mul_of_pos_right h1 hZpos
          _ ≤ Nat.card E := hn
          _ ≤ 2 ^ (r * t) * Nat.card C := hWc
      rw [hWcard]
      exact Nat.lt_of_mul_lt_mul_left h2
    have hex : ∃ x ∈ C, x ∉ W := by
      by_contra hno
      push Not at hno
      have : C ≤ W := fun x hx => hno x hx
      exact absurd (Subgroup.card_le_of_le this) (not_le.2 hlt)
    obtain ⟨x, hxC, hxW⟩ := hex
    have hxE : x ∈ E := hxC.1
    have hxc : ∀ w ∈ W, w * x = x * w := fun w hw => mem_centralizer_iff.1 hxC.2 w hw
    obtain ⟨W', hWW', hW'E, hxW', hcard, hcent, hab⟩ :=
      exists_extension h hWE hZW hxE hxc hxW
    refine ⟨W', hW'E, hZW.trans hWW', hab hWab, ?_, ?_⟩
    · rw [hcard, hWcard, pow_succ]
      ring
    · have hCE : C ≤ E := inf_le_left
      have h1 := card_le_mul_card_inf_centralizer h hCE hxE
      have h2 : C ⊓ centralizer ({x} : Set X) ≤ E ⊓ centralizer (W' : Set X) := by
        refine le_inf (inf_le_left.trans inf_le_left) fun y hy => ?_
        rw [mem_centralizer_iff]
        intro w' hw'
        have := hcent y (fun w hw => (mem_centralizer_iff.1 hy.1.2 w hw).symm)
          (mem_centralizer_singleton_iff.1 hy.2) w' hw'
        exact this.symm
      calc Nat.card E ≤ 2 ^ (r * t) * Nat.card C := hWc
        _ ≤ 2 ^ (r * t) * (2 ^ r * Nat.card ↥(C ⊓ centralizer ({x} : Set X))) :=
          Nat.mul_le_mul_left _ h1
        _ ≤ 2 ^ (r * t) * (2 ^ r * Nat.card ↥(E ⊓ centralizer (W' : Set X))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le h2))
        _ = 2 ^ (r * (t + 1)) * Nat.card ↥(E ⊓ centralizer (W' : Set X)) := by ring

theorem exists_elementaryAbelian_of_abelian [Finite X] (h : CentralLift Z E r) {W : Subgroup X}
    (hWE : W ≤ E) (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    ∃ A : Subgroup X, A ≤ W ∧ IsElementaryAbelian 2 A ∧ Nat.card W ≤ Nat.card A * Nat.card Z := by
  let φ : ↥W →* X :=
    { toFun := fun w => (w : X) * w
      map_one' := by simp
      map_mul' := fun a b => by
        have hba := hab a a.2 b b.2
        simp only [Subgroup.coe_mul]
        calc (a : X) * b * ((a : X) * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hba]
          _ = ((a : X) * a) * ((b : X) * b) := by group }
  have hrange : φ.range ≤ Z := by
    rintro _ ⟨w, rfl⟩
    exact h.sq_mem _ (hWE w.2)
  let A : Subgroup X := φ.ker.map W.subtype
  have hAW : A ≤ W := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hsq : ∀ a ∈ A, a * a = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw
  refine ⟨A, hAW, ?_, ?_⟩
  · exact isElementaryAbelian_of_sq_eq_one A (fun a ha b hb => hab a (hAW ha) b (hAW hb)) hsq
  · have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card A = Nat.card φ.ker :=
      Nat.card_congr (φ.ker.equivMapOfInjective W.subtype W.subtype_injective).toEquiv.symm
    have h3 : Nat.card φ.range ≤ Nat.card Z := Subgroup.card_le_of_le hrange
    calc Nat.card W = Nat.card φ.ker * Nat.card φ.range := h1.symm
      _ ≤ Nat.card A * Nat.card Z := by rw [h2]; exact Nat.mul_le_mul_left _ h3

theorem exists_elementaryAbelian_of_central_lift [Finite X] (h : CentralLift Z E r) {n t : ℕ}
    (hn : 2 ^ n * Nat.card Z ≤ Nat.card E) (ht : ∀ k < t, k * (r + 1) < n) :
    ∃ A : Subgroup X, A ≤ E ∧ IsElementaryAbelian 2 A ∧ ∃ k, t ≤ k ∧ Nat.card A = 2 ^ k := by
  obtain ⟨W, hWE, -, hab, hcard, -⟩ := exists_abelian_chain h hn t ht
  obtain ⟨A, hAW, hA, hAc⟩ := exists_elementaryAbelian_of_abelian h hWE hab
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  refine ⟨A, hAW.trans hWE, hA, k, ?_, hk⟩
  have h1 : 2 ^ t ≤ 2 ^ k := by
    rw [hcard] at hAc
    rw [hk] at hAc
    exact Nat.le_of_mul_le_mul_right hAc hZpos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

end CentralLift

theorem exists_elementaryAbelian_of_quotient [Finite X] {Q : Type*} [Group Q] (π : X →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center X) {r n t : ℕ}
    (hr : ∀ A : Subgroup X, A ≤ π.ker → (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 2 ^ r)
    (V : Subgroup Q) [hV : IsElementaryAbelian 2 V] (hVn : 2 ^ n ≤ Nat.card V)
    (ht : ∀ k < t, k * (r + 1) < n) :
    ∃ A : Subgroup X, IsElementaryAbelian 2 A ∧ ∃ k, t ≤ k ∧ Nat.card A = 2 ^ k := by
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have h1 : (⟨v, hv⟩ : V) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨v, hv⟩
    simpa [pow_two] using congrArg Subtype.val h1
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have := hV.toIsMulCommutative.is_comm.comm (⟨v, hv⟩ : V) ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  let E : Subgroup X := V.comap π
  have hE : CentralLift π.ker E r :=
    { central := hker
      le := fun z hz => by
        show π z ∈ V
        rw [MonoidHom.mem_ker.1 hz]
        exact V.one_mem
      sq_mem := fun e he => by
        rw [MonoidHom.mem_ker, map_mul]
        exact hVsq _ he
      comm_mem := fun e he f hf => by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        have := hVcomm _ he _ hf
        calc π e * π f * (π e)⁻¹ * (π f)⁻¹ = π f * π e * (π e)⁻¹ * (π f)⁻¹ := by rw [this]
          _ = 1 := by group
      bound := hr }
  have hcard : Nat.card E = Nat.card V * Nat.card π.ker := by
    let ψ : ↥E →* ↥V :=
      { toFun := fun d => ⟨π d, d.2⟩
        map_one' := Subtype.ext (map_one π)
        map_mul' := fun a b => Subtype.ext (map_mul π (a : X) (b : X)) }
    have hψker : ψ.ker = π.ker.subgroupOf E := by
      ext d
      simp [ψ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    have hψrange : ψ.range = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      obtain ⟨x, rfl⟩ := hπ v
      exact ⟨⟨x, hv⟩, rfl⟩
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hψrange, hψker] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.le).toEquiv,
      Nat.card_congr (Subgroup.topEquiv).toEquiv] at h1
    rw [mul_comm]
    exact h1.symm
  have hn : 2 ^ n * Nat.card π.ker ≤ Nat.card E := by
    rw [hcard]
    exact Nat.mul_le_mul_right _ hVn
  obtain ⟨A, -, hA, hk⟩ := CentralLift.exists_elementaryAbelian_of_central_lift hE hn ht
  exact ⟨A, hA, hk⟩

theorem card_le_two_pow_of_dvd {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y}
    (hA : ∀ a ∈ A, a * a = 1) {N r : ℕ} (hdvd : Nat.card A ∣ N) (hN : ¬ 2 ^ (r + 1) ∣ N) :
    Nat.card A ≤ 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥A := fun a => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hA a a.2⟩
  obtain ⟨j, hj⟩ := hp.exists_card_eq
  rw [hj] at hdvd ⊢
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hjr
  exact hN ((pow_dvd_pow 2 (by omega)).trans hdvd)

end CFSG.EvenSporadicStandard.Induction.Hyp
