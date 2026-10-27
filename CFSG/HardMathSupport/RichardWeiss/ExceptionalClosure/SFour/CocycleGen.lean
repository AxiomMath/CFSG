module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_g_commutator_eq {Y : Subgroup G}
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {g δ z : G} (hu : ⁅g, z⁆ ∈ Y) (hw : ⁅δ, z⁆ ∈ Y) :
    ⁅g, ⁅δ, z⁆⁆ =
      ((δ * g) * ⁅(δ * g)⁻¹ * (g * δ), z⁆ * (δ * g)⁻¹) * ⁅δ, ⁅g, z⁆⁆ := by
  set u : G := ⁅g, z⁆ with hudef
  set w : G := ⁅δ, z⁆ with hwdef
  set k : G := (δ * g)⁻¹ * (g * δ) with hkdef
  set x : G := (δ * g) * ⁅k, z⁆ * (δ * g)⁻¹ with hxdef
  set A : G := g * w * g⁻¹ with hAdef
  set B : G := δ * u * δ⁻¹ with hBdef
  have hgz : g * z * g⁻¹ = u * z := by rw [hudef, commutatorElement_def]; group
  have hδz : δ * z * δ⁻¹ = w * z := by rw [hwdef, commutatorElement_def]; group
  have hk : g * δ = δ * g * k := by rw [hkdef]; group
  have hkz : k * z * k⁻¹ = ⁅k, z⁆ * z := by rw [commutatorElement_def]; group
  have e1 : g * δ * z * (g * δ)⁻¹ = A * (u * z) := by
    calc g * δ * z * (g * δ)⁻¹ = g * (δ * z * δ⁻¹) * g⁻¹ := by group
      _ = g * (w * z) * g⁻¹ := by rw [hδz]
      _ = (g * w * g⁻¹) * (g * z * g⁻¹) := by group
      _ = A * (u * z) := by rw [hgz]
  have e2 : g * δ * z * (g * δ)⁻¹ = x * (B * (w * z)) := by
    calc g * δ * z * (g * δ)⁻¹ = (δ * g) * (k * z * k⁻¹) * (δ * g)⁻¹ := by rw [hk]; group
      _ = (δ * g) * (⁅k, z⁆ * z) * (δ * g)⁻¹ := by rw [hkz]
      _ = x * ((δ * g) * z * (δ * g)⁻¹) := by rw [hxdef]; group
      _ = x * (δ * (g * z * g⁻¹) * δ⁻¹) := by congr 1; group
      _ = x * (δ * (u * z) * δ⁻¹) := by rw [hgz]
      _ = x * ((δ * u * δ⁻¹) * (δ * z * δ⁻¹)) := by congr 1; group
      _ = x * (B * (w * z)) := by rw [hδz]
  have hrel : A * u = x * B * w := by
    have h := e1.symm.trans e2
    have h' : (A * u) * z = (x * B * w) * z := by simpa only [mul_assoc] using h
    exact mul_right_cancel h'
  have hwu : w * u⁻¹ = u⁻¹ * w := hYc w hw u⁻¹ (Y.inv_mem hu)
  have e : A = x * B * w * u⁻¹ := by
    have := congrArg (fun y => y * u⁻¹) hrel
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
  calc ⁅g, w⁆ = A * w⁻¹ := by rw [commutatorElement_def]
    _ = x * B * w * u⁻¹ * w⁻¹ := by rw [e]
    _ = x * B * (w * u⁻¹) * w⁻¹ := by group
    _ = x * B * (u⁻¹ * w) * w⁻¹ := by rw [hwu]
    _ = x * (B * u⁻¹) := by group
    _ = x * ⁅δ, u⁆ := by rw [commutatorElement_def]

theorem commutator_g_conj_eq {Y V : Subgroup G} (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a ^ 2 = 1)
    {g : G} (hg3 : g ^ 3 = 1) (hgY : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hgV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) {y : G} (hy : y ∈ Y) (ha : ⁅g, y⁆ ∈ V) :
    ⁅g, g * ⁅g, y⁆ * g⁻¹⁆ = ⁅g, y⁆ := by
  set y1 : G := g * y * g⁻¹ with hy1def
  set y2 : G := g * y1 * g⁻¹ with hy2def
  have hy1 : y1 ∈ Y := hgY y hy
  have hy2 : y2 ∈ Y := hgY y1 hy1
  have h3 : g * y2 * g⁻¹ = y := by
    have hg3' : g * g * g = 1 := by rw [← hg3, pow_succ, pow_two]
    have e : g * y2 * g⁻¹ = (g * g * g) * y * (g * g * g)⁻¹ := by
      rw [hy2def, hy1def]; group
    rw [e, hg3']; simp
  set a : G := ⁅g, y⁆ with hadef
  have haV : a ∈ V := ha
  have hb : g * a * g⁻¹ = y2 * y1⁻¹ := by
    rw [hadef, commutatorElement_def, hy2def, hy1def]; group
  have hbV : g * a * g⁻¹ ∈ V := hgV a haV
  have hc : g * (g * a * g⁻¹) * g⁻¹ = y * y2⁻¹ := by
    rw [hb]
    calc g * (y2 * y1⁻¹) * g⁻¹ = (g * y2 * g⁻¹) * (g * y1 * g⁻¹)⁻¹ := by group
      _ = y * y2⁻¹ := by rw [h3, ← hy2def]
  have hcV : g * (g * a * g⁻¹) * g⁻¹ ∈ V := hgV _ hbV
  have habc : a * (g * a * g⁻¹) * (g * (g * a * g⁻¹) * g⁻¹) = 1 := by
    let _ : CommGroup ↥Y := { (inferInstance : Group ↥Y) with
      mul_comm := fun a b => Subtype.ext (hYc a a.2 b b.2) }
    have hay : a = y1 * y⁻¹ := by rw [hadef, commutatorElement_def, hy1def]
    have key : ((⟨y1, hy1⟩ : ↥Y) * ⟨y, hy⟩⁻¹) * (⟨y2, hy2⟩ * ⟨y1, hy1⟩⁻¹) *
        (⟨y, hy⟩ * ⟨y2, hy2⟩⁻¹) = 1 := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    have key' := congrArg Subtype.val key
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at key'
    rw [hc, hb, hay]
    exact key'
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 a haV)
  have hb1 : (g * a * g⁻¹)⁻¹ = g * a * g⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 _ hbV)
  have hc' : g * (g * a * g⁻¹) * g⁻¹ = (a * (g * a * g⁻¹))⁻¹ :=
    eq_inv_of_mul_eq_one_right habc
  rw [commutatorElement_def, hc', mul_inv_rev, ha1, hb1]
  calc (g * a * g⁻¹) * a * (g * a * g⁻¹) = a * ((g * a * g⁻¹) * (g * a * g⁻¹)) := by
        rw [← mul_assoc, hVc _ hbV a haV, mul_assoc, mul_assoc]
    _ = a := by rw [← pow_two, hV2 _ hbV, mul_one]

theorem eq_one_of_conj_eq_mul {g w κ : G} (hgw : g * w * g⁻¹ = κ * w)
    (hgκ : g * κ * g⁻¹ = κ) (hκ2 : κ ^ 2 = 1) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1) :
    κ = 1 := by
  have key : ∀ n : ℕ, g ^ n * w * (g ^ n)⁻¹ = κ ^ n * w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : g ^ (n + 1) * w * (g ^ (n + 1))⁻¹ = g * (g ^ n * w * (g ^ n)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      rw [this, ih]
      calc g * (κ ^ n * w) * g⁻¹ = (g * κ * g⁻¹) ^ n * (g * w * g⁻¹) := by
            rw [conj_pow]
            simp only [mul_assoc, inv_mul_cancel_left]
        _ = κ ^ (n + 1) * w := by rw [hgκ, hgw, pow_succ, mul_assoc]
  have hκm : κ ^ m = 1 := by
    have h := key m
    rw [hgm] at h
    simp only [inv_one, one_mul, mul_one] at h
    exact mul_eq_right.1 h.symm
  obtain ⟨j, rfl⟩ := hm
  calc κ = κ ^ (2 * j) * κ := by rw [pow_mul, hκ2, one_pow, one_mul]
    _ = κ ^ (2 * j + 1) := by rw [pow_succ]
    _ = 1 := hκm

theorem commutator_mem_sup {Z V : Subgroup G} (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hZV : ∀ z ∈ Z, ∀ v ∈ V, z * v = v * z) {g : G} (hgZ : ∀ z ∈ Z, ⁅g, z⁆ ∈ V)
    (hgV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) : ∀ y ∈ Z ⊔ V, ⁅g, y⁆ ∈ V := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  have key : ∀ y (hy : y ∈ Subgroup.closure ((Z : Set G) ∪ (V : Set G))),
      (∀ v ∈ V, y * v = v * y) ∧ ⁅g, y⁆ ∈ V := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hyZ | hyV
      · exact ⟨hZV y hyZ, hgZ y hyZ⟩
      · refine ⟨fun v hv => hVc y hyV v hv, ?_⟩
        rw [commutatorElement_def]
        exact V.mul_mem (hgV y hyV) (V.inv_mem hyV)
    | one => exact ⟨fun v _ => by simp, by simp⟩
    | mul y y' hy hy' ihy ihy' =>
      obtain ⟨hc, hq⟩ := ihy
      obtain ⟨hc', hq'⟩ := ihy'
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [mul_assoc, hc' v hv, ← mul_assoc, hc v hv, mul_assoc]
      · have e : ⁅g, y * y'⁆ = ⁅g, y⁆ * (y * ⁅g, y'⁆ * y⁻¹) := by
          simp only [commutatorElement_def]; group
        have e2 : y * ⁅g, y'⁆ * y⁻¹ = ⁅g, y'⁆ := by
          rw [mul_inv_eq_iff_eq_mul]; exact hc _ hq'
        rw [e, e2]; exact V.mul_mem hq hq'
    | inv y hy ihy =>
      obtain ⟨hc, hq⟩ := ihy
      refine ⟨fun v hv => ?_, ?_⟩
      · have := hc v hv
        calc y⁻¹ * v = y⁻¹ * (v * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * v) * y⁻¹ := by rw [this]
          _ = v * y⁻¹ := by group
      · have e : ⁅g, y⁻¹⁆ = (y⁻¹ * ⁅g, y⁆ * y)⁻¹ := by
          simp only [commutatorElement_def]; group
        have e2 : y⁻¹ * ⁅g, y⁆ * y = ⁅g, y⁆ := by
          have h1 := hc _ hq
          calc y⁻¹ * ⁅g, y⁆ * y = y⁻¹ * (⁅g, y⁆ * y) := mul_assoc _ _ _
            _ = y⁻¹ * (y * ⁅g, y⁆) := by rw [h1]
            _ = ⁅g, y⁆ := by group
        rw [e, e2]; exact V.inv_mem hq
  exact (key y hy).2

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
