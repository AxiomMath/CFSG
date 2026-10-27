module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Fpf

variable {P : Type*} [Group P]

theorem fpf_inverts_abelian {V : Subgroup P} [V.Normal] [Finite V] {t : P} (ht : t * t = 1)
    (hfpf : ∀ v ∈ V, t * v * t⁻¹ = v → v = 1) :
    (∀ v ∈ V, t * v * t⁻¹ = v⁻¹) ∧ (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) := by
  have hmem : ∀ v ∈ V, v⁻¹ * (t * v * t⁻¹) ∈ V := fun v hv =>
    V.mul_mem (V.inv_mem hv) ((inferInstance : V.Normal).conj_mem v hv t)
  let f : V → V := fun v => ⟨v⁻¹ * (t * v * t⁻¹), hmem v v.2⟩
  have hinj : Function.Injective f := by
    intro v w hvw
    have h1 : (v : P)⁻¹ * (t * v * t⁻¹) = (w : P)⁻¹ * (t * w * t⁻¹) := congrArg Subtype.val hvw
    have h2 : t * ((w : P) * (v : P)⁻¹) * t⁻¹ = (w : P) * (v : P)⁻¹ := by
      calc t * ((w : P) * (v : P)⁻¹) * t⁻¹ = (t * w * t⁻¹) * (t * v * t⁻¹)⁻¹ := by group
        _ = (w * ((w : P)⁻¹ * (t * w * t⁻¹))) * (t * v * t⁻¹)⁻¹ := by group
        _ = (w * ((v : P)⁻¹ * (t * v * t⁻¹))) * (t * v * t⁻¹)⁻¹ := by rw [← h1]
        _ = (w : P) * (v : P)⁻¹ := by group
    have h3 := hfpf _ (V.mul_mem w.2 (V.inv_mem v.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h3).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  have hinv : ∀ v ∈ V, t * v * t⁻¹ = v⁻¹ := by
    intro x hx
    obtain ⟨v, hv⟩ := hsurj ⟨x, hx⟩
    have hx' : x = (v : P)⁻¹ * (t * v * t⁻¹) := (congrArg Subtype.val hv).symm
    rw [hx']
    calc t * ((v : P)⁻¹ * (t * v * t⁻¹)) * t⁻¹
        = (t * (v : P)⁻¹ * t⁻¹) * ((t * t) * v * (t * t)⁻¹) := by group
      _ = ((v : P)⁻¹ * (t * v * t⁻¹))⁻¹ := by rw [ht]; group
  refine ⟨hinv, fun v hv w hw => ?_⟩
  have h1 := hinv (v * w) (V.mul_mem hv hw)
  have h2 : t * (v * w) * t⁻¹ = (t * v * t⁻¹) * (t * w * t⁻¹) := by group
  rw [h2, hinv v hv, hinv w hw, mul_inv_rev] at h1
  calc v * w = (w⁻¹ * v⁻¹)⁻¹ := by group
    _ = (v⁻¹ * w⁻¹)⁻¹ := by rw [← h1]
    _ = w * v := by group

theorem le_of_comm_mem {Q C : Subgroup P} (hQ : ⁅Q, Q⁆ = Q)
    (h : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ C) : Q ≤ C := by
  rw [← hQ, Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact h a ha b hb

theorem centralizes_of_perfect {Q D : Subgroup P} (hQ : ⁅Q, Q⁆ = Q) {g : P}
    (hc : ∀ a ∈ Q, a * g * a⁻¹ * g⁻¹ ∈ D) (hDQ : ∀ d ∈ D, ∀ a ∈ Q, d * a = a * d)
    (hDD : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) :
    ∀ a ∈ Q, a * g = g * a := by
  have key : ∀ a ∈ Q, a * g * a⁻¹ = (a * g * a⁻¹ * g⁻¹) * g ∧
      a⁻¹ * g * a = (a * g * a⁻¹ * g⁻¹)⁻¹ * g := by
    intro a ha
    refine ⟨by group, ?_⟩
    set c := a * g * a⁻¹ * g⁻¹ with hcdef
    have hcD : c ∈ D := hc a ha
    have hcom : a⁻¹ * c * a = c := by
      have := hDQ c hcD a ha
      calc a⁻¹ * c * a = a⁻¹ * (c * a) := by group
        _ = a⁻¹ * (a * c) := by rw [this]
        _ = c := by group
    have h1 : g = c * (a⁻¹ * g * a) := by
      calc g = a⁻¹ * (a * g * a⁻¹) * a := by group
        _ = a⁻¹ * (c * g) * a := by rw [hcdef]; group
        _ = (a⁻¹ * c * a) * (a⁻¹ * g * a) := by group
        _ = c * (a⁻¹ * g * a) := by rw [hcom]
    calc a⁻¹ * g * a = c⁻¹ * (c * (a⁻¹ * g * a)) := by group
      _ = c⁻¹ * g := by rw [← h1]
  have hC : Q ≤ Subgroup.centralizer ({g} : Set P) := by
    refine le_of_comm_mem hQ (fun a₁ h₁ a₂ h₂ => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨e1, f1⟩ := key a₁ h₁
    obtain ⟨e2, f2⟩ := key a₂ h₂
    set c₁ := a₁ * g * a₁⁻¹ * g⁻¹ with hc₁
    set c₂ := a₂ * g * a₂⁻¹ * g⁻¹ with hc₂
    have hc₁D : c₁ ∈ D := hc a₁ h₁
    have hc₂D : c₂ ∈ D := hc a₂ h₂
    have hc₁i : c₁⁻¹ ∈ D := D.inv_mem hc₁D
    have hc₂i : c₂⁻¹ ∈ D := D.inv_mem hc₂D
    have hq : ∀ d ∈ D, ∀ a ∈ Q, a * d * a⁻¹ = d := by
      intro d hd a ha
      rw [← hDQ d hd a ha]; group
    have hqi : ∀ d ∈ D, ∀ a ∈ Q, a⁻¹ * d * a = d := by
      intro d hd a ha
      have := hDQ d hd a ha
      calc a⁻¹ * d * a = a⁻¹ * (d * a) := by group
        _ = a⁻¹ * (a * d) := by rw [this]
        _ = d := by group
    have step1 : a₂⁻¹ * g * a₂ = c₂⁻¹ * g := f2
    have step2 : a₁⁻¹ * (c₂⁻¹ * g) * a₁ = c₂⁻¹ * (c₁⁻¹ * g) := by
      calc a₁⁻¹ * (c₂⁻¹ * g) * a₁ = (a₁⁻¹ * c₂⁻¹ * a₁) * (a₁⁻¹ * g * a₁) := by group
        _ = c₂⁻¹ * (c₁⁻¹ * g) := by rw [hqi _ hc₂i a₁ h₁, f1]
    have step3 : a₂ * (c₂⁻¹ * (c₁⁻¹ * g)) * a₂⁻¹ = c₂⁻¹ * c₁⁻¹ * (c₂ * g) := by
      calc a₂ * (c₂⁻¹ * (c₁⁻¹ * g)) * a₂⁻¹ = (a₂ * (c₂⁻¹ * c₁⁻¹) * a₂⁻¹) * (a₂ * g * a₂⁻¹) := by
            group
        _ = c₂⁻¹ * c₁⁻¹ * (c₂ * g) := by
            rw [hq _ (D.mul_mem hc₂i hc₁i) a₂ h₂, e2]
    have step4 : a₁ * (c₂⁻¹ * c₁⁻¹ * (c₂ * g)) * a₁⁻¹ = g := by
      calc a₁ * (c₂⁻¹ * c₁⁻¹ * (c₂ * g)) * a₁⁻¹
          = (a₁ * (c₂⁻¹ * c₁⁻¹ * c₂) * a₁⁻¹) * (a₁ * g * a₁⁻¹) := by group
        _ = c₂⁻¹ * c₁⁻¹ * c₂ * (c₁ * g) := by
            rw [hq _ (D.mul_mem (D.mul_mem hc₂i hc₁i) hc₂D) a₁ h₁, e1]
        _ = (c₂⁻¹ * (c₁⁻¹ * c₂ * c₁)) * g := by group
        _ = (c₂⁻¹ * (c₂ * c₁⁻¹ * c₁)) * g := by rw [hDD c₁⁻¹ hc₁i c₂ hc₂D]
        _ = g := by group
    have hk : (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * g * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹)⁻¹ = g := by
      calc (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * g * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹)⁻¹
          = a₁ * (a₂ * (a₁⁻¹ * (a₂⁻¹ * g * a₂) * a₁) * a₂⁻¹) * a₁⁻¹ := by group
        _ = g := by rw [step1, step2, step3, step4]
    calc (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * g
        = ((a₁ * a₂ * a₁⁻¹ * a₂⁻¹) * g * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹)⁻¹) *
            (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) := by
          group
      _ = g * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) := by rw [hk]
  exact fun a ha => Subgroup.mem_centralizer_singleton_iff.1 (hC ha)

end Fpf

end CFSG.OddStandard.AltStdSec
