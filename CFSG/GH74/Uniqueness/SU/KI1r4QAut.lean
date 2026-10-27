module

public import CFSG.GH74.Uniqueness.SU.SU5Models
public import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public meta import CFSG.GH74.Uniqueness.SU.SU5F4
public meta import CFSG.GH74.Uniqueness.SU.SU5Models
public meta import CFSG.GH74.Uniqueness.SU.KI1r4QAbs
public import CFSG.GH74.Uniqueness.SU.KI1r4QAutInputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4QAutInputs
public import Certificates.Certificate5141

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.Q64

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.GH74.GLS.Bg.TwoGroups

theorem prod_wordOf : ∀ g : L34Syl, ((wordOf g).map gen).prod = g := by decide +kernel

theorem wordOf_one : wordOf 1 = [] := by decide

theorem wordOf_gen : ∀ i, wordOf (gen i) = [i] := by decide

theorem mem_allP : ∀ g : L34Syl, g ∈ allP := by decide +kernel

theorem nodup_allP : allP.Nodup := by decide +kernel

theorem mem_candList (α : MulAut L34Syl) :
    (fun i => α (gen i)) ∈ candList := by
  have hsq : ∀ i, α (gen i) * α (gen i) = 1 := by
    intro i
    have h : gen i * gen i = 1 := by revert i; decide
    rw [← map_mul, h, map_one]
  have hc01 : α (gen 0) * α (gen 1) = α (gen 1) * α (gen 0) := by
    have h : gen 0 * gen 1 = gen 1 * gen 0 := by decide
    rw [← map_mul, ← map_mul, h]
  have hc23 : α (gen 2) * α (gen 3) = α (gen 3) * α (gen 2) := by
    have h : gen 2 * gen 3 = gen 3 * gen 2 := by decide
    rw [← map_mul, ← map_mul, h]
  have hmem : ∀ i, α (gen i) ∈ involList := fun i => by
    unfold involList
    rw [List.mem_filter]
    exact ⟨mem_allP _, by simpa using hsq i⟩
  have hfun : (fun i => α (gen i)) = ![α (gen 0), α (gen 1), α (gen 2), α (gen 3)] := by
    funext i; fin_cases i <;> rfl
  rw [hfun]
  unfold candList
  rw [List.mem_flatMap]
  refine ⟨α (gen 0), hmem 0, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨α (gen 1), ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨hmem 1, by simpa using hc01⟩
  rw [List.mem_flatMap]
  refine ⟨α (gen 2), hmem 2, ?_⟩
  rw [List.mem_map]
  refine ⟨α (gen 3), ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hmem 3, by simpa using hc23⟩

theorem key_check : ∀ t ∈ candList,
    (∀ i, evalT wordOf t (evalT wordOf t (gen i)) = gen i) →
    IsAutT allP gen wordOf t →
    (allP.filter (fun g => evalT wordOf t g = g)).length = 8 →
    (allP.filter (fun g => evalT wordOf t g = g ∧ g * g = 1)).length = 2 →
    ∃ p ∈ pairList, IsAutT allP gen wordOf (mkS t p) ∧
      ∀ i, evalT wordOf (mkS t p) (phiFun (gen i)) = evalT wordOf t (mkS t p i) :=
  Certificates.certificate5141

theorem exists_conj_phi (α : MulAut L34Syl) (hα : α * α = 1)
    (hfix : Nat.card {g // α g = g} = 8) (hfix2 : Nat.card {g // α g = g ∧ g * g = 1} = 2) :
    ∃ β : MulAut L34Syl, β * phi = α * β :=
  exists_conj_of_check gen wordOf prod_wordOf wordOf_one wordOf_gen allP mem_allP nodup_allP phi
    candList (fun α _ _ _ => mem_candList α)
    (fun t ht h0 h1 h2 h3 => by
      obtain ⟨p, -, hp1, hp2⟩ := key_check t ht h0 h1 h2 h3
      exact ⟨mkS t p, hp1, hp2⟩) α hα hfix hfix2

section Extension

variable {H : Type*} [Group H]

@[expose] def conjAut (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : MulAut ↥R where
  toFun r := ⟨x * r * x⁻¹, hN r r.2⟩
  invFun r := ⟨x * r * x⁻¹, hN r r.2⟩
  left_inv r := by
    apply Subtype.ext
    show x * (x * (r : H) * x⁻¹) * x⁻¹ = r
    calc x * (x * (r : H) * x⁻¹) * x⁻¹ = (x * x) * (r : H) * (x * x)⁻¹ := by group
      _ = r := by rw [hx2]; group
  right_inv r := by
    apply Subtype.ext
    show x * (x * (r : H) * x⁻¹) * x⁻¹ = r
    calc x * (x * (r : H) * x⁻¹) * x⁻¹ = (x * x) * (r : H) * (x * x)⁻¹ := by group
      _ = r := by rw [hx2]; group
  map_mul' a b := by
    apply Subtype.ext
    show x * ((a : H) * b) * x⁻¹ = x * (a : H) * x⁻¹ * (x * (b : H) * x⁻¹)
    group

variable {N : Type*} [Group N]

@[expose] def alphaOf (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (e : ↥R ≃* N) : MulAut N :=
  (e.symm.trans (conjAut R x hx2 hN)).trans e

theorem alphaOf_mul_self (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (e : ↥R ≃* N) :
    alphaOf R x hx2 hN e * alphaOf R x hx2 hN e = 1 := by
  ext g
  show e (conjAut R x hx2 hN (e.symm (e (conjAut R x hx2 hN (e.symm g))))) = g
  rw [e.symm_apply_apply]
  have : conjAut R x hx2 hN (conjAut R x hx2 hN (e.symm g)) = e.symm g := by
    apply Subtype.ext
    show x * (x * ((e.symm g : ↥R) : H) * x⁻¹) * x⁻¹ = ((e.symm g : ↥R) : H)
    calc x * (x * ((e.symm g : ↥R) : H) * x⁻¹) * x⁻¹
        = (x * x) * ((e.symm g : ↥R) : H) * (x * x)⁻¹ := by group
      _ = ((e.symm g : ↥R) : H) := by rw [hx2]; group
  rw [this]
  simp

@[expose] def fixEquiv (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (e : ↥R ≃* N) :
    {g // alphaOf R x hx2 hN e g = g} ≃ ↥(centralizer ({x} : Set H) ⊓ R) where
  toFun g := ⟨((e.symm g.1 : ↥R) : H), by
    refine Subgroup.mem_inf.mpr ⟨?_, (e.symm g.1).2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : alphaOf R x hx2 hN e g.1 = g.1 := g.2
    have h2 : conjAut R x hx2 hN (e.symm g.1) = e.symm g.1 := by
      have := congrArg e.symm h1
      simpa [alphaOf] using this
    have h3 : x * ((e.symm g.1 : ↥R) : H) * x⁻¹ = ((e.symm g.1 : ↥R) : H) :=
      congrArg Subtype.val h2
    calc ((e.symm g.1 : ↥R) : H) * x = x * ((e.symm g.1 : ↥R) : H) * x⁻¹ * x := by rw [h3]
      _ = x * ((e.symm g.1 : ↥R) : H) := by group⟩
  invFun c := ⟨e ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩, by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).1
    show alphaOf R x hx2 hN e (e ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩) = e ⟨c.1, _⟩
    simp only [alphaOf, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    show x * (c.1 : H) * x⁻¹ = c.1
    calc x * (c.1 : H) * x⁻¹ = (c.1 : H) * x * x⁻¹ := by rw [← h1]
      _ = c.1 := by group⟩
  left_inv g := by simp
  right_inv c := by simp

theorem card_sq_one_quaternion : Nat.card {q : QuaternionGroup 2 // q * q = 1} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_sq_one_of_mulEquiv {X : Type*} [Group X] (e : X ≃* QuaternionGroup 2) :
    Nat.card {c : X // c * c = 1} = 2 := by
  rw [← card_sq_one_quaternion]
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun c => ?_)
  constructor
  · intro h
    show e c * e c = 1
    rw [← map_mul, h, map_one]
  · intro h
    have h' : e c * e c = 1 := h
    apply e.injective
    rw [map_mul, h', map_one]

theorem card_le_two_of_sq_one {X : Type*} [Group X] [Finite X] (e : X ≃* QuaternionGroup 2)
    (W : Subgroup X) (hW : ∀ w ∈ W, w * w = 1) : Nat.card W ≤ 2 := by
  rw [← card_sq_one_of_mulEquiv e]
  exact Nat.card_le_card_of_injective (fun w : W => (⟨(w : X), hW w w.2⟩ : {c : X // c * c = 1}))
    (fun a b h => Subtype.ext (congrArg (fun c : {c : X // c * c = 1} => (c : X)) h))

theorem card_fix_sq_alphaOf (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (e : ↥R ≃* N) :
    Nat.card {g // alphaOf R x hx2 hN e g = g ∧ g * g = 1} =
      Nat.card {c : ↥(centralizer ({x} : Set H) ⊓ R) // c * c = 1} := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun g : N => alphaOf R x hx2 hN e g = g) (fun g : N => g * g = 1)).symm]
  refine Nat.card_congr ((fixEquiv R x hx2 hN e).subtypeEquiv fun g => ?_)
  constructor
  · intro h
    apply Subtype.ext
    show ((e.symm g.1 : ↥R) : H) * ((e.symm g.1 : ↥R) : H) = 1
    have : e.symm g.1 * e.symm g.1 = 1 := by rw [← map_mul, h, map_one]
    exact congrArg Subtype.val this
  · intro h
    have h' : ((e.symm g.1 : ↥R) : H) * ((e.symm g.1 : ↥R) : H) = 1 := congrArg Subtype.val h
    have h'' : e.symm g.1 * e.symm g.1 = 1 := Subtype.ext h'
    have := congrArg e h''
    simpa using this

theorem exists_beta_intertwine (R : Subgroup H) (x : H) (hx2 : x * x = 1)
    (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R) (e : ↥R ≃* N) (φ : MulAut N)
    (hconj : ∀ α : MulAut N, α * α = 1 → Nat.card {g // α g = g} = 8 →
      Nat.card {g // α g = g ∧ g * g = 1} = 2 → ∃ β : MulAut N, β * φ = α * β)
    (hQ8 : Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) :
    ∃ β : MulAut N, ∀ n : N,
      e.symm (β (φ n)) = conjAut R x hx2 hN (e.symm (β n)) := by
  obtain ⟨e8⟩ := hQ8
  obtain ⟨β, hβ⟩ := hconj (alphaOf R x hx2 hN e) (alphaOf_mul_self R x hx2 hN e)
    (by
      rw [Nat.card_congr (fixEquiv R x hx2 hN e), Nat.card_congr e8.toEquiv]
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card])
    (by rw [card_fix_sq_alphaOf R x hx2 hN e]; exact card_sq_one_of_mulEquiv e8)
  refine ⟨β, fun n => ?_⟩
  have h1 : β (φ n) = alphaOf R x hx2 hN e (β n) := by
    have := congrArg (fun m : MulAut N => m n) hβ
    simpa using this
  rw [h1]
  simp [alphaOf]

end Extension

section Types

variable {H : Type*} [Group H]

theorem isJ2Type_of_extension
    (T R : Subgroup H) (x : H) (hRT : R ≤ T) (hxT : x ∈ T)
    (hx2 : x * x = 1) (hxR : x ∉ R) (hN : ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hgen : T = R ⊔ zpowers x) (hL : IsL34Type ↥R)
    (hQ8 : Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) : IsJ2Type ↥T := by
  obtain ⟨e⟩ := (isL34Type_iff.mp hL)
  obtain ⟨β, hβ⟩ := exists_beta_intertwine R x hx2 hN e phi
    (fun α hα h8 h2 => exists_conj_phi α hα h8 h2) hQ8
  have hψ1 : psi (Multiplicative.ofAdd 1) = phi := by
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    simp [psi, hne]
  have hcomp : ∀ n : L34Syl, ((e.symm (β (psi (Multiplicative.ofAdd 1) n)) : ↥R) : H) =
      x * ((e.symm (β n) : ↥R) : H) * x⁻¹ := by
    intro n
    rw [hψ1, hβ n]
    rfl
  exact nonempty_mulEquiv_semidirect T R x hRT hxT hx2 hxR hgen e β psi hcomp

end Types

end CFSG.GH74.Uniqueness.SU.K.R4.Q64
