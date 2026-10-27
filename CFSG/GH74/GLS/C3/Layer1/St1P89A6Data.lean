module

public import CFSG.GH74.KGroups.A6Inputs

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open CFSG.GH74.KGroups.A6 CFSG.Sporadic.Schreier

@[expose] abbrev G10 : Type := Equiv.Perm (Fin 10)

@[expose] def cyc (l : List (Fin 10)) : G10 := List.formPerm l

@[expose] def LAll {α : Type} (l : List α) (p : α → Prop) : Prop := ∀ x ∈ l, p x

@[expose] def LEx {α : Type} (l : List α) (p : α → Prop) : Prop := ∃ x ∈ l, p x

instance {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : Decidable (LAll l p) :=
  List.decidableBAll p l

instance {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] : Decidable (LEx l p) :=
  List.decidableBEx p l

@[expose] def Bl : List G10 := [
    1,
    cyc [2, 5] * cyc [6, 7] * cyc [8, 9],
    cyc [2, 8] * cyc [3, 4] * cyc [5, 9],
    cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7],
    cyc [0, 1] * cyc [3, 4] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 5] * cyc [3, 4] * cyc [8, 9],
    cyc [0, 1] * cyc [2, 8] * cyc [5, 9] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 9] * cyc [5, 8],
    cyc [0, 2] * cyc [1, 8] * cyc [3, 4] * cyc [5, 7] * cyc [6, 9],
    cyc [0, 2, 1, 8] * cyc [5, 6, 9, 7],
    cyc [0, 2, 6, 5, 1, 8, 7, 9],
    cyc [0, 2, 7, 9, 1, 8, 6, 5] * cyc [3, 4],
    cyc [0, 5, 6, 8, 1, 9, 7, 2] * cyc [3, 4],
    cyc [0, 5, 7, 2, 1, 9, 6, 8],
    cyc [0, 5] * cyc [1, 9] * cyc [2, 6] * cyc [3, 4] * cyc [7, 8],
    cyc [0, 5, 1, 9] * cyc [2, 7, 8, 6],
    cyc [0, 6] * cyc [1, 7] * cyc [3, 4] * cyc [5, 9],
    cyc [0, 6, 1, 7] * cyc [2, 5, 8, 9],
    cyc [0, 6] * cyc [1, 7] * cyc [2, 8],
    cyc [0, 6, 1, 7] * cyc [2, 9, 8, 5] * cyc [3, 4],
    cyc [0, 7] * cyc [1, 6] * cyc [5, 9],
    cyc [0, 7, 1, 6] * cyc [2, 5, 8, 9] * cyc [3, 4],
    cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4],
    cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5],
    cyc [0, 8, 1, 2] * cyc [5, 7, 9, 6],
    cyc [0, 8] * cyc [1, 2] * cyc [3, 4] * cyc [5, 6] * cyc [7, 9],
    cyc [0, 8, 7, 5, 1, 2, 6, 9] * cyc [3, 4],
    cyc [0, 8, 6, 9, 1, 2, 7, 5],
    cyc [0, 9, 7, 8, 1, 5, 6, 2],
    cyc [0, 9, 6, 2, 1, 5, 7, 8] * cyc [3, 4],
    cyc [0, 9, 1, 5] * cyc [2, 6, 8, 7],
    cyc [0, 9] * cyc [1, 5] * cyc [2, 7] * cyc [3, 4] * cyc [6, 8]]

@[expose] def Pl : List G10 := [
    1,
    cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 5] * cyc [3, 4] * cyc [8, 9],
    cyc [0, 1] * cyc [2, 8] * cyc [5, 9] * cyc [6, 7],
    cyc [0, 6] * cyc [1, 7] * cyc [3, 4] * cyc [5, 9],
    cyc [0, 6, 1, 7] * cyc [2, 5, 8, 9],
    cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4],
    cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5]]

@[expose] def P3 : List G10 := [
    cyc [0, 8, 2] * cyc [1, 5, 9] * cyc [3, 4, 7],
    cyc [0, 6, 3] * cyc [1, 7, 4] * cyc [2, 8, 5],
    cyc [0, 6, 9] * cyc [1, 5, 7] * cyc [2, 4, 8],
    cyc [0, 1, 8] * cyc [2, 6, 7] * cyc [3, 9, 4],
    cyc [0, 3, 4] * cyc [2, 7, 8] * cyc [5, 6, 9],
    cyc [1, 6, 7] * cyc [2, 5, 3] * cyc [4, 8, 9]]

@[expose] def Xl : List G10 := [
    cyc [0, 2] * cyc [1, 8] * cyc [3, 4] * cyc [5, 7] * cyc [6, 9],
    cyc [0, 5] * cyc [1, 9] * cyc [2, 6] * cyc [3, 4] * cyc [7, 8],
    cyc [0, 8] * cyc [1, 2] * cyc [3, 4] * cyc [5, 6] * cyc [7, 9],
    cyc [0, 9] * cyc [1, 5] * cyc [2, 7] * cyc [3, 4] * cyc [6, 8]]

@[expose] def E1 : List G10 := [
    1,
    cyc [2, 5] * cyc [6, 7] * cyc [8, 9],
    cyc [2, 8] * cyc [3, 4] * cyc [5, 9],
    cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7],
    cyc [0, 1] * cyc [3, 4] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 5] * cyc [3, 4] * cyc [8, 9],
    cyc [0, 1] * cyc [2, 8] * cyc [5, 9] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 9] * cyc [5, 8]]

@[expose] def E2 : List G10 := [
    1,
    cyc [2, 8] * cyc [3, 4] * cyc [5, 9],
    cyc [0, 1] * cyc [3, 4] * cyc [6, 7],
    cyc [0, 1] * cyc [2, 8] * cyc [5, 9] * cyc [6, 7],
    cyc [0, 6] * cyc [1, 7] * cyc [3, 4] * cyc [5, 9],
    cyc [0, 6] * cyc [1, 7] * cyc [2, 8],
    cyc [0, 7] * cyc [1, 6] * cyc [5, 9],
    cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4]]

@[expose] def Wt : List (G10 × ℕ × (G10 × G10 × G10 × G10 × G10)) := [
    (cyc [0, 2] * cyc [1, 8] * cyc [3, 4] * cyc [5, 7] * cyc [6, 9], 0, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7], cyc [0, 1] * cyc [3, 4] * cyc [6, 7], cyc [0, 4] * cyc [1, 3] * cyc [2, 5] * cyc [6, 7], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4])),
    (cyc [0, 2] * cyc [1, 8] * cyc [3, 4] * cyc [5, 7] * cyc [6, 9], 1, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4], cyc [2, 8] * cyc [3, 4] * cyc [5, 9], cyc [1, 7] * cyc [2, 8] * cyc [3, 9] * cyc [4, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7])),
    (cyc [0, 5] * cyc [1, 9] * cyc [2, 6] * cyc [3, 4] * cyc [7, 8], 0, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7], cyc [0, 1] * cyc [3, 4] * cyc [6, 7], cyc [0, 4] * cyc [1, 3] * cyc [2, 5] * cyc [6, 7], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4])),
    (cyc [0, 5] * cyc [1, 9] * cyc [2, 6] * cyc [3, 4] * cyc [7, 8], 1, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4], cyc [2, 8] * cyc [3, 4] * cyc [5, 9], cyc [1, 7] * cyc [2, 8] * cyc [3, 9] * cyc [4, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7])),
    (cyc [0, 8] * cyc [1, 2] * cyc [3, 4] * cyc [5, 6] * cyc [7, 9], 0, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7], cyc [0, 1] * cyc [3, 4] * cyc [6, 7], cyc [0, 4] * cyc [1, 3] * cyc [2, 5] * cyc [6, 7], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4])),
    (cyc [0, 8] * cyc [1, 2] * cyc [3, 4] * cyc [5, 6] * cyc [7, 9], 1, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4], cyc [2, 8] * cyc [3, 4] * cyc [5, 9], cyc [1, 7] * cyc [2, 8] * cyc [3, 9] * cyc [4, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7])),
    (cyc [0, 9] * cyc [1, 5] * cyc [2, 7] * cyc [3, 4] * cyc [6, 8], 0, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7], cyc [0, 1] * cyc [3, 4] * cyc [6, 7], cyc [0, 4] * cyc [1, 3] * cyc [2, 5] * cyc [6, 7], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4])),
    (cyc [0, 9] * cyc [1, 5] * cyc [2, 7] * cyc [3, 4] * cyc [6, 8], 1, (cyc [0, 7, 1, 6] * cyc [2, 9, 8, 5], cyc [0, 7] * cyc [1, 6] * cyc [2, 8] * cyc [3, 4], cyc [2, 8] * cyc [3, 4] * cyc [5, 9], cyc [1, 7] * cyc [2, 8] * cyc [3, 9] * cyc [4, 5], cyc [2, 9] * cyc [3, 4] * cyc [5, 8] * cyc [6, 7]))]


@[expose] def P89CondP (r s : G10) : Prop :=
  r ∈ Pl ∧ s ∈ Pl ∧ r ^ 4 = 1 ∧ s ^ 2 = 1 ∧ s * r * s⁻¹ = r⁻¹ ∧ r ^ 2 ≠ 1 ∧
  LAll Pl fun p => LEx (List.range 4) fun i => LEx (List.range 2) fun j => p = r ^ i * s ^ j

@[expose] def P89CondX (x r s : G10) : Prop :=
  x * r * x⁻¹ = r⁻¹ ∧ (x * s * x⁻¹ = r * s ∨ x * s * x⁻¹ = r ^ 3 * s)

@[expose] def P89CondF (x : G10) (E : List G10) (r s f : G10) : Prop :=
  f ∈ E ∧ f ^ 2 = 1 ∧ LAll Pl (fun p => f * p = p * f) ∧ f ≠ 1 ∧ f ≠ r ^ 2 ∧
  x * f * x⁻¹ = r ^ 2 * f ∧ s ∈ E ∧ r ^ 2 ∈ E

@[expose] def P89CondB (x r f : G10) : Prop :=
  LAll Bl (fun b => LEx Pl fun p => LEx (List.range 2) fun i => LEx (List.range 2) fun j =>
    b = p * f ^ i * x ^ j) ∧
  LAll Bl (fun b => LAll Pl (fun p => b * p = p * b) →
    LEx (List.range 2) fun i => LEx (List.range 2) fun j => b = r ^ (2 * i) * f ^ j) ∧
  LAll Bl (fun b => LAll Bl (fun b' => b * b' = b' * b) → b = 1 ∨ b = r ^ 2)

@[expose] def P89CondK (r s f k₁ k₂ : G10) : Prop :=
  QP.sift k₁ 0 = true ∧ QP.sift k₂ 0 = true ∧
  k₁ * r ^ 2 * k₁⁻¹ = s ∧ k₁ * s * k₁⁻¹ = r ^ 2 ∧ f * k₁ = k₁ * f ∧
  k₂ * r ^ 2 * k₂⁻¹ = r ^ 2 ∧ k₂ * s * k₂⁻¹ = r ^ 2 * s ∧ f * k₂ = k₂ * f

instance (r s : G10) : Decidable (P89CondP r s) := by unfold P89CondP; infer_instance

instance (x r s : G10) : Decidable (P89CondX x r s) := by unfold P89CondX; infer_instance

instance (x : G10) (E : List G10) (r s f : G10) : Decidable (P89CondF x E r s f) := by
  unfold P89CondF; infer_instance

instance (x r f : G10) : Decidable (P89CondB x r f) := by unfold P89CondB; infer_instance

instance (r s f k₁ k₂ : G10) : Decidable (P89CondK r s f k₁ k₂) := by
  unfold P89CondK; infer_instance

@[expose] def P89Cond (x : G10) (E : List G10) (r s f k₁ k₂ : G10) : Prop :=
  P89CondP r s ∧ P89CondX x r s ∧ P89CondF x E r s f ∧ P89CondB x r f ∧ P89CondK r s f k₁ k₂

instance (x : G10) (E : List G10) (r s f k₁ k₂ : G10) : Decidable (P89Cond x E r s f k₁ k₂) := by
  unfold P89Cond; infer_instance

@[expose] def P89F1 : Prop :=
  (Bl.Nodup ∧ Bl.length = 32 ∧ (1 : G10) ∈ Bl ∧ LAll Bl (fun a => LAll Bl fun b => a * b ∈ Bl) ∧
    LAll Bl (fun a => a⁻¹ ∈ Bl)) ∧ LAll Bl (fun b => QA.sift b 0 = true)

@[expose] def P89F2 : Prop :=
  Pl.Nodup ∧ Pl.length = 8 ∧ LAll Pl (fun p => p ∈ Bl) ∧
    LAll Bl (fun b => (b ∈ Pl ↔ QP.sift b 0 = true))

@[expose] def P89F3 : Prop :=
  LAll P3 (fun c => c ^ 3 = 1 ∧ c ≠ 1 ∧ QP.sift c 0 = true) ∧
  LAll Bl (fun x => x ^ 2 = 1 → x ∉ Pl → LAll P3 (fun c => x * c ≠ c * x) → x ∈ Xl)

@[expose] def P89Indep (a b c : G10) : Prop :=
  a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ c ^ 2 = 1 ∧ a * b = b * a ∧ a * c = c * a ∧ b * c = c * b ∧ a ≠ 1 ∧
    b ≠ 1 ∧ b ≠ a ∧ c ∉ [1, a, b, a * b]

instance (a b c : G10) : Decidable (P89Indep a b c) := by unfold P89Indep; infer_instance

@[expose] def P89Span (E : List G10) (a b c : G10) : Prop :=
  LAll E (fun y => y ∈ [1, a, b, c, a * b, a * c, b * c, a * b * c])

instance (E : List G10) (a b c : G10) : Decidable (P89Span E a b c) := by
  unfold P89Span; infer_instance

@[expose] def P89F4 : Prop :=
  LAll Bl fun a => LAll Bl fun b => LAll Bl fun c =>
    P89Indep a b c → (P89Span E1 a b c ∨ P89Span E2 a b c)

@[expose] def P89F5 : Prop :=
  LAll Xl fun x => LAll (List.range 2) fun i => LEx Wt fun w => w.1 = x ∧ w.2.1 = i ∧
    P89Cond x (if i = 0 then E1 else E2) w.2.2.1 w.2.2.2.1 w.2.2.2.2.1 w.2.2.2.2.2.1
      w.2.2.2.2.2.2

instance : Decidable P89F1 := by unfold P89F1; infer_instance

instance : Decidable P89F2 := by unfold P89F2; infer_instance

instance : Decidable P89F3 := by unfold P89F3; infer_instance

instance : Decidable P89F4 := by unfold P89F4; infer_instance

instance : Decidable P89F5 := by unfold P89F5; infer_instance

@[expose] def P89Facts : Prop := P89F1 ∧ P89F2 ∧ P89F3 ∧ P89F4 ∧ P89F5

instance : Decidable P89Facts := by unfold P89Facts; infer_instance

end CFSG.GH74.GLS.C3.Layer1.P89
