module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Perm

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup AltStdCycTwo

theorem le89 : 8 ≤ 9 := by norm_num

theorem le811 : 8 ≤ 11 := by norm_num

@[expose] def rBar9 : Subgroup (Perm (Fin 9)) :=
  closure {swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7),
    swap 0 5 * swap 1 4 * (swap 2 6 * swap 3 7)}

@[expose] def rBarS9 : Subgroup (Perm (Fin 9)) :=
  closure {swap 0 1, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7)}

@[expose] def rBar11 : Subgroup (Perm (Fin 11)) :=
  closure {swap 0 1 * swap 8 9, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7)}

structure FusR (n : ℕ) (hn : 8 ≤ n) (Nbar Rbar : Subgroup (Perm (Fin n))) (k : ℕ)
    (cc : Subgroup (Perm (Fin n)) → Prop) : Prop where
  le : Rbar ≤ Nbar
  card : Nat.card Rbar = 2 ^ k
  tr_mem : ∀ v : Fin 8, tr hn v ∈ Rbar
  center : ∀ r ∈ Rbar, (∀ s ∈ Rbar, r * s = s * r) → r = 1 ∨ r = tr hn 1
  comm : ∃ a ∈ Rbar, ∃ b ∈ Rbar, a * b * a⁻¹ * b⁻¹ = tr hn 1
  fx : ∀ X : Subgroup (Perm (Fin n)), X ≤ Rbar → tr hn 1 ∈ X → Nat.card X = 8 →
    (∀ x ∈ X, x * x = 1) →
      (∃ t ∈ Nbar, t * t = 1 ∧ t ∉ X ∧ ∀ x ∈ X, t * x = x * t) ∨
      (∃ g ∈ Nbar, (∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧ g * tr hn 1 ≠ tr hn 1 * g) ∨ cc X

@[expose] def bBar : Subgroup (Perm (Fin 9)) :=
  closure {swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7}

@[expose] def mBar : Perm (Fin 9) := swap 1 2 * swap 5 6

@[expose] def cc9 (X : Subgroup (Perm (Fin 9))) : Prop :=
  ∀ y ∈ X, y ∈ bBar → y ≠ 1 → y ≠ tr le89 1 → y.support.card = 4

structure FusJ : Prop where
  bBar_le : bBar ≤ rBar9
  cent_iff : ∀ r ∈ rBar9,
    (∀ a ∈ rBar9, ∀ b ∈ rBar9, r * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * r) ↔ r ∈ bBar
  mBar_mem : mBar ∈ alternatingGroup (Fin 9)
  mBar_conj : mBar * tr le89 1 * mBar⁻¹ = tr le89 2
  mBar_norm : ∀ b ∈ bBar, mBar * b * mBar⁻¹ ∈ bBar
  tr_two_mem : tr le89 2 ∈ bBar

section Group

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def bSub (θ : L ≃* alternatingGroup (Fin 9)) : Subgroup G :=
  ((bBar.comap (alternatingGroup (Fin 9)).subtype).map θ.symm.toMonoidHom).map L.subtype

@[expose] def vSub (θ : L ≃* alternatingGroup (Fin 9)) (z : G) : Subgroup G := bSub θ ⊔ zpowers z

end Group

@[expose] def FusP42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (θ : L ≃* alternatingGroup (Fin 9))
    (z : G), Config G L Q 9 θ z → centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) →
    ∀ x ∈ normalizer (vSub θ z : Set G), x * z * x⁻¹ = z * w θ le89 →
    ∀ g ∈ normalizer (vSub θ z : Set G), ∀ l : L,
      ((θ l : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ bBar →
      ((θ l : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card = 4 →
        g * w θ le89 * g⁻¹ ≠ l

end CFSG.OddStandard.AltStdSmall4.Fus
