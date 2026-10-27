module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Perm

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus

open Equiv Subgroup AltStdCycTwo

theorem le88 : 8 ≤ 8 := le_rfl

theorem le810 : 8 ≤ 10 := by norm_num

@[expose] def rBar8 : Subgroup (Perm (Fin 8)) :=
  closure {swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7),
    swap 0 5 * swap 1 4 * (swap 2 6 * swap 3 7)}

@[expose] def rBarS8 : Subgroup (Perm (Fin 8)) :=
  closure {swap 0 1, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7)}

@[expose] def rBar10 : Subgroup (Perm (Fin 10)) :=
  closure {swap 0 1 * swap 8 9, swap 0 2 * swap 1 3, swap 0 4 * swap 1 5 * (swap 2 6 * swap 3 7)}

@[expose] def bBar8 : Subgroup (Perm (Fin 8)) :=
  closure {swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7}

@[expose] def mBar8 : Perm (Fin 8) := swap 1 2 * swap 5 6

@[expose] def cc8 (X : Subgroup (Perm (Fin 8))) : Prop :=
  ∀ y ∈ X, y ∈ bBar8 → y ≠ 1 → y ≠ tr le88 1 → y.support.card = 4

structure FusJ8 : Prop where
  bBar_le : bBar8 ≤ rBar8
  cent_iff : ∀ r ∈ rBar8,
    (∀ a ∈ rBar8, ∀ b ∈ rBar8, r * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * r) ↔ r ∈ bBar8
  mBar_mem : mBar8 ∈ alternatingGroup (Fin 8)
  mBar_conj : mBar8 * tr le88 1 * mBar8⁻¹ = tr le88 2
  mBar_norm : ∀ b ∈ bBar8, mBar8 * b * mBar8⁻¹ ∈ bBar8
  tr_two_mem : tr le88 2 ∈ bBar8

section Group

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def bSub8 (θ : L ≃* alternatingGroup (Fin 8)) : Subgroup G :=
  ((bBar8.comap (alternatingGroup (Fin 8)).subtype).map θ.symm.toMonoidHom).map L.subtype

@[expose] def vSub8 (θ : L ≃* alternatingGroup (Fin 8)) (z : G) : Subgroup G := bSub8 θ ⊔ zpowers z

end Group

@[expose] def FusP42Eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (θ : L ≃* alternatingGroup (Fin 8))
    (z : G), StandardSetting G L → AltStdBal.Cyc L Q z → Nat.card Q = 2 →
    centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G) →
    ∀ x ∈ normalizer (vSub8 θ z : Set G), x * z * x⁻¹ = z * w θ le88 →
    ∀ g ∈ normalizer (vSub8 θ z : Set G), ∀ l : L,
      ((θ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) ∈ bBar8 →
      ((θ l : alternatingGroup (Fin 8)) : Perm (Fin 8)).support.card = 4 →
        g * w θ le88 * g⁻¹ ≠ l

end CFSG.OddStandard.AltStdSmall4.Fus
