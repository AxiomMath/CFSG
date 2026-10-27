module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.SeitzReduction.F4Pilot (ordSL ordSU ordSL_two ordSL_three ordSU_three)

inductive SpRow
  | field
  | swap
  | linearEven
  | unitaryEven
  | linearOdd
  | unitaryOdd
  | omegaPlus
  | omegaMinus
  deriving DecidableEq

@[expose] def SpRow.rootKind (m : ℕ) : SpRow → Sp2mKind
  | .field => .field
  | .swap => .swap
  | .linearEven => .linearEven
  | .unitaryEven => .unitaryEven
  | .linearOdd => .linearOdd
  | .unitaryOdd => .unitaryOdd
  | .omegaPlus => if m = 2 then .linearEven else .omegaPlus
  | .omegaMinus => if m = 2 then .unitaryEven else .omegaMinus

@[expose] def SpRow.ofKind : Sp2mKind → SpRow
  | .field => .field
  | .swap => .swap
  | .linearEven => .linearEven
  | .unitaryEven => .unitaryEven
  | .linearOdd => .linearOdd
  | .unitaryOdd => .unitaryOdd
  | .omegaPlus => .omegaPlus
  | .omegaMinus => .omegaMinus

theorem SpRow.rootKind_ofKind {m : ℕ} (hm : m ≠ 2) (κ : Sp2mKind) :
    (SpRow.ofKind κ).rootKind m = κ := by
  cases κ <;> simp [SpRow.ofKind, SpRow.rootKind, hm]

theorem SpRow.ofKind_rootKind {m : ℕ} (hm : m ≠ 2) (ρ : SpRow) :
    SpRow.ofKind (ρ.rootKind m) = ρ := by
  cases ρ <;> simp [SpRow.ofKind, SpRow.rootKind, hm]

theorem SpRow.rootKind_injective {m : ℕ} (hm : m ≠ 2) : Function.Injective (SpRow.rootKind m) :=
  fun ρ ρ' h => by rw [← SpRow.ofKind_rootKind hm ρ, h, SpRow.ofKind_rootKind hm ρ']

theorem SpRow.existsUnique_rootKind {m : ℕ} (hm : m ≠ 2) (κ : Sp2mKind) :
    ∃! ρ : SpRow, ρ.rootKind m = κ :=
  ⟨SpRow.ofKind κ, SpRow.rootKind_ofKind hm κ, fun ρ hρ => by
    rw [← hρ, SpRow.ofKind_rootKind hm ρ]⟩

theorem SpRow.rootKind_two_eq_linearEven_iff (ρ : SpRow) :
    ρ.rootKind 2 = .linearEven ↔ ρ = .linearEven ∨ ρ = .omegaPlus := by
  cases ρ <;> simp [SpRow.rootKind]

theorem SpRow.rootKind_two_eq_unitaryEven_iff (ρ : SpRow) :
    ρ.rootKind 2 = .unitaryEven ↔ ρ = .unitaryEven ∨ ρ = .omegaMinus := by
  cases ρ <;> simp [SpRow.rootKind]

theorem SpRow.rootKind_two_eq_iff (ρ ρ' : SpRow) :
    ρ.rootKind 2 = ρ'.rootKind 2 ↔ ρ = ρ' ∨
      ((ρ = .linearEven ∨ ρ = .omegaPlus) ∧ (ρ' = .linearEven ∨ ρ' = .omegaPlus)) ∨
      ((ρ = .unitaryEven ∨ ρ = .omegaMinus) ∧ (ρ' = .unitaryEven ∨ ρ' = .omegaMinus)) := by
  cases ρ <;> cases ρ' <;> simp [SpRow.rootKind]

theorem SpRow.rootKind_two_ne (ρ : SpRow) :
    ρ.rootKind 2 ≠ .omegaPlus ∧ ρ.rootKind 2 ≠ .omegaMinus := by
  cases ρ <;> simp [SpRow.rootKind]

@[expose] def SpRow.pieceOrders : SpRow → ℕ → ℕ × ℕ
  | .field, q => (ordSL 2 (q ^ 2), ordSL 2 (q ^ 2))
  | .swap, q => (ordSL 2 q ^ 2, ordSL 2 q ^ 2)
  | .linearEven, q => (ordSL 2 q ^ 2, ordSL 2 q)
  | .unitaryEven, q => (ordSL 2 (q ^ 2), ordSL 2 q)
  | .linearOdd, q => (ordSL 2 q ^ 2, ordSL 3 q)
  | .unitaryOdd, q => (ordSL 2 (q ^ 2), ordSU 3 q)
  | .omegaPlus, q => (ordSL 2 q, ordSL 2 q ^ 2)
  | .omegaMinus, q => (ordSL 2 q, ordSL 2 (q ^ 2))

private theorem cast_add_two_pow_sub_one' (p j : ℕ) :
    (((p + 2) ^ j - 1 : ℕ) : ℤ) = ((p : ℤ) + 2) ^ j - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
  push_cast
  ring

theorem ordSL_two_sq_lt_ordSL_two_sq {q : ℕ} (hq : 2 ≤ q) : ordSL 2 q ^ 2 < ordSL 2 (q ^ 2) := by
  rw [ordSL_two, ordSL_two, ← pow_mul]
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
  zify
  simp only [cast_add_two_pow_sub_one']
  rw [← sub_pos]
  ring_nf
  positivity

theorem SpRow.pieceOrders_injective {q : ℕ} (hq : 2 ≤ q) :
    Function.Injective (fun ρ : SpRow => ρ.pieceOrders q) := by
  intro ρ ρ' h
  have m1 := F4Pilot.ordSL_two_lt_sq hq
  have m2 := F4Pilot.ordSL_two_lt_ordSL_two_sq hq
  have m3 := F4Pilot.ordSL_two_sq_lt_ordSL_three hq
  have m4 := F4Pilot.ordSL_two_sq'_lt_ordSU_three hq
  have m5 := ordSL_two_sq_lt_ordSL_two_sq hq
  simp only at h
  cases ρ <;> cases ρ' <;> simp [SpRow.pieceOrders, Prod.ext_iff] at h ⊢ <;> omega

theorem SpRow.eq_of_rootKind_two_of_pieceOrders {q : ℕ} (hq : 2 ≤ q) {ρ ρ' : SpRow}
    (_hk : ρ.rootKind 2 = ρ'.rootKind 2) (hp : ρ.pieceOrders q = ρ'.pieceOrders q) : ρ = ρ' :=
  SpRow.pieceOrders_injective hq hp

theorem SpRow.eq_linearEven_of_rootKind_two {q : ℕ} (hq : 2 ≤ q) {ρ : SpRow}
    (hk : ρ.rootKind 2 = .linearEven) (hp : (ρ.pieceOrders q).1 = ordSL 2 q ^ 2) :
    ρ = .linearEven := by
  have m1 := F4Pilot.ordSL_two_lt_sq hq
  rcases (SpRow.rootKind_two_eq_linearEven_iff ρ).1 hk with rfl | rfl
  · rfl
  · simp [SpRow.pieceOrders] at hp
    omega

theorem SpRow.eq_omegaPlus_of_rootKind_two {q : ℕ} (hq : 2 ≤ q) {ρ : SpRow}
    (hk : ρ.rootKind 2 = .linearEven) (hp : (ρ.pieceOrders q).1 = ordSL 2 q) :
    ρ = .omegaPlus := by
  have m1 := F4Pilot.ordSL_two_lt_sq hq
  rcases (SpRow.rootKind_two_eq_linearEven_iff ρ).1 hk with rfl | rfl
  · simp [SpRow.pieceOrders] at hp
    omega
  · rfl

theorem SpRow.eq_unitaryEven_of_rootKind_two {q : ℕ} (hq : 2 ≤ q) {ρ : SpRow}
    (hk : ρ.rootKind 2 = .unitaryEven) (hp : (ρ.pieceOrders q).1 = ordSL 2 (q ^ 2)) :
    ρ = .unitaryEven := by
  have m2 := F4Pilot.ordSL_two_lt_ordSL_two_sq hq
  rcases (SpRow.rootKind_two_eq_unitaryEven_iff ρ).1 hk with rfl | rfl
  · rfl
  · simp [SpRow.pieceOrders] at hp
    omega

theorem SpRow.eq_omegaMinus_of_rootKind_two {q : ℕ} (hq : 2 ≤ q) {ρ : SpRow}
    (hk : ρ.rootKind 2 = .unitaryEven) (hp : (ρ.pieceOrders q).1 = ordSL 2 q) :
    ρ = .omegaMinus := by
  have m2 := F4Pilot.ordSL_two_lt_ordSL_two_sq hq
  rcases (SpRow.rootKind_two_eq_unitaryEven_iff ρ).1 hk with rfl | rfl
  · simp [SpRow.pieceOrders] at hp
    omega
  · rfl

inductive SiegelKind
  | trivial
  | field
  | swap
  deriving DecidableEq

@[expose] def SiegelKind.pieceOrder : SiegelKind → ℕ → ℕ
  | .trivial, q => ordSL 2 q
  | .field, q => ordSL 2 (q ^ 2)
  | .swap, q => ordSL 2 q ^ 2

@[expose] def SpRow.siegelKind : SpRow → SiegelKind
  | .field => .field
  | .swap => .swap
  | .linearEven => .swap
  | .unitaryEven => .field
  | .linearOdd => .swap
  | .unitaryOdd => .field
  | .omegaPlus => .trivial
  | .omegaMinus => .trivial

theorem SpRow.siegelKind_pieceOrder (ρ : SpRow) (q : ℕ) :
    ρ.siegelKind.pieceOrder q = (ρ.pieceOrders q).1 := by
  cases ρ <;> rfl

theorem SiegelKind.pieceOrder_injective {q : ℕ} (hq : 2 ≤ q) :
    Function.Injective (fun σ : SiegelKind => σ.pieceOrder q) := by
  intro σ σ' h
  have m1 := F4Pilot.ordSL_two_lt_sq hq
  have m2 := F4Pilot.ordSL_two_lt_ordSL_two_sq hq
  have m5 := ordSL_two_sq_lt_ordSL_two_sq hq
  simp only at h
  cases σ <;> cases σ' <;> simp [SiegelKind.pieceOrder] at h ⊢ <;> omega

theorem SpRow.eq_siegelKind_of_pieceOrder {q : ℕ} (hq : 2 ≤ q) {ρ : SpRow} {σ : SiegelKind}
    (h : σ.pieceOrder q = (ρ.pieceOrders q).1) : σ = ρ.siegelKind :=
  SiegelKind.pieceOrder_injective hq (h.trans (SpRow.siegelKind_pieceOrder ρ q).symm)

end CFSG.SeitzReduction.SymplecticPilot
