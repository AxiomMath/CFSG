module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

theorem gzNo_card_modEq_five {K : Type*} [Group K] [Finite K] {ρ : K} (hρ : orderOf ρ = 5)
    (S : Set K) (hS : ∀ s ∈ S, ρ * s * ρ⁻¹ ∈ S) :
    Nat.card S ≡ Nat.card {s : K // s ∈ S ∧ s * ρ = ρ * s} [MOD 5] := by
  classical
  haveI : Fintype ↥S := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let f : Function.End ↥S := fun s => ⟨ρ * s * ρ⁻¹, hS s s.2⟩
  have hiter : ∀ (n : ℕ) (s : ↥S), ((f^[n] s : ↥S) : K) = ρ ^ n * s * (ρ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
        intro s
        change (s : K) = ρ ^ 0 * s * (ρ ^ 0)⁻¹
        simp
    | succ n ih =>
        intro s
        rw [Function.iterate_succ_apply']
        change ρ * ((f^[n] s : ↥S) : K) * ρ⁻¹ = ρ ^ (n + 1) * s * (ρ ^ (n + 1))⁻¹
        rw [ih, pow_succ']
        group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    change ((f^[5] s : ↥S) : K) = s
    rw [hiter 5, show ρ ^ 5 = 1 by rw [← hρ, pow_orderOf_eq_one]]
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
  have hfix : Nat.card (Function.fixedPoints f) =
      Nat.card {s : K // s ∈ S ∧ s * ρ = ρ * s} := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : K), w.1.2, by
          have h : ρ * (w.1 : K) * ρ⁻¹ = w.1 := congrArg Subtype.val w.2
          calc (w.1 : K) * ρ = ρ * (w.1 : K) * ρ⁻¹ * ρ := by rw [h]
            _ = ρ * w.1 := by group⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
          apply Subtype.ext
          change ρ * w.1 * ρ⁻¹ = w.1
          rw [← w.2.2, mul_inv_cancel_right]⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  rw [← hfix, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hmod

theorem gzNo_card_le_sq {K : Type*} [Group K] [Finite K] (D : Subgroup K)
    (hD : ∀ d ∈ D, d ^ 2 = 1) {y : K} (hy : y ^ 2 = 1) (hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D) :
    Nat.card D ≤ Nat.card {d : K // d ∈ D ∧ d * y = y * d} ^ 2 := by
  have hinv : ∀ d ∈ D, d⁻¹ = d := fun d hd =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hD d hd)
  have hcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d := by
    intro d hd e he
    have h1 := hinv (d * e) (mul_mem hd he)
    rw [mul_inv_rev, hinv d hd, hinv e he] at h1
    exact h1.symm
  have hyy : y * y = 1 := by rw [← sq]; exact hy
  have hkey : ∀ d ∈ D, d * (y * d * y⁻¹) = 1 ↔ d * y = y * d := by
    intro d hd
    constructor
    · intro h
      have h' : y * d * y⁻¹ = d := by
        calc y * d * y⁻¹ = d⁻¹ * (d * (y * d * y⁻¹)) := by group
          _ = d := by rw [h, mul_one, hinv d hd]
      calc d * y = (y * d * y⁻¹) * y := by rw [h']
        _ = y * d := by group
    · intro h
      rw [← h, mul_inv_cancel_right, ← sq]
      exact hD d hd
  let φ : ↥D →* ↥D :=
    { toFun := fun d => ⟨d * (y * d * y⁻¹), mul_mem d.2 (hyD d d.2)⟩
      map_one' := by
        apply Subtype.ext
        change (1 : K) * (y * 1 * y⁻¹) = 1
        group
      map_mul' := by
        intro d e
        apply Subtype.ext
        change ((d : K) * e) * (y * ((d : K) * e) * y⁻¹) =
          (d * (y * d * y⁻¹)) * (e * (y * e * y⁻¹))
        have hc := hcomm (e : K) e.2 (y * d * y⁻¹) (hyD d d.2)
        calc ((d : K) * e) * (y * ((d : K) * e) * y⁻¹)
            = d * (e * (y * d * y⁻¹)) * (y * e * y⁻¹) := by group
          _ = d * ((y * d * y⁻¹) * e) * (y * e * y⁻¹) := by rw [hc]
          _ = (d * (y * d * y⁻¹)) * (e * (y * e * y⁻¹)) := by group }
  have hφy : ∀ d : ↥D, ((φ d : ↥D) : K) * y = y * ((φ d : ↥D) : K) := by
    intro d
    change (d : K) * (y * d * y⁻¹) * y = y * ((d : K) * (y * d * y⁻¹))
    have h1 : y * (y * (d : K) * y⁻¹) * y⁻¹ = d := by
      calc y * (y * (d : K) * y⁻¹) * y⁻¹ = (y * y) * d * (y * y)⁻¹ := by group
        _ = d := by rw [hyy]; group
    have h3 : y * ((d : K) * (y * d * y⁻¹)) * y⁻¹ = (d : K) * (y * d * y⁻¹) := by
      calc y * ((d : K) * (y * d * y⁻¹)) * y⁻¹
          = (y * d * y⁻¹) * (y * (y * (d : K) * y⁻¹) * y⁻¹) := by group
        _ = (y * d * y⁻¹) * d := by rw [h1]
        _ = (d : K) * (y * d * y⁻¹) := (hcomm _ d.2 _ (hyD d d.2)).symm
    calc (d : K) * (y * d * y⁻¹) * y = (y * ((d : K) * (y * d * y⁻¹)) * y⁻¹) * y := by
          rw [h3]
      _ = y * ((d : K) * (y * d * y⁻¹)) := by group
  have hker : Nat.card ↥φ.ker = Nat.card {d : K // d ∈ D ∧ d * y = y * d} := by
    refine Nat.card_congr
      { toFun := fun w => ⟨((w : ↥D) : K), (w : ↥D).2,
          (hkey _ (w : ↥D).2).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp w.2))⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩,
          MonoidHom.mem_ker.mpr (Subtype.ext ((hkey w.1 w.2.1).mpr w.2.2))⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  have hcommy : ∀ w : ↥φ.range, (((w : ↥D) : K)) * y = y * ((w : ↥D) : K) := by
    intro w
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp w.2
    rw [← hd]
    exact hφy d
  have hrange : Nat.card ↥φ.range ≤ Nat.card {d : K // d ∈ D ∧ d * y = y * d} := by
    refine Nat.card_le_card_of_injective
      (fun w => ⟨((w : ↥D) : K), (w : ↥D).2, hcommy w⟩) ?_
    intro w w' hww'
    have h := congrArg Subtype.val hww'
    exact Subtype.ext (Subtype.ext h)
  calc Nat.card ↥D = Nat.card ↥φ.ker * Nat.card ↥φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card {d : K // d ∈ D ∧ d * y = y * d} *
          Nat.card {d : K // d ∈ D ∧ d * y = y * d} := Nat.mul_le_mul hker.le hrange
    _ = Nat.card {d : K // d ∈ D ∧ d * y = y * d} ^ 2 := (sq _).symm

theorem gzNo_card_mul_le {K : Type*} [Group K] [Finite K] {H L D : Subgroup K} (hH : H ≤ D)
    (hL : L ≤ D) : Nat.card H * Nat.card L ≤ Nat.card D * Nat.card ↥(H ⊓ L) := by
  have h1 : H.relIndex L * Nat.card ↥(H ⊓ L) = Nat.card L := Subgroup.relIndex_mul_card H L
  have h2 : H.relIndex D * Nat.card ↥(H ⊓ D) = Nat.card D := Subgroup.relIndex_mul_card H D
  rw [inf_of_le_left hH] at h2
  have hD0 : 0 < Nat.card D := Nat.card_pos
  have h0 : H.relIndex D ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    omega
  have h3 : H.relIndex L ≤ H.relIndex D := Subgroup.relIndex_le_of_le_right hL h0
  calc Nat.card H * Nat.card L = Nat.card H * (H.relIndex L * Nat.card ↥(H ⊓ L)) := by
        rw [h1]
    _ ≤ Nat.card H * (H.relIndex D * Nat.card ↥(H ⊓ L)) := by gcongr
    _ = (H.relIndex D * Nat.card H) * Nat.card ↥(H ⊓ L) := by ring
    _ = Nat.card D * Nat.card ↥(H ⊓ L) := by rw [h2]

theorem gzNo_nonempty_centralizer_conj {Γ : Type*} [Group Γ] (b u : Γ) :
    Nonempty (↥(Subgroup.centralizer ({u} : Set Γ)) ≃*
      ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set Γ))) := by
  have hf : ∀ k : Γ, k ∈ Subgroup.centralizer ({u} : Set Γ) →
      b * k * b⁻¹ ∈ Subgroup.centralizer ({b * u * b⁻¹} : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    calc b * k * b⁻¹ * (b * u * b⁻¹) = b * (k * u) * b⁻¹ := by group
      _ = b * (u * k) * b⁻¹ := by rw [hk]
      _ = b * u * b⁻¹ * (b * k * b⁻¹) := by group
  have hg : ∀ k : Γ, k ∈ Subgroup.centralizer ({b * u * b⁻¹} : Set Γ) →
      b⁻¹ * k * b ∈ Subgroup.centralizer ({u} : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    calc b⁻¹ * k * b * u = b⁻¹ * (k * (b * u * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * u * b⁻¹) * k) * b := by rw [hk]
      _ = u * (b⁻¹ * k * b) := by group
  exact ⟨{ toFun := fun k => ⟨b * k * b⁻¹, hf k k.2⟩
           invFun := fun k => ⟨b⁻¹ * k * b, hg k k.2⟩
           left_inv := fun k => Subtype.ext (show b⁻¹ * (b * (k : Γ) * b⁻¹) * b = k by group)
           right_inv := fun k => Subtype.ext (show b * (b⁻¹ * (k : Γ) * b) * b⁻¹ = k by group)
           map_mul' := fun k l => Subtype.ext
             (show b * ((k : Γ) * l) * b⁻¹ = b * k * b⁻¹ * (b * l * b⁻¹) by group) }⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
