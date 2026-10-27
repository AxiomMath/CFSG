module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem nonempty_mulEquiv_stabilizer (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (h8 : finrank (ZMod 2) V = 8)
    (hfix : ∀ y : A5, orderOf y = 5 →
      (∀ u : V, σ (y, 1) u = u → u = 0) ∧ (∀ u : V, σ (1, y) u = u → u = 0))
    (v : V) (hv : v ≠ 0) (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hvk : σ (a₀ ^ k, a₀) v = v)
    (S : Subgroup (A5 × A5)) (hS : ∀ g, g ∈ S ↔ σ g v = v) : Nonempty (S ≃* A5) := by
  classical
  let T : Subgroup A5 := S.comap (MonoidHom.inr A5 A5)
  have hT : ∀ y : A5, y ∈ T ↔ (1, y) ∈ S := fun y => Subgroup.mem_comap
  have hm : (a₀ ^ k, a₀) ∈ S := (hS _).mpr hvk
  have hconj : ∀ (i : ℕ) (y : A5), y ∈ T → a₀ ^ i * y * (a₀ ^ i)⁻¹ ∈ T := by
    intro i y hy
    have h1 : (a₀ ^ k, a₀) ^ i ∈ S := S.pow_mem hm i
    have h2 : (1, y) ∈ S := (hT y).mp hy
    have h3 : (a₀ ^ k, a₀) ^ i * (1, y) * ((a₀ ^ k, a₀) ^ i)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem h1 h2) (S.inv_mem h1)
    have heq : (a₀ ^ k, a₀) ^ i * (1, y) * ((a₀ ^ k, a₀) ^ i)⁻¹
        = (1, a₀ ^ i * y * (a₀ ^ i)⁻¹) := by
      ext <;> simp
    rw [heq] at h3
    exact (hT _).mpr h3
  have hTbot : T = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    by_contra hy1
    obtain ⟨i, j, hij⟩ := exists_orderOf_eq_five_mul_conj hy1
    have hwT : (a₀ ^ i * y * (a₀ ^ i)⁻¹) * (a₀ ^ j * y * (a₀ ^ j)⁻¹) ∈ T :=
      T.mul_mem (hconj i y hy) (hconj j y hy)
    have hwS : (1, (a₀ ^ i * y * (a₀ ^ i)⁻¹) * (a₀ ^ j * y * (a₀ ^ j)⁻¹)) ∈ S :=
      (hT _).mp hwT
    have hvv : σ (1, (a₀ ^ i * y * (a₀ ^ i)⁻¹) * (a₀ ^ j * y * (a₀ ^ j)⁻¹)) v = v :=
      (hS _).mp hwS
    exact hv ((hfix _ hij).2 v hvv)
  let φ : S →* A5 := (MonoidHom.fst A5 A5).comp S.subtype
  have hφ_inj : Function.Injective φ := by
    intro s s' h
    have hfst : (s : A5 × A5).1 = (s' : A5 × A5).1 := h
    have hfirst : ((s⁻¹ * s' : S) : A5 × A5).1 = 1 := by
      simp [hfst]
    have haeq : ((s⁻¹ * s' : S) : A5 × A5) = (1, ((s⁻¹ * s' : S) : A5 × A5).2) :=
      Prod.ext hfirst rfl
    have hmemT : ((s⁻¹ * s' : S) : A5 × A5).2 ∈ T := by
      rw [hT]
      rw [← haeq]
      exact (s⁻¹ * s').property
    have hsecond : ((s⁻¹ * s' : S) : A5 × A5).2 = 1 := by
      have hmem : ((s⁻¹ * s' : S) : A5 × A5).2 ∈ (⊥ : Subgroup A5) := by
        simpa [hTbot] using hmemT
      simpa using hmem
    have hone : s⁻¹ * s' = 1 := by
      apply Subtype.ext
      rw [haeq, hsecond]
      rfl
    have h2 : s⁻¹ * s' = s⁻¹ * s := by rw [hone, inv_mul_cancel]
    exact (mul_left_cancel h2).symm
  have hcardG : Nat.card (A5 × A5) = 3600 := by
    have hA5 : Nat.card A5 = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      decide
    calc Nat.card (A5 × A5) = Nat.card A5 * Nat.card A5 := Nat.card_prod A5 A5
      _ = 60 * 60 := by rw [hA5]
      _ = 3600 := by norm_num
  have hVcard : Nat.card V = 256 := by
    haveI : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), h8, ZMod.card]
    norm_num
  have hsub : Nat.card {u : V // u ≠ 0} ≤ 255 := by
    have hlt : Nat.card {u : V // u ≠ 0} < Nat.card V :=
      Finite.card_subtype_lt (p := fun u : V => u ≠ 0) (x := 0) (by simp)
    rw [hVcard] at hlt
    omega
  have hkey : ∀ a b : A5 × A5, σ a v = σ b v ↔ a⁻¹ * b ∈ S := by
    intro a b
    constructor
    · intro h
      rw [hS]
      have h2 : σ a⁻¹ (σ a v) = σ a⁻¹ (σ b v) := congrArg (fun w => σ a⁻¹ w) h
      have h3 : σ a⁻¹ (σ a v) = v := by
        rw [← LinearEquiv.mul_apply, map_inv, inv_mul_cancel]
        simp
      have h4 : σ a⁻¹ (σ b v) = v := h2.symm.trans h3
      rw [← LinearEquiv.mul_apply, ← map_mul] at h4
      exact h4
    · intro h
      have hfixv : σ (a⁻¹ * b) v = v := (hS _).mp h
      rw [map_mul, LinearEquiv.mul_apply] at hfixv
      calc σ a v = σ a (σ a⁻¹ (σ b v)) := by rw [hfixv]
        _ = (σ a * σ a⁻¹) (σ b v) := by rw [LinearEquiv.mul_apply]
        _ = σ b v := by rw [map_inv, mul_inv_cancel]; simp
  let g : A5 × A5 → {u : V // u ≠ 0} := fun a =>
    ⟨σ a v, fun h0 => hv ((σ a).injective (by simpa using h0))⟩
  have hg : ∀ a b : A5 × A5, QuotientGroup.leftRel S a b → g a = g b := fun a b hab =>
    Subtype.ext ((hkey a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  let f : (A5 × A5) ⧸ S → {u : V // u ≠ 0} := Quotient.lift g hg
  have hf_inj : Function.Injective f := by
    intro q q' h
    revert h
    refine Quotient.inductionOn₂ q q' ?_
    intro a b h
    change g a = g b at h
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr ((hkey a b).mp (Subtype.ext_iff.mp h))
  have hindex : S.index ≤ 255 := by
    have hle : Nat.card ((A5 × A5) ⧸ S) ≤ Nat.card {u : V // u ≠ 0} :=
      Nat.card_le_card_of_injective f hf_inj
    rw [Subgroup.index_eq_card]
    exact le_trans hle hsub
  have hcardS : 15 ≤ Nat.card S := by
    have hLagrange : S.index * Nat.card S = Nat.card (A5 × A5) := Subgroup.index_mul_card S
    rw [hcardG] at hLagrange
    have hle : S.index * Nat.card S ≤ 255 * Nat.card S := Nat.mul_le_mul_right _ hindex
    omega
  have hK : 15 ≤ Nat.card φ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ_inj).toEquiv]
    exact hcardS
  exact ⟨MulEquiv.ofBijective φ ⟨hφ_inj, MonoidHom.range_eq_top.mp (eq_top_of_fifteen_le_card hK)⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Fpf
