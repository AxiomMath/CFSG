module

public import CFSG.LargeExtraspecial.S111SJNon
public import CFSG.LargeExtraspecial.S111SJLay
public import CFSG.GH74.Uniqueness.Bender.Out

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

structure LayerCfg {X : Type} [Group X] (E O L : Subgroup X) (w : ℕ) {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : X →* (V ≃ₗ[ZMod 2] V)) (a : V) : Prop where
  quasi : CFSG.Open.IsQuasisimple E
  card_O : Nat.card O ∣ 3
  fstar_inv : ∀ v : X, v * v = 1 → v ∈ centralizer ((O ⊔ E : Subgroup X) : Set X) → v = 1
  fstar_cent : centralizer ((O ⊔ E : Subgroup X) : Set X) ≤ O ⊔ E
  L_sq : ∀ x ∈ L, x * x = 1
  L_comm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x
  L_faith : ∀ x ∈ L, (∀ e ∈ E, e * x = x * e) → x = 1
  four_le : 4 ≤ w
  card_L : Nat.card L = 2 ^ (w - 1)
  weakly : ∀ x : X, L.map (MulAut.conj x).toMonoidHom ≤ normalizer (L : Set X) →
    L.map (MulAut.conj x).toMonoidHom = L
  not_TI : ∃ t ∈ L, t ≠ 1 ∧ ∃ x : X, t ∈ L.map (MulAut.conj x).toMonoidHom ∧
    L.map (MulAut.conj x).toMonoidHom ≠ L
  rho_inj : Function.Injective ρ
  finrank_eq : Module.finrank (ZMod 2) V = 2 * w
  irr : ∀ W : Submodule (ZMod 2) V, (∀ x : X, ∀ v ∈ W, ρ x v ∈ W) → W = ⊥ ∨ W = ⊤
  a_ne : a ≠ 0
  a_fix : ∀ x ∈ L, ρ x a = a
  fix_eq : ∀ v : V, (∀ x ∈ L, ρ x v = v) → v = 0 ∨ v = a

namespace LayerCfg

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem perfect (C : LayerCfg E O L w ρ a) : Group.IsPerfect E := ⟨C.quasi.1⟩

theorem eq_one_of_barAct [E.Normal] (C : LayerCfg E O L w ρ a) {x : X} (hx : x ∈ L)
    (h1 : barAct E x = 1) : x = 1 := by
  have := C.perfect
  exact C.L_faith x hx fun e he => (commute_of_barAct_eq_one h1 e he).symm

theorem card_lam [E.Normal] (C : LayerCfg E O L w ρ a) :
    Nat.card (L.map (barAct E)) = 2 ^ (w - 1) := by
  have hinj : Function.Injective ((barAct E).comp L.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (C.eq_one_of_barAct x.2 hx)
  have hrange : ((barAct E).comp L.subtype).range = L.map (barAct E) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, C.card_L]

theorem lam_sq [E.Normal] (C : LayerCfg E O L w ρ a) {l : MulAut (E ⧸ center E)}
    (hl : l ∈ L.map (barAct E)) : l * l = 1 := by
  obtain ⟨x, hx, rfl⟩ := hl
  rw [← map_mul, C.L_sq x hx, map_one]

theorem lam_comm [E.Normal] (C : LayerCfg E O L w ρ a) {l l' : MulAut (E ⧸ center E)}
    (hl : l ∈ L.map (barAct E)) (hl' : l' ∈ L.map (barAct E)) : l * l' = l' * l := by
  obtain ⟨x, hx, rfl⟩ := hl
  obtain ⟨x', hx', rfl⟩ := hl'
  rw [← map_mul, ← map_mul, C.L_comm x hx x' hx']

theorem thirtytwo_le_card_lam [E.Normal] (C : LayerCfg E O L w ρ a) (h6 : 6 ≤ w) :
    32 ≤ Nat.card (L.map (barAct E)) := by
  rw [C.card_lam]
  calc 32 = 2 ^ 5 := by norm_num
    _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem false_of_nonBender
    [Finite X] [E.Normal] (C : LayerCfg E O L w ρ a) (h6 : 6 ≤ w)
    (h : (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (E ⧸ center E ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card (E ⧸ center E) = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (E ⧸ center E ≃* goldschmidtJ1)) : False := by
  have : IsSimpleGroup (E ⧸ center E) := C.quasi.2
  have h8 := card_le_eight_of_nonBender h (L.map (barAct E)) fun l hl => C.lam_sq hl
  have := C.thirtytwo_le_card_lam h6
  omega

theorem width_le [Finite X] [E.Normal]
    (C : LayerCfg E O L w ρ a) {f i e : ℕ}
    (hB : BenderType (E ⧸ center E) f i e) : w ≤ f + 2 ∧ (i ≠ 3 → w ≤ f + 1) := by
  obtain ⟨h1, h2⟩ := hB.card_le_of_sq_eq_one_aut (L.map (barAct E)) fun l hl => C.lam_sq hl
  rw [C.card_lam] at h1 h2
  have h6 := C.four_le
  refine ⟨?_, fun hi => ?_⟩
  · have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  · have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (h2 hi)
    omega

end LayerCfg

end CFSG.LargeExtraspecial.S11
