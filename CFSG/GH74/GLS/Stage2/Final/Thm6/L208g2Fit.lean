module

public import CFSG.GH74.GLS.SP.Local.SPLFitA
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem fit_factor {Y : Type} [Group Y] [Finite Y] {Lk : Subgroup Y} [Lk.Normal] {r : ℕ}
    (hr : Odd r) (hr3 : 3 < r) (hm : HasSL2Model ↥Lk (fun q => q = r))
    {a : Y} (ha : a ∈ Lk) (ha2 : a * a ≠ 1) (hsq : ∀ c ∈ Lk, c * (a * a) = (a * a) * c)
    (M : Subgroup Y)
    (hM : ∀ m ∈ M, ∀ c ∈ Lk, c * (m * a * m⁻¹ * a⁻¹) = (m * a * m⁻¹ * a⁻¹) * c)
    (W : Subgroup Y) (hWM : W ≤ M) (hWodd : Odd (Nat.card ↥W))
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hX : ∀ k ∈ Lk, Odd (orderOf k) → k * a = a * k →
      ∃ m ∈ M, (∀ x ∈ Lk, m * x * m⁻¹ = k * x * k⁻¹) ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, ∃ k ∈ Lk, Odd (orderOf k) ∧ k * a = a * k ∧ ∀ x ∈ Lk, w * x * w⁻¹ = k * x * k⁻¹ := by
  obtain ⟨F, hF, hFin, hq, ⟨e⟩⟩ := hm
  have hq' : Nat.card F = r := hq
  have hL2 : CFSG.GH74.GLS.IVK.L2Field F := ⟨hq' ▸ hr, hq' ▸ hr3⟩
  let u₁ : ↥Lk := ⟨a, ha⟩
  have hu₁c : u₁ ^ 2 ∈ Subgroup.center ↥Lk := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    simpa [u₁, pow_two] using hsq c.1 c.2
  have hu₁1 : u₁ ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have := congrArg Subtype.val h
    simpa [u₁, pow_two] using this
  let α : ↥M →* MulAut ↥Lk := (MulAut.conjNormal : Y →* MulAut ↥Lk).comp M.subtype
  have hα : ∀ m : ↥M, α m u₁ * u₁⁻¹ ∈ Subgroup.center ↥Lk := by
    intro m
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa [α, u₁, MulAut.conjNormal_apply] using hM m.1 m.2 g.1 g.2
  have hWodd' : Odd (Nat.card ↥(W.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv]
  have hWab' : ∀ x ∈ W.subgroupOf M, ∀ y ∈ W.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hWab x.1 hx y.1 hy
  have hX' : ∀ k : ↥Lk, Odd (orderOf k) → k * u₁ = u₁ * k →
      ∃ m : ↥M, α m = MulAut.conj k ∧ ∀ w ∈ W.subgroupOf M, m * w * m⁻¹ ∈ W.subgroupOf M := by
    intro k hk hkc
    have hko : Odd (orderOf (k : Y)) := by rwa [Subgroup.orderOf_coe]
    have hka : (k : Y) * a = a * k := by
      have := congrArg Subtype.val hkc
      simpa [u₁] using this
    obtain ⟨m, hmM, hmx, hmW⟩ := hX k.1 k.2 hko hka
    refine ⟨⟨m, hmM⟩, ?_, ?_⟩
    · ext x
      have := hmx x.1 x.2
      simpa [α, MulAut.conjNormal_apply] using this
    · intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hmW w.1 hw
  have hmain := CFSG.GH74.GLS.SP.Local.spl_fit_A1 F hL2 ↥Lk e u₁ hu₁c hu₁1 ↥M α hα
    (W.subgroupOf M) hWodd' hWab' hX'
  intro w hw
  obtain ⟨k, hkodd, hkc, hαk⟩ := hmain ⟨w, hWM hw⟩ (by rw [Subgroup.mem_subgroupOf]; exact hw)
  refine ⟨k.1, k.2, ?_, ?_, ?_⟩
  · rwa [Subgroup.orderOf_coe]
  · have := congrArg Subtype.val hkc
    simpa [u₁] using this
  · intro x hx
    have := congrArg (fun φ => ((φ ⟨x, hx⟩ : ↥Lk) : Y)) hαk
    simpa [α, MulAut.conjNormal_apply] using this

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
