module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172ALayerGL
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperShared
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
import CFSG.Milestones.ASVolI.B4Ext.GL4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore (exists_struct)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Std (exists_elemAb_card)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem linTwo_isPGroup_two_of_mul_self {G : Type*} [Group G] (H : Subgroup G)
    (h : ∀ x ∈ H, x * x = 1) : IsPGroup 2 H := by
  intro x
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two]
  exact Subtype.ext (h x x.2)

private theorem linTwo_Q_conj_mem {P : Submodule (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ x ∈ P, g x ∈ P) (hg' : ∀ x ∈ P, g⁻¹ x ∈ P) {q : V ≃ₗ[ZMod 2] V}
    (hq : q ∈ CFSG.ASVolI.burnsideB49x_gl_Q P) :
    g * q * g⁻¹ ∈ CFSG.ASVolI.burnsideB49x_gl_Q P := by
  rw [CFSG.ASVolI.burnsideB49x_gl_mem_Q] at hq ⊢
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · have h1 : q (g⁻¹ x) - g⁻¹ x ∈ P := hq.1 (g⁻¹ x)
    have h2 : g (q (g⁻¹ x) - g⁻¹ x) ∈ P := hg _ h1
    rw [map_sub] at h2
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h2
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv] using h2
  · have h1 : g⁻¹ y ∈ P := hg' y hy
    have h2 : q (g⁻¹ y) = g⁻¹ y := hq.2 _ h1
    simp only [LinearEquiv.mul_apply]
    rw [h2]
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

theorem lin_two_twoLocalRank (hV : 3 ≤ Module.finrank (ZMod 2) V) :
    GLATwoLocalRank 3 (V ≃ₗ[ZMod 2] V) = Module.finrank (ZMod 2) V / 2 := by
  have hupper : GLATwoLocalRank 3 (V ≃ₗ[ZMod 2] V) ≤ Module.finrank (ZMod 2) V / 2 :=
    glaTwoLocalRank_le_of_card_le Nat.prime_three
      (fun _ E _ _ _ hE => CFSG.LocalAnalysis.GLTheoremA.S172A.GL.card_le_three_pow E hE)
  obtain ⟨E, hEel, hEcard⟩ := exists_elemAb_card V (Module.finrank (ZMod 2) V) rfl
  haveI : Fintype E := Fintype.ofFinite E
  have hge : 3 ^ (Module.finrank (ZMod 2) V / 2) ≤ Fintype.card E := by
    rw [← Nat.card_eq_fintype_card]
    exact hEcard.ge
  obtain ⟨k, X, ρf, hXprop, hind, hsup, hρf, hPcard, hpe⟩ := exists_struct E hEel hge
  have hpos : 0 < Fintype.card {i // Module.finrank (ZMod 2) (X i) = 2} := by
    rw [hPcard]
    omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.1 hpos
  let P : Submodule (ZMod 2) V := X p.1
  have hP2 : Module.finrank (ZMod 2) P = 2 := p.2
  have hPinv : ∀ g ∈ E, ∀ x ∈ P, g x ∈ P := (hXprop p.1).1
  set U : Subgroup (V ≃ₗ[ZMod 2] V) := CFSG.ASVolI.burnsideB49x_gl_Q P with hU
  have hUcard : Nat.card U = 2 ^ (2 * (Module.finrank (ZMod 2) V - 2)) := by
    rw [hU]
    exact CFSG.ASVolI.burnsideB49x_gl_card_Q (W := V) (X := P) hP2 rfl
  have hUne : U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card U = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hUcard] at h1
    have h2 : 1 < 2 ^ (2 * (Module.finrank (ZMod 2) V - 2)) := by
      have hle : 1 ≤ 2 * (Module.finrank (ZMod 2) V - 2) := by omega
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * (Module.finrank (ZMod 2) V - 2)) :=
            Nat.pow_le_pow_right (by norm_num) hle
    exact absurd h1 (ne_of_gt h2)
  have hU2 : IsPGroup 2 U := by
    refine linTwo_isPGroup_two_of_mul_self U ?_
    intro x hx
    rw [hU] at hx
    exact CFSG.ASVolI.burnsideB49x_gl_Q_mul_self hx
  have hEnorm : E ≤ Subgroup.normalizer (U : Set (V ≃ₗ[ZMod 2] V)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact linTwo_Q_conj_mem (fun x hx => hPinv g hg x hx)
        (fun x hx => hPinv g⁻¹ (E.inv_mem hg) x hx) hq
    · intro hq
      have h := linTwo_Q_conj_mem (P := P) (g := g⁻¹)
        (fun x hx => hPinv g⁻¹ (E.inv_mem hg) x hx)
        (fun x hx => by simpa using hPinv g hg x hx) hq
      have e : g⁻¹ * (g * q * g⁻¹) * (g⁻¹)⁻¹ = q := by group
      rwa [e] at h
  have hlower : Module.finrank (ZMod 2) V / 2 ≤ GLATwoLocalRank 3 (V ≃ₗ[ZMod 2] V) :=
    le_twoLocalPrimeRank_of_normalizer (G := V ≃ₗ[ZMod 2] V) (X := U) (E := E)
      Nat.prime_three hUne hU2 hEel hEcard hEnorm
  exact le_antisymm hupper hlower

theorem lin_two_bmax_card (hV : 3 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} (hA : GLAIsBmax 3 A) :
    IsElemAbelian 3 A ∧ Nat.card A = 3 ^ (Module.finrank (ZMod 2) V / 2) :=
  ⟨hA.1, by rw [hA.2.1, lin_two_twoLocalRank hV]⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
