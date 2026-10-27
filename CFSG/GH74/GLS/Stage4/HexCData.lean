module

public import CFSG.GH74.GLS.Stage4.HexCK6

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

structure HexData (root : ℤ → Subgroup G) (F : Type) [Field F] where
  φ : SL2 F →* G
  T : Fˣ → G
  p1 : F → G
  p2 : F → G
  p4 : F → G
  p5 : F → G
  p6 : F → G
  T_eq : ∀ t, T t = φ (sl2D t)
  p6_eq : ∀ c, p6 c = φ (sl2U c)
  cent3 : ∀ g : SL2 F, ∀ u ∈ root 3, φ g * u = u * φ g
  T_mul : ∀ t t', T (t * t') = T t * T t'
  p1_add : ∀ c d, p1 (c + d) = p1 c * p1 d
  p2_add : ∀ c d, p2 (c + d) = p2 c * p2 d
  p4_add : ∀ c d, p4 (c + d) = p4 c * p4 d
  p5_add : ∀ c d, p5 (c + d) = p5 c * p5 d
  p6_add : ∀ c d, p6 (c + d) = p6 c * p6 d
  p1_inj : Function.Injective p1
  p2_inj : Function.Injective p2
  p4_inj : Function.Injective p4
  p5_inj : Function.Injective p5
  p6_inj : Function.Injective p6
  p1_mem : ∀ d, p1 d ∈ root 1
  p2_mem : ∀ d, p2 d ∈ root 2
  p4_mem : ∀ d, p4 d ∈ root 4
  p5_mem : ∀ d, p5 d ∈ root 5
  p6_mem : ∀ d, p6 d ∈ root 6
  p1_surj : ∀ b ∈ root 1, ∃ d, p1 d = b
  p2_surj : ∀ b ∈ root 2, ∃ d, p2 d = b
  p4_surj : ∀ b ∈ root 4, ∃ d, p4 d = b
  p5_surj : ∀ b ∈ root 5, ∃ d, p5 d = b
  p6_surj : ∀ b ∈ root 6, ∃ d, p6 d = b
  rel_long : ∀ c d, ⁅p6 c, p2 d⁆ = p4 (c * d)
  rel_short : ∀ c d, (p5 (c * d))⁻¹ * ⁅p6 c, p1 d⁆ ∈ Vsub root 2 4
  w1 : ∀ (t : Fˣ) d, T t * p1 d * (T t)⁻¹ = p1 ((t : F)⁻¹ * d)
  w2 : ∀ (t : Fˣ) d, T t * p2 d * (T t)⁻¹ = p2 ((t : F)⁻¹ * d)
  w4 : ∀ (t : Fˣ) d, T t * p4 d * (T t)⁻¹ = p4 ((t : F) * d)
  w5 : ∀ (t : Fˣ) d, T t * p5 d * (T t)⁻¹ = p5 ((t : F) * d)
  w6 : ∀ (t : Fˣ) d, T t * p6 d * (T t)⁻¹ = p6 ((t : F) ^ 2 * d)

theorem phi6_injective {N : Subgroup G} (E : SL2Pos H N root 4) :
    Function.Injective (phi6 r₁ r₂ E.φ) :=
  (MulAut.conj (r₁ * r₂)).injective.comp E.inj

theorem phi6_w6 {N : Subgroup G} (E : SL2Pos H N root 4) (t : E.Fˣ) (d : E.F) :
    phi6 r₁ r₂ E.φ (sl2D t) * phi6 r₁ r₂ E.φ (sl2U d) * (phi6 r₁ r₂ E.φ (sl2D t))⁻¹ =
      phi6 r₁ r₂ E.φ (sl2U ((t : E.F) ^ 2 * d)) := by
  rw [← map_inv, ← map_mul, ← map_mul, sl2D_mul_sl2U_eq, mul_assoc, mul_inv_cancel, mul_one]

theorem phi6_cent3 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    {u : G} (hu : u ∈ root 3) (g : SL2 E.F) : phi6 r₁ r₂ E.φ g * u = u * phi6 r₁ r₂ E.φ g := by
  have key := sl2_hom_mem (phi6 r₁ r₂ E.φ) (Subgroup.centralizer {u})
    (fun c => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hC.o36 h hu _ (phi6_U_mem R E c))
    (fun c => by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hz := r2_neg6_mem R (phi6_L_mem R E c)
      have hu' : r₂ * h * r₂⁻¹ ∈ root 3 := by
        have := (RGD2.mem_iff_r₂ R (i := 3) (by norm_num) (by norm_num) h).1 hu
        norm_num at this; exact this
      have := hC.o36 _ hu' _ hz
      refine comm_via r₂⁻¹ ?_
      simpa using this) g
  rw [Subgroup.mem_centralizer_iff] at key
  exact (key u (Set.mem_singleton u)).symm

theorem phi6_U_surj (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) {b : G}
    (hb : b ∈ root 6) : ∃ c : E.F, phi6 r₁ r₂ E.φ (sl2U c) = b := by
  have hx : (r₁ * r₂)⁻¹ * b * (r₁ * r₂) ∈ root 4 := by
    rw [mem_iff_r12 R]
    simpa [mul_assoc] using hb
  obtain ⟨c, hc⟩ := (E.hU _).1 hx
  refine ⟨c, ?_⟩
  rw [phi6_apply, hc]
  group

end CFSG.GH74.GLS.Stage4.Hex
