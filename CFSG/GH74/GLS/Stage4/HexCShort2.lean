module

public import CFSG.GH74.GLS.Stage4.HexCShort
public import CFSG.GH74.GLS.Stage4.HexCUniq

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem phi6_W {N : Subgroup G} (E : SL2Pos H N root 4) :
    phi6 r₁ r₂ E.φ (sl2W E.F) = phi6 r₁ r₂ E.φ (sl2U 1) * phi6 r₁ r₂ E.φ (sl2L (-1)) *
      phi6 r₁ r₂ E.φ (sl2U 1) := by
  rw [sl2W_eq_sl2Wc]
  simp only [sl2Wc, map_mul, inv_one]

theorem Rt6_one : Rt 6 0 = 1 := (Rt6_eq_pos (q := 0) (by norm_num) (by norm_num)).2 (by norm_num)

theorem Rt6_five : Rt 6 4 = 5 := (Rt6_eq_pos (q := 4) (by norm_num) (by norm_num)).2 (by norm_num)

theorem weyl_conj_eq {u l b : G} (hlbl : l * b * l⁻¹ = b) :
    (u * l * u) * b * (u * l * u)⁻¹ = (u * (l * ⁅u, b⁆ * l⁻¹) * u⁻¹ * ⁅u, b⁆) * b := by
  calc (u * l * u) * b * (u * l * u)⁻¹ = u * l * (u * b * u⁻¹) * l⁻¹ * u⁻¹ := by group
    _ = u * l * (⁅u, b⁆ * b) * l⁻¹ * u⁻¹ := by simp only [commutatorElement_def]; group
    _ = u * (l * ⁅u, b⁆ * l⁻¹) * (l * b * l⁻¹) * u⁻¹ := by group
    _ = u * (l * ⁅u, b⁆ * l⁻¹) * b * u⁻¹ := by rw [hlbl]
    _ = (u * (l * ⁅u, b⁆ * l⁻¹) * u⁻¹) * (u * b * u⁻¹) := by group
    _ = (u * (l * ⁅u, b⁆ * l⁻¹) * u⁻¹) * (⁅u, b⁆ * b) := by
        simp only [commutatorElement_def]; group
    _ = (u * (l * ⁅u, b⁆ * l⁻¹) * u⁻¹ * ⁅u, b⁆) * b := by group

theorem weyl_conj_eq' {u l a : G} (hua : u * a * u⁻¹ = a) :
    (u * l * u) * a * (u * l * u)⁻¹ = (u * ⁅l, a⁆ * u⁻¹) * a := by
  calc (u * l * u) * a * (u * l * u)⁻¹ = u * l * (u * a * u⁻¹) * l⁻¹ * u⁻¹ := by group
    _ = u * l * a * l⁻¹ * u⁻¹ := by rw [hua]
    _ = (u * ⁅l, a⁆ * u⁻¹) * (u * a * u⁻¹) := by simp only [commutatorElement_def]; group
    _ = (u * ⁅l, a⁆ * u⁻¹) * a := by rw [hua]

theorem short_ndU (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {b : G}
    (hb : b ∈ root 1) (hk : ⁅phi6 r₁ r₂ E.φ (sl2U 1), b⁆ ∈ Vsub root 2 4) :
    b ∈ Vsub root 2 4 := by
  have hlb : ⁅phi6 r₁ r₂ E.φ (sl2L (-1)), b⁆ = 1 := short_lB R E hC (-1) hb
  have hlbl : phi6 r₁ r₂ E.φ (sl2L (-1)) * b * (phi6 r₁ r₂ E.φ (sl2L (-1)))⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]; exact commutatorElement_eq_one_iff_mul_comm.1 hlb
  have hUN : ∀ n ∈ Vsub root 2 4, phi6 r₁ r₂ E.φ (sl2U 1) * n * (phi6 r₁ r₂ E.φ (sl2U 1))⁻¹ ∈
      Vsub root 2 4 := fun n hn => root6_norm hC (phi6_U_mem R E 1) hn
  have hLN : ∀ n ∈ Vsub root 2 4, phi6 r₁ r₂ E.φ (sl2L (-1)) * n *
      (phi6 r₁ r₂ E.φ (sl2L (-1)))⁻¹ ∈ Vsub root 2 4 := fun n hn =>
    rootNeg6_norm R hC (phi6_L_mem R E (-1)) hn
  have hWb := weyl_conj_eq (u := phi6 r₁ r₂ E.φ (sl2U 1)) hlbl
  rw [← phi6_W E] at hWb
  have hn := Subgroup.mul_mem _ (hUN _ (hLN _ hk)) hk
  have h5 : phi6 r₁ r₂ E.φ (sl2W E.F) * b * (phi6 r₁ r₂ E.φ (sl2W E.F))⁻¹ ∈ root 5 := by
    have h := actsPos_weylSix R E hO 0 b (by rw [Rt6_one]; exact hb)
    simpa [Rt6_five] using h
  rw [hWb] at h5
  have h1 := root1_norm R ((root 1).inv_mem hb) hn
  have h1' : b⁻¹ * ((phi6 r₁ r₂ E.φ (sl2U 1) * (phi6 r₁ r₂ E.φ (sl2L (-1)) *
      ⁅phi6 r₁ r₂ E.φ (sl2U 1), b⁆ * (phi6 r₁ r₂ E.φ (sl2L (-1)))⁻¹) *
      (phi6 r₁ r₂ E.φ (sl2U 1))⁻¹ * ⁅phi6 r₁ r₂ E.φ (sl2U 1), b⁆) * b) ∈ Vsub root 2 4 := by
    simpa [mul_assoc] using h1
  have := (rgd2_unique_15 R ((root 1).inv_mem hb) h5 h1').1
  have hb1 : b = 1 := inv_eq_one.1 this
  rw [hb1]; exact Subgroup.one_mem _

theorem short_ndL (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {a : G}
    (ha : a ∈ root 5) (hk : ⁅phi6 r₁ r₂ E.φ (sl2L 1), a⁆ ∈ Vsub root 2 4) :
    a ∈ Vsub root 2 4 := by
  have hll : phi6 r₁ r₂ E.φ (sl2L (-1)) = (phi6 r₁ r₂ E.φ (sl2L 1))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← map_mul, ← sl2L_add, neg_add_cancel, sl2L_zero, map_one]
  have hua : phi6 r₁ r₂ E.φ (sl2U 1) * a * (phi6 r₁ r₂ E.φ (sl2U 1))⁻¹ = a := by
    rw [mul_inv_eq_iff_eq_mul]
    exact commutatorElement_eq_one_iff_mul_comm.1 (short_uA R E hC 1 ha)
  have hl1mem : (phi6 r₁ r₂ E.φ (sl2L 1))⁻¹ ∈ root (-6) :=
    (root (-6)).inv_mem (phi6_L_mem R E 1)
  have hk' : ⁅phi6 r₁ r₂ E.φ (sl2L (-1)), a⁆ ∈ Vsub root 2 4 := by
    have h1 := rootNeg6_norm R hC hl1mem (Subgroup.inv_mem _ hk)
    have e : ⁅phi6 r₁ r₂ E.φ (sl2L (-1)), a⁆ = (phi6 r₁ r₂ E.φ (sl2L 1))⁻¹ *
        (⁅phi6 r₁ r₂ E.φ (sl2L 1), a⁆)⁻¹ * (phi6 r₁ r₂ E.φ (sl2L 1))⁻¹⁻¹ := by
      rw [hll]; simp only [commutatorElement_def]; group
    rw [e]; exact h1
  have hn : phi6 r₁ r₂ E.φ (sl2U 1) * ⁅phi6 r₁ r₂ E.φ (sl2L (-1)), a⁆ *
      (phi6 r₁ r₂ E.φ (sl2U 1))⁻¹ ∈ Vsub root 2 4 := root6_norm hC (phi6_U_mem R E 1) hk'
  have hWa := weyl_conj_eq' (l := phi6 r₁ r₂ E.φ (sl2L (-1))) hua
  rw [← phi6_W E] at hWa
  have h1 : phi6 r₁ r₂ E.φ (sl2W E.F) * a * (phi6 r₁ r₂ E.φ (sl2W E.F))⁻¹ ∈ root 1 := by
    have h := actsPos_weylSix R E hO 4 a (by rw [Rt6_five]; exact ha)
    simpa [Rt6_one] using h
  rw [hWa] at h1
  have h2 : ((phi6 r₁ r₂ E.φ (sl2U 1) * ⁅phi6 r₁ r₂ E.φ (sl2L (-1)), a⁆ *
      (phi6 r₁ r₂ E.φ (sl2U 1))⁻¹) * a) * a⁻¹ ∈ Vsub root 2 4 := by
    simpa [mul_assoc] using hn
  have := (rgd2_unique_15 R h1 ((root 5).inv_mem ha) h2).2
  have ha1 : a = 1 := inv_eq_one.1 this
  rw [ha1]; exact Subgroup.one_mem _

end CFSG.GH74.GLS.Stage4.Hex
