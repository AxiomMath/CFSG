module

public import CFSG.GH74.GLS.Stage4.HexCD4Tower
public import CFSG.GH74.GLS.Stage4.HexCData

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

structure HexData4 (root : ℤ → Subgroup G) (F K : Type) [Field F] [Field K] where
  θ : F →+* K
  φ : SL2 F →* G
  T : Fˣ → G
  T₁ : Kˣ → G
  p1 : K → G
  p2 : F → G
  p4 : F → G
  p5 : K → G
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
  rel_short : ∀ c s, (p5 (θ c * s))⁻¹ * ⁅p6 c, p1 s⁆ ∈ Vsub root 2 4
  w1 : ∀ (t : Fˣ) s, T t * p1 s * (T t)⁻¹ = p1 ((θ (t : F))⁻¹ * s)
  w2 : ∀ (t : Fˣ) d, T t * p2 d * (T t)⁻¹ = p2 ((t : F)⁻¹ * d)
  w4 : ∀ (t : Fˣ) d, T t * p4 d * (T t)⁻¹ = p4 ((t : F) * d)
  w5 : ∀ (t : Fˣ) s, T t * p5 s * (T t)⁻¹ = p5 (θ (t : F) * s)
  w6 : ∀ (t : Fˣ) d, T t * p6 d * (T t)⁻¹ = p6 ((t : F) ^ 2 * d)
  T₁_mul : ∀ ρ ρ', T₁ (ρ * ρ') = T₁ ρ * T₁ ρ'
  T₁_comm : ∀ (ρ : Kˣ) (t : Fˣ), T₁ ρ * T t = T t * T₁ ρ
  T₁_cent4 : ∀ (ρ : Kˣ), ∀ x ∈ root 4, T₁ ρ * x = x * T₁ ρ
  T₁_norm : ∀ (ρ : Kˣ) (i : ℤ), 1 ≤ i → i ≤ 6 → ∀ x ∈ root i, T₁ ρ * x * (T₁ ρ)⁻¹ ∈ root i
  w1' : ∀ (ρ : Kˣ) s, T₁ ρ * p1 s * (T₁ ρ)⁻¹ = p1 ((ρ : K) ^ 2 * s)

theorem hexData4_exists_phi (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (E₁ : SL2Pos H R.N root 1) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {q : ℕ}
    (hq : RootOrdersD4a root q) (hqodd : Odd q) :
    ∃ D : HexData4 root E.F E₁.F, D.φ = phi6 r₁ r₂ E.φ ∧ (∀ s, D.p1 s = E₁.φ (sl2U s)) ∧
      ∀ ρ, D.T₁ ρ = E₁.φ (sl2D ρ) := by
  have hcardE : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]
    have := hq 4 (by norm_num) (by norm_num)
    simpa using this
  obtain ⟨x₂, x₄, h2add, h2inj, h2mem, h2surj, h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩ :=
    long_coords R E (by rw [hcardE]; exact hqodd) hO hC.l24 hC.l46 hC.l26
      (hC.ab 4 (by norm_num) (by norm_num)) (hC.ab 2 (by norm_num) (by norm_num))
  obtain ⟨θ, x₅, h5add, h5inj, h5mem, h5surj, hrel', hw1, hw5⟩ :=
    short_coordsK R E E₁ hC hO hq hqodd
  have hT₁H : ∀ ρ : E₁.Fˣ, E₁.φ (sl2D ρ) ∈ H := E₁.hD
  have hT₁S : ∀ ρ : E₁.Fˣ, E₁.φ (sl2D ρ) ∈ root 1 ⊔ root (-1) := fun ρ =>
    sl2_hom_mem E₁.φ (root 1 ⊔ root (-1))
      (fun c => Subgroup.mem_sup_left (sl2Pos_U_mem E₁ c))
      (fun c => Subgroup.mem_sup_right (sl2Pos_L_mem E₁ c)) (sl2D ρ)
  refine ⟨{ θ := θ
            φ := phi6 r₁ r₂ E.φ
            T := fun t => phi6 r₁ r₂ E.φ (sl2D t)
            T₁ := fun ρ => E₁.φ (sl2D ρ)
            p1 := fun s => E₁.φ (sl2U s), p2 := x₂, p4 := x₄, p5 := x₅,
            p6 := fun c => phi6 r₁ r₂ E.φ (sl2U c)
            T_eq := fun t => rfl, p6_eq := fun c => rfl
            cent3 := fun g u hu => phi6_cent3 R E hC hu g
            T_mul := fun t t' => by rw [sl2D_mul, map_mul]
            p1_add := fun c d => by rw [sl2U_add, map_mul]
            p2_add := h2add, p4_add := h4add, p5_add := h5add
            p6_add := fun c d => by rw [sl2U_add, map_mul]
            p1_inj := fun c d h => sl2U_injective (E₁.inj h)
            p2_inj := h2inj, p4_inj := h4inj, p5_inj := h5inj
            p6_inj := fun c d h => sl2U_injective (phi6_injective E h)
            p1_mem := fun d => sl2Pos_U_mem E₁ d
            p2_mem := h2mem, p4_mem := h4mem, p5_mem := h5mem
            p6_mem := phi6_U_mem R E
            p1_surj := fun b hb => (E₁.hU b).1 hb
            p2_surj := h2surj, p4_surj := h4surj, p5_surj := h5surj
            p6_surj := fun b hb => phi6_U_surj R E hb
            rel_long := hrel, rel_short := hrel', w1 := hw1, w2 := hw2, w4 := hw4, w5 := hw5
            w6 := phi6_w6 E
            T₁_mul := fun ρ ρ' => by rw [sl2D_mul, map_mul]
            T₁_comm := fun ρ t => R.comm_H _ (hT₁H ρ) _ (phi6_D_mem R E t)
            T₁_cent4 := fun ρ x hx => hO _ (hT₁S ρ) x (Subgroup.mem_sup_left hx)
            T₁_norm := fun ρ i hi1 hi6 x hx =>
              R.invariant i (isRoot_of_pos_le hi1 hi6) _ (hT₁H ρ) x hx
            w1' := fun ρ s => by
              rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, sl2D_mul_sl2U_eq] }, rfl,
    fun s => rfl, fun ρ => rfl⟩

end CFSG.GH74.GLS.Stage4.Hex
