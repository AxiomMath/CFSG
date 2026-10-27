module

public import CFSG.GH74.GLS.Stage4.HexCData
public import CFSG.GH74.GLS.Stage4.HexCShort4

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem hexData_exists_phi (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 4)
    (E₁ : SL2Pos H R.N root 1) (hC : Hex6Comm root)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {q : ℕ}
    (hq : RootOrdersG2 root q) (hqodd : Odd q) :
    ∃ D : HexData root E.F, D.φ = phi6 r₁ r₂ E.φ := by
  have hcardE : Nat.card E.F = q := by
    rw [← E.toRankOneAt.card_root]; exact hq 4 (by norm_num) (by norm_num)
  obtain ⟨x₂, x₄, h2add, h2inj, h2mem, h2surj, h4add, h4inj, h4mem, h4surj, hrel, hw2, hw4⟩ :=
    long_coords R E (by rw [hcardE]; exact hqodd) hO hC.l24 hC.l46 hC.l26
      (hC.ab 4 (by norm_num) (by norm_num)) (hC.ab 2 (by norm_num) (by norm_num))
  obtain ⟨x₁, x₅, h1add, h1inj, h1mem, h1surj, h5add, h5inj, h5mem, h5surj, hrel', hw1, hw5⟩ :=
    short_coords R E E₁ hC hO hq hqodd
  refine ⟨{ φ := phi6 r₁ r₂ E.φ
            T := fun t => phi6 r₁ r₂ E.φ (sl2D t)
            p1 := x₁, p2 := x₂, p4 := x₄, p5 := x₅, p6 := fun c => phi6 r₁ r₂ E.φ (sl2U c)
            T_eq := fun t => rfl, p6_eq := fun c => rfl
            cent3 := fun g u hu => phi6_cent3 R E hC hu g
            T_mul := fun t t' => by rw [sl2D_mul, map_mul]
            p1_add := h1add, p2_add := h2add, p4_add := h4add, p5_add := h5add
            p6_add := fun c d => by rw [sl2U_add, map_mul]
            p1_inj := h1inj, p2_inj := h2inj, p4_inj := h4inj, p5_inj := h5inj
            p6_inj := fun c d h => sl2U_injective (phi6_injective E h)
            p1_mem := h1mem, p2_mem := h2mem, p4_mem := h4mem, p5_mem := h5mem
            p6_mem := phi6_U_mem R E
            p1_surj := h1surj, p2_surj := h2surj, p4_surj := h4surj, p5_surj := h5surj
            p6_surj := fun b hb => phi6_U_surj R E hb
            rel_long := hrel, rel_short := hrel', w1 := hw1, w2 := hw2, w4 := hw4, w5 := hw5
            w6 := phi6_w6 E }, rfl⟩

end CFSG.GH74.GLS.Stage4.Hex
