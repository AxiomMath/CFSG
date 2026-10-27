module

public import CFSG.Quasithin.H13.L32NLem14332a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14332

variable {G : Type} [Group G]

theorem conj_zU_le_F4 [CFSG.GH74.QTGen4.Finite4 G] (h12813 : Lemma12_8_13_F4) {T L V V₂ : Subgroup G} {g : G}
    (hs : Setting1282One G T L V 3 (fsuV1 T V) V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) :
    CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V := by
  obtain ⟨-, h2, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  exact (h2.trans (Subgroup.centralizer_le (inf_le_left : fsuV1 T V ≤ V))).trans
    (Subgroup.centralizer_le_normalizer _)

theorem card_img_conj_zU_F4 [CFSG.GH74.QTGen4.Finite4 G] (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4)
    {T L V V₂ : Subgroup G} {g : G} (hs : Setting1282One G T L V 3 (fsuV1 T V) V₂)
    (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (hZ : centerOf (i128 T L V (fsuV1 T V)) = ⊥) (hV1Z : fsuV1 T V ≤ centerOf (fsuU T V))
    (hV1 : Nat.card ↥(fsuV1 T V) = 2) (D : HatModelU (fsuU T V)) :
    Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) * 2 =
      Nat.card ↥(centerOf (fsuU T V)) := by
  obtain ⟨-, -, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := h6
  have heq : CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) =
        CFSG.conjugate (fsuV1 T V) g := by
    rw [e1, e2, e3, e4, e5, hZ, bot_sup_eq]
  have hle := conj_zU_le_F4 h12813 hs hgP hgN
  have hN : CFSG.conjugate (centerOf (fsuU T V)) g ≤
      Subgroup.normalizer (fsuU T V : Set G) := hle.trans (l32nH_le_normalizer_fsuU T V)
  have hker : ∀ x ∈ CFSG.conjugate (centerOf (fsuU T V)) g,
      (∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨x, hxN⟩ = 1) ↔
        x ∈ CFSG.conjugate (fsuV1 T V) g := by
    intro x hx
    rw [← heq]
    constructor
    · rintro ⟨hxN, h1⟩
      refine Subgroup.mem_inf.mpr ⟨hx, hle hx,
        normalizer_le_normalizer_centerOf _ hxN, fun u hu => ?_⟩
      exact (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1 u hu
    · intro h1
      obtain ⟨-, ⟨-, -, h2⟩⟩ := Subgroup.mem_inf.mp h1
      exact ⟨hN hx, (L128A.HatU.rho_eq_one_iff D ⟨x, hN hx⟩).mpr h2⟩
  rw [L128A.HatU.card_img_eq_relIndex D hN hker]
  have hle1 : CFSG.conjugate (fsuV1 T V) g ≤ CFSG.conjugate (centerOf (fsuU T V)) g :=
    Subgroup.map_mono hV1Z
  have h1 := Subgroup.relIndex_mul_card (H := CFSG.conjugate (fsuV1 T V) g)
    (K := CFSG.conjugate (centerOf (fsuU T V)) g)
  rw [inf_eq_left.mpr hle1] at h1
  rw [CFSG.conjugate, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hV1] at h1
  exact h1

variable {T V V₂ : Subgroup G} (D : HatModelU (fsuU T V))

end L14332

end CFSG.Quasithin.H13
