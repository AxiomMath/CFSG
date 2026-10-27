module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

namespace Lin2Hyp0

section LQ1

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem AT {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    ∀ A : Subgroup G, IsMaxElemAbelian T A ↔ A = blockU L ∨ A = conjR (blockU L) x :=
  ((E.h8 G T M H S L D n hcfg).2.2.1.2.2 x hx hxS).2.2.2

theorem conjR_R_le_R_of_le_T {g : G} (h : conjR (thompsonJ S) g ≤ T) :
    conjR (thompsonJ S) g ≤ thompsonJ S := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have h19 : thompsonJ S = weakClosure Z T := E.h19 G T M H S L D n hcfg Z hZdef
  have hZR : Z ≤ thompsonJ S := (lin2Z_le_centerOf E.h16 hcfg hZdef).trans inf_le_left
  rw [conjR_le_iff]
  conv_lhs => rw [h19]
  refine iSup₂_le fun y hy => ?_
  rw [← conjR_le_iff]
  have h1 : conjR Z y ≤ thompsonJ S := h19 ▸ le_weakClosure hy
  have h2 : conjR (conjR Z y) g ≤ T := (conjR_mono h1 g).trans h
  rw [conjR_conjR] at h2 ⊢
  exact h19 ▸ le_weakClosure h2

theorem conjR_R_eq_of_le_T {g : G} (h : conjR (thompsonJ S) g ≤ T) :
    conjR (thompsonJ S) g = thompsonJ S := by
  have h1 := E.conjR_R_le_R_of_le_T hcfg h
  exact eq_of_le_of_card_le' h1 (by rw [card_conjR])

theorem card_R_of_eq_bot (hc : centerOf L = ⊥) : Nat.card (thompsonJ S) = 2 ^ (3 * n) := by
  have h1 := lin2_card_sylow hcfg.lin2 (E.Rsyl hcfg)
  rw [E.OL hcfg, E.card_U' hcfg, hc, Subgroup.card_bot, mul_one, ← pow_add] at h1
  rw [h1]
  congr 1
  omega

theorem card_le_card_U_of_isElemAbelian {x : G} (hx : x ∈ T) (hxS : x ∉ S) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) : Nat.card B ≤ Nat.card (blockU L) := by
  have hB2 : IsPGroup 2 B := fun y => ⟨1, Subtype.ext (by simpa using hB.2 y y.2)⟩
  obtain ⟨d, -, hd⟩ := exists_le_conjR_of_isSylowTwoOf hcfg.sylowT (le_top : B ≤ ⊤) hB2
  have hU : IsMaxElemAbelian T (blockU L) := (E.AT hcfg hx hxS _).2 (Or.inl rfl)
  have hle : conjR B d⁻¹ ≤ T := by
    rw [conjR_le_iff, inv_inv]; exact hd
  have := hU.2.2 (conjR B d⁻¹) hle ((isElemAbelian_conjR_iff B d⁻¹).2 hB)
  rwa [card_conjR] at this

theorem eq_or_eq_of_card_eq_of_le_conjR_T {x : G} (hx : x ∈ T) (hxS : x ∉ S) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hcard : Nat.card B = Nat.card (blockU L)) {m : G}
    (hBT : B ≤ conjR T m) :
    B = conjR (blockU L) m ∨ B = conjR (conjR (blockU L) x) m := by
  have hle : conjR B m⁻¹ ≤ T := by
    rw [conjR_le_iff, inv_inv]; exact hBT
  have hmax : IsMaxElemAbelian T (conjR B m⁻¹) := by
    refine ⟨hle, (isElemAbelian_conjR_iff B m⁻¹).2 hB, fun B' hB'T hB'e => ?_⟩
    have hU : IsMaxElemAbelian T (blockU L) := (E.AT hcfg hx hxS _).2 (Or.inl rfl)
    rw [card_conjR, hcard]
    exact hU.2.2 B' hB'T hB'e
  rcases (E.AT hcfg hx hxS _).1 hmax with h | h
  · left
    rw [← h, conjR_inv_conjR]
  · right
    rw [← h, conjR_inv_conjR]

end LQ1

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
