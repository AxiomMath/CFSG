module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type*} [Group G]

theorem conjR_zpowers (s h : G) :
    conjR (Subgroup.zpowers s) h = Subgroup.zpowers (h⁻¹ * s * h) := by
  rw [conjR_def, MonoidHom.map_zpowers]
  simp

theorem relIndex_conjR [Finite G] {S T : Subgroup G} (hST : S ≤ T) (h : G) :
    (conjR S h).relIndex (conjR T h) = S.relIndex T := by
  have h1 := card_eq_mul_of_relIndex hST
  have h2 := card_eq_mul_of_relIndex (conjR_mono hST h)
  rw [card_conjR, card_conjR] at h2
  have hpos : 0 < Nat.card S := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)).symm

end Generic

namespace Lin2Hyp0

section ZNe

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem card_centerOf_R_of_ne_bot (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    Nat.card (centerOf (thompsonJ S)) = 2 ^ (2 * n) := by
  obtain ⟨hZel, hZcard, hZS⟩ := E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl
  rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, hZinf⟩
  · exact absurd hc' hc
  · have hZR : lin2Z L (thompsonJ S) ≤ centerOf (thompsonJ S) :=
      lin2Z_le_centerOf E.h16 hcfg rfl
    have hZxR : conjR (lin2Z L (thompsonJ S)) x ≤ centerOf (thompsonJ S) := by
      rw [hZR2]; exact le_sup_right
    have hcomm : ∀ y ∈ conjR (lin2Z L (thompsonJ S)) x, ∀ z ∈ lin2Z L (thompsonJ S),
        y * z = z * y := fun y hy z hz =>
      (Subgroup.mem_centralizer_iff.1 (hZxR hy).2 z (hZR hz).1).symm
    have hN : lin2Z L (thompsonJ S) ≤
        Subgroup.normalizer (conjR (lin2Z L (thompsonJ S)) x : Set G) :=
      le_normalizer_of_commute hcomm
    have h := card_sup_mul_card_inf hN
    rw [← hZR2, hZinf, Subgroup.card_bot, mul_one, hZcard, card_conjR, hZcard, ← pow_add] at h
    rw [h]
    congr 1
    omega

theorem not_forall_commute_Z (hc : centerOf L ≠ ⊥) {a : G} (haT : a ∈ T)
    (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) :
    ¬ ∀ y ∈ lin2Z L (thompsonJ S), a * y = y * a := by
  intro hall
  by_cases haS : a ∈ S
  · have hRlt : thompsonJ S < S :=
      lt_of_le_of_ne (thompsonJ_le_self S) (fun h => haR (by rw [h]; exact haS))
    have hcard := E.card_Z_inf_centralizer hcfg hRlt (Z := lin2Z L (thompsonJ S)) rfl haS haR ha2
    have hle : lin2Z L (thompsonJ S) ≤
        lin2Z L (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) := fun y hy =>
      ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 (hall y hy).symm⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 := (E.Zbasic hcfg (Z := lin2Z L (thompsonJ S)) rfl).2.1
    rw [hcard, h2] at h1
    have hn := hcfg.one_lt
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show n / 2 < n by omega)
    omega
  · rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl haT haS with ⟨hc', -⟩ | ⟨-, -, hZinf⟩
    · exact hc hc'
    · have hbot : lin2Z L (thompsonJ S) = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have hy' : y ∈ conjR (lin2Z L (thompsonJ S)) a := by
          rw [mem_conjR]
          have : a * y * a⁻¹ = y := by rw [hall y hy]; group
          rw [this]; exact hy
        have : y ∈ lin2Z L (thompsonJ S) ⊓ conjR (lin2Z L (thompsonJ S)) a := ⟨hy, hy'⟩
        rwa [hZinf] at this
      exact lin2Z_ne_bot E.h16 hcfg (Z := lin2Z L (thompsonJ S)) rfl hbot

theorem exists_le_conjR_S_of_le_centralizer (hc : centerOf L ≠ ⊥) {g a : G}
    (ha : a ∈ conjR (lin2Z L (thompsonJ S)) g) (ha1 : a ≠ 1) {P : Subgroup G}
    (hP : P ≤ Subgroup.centralizer ({a} : Set G)) (hP2 : IsPGroup 2 P) :
    ∃ g' : G, conjR (lin2Z L (thompsonJ S)) g' = conjR (lin2Z L (thompsonJ S)) g ∧
      P ≤ conjR S g' := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hTI : fusionIsTI (conjR Z g) := fusionIsTI_conjR (E.ZTI hcfg hZdef) g
  have hNP : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (conjR Z g : Set G) :=
    centralizer_le_normalizer_of_TI hTI ha ha1
  have hPN : conjR P g⁻¹ ≤ Subgroup.normalizer (Z : Set G) := by
    have h1 : P ≤ conjR (Subgroup.normalizer (Z : Set G)) g := by
      rw [← conjR_normalizer]; exact hP.trans hNP
    rw [conjR_le_iff, inv_inv]; exact h1
  obtain ⟨c, hc', hcS⟩ := exists_le_conjR_of_isSylowTwoOf
    (lin2_isSylowTwoOf_normalizer_Z E.h16 hcfg hZdef hc) hPN ((isPGroup_conjR_iff 2).2 hP2)
  refine ⟨c * g, ?_, ?_⟩
  · rw [← conjR_conjR, conjR_eq_of_mem_normalizer hc']
  · have := conjR_mono hcS g
    rwa [conjR_inv_conjR, conjR_conjR] at this

omit [Finite G] E hcfg in
theorem conjR_centerOf_le_centralizer {g w : G} (hw : w ∈ conjR (thompsonJ S) g) :
    conjR (centerOf (thompsonJ S)) g ≤ Subgroup.centralizer ({w} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := mem_conjR.1 hy
  have h2 := mem_conjR.1 hw
  have h3 := Subgroup.mem_centralizer_iff.1 h1.2 _ h2
  calc y * w = g⁻¹ * ((g * y * g⁻¹) * (g * w * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * w * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h3]
    _ = w * y := by group

omit E in
theorem isPGroup_conjR_centerOf (g : G) : IsPGroup 2 ↥(conjR (centerOf (thompsonJ S)) g) :=
  (isPGroup_conjR_iff 2).2 (hcfg.sylowT.isPGroup.to_le
    (inf_le_left.trans ((thompsonJ_le_self S).trans hcfg.S_le_T)))

theorem conjR_centerOf_eq_sup (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S) (g : G) :
    conjR (centerOf (thompsonJ S)) g =
      conjR (lin2Z L (thompsonJ S)) g ⊔ conjR (lin2Z L (thompsonJ S)) (x * g) := by
  rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, -⟩
  · exact absurd hc' hc
  · rw [hZR2, conjR_sup, conjR_conjR]

theorem conjR_centerOf_eq_weakClosure (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    (g : G) :
    conjR (centerOf (thompsonJ S)) g =
        weakClosure (lin2Z L (thompsonJ S)) (conjR (centerOf (thompsonJ S)) g) := by
  have hX := E.conjR_centerOf_eq_sup hcfg hc hx hxS g
  set X := conjR (centerOf (thompsonJ S)) g with hXdef
  have h1 : conjR (lin2Z L (thompsonJ S)) g ≤ X := hX ▸ le_sup_left
  have h2 : conjR (lin2Z L (thompsonJ S)) (x * g) ≤ X := hX ▸ le_sup_right
  apply le_antisymm
  · calc X = conjR (lin2Z L (thompsonJ S)) g ⊔ conjR (lin2Z L (thompsonJ S)) (x * g) := hX
      _ ≤ weakClosure (lin2Z L (thompsonJ S)) X :=
        sup_le (le_weakClosure h1) (le_weakClosure h2)
  · exact weakClosure_le

end ZNe

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
