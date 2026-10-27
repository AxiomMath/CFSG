module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Cfg

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.exists_mem_T_not_mem_S (h : Lin2Cfg G T M H S L n D) : ∃ x ∈ T, x ∉ S := by
  by_contra hcon
  exact h.S_ne_T (le_antisymm h.S_le_T fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩)

theorem Lin2Cfg.four_le_two_pow (h : Lin2Cfg G T M H S L n D) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_lt

theorem Lin2Cfg.D_le_M (h : Lin2Cfg G T M H S L n D) : D ≤ M := h.hall.1.trans inf_le_right

theorem Lin2Cfg.D_le_L (h : Lin2Cfg G T M H S L n D) : D ≤ L := h.hall.1.trans inf_le_left

theorem Lin2Cfg.B_le_M (h : Lin2Cfg G T M H S L n D) {B : Subgroup G}
    (hB : Lin2BProps T S (thompsonJ S) D B) : B ≤ M :=
  hB.2.1.1.trans (sup_le h.T_le_M h.D_le_M)

end Cfg

theorem le_normalizer_centerOf {G : Type*} [Group G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer ((centerOf X : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjR_eq_self_iff, conjR_centerOf, conjR_eq_of_mem hg]

section Cfg2

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.H_le_normalizer_centerOf (h : Lin2Cfg G T M H S L n D) :
    H ≤ Subgroup.normalizer ((centerOf L : Subgroup G) : Set G) := by
  rw [h.H_eq]
  refine sup_le (le_normalizer_centerOf L) (fun g hg => ?_)
  rw [← conjR_eq_self_iff, conjR_centerOf, conjR_eq_of_mem_normalizer (h.S_le_normalizer hg)]

end Cfg2

theorem lin2Z_cases {G : Type*} [Group G] {L R Z : Subgroup G} (hZ : Z = lin2Z L R) :
    (centerOf L = ⊥ ∧ Z = centerOf R) ∨ (centerOf L ≠ ⊥ ∧ Z = centerOf L) := by
  by_cases hc : centerOf L = ⊥
  · left; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩
  · right; exact ⟨hc, by simp [hZ, lin2Z, hc]⟩

section FromLemma2416

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem lin2Z_le_centerOf (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) : Z ≤ centerOf (thompsonJ S) := by
  obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨-, hZ2, -⟩ := h16 G T M H S L D n hcfg Z hZ
  rcases hZ2 x₀ hx₀T hx₀S with ⟨-, -, hZe⟩ | ⟨-, hZR2, -⟩
  · exact hZe.le
  · rw [hZR2]; exact le_sup_left

theorem lin2Z_ne_bot (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) : Z ≠ ⊥ := by
  obtain ⟨⟨-, hZcard, -⟩, -, -⟩ := h16 G T M H S L D n hcfg Z hZ
  intro h
  have h1 : Nat.card Z = 1 := by rw [h]; exact Subgroup.card_bot
  rw [hZcard] at h1
  have := hcfg.four_le_two_pow
  omega

theorem lin2Z_centralized (h16 : Lemma2_4_16) (hcfg : Lin2Cfg G T M H S L n D) {Z : Subgroup G}
    (hZ : Z = lin2Z L (thompsonJ S)) : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 (lin2Z_le_centerOf h16 hcfg hZ hz).2 r hr).symm

end FromLemma2416

end CFSG.QuasithinUnique.Lin2
