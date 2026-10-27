module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421B2N
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421B2F
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421ZNeB

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Lin2Hyp0

section B2

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (E : Lin2Hyp0) (hcfg : Lin2Cfg G T M H S L n D)

include E hcfg

theorem false_of_B2_S (hn : n = 2) (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    {a : G} (haS : a ∈ S) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g u : G}
    (hu : u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x) (hg : a = g⁻¹ * u * g) :
    False := by
  have haT : a ∈ T := hcfg.S_le_T haS
  have hnab := E.not_commutative_of_mem_S_ne hcfg hc hx hxS haS haR ha2
  push Not at hnab
  obtain ⟨i, hi, j, hj, hij⟩ := hnab
  have hw1 : ⁅i, j⁆ ≠ 1 := fun h => hij (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hwmem := E.commutator_inf_centralizer_le hcfg a (Subgroup.commutator_mem_commutator hi hj)
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  have hI2 : IsPGroup 2 ↥(thompsonJ S ⊓ Subgroup.centralizer ({a} : Set G)) :=
    hcfg.sylowT.isPGroup.to_le (inf_le_left.trans hRT)
  obtain ⟨m, -, hIT, hRmg⟩ := E.exists_le_conjR_T_of_delta hcfg hc hx hxS hu hg inf_le_right hI2
  have hTT : ⁅conjR T (m * g), conjR T (m * g)⁆ ≤ conjR (thompsonJ S) (m * g) := by
    rw [← conjR_commutator]
    exact conjR_mono (E.commutator_T_le_R hcfg hn) _
  have hwN : ⁅i, j⁆ ∈ conjR (thompsonJ S) g := by
    rw [← hRmg]
    exact hTT (Subgroup.commutator_mem_commutator (hIT hi) (hIT hj))
  exact E.false_of_ZLne1_B_end hcfg hc hx hxS haT haR ha2 hu hg hwmem.1 hwN hw1

theorem false_of_B2_T (hn : n = 2) (hc : centerOf L ≠ ⊥) {x : G} (hx : x ∈ T) (hxS : x ∉ S)
    {a : G} (haT : a ∈ T) (haR : a ∉ thompsonJ S) (ha2 : a ^ 2 = 1) {g u : G}
    (hu : u ∈ lin2Delta (thompsonJ S) (lin2Z L (thompsonJ S)) x) (hg : a = g⁻¹ * u * g) :
    False := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  have hRT : thompsonJ S ≤ T := (thompsonJ_le_self S).trans hcfg.S_le_T
  set Ea := centerOf (thompsonJ S) ⊓ Subgroup.centralizer ({a} : Set G) with hEa
  have hEael : IsElemAbelian 2 Ea :=
    IsElemAbelian.mono inf_le_left (E.centerOf_R_isElemAbelian hcfg)
  have hnorm : ∀ v ∈ centerOf (thompsonJ S), a * v * a⁻¹ ∈ centerOf (thompsonJ S) := by
    intro v hv
    have h1 := centerOf_normalized (E.TnR hcfg haT)
    have : v ∈ conjR (centerOf (thompsonJ S)) a := by rw [h1]; exact hv
    exact mem_conjR.1 this
  have hcardEa : 2 ^ n ≤ Nat.card Ea := by
    have h1 := card_le_sq_card_centralizer (E.centerOf_R_isElemAbelian hcfg) hnorm ha2
    rw [E.card_centerOf_R_of_ne_bot hcfg hc hx hxS,
      show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm]] at h1
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h1
  have hn2 : 2 < Nat.card Ea := by
    have : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by have := hcfg.one_lt; omega)
    omega
  have hEa2 : IsPGroup 2 ↥Ea :=
    hcfg.sylowT.isPGroup.to_le (inf_le_left.trans (inf_le_left.trans hRT))
  obtain ⟨m, -, hEaT, hRmg⟩ := E.exists_le_conjR_T_of_delta hcfg hc hx hxS hu hg inf_le_right hEa2
  by_cases hbot : Ea ⊓ conjR (thompsonJ S) g = ⊥
  ·
    have hidx : (conjR S (m * g)).relIndex (conjR T (m * g)) = 2 := by
      rw [relIndex_conjR hcfg.S_le_T, E.idxTS hcfg]
    have hone := one_lt_card_inf_of_relIndex_two hEaT hidx hn2
    have hne : Ea ⊓ conjR S (m * g) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hone
      omega
    obtain ⟨⟨e₀, he₀⟩, he₁'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have he₁ : e₀ ≠ 1 := fun h => he₁' (Subtype.ext h)
    have he₀R : e₀ ∈ centerOf (thompsonJ S) := he₀.1.1
    have he₀2 : e₀ ^ 2 = 1 := hEael.2 e₀ he₀.1
    have ha'S : (m * g) * e₀ * (m * g)⁻¹ ∈ S := mem_conjR.1 he₀.2
    have ha'R : (m * g) * e₀ * (m * g)⁻¹ ∉ thompsonJ S := by
      intro h
      have h1 : e₀ ∈ conjR (thompsonJ S) (m * g) := mem_conjR.2 h
      rw [hRmg] at h1
      have : e₀ ∈ Ea ⊓ conjR (thompsonJ S) g := ⟨he₀.1, h1⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact he₁ this
    have ha'2 : ((m * g) * e₀ * (m * g)⁻¹) ^ 2 = 1 := by
      have : ((m * g) * e₀ * (m * g)⁻¹) ^ 2 = (m * g) * e₀ ^ 2 * (m * g)⁻¹ := by
        simp only [pow_two]; group
      rw [this, he₀2]; group
    have ha'g : (m * g) * e₀ * (m * g)⁻¹ = ((m * g)⁻¹)⁻¹ * e₀ * (m * g)⁻¹ := by rw [inv_inv]
    by_cases hwZ : e₀ ∈ Z
    · exact E.false_of_ZLne1_A hcfg hc hx hxS (hcfg.S_le_T ha'S) ha'R ha'2 hwZ ha'g
    · by_cases hwZx : e₀ ∈ conjR Z x
      · have hz : x * e₀ * x⁻¹ ∈ Z := mem_conjR.1 hwZx
        refine E.false_of_ZLne1_A hcfg hc hx hxS (hcfg.S_le_T ha'S) ha'R ha'2 hz
          (g := x * (m * g)⁻¹) ?_
        rw [ha'g]; group
      · refine E.false_of_B2_S hcfg hn hc hx hxS ha'S ha'R ha'2 (g := (m * g)⁻¹) (u := e₀)
          ⟨he₀R, hwZ, hwZx⟩ ha'g
  · obtain ⟨⟨w, hw⟩, hw1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    have hw1 : w ≠ 1 := fun h => hw1' (Subtype.ext h)
    exact E.false_of_ZLne1_B_end hcfg hc hx hxS haT haR ha2 hu hg hw.1.1 hw.2 hw1

end B2

end Lin2Hyp0

theorem lemma2421B2_of_hyp0 (E : Lin2Hyp0) : Lemma2421B2 := by
  intro G _ _ T M H S L D n hcfg hc hn x hx hxS a haT haR ha2 g u hu hg
  by_cases haS : a ∈ S
  · exact E.false_of_B2_S hcfg hn hc hx hxS haS haR ha2 hu hg
  · exact E.false_of_B2_T hcfg hn hc hx hxS haT haR ha2 hu hg

end CFSG.QuasithinUnique.Lin2
