module

public import CFSG.Quasithin.Vol2.Ch12Sec4MParam
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Cx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem mParam1244_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (h12210 : Stmt12_2_10_F4) (hG2 : G2MParamFact1244) : MParam1244_F4 := by
  intro G _ _ T L V hcx hq
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx hq
  have := hf.comm
  refine ⟨hf.isElemAbelian, ?_⟩
  have hW2 : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)

  have hM : autOn (⊤ : Subgroup G) V = autOn L V ⊔ autOn T V := by
    have h1 : autOn (⊤ : Subgroup G) V = hyp.MVbar := by
      show autOn (⊤ : Subgroup G) V =
        autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V
      rw [hf.MN, inf_idem]
      unfold autOn
      rw [Subgroup.top_subgroupOf, Subgroup.subgroupOf_self]
    rw [h1, (h12210 G T L V hyp).2.2]
  have hsup : autOn (L ⊔ T) V = autOn L V ⊔ autOn T V := by
    unfold autOn
    rw [Subgroup.subgroupOf_sup hf.normalizes hf.T_le, Subgroup.map_sup]
  have hcommGr := commV_autOn_eq_top hf.normalizes hf.commutator
  change E3.mParam (autOn (⊤ : Subgroup G) V) = 2
  rcases hq with h3 | hU
  ·
    obtain ⟨hV16, -, hGr, hnat⟩ := cx_l3_module_F4 h1222 hcx hf h3
    obtain ⟨-, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
    have hML : autOn (⊤ : Subgroup G) V = autOn L V := by
      rw [hM, hTeq]
      exact sup_eq_left.2 (A4.autOn_mono inf_le_right)
    obtain ⟨D⟩ := hnat.toL3Coord
    have h16 : Nat.card ↥V = 16 := by rw [hV16]; norm_num
    have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
    obtain ⟨-, -, -, h4⟩ := B4_8_2 hW2 h16 hnat hind
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hrk : ∀ t ∈ autOn L V, orderOf t = 2 → rkIdx (fixV (Subgroup.zpowers t)) = 2 := by
      intro t ht hto
      have ht1 : t ≠ 1 := fun h => by
        rw [h, orderOf_one] at hto
        norm_num at hto
      have ht2 : t ^ 2 = 1 := by rw [← hto, pow_orderOf_eq_one]
      obtain ⟨-, hr⟩ := h4 t ht ht1 ht2
      have hF : Nat.card ↥(fixV (Subgroup.zpowers t)) = 4 := by
        rw [card_eq_two_pow hW2, hr]
        norm_num
      have hidx := (fixV (Subgroup.zpowers t)).card_mul_index
      rw [hF, h16] at hidx
      have h4' : (fixV (Subgroup.zpowers t)).index = 4 := by omega
      unfold rkIdx
      rw [h4', show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    rw [hML]
    unfold E3.mParam
    have hev : Even (Nat.card ↥(autOn L V)) := by
      rw [hGr]
      exact ⟨84, by norm_num⟩
    rw [ite_eq_left hev]
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autOn L V)) 2
      (even_iff_two_dvd.1 hev)
    have hto : orderOf (t : MulAut ↥V) = 2 := by rw [Subgroup.orderOf_coe, ht]
    have ht2 := hrk t t.2 hto
    refine le_antisymm (Nat.sInf_le ⟨t, t.2, hto, ht2.symm⟩)
      (le_csInf ⟨2, t, t.2, hto, ht2.symm⟩ ?_)
    rintro _ ⟨s, hs, hso, rfl⟩
    exact (hrk s hs hso).ge
  ·
    obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223_F4 h1222 hyp
    have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
      rw [fixV_autOn_eq hf.normalizes]
      exact hcases.2.1 hU
    have hfix : Nat.card (fixV (autOn L V)) = 2 := by
      rw [fixV_autOn_eq hf.normalizes, card_subgroupOf_eq_card_inf, hf.card_zV]
    have hX2 : ∀ x ∈ autOn (L ⊔ T) V, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn L V :=
      InternalSec.autOn_two_of hf.normalizes fun y hy => by
        obtain ⟨k, hk⟩ := E6.exists_pow_mem_of_mem_sup hyp.sylow.1 hyp.normalizes hy
        exact ⟨k, le_sup_left (b := Subgroup.centralizer (V : Set G)) hk⟩
    rw [hM]
    refine hG2 ↥V hW2 (autOn L V ⊔ autOn T V) (autOn L V) le_sup_left
      (sup_le Subgroup.le_normalizer (autOn_le_normalizer_autOn_of_le hyp.normalizes))
      (fun x hx => hX2 x (by rw [hsup]; exact hx)) hcommGr hfix hnat

end CFSG.Quasithin.H13
