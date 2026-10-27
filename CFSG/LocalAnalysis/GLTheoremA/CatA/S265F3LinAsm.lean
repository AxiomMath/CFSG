module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3End
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3LinRec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qUConcl_of_linear {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg 3 S B T x b)
    (hF : FieldOn 3 b S) {labK : GLALabel}
    (hkind : FieldKind (PSimple 3 S) labK (indAut 3 S b hF.1)) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hcan : canonLabel labK = ⟨.A, 2, 3 * m⟩) : QUConcl 3 S B x b := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp3 cfg.comp
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨K, _, _, d, -, hKcard, -, hrank, A, σ, u, e, heu, hu, hσ⟩ :=
    Y10GFldLinMark.fieldKind_linear_data hcen (K155X.famLin_of_canon hcan) hkind
  rw [hcan] at hKcard hrank
  have hd : d = 3 := by
    have h : 2 + 1 = d := hrank
    omega
  subst hd
  have hK : Nat.card K = 2 ^ (3 * m) := hKcard
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hαL := congr_not_mem_linearAutGroup le_rfl A hσ e heu hu
  have hinv : chevAut 3 S ⟨b, hF.1⟩ = (indAut 3 S b hF.1)⁻¹ := by
    have h : indAut 3 S b hF.1 = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h, inv_inv]
  have hβL : MulAut.congr (e.trans (CFSG.StandardType.TypeA.recipeEquiv 3 K))
      (chevAut 3 S ⟨b, hF.1⟩) ∉ linearAutGroup 3 K := by
    rw [hinv, map_inv, inv_mem_iff]
    exact hαL
  have hβ3 : chevAut 3 S ⟨b, hF.1⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 S hF.1 (cfg.elem.2 b cfg.hb)
  refine qUConcl_of_model cfg hF.1 ?_
  intro Eb hE3 hEcomm h9 t ht hEt
  exact exists_layer_of_linear_model (hm.mul_left 3) (by omega) hK
    (e.trans (CFSG.StandardType.TypeA.recipeEquiv 3 K)) hβ3 hβL Eb hE3 hEcomm
    ((show (9 : ℕ) = 3 ^ 2 by norm_num).trans_le h9) ht hEt

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
