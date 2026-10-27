module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3End
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3LinRec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qUConcl_of_linear_prime {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hF : FieldOn p b S) {labK : GLALabel}
    (hkind : FieldKind (PSimple p S) labK (indAut p S b hF.1)) {m : ℕ} (hm2 : 2 ≤ m)
    (hpm : p ∣ 2 ^ m - 1) (hcan : canonLabel labK = ⟨.A, p - 1, p * m⟩) : QUConcl p S B x b := by
  classical
  have hp : p.Prime := cfg.prime
  have hp2 : p ≠ 2 := cfg.odd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp cfg.comp
  have hcen : Subgroup.center (PSimple p S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨K, _, _, d, -, hKcard, -, hrank, A, σ, u, e, heu, hu, hσ⟩ :=
    Y10GFldLinMark.fieldKind_linear_data hcen (K155X.famLin_of_canon hcan) hkind
  rw [hcan] at hKcard hrank
  have hd : d = p := by
    have h : p - 1 + 1 = d := hrank
    omega
  clear hrank
  subst d
  have hK : Nat.card K = 2 ^ (p * m) := hKcard
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hαL := S265F3.congr_not_mem_linearAutGroup hp3 A hσ e heu hu
  have hinv : chevAut p S ⟨b, hF.1⟩ = (indAut p S b hF.1)⁻¹ := by
    have h : indAut p S b hF.1 = (chevAut p S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h, inv_inv]
  have hβL : MulAut.congr (e.trans (CFSG.StandardType.TypeA.recipeEquiv p K))
      (chevAut p S ⟨b, hF.1⟩) ∉ linearAutGroup p K := by
    rw [hinv, map_inv, inv_mem_iff]
    exact hαL
  have hβp : chevAut p S ⟨b, hF.1⟩ ^ p = 1 := chevAut_pow_eq_one p S hF.1 (cfg.elem.2 b cfg.hb)
  have he1 : 1 ≤ p * m := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hp.ne_zero (by omega))
  have hpe : p ∣ 2 ^ (p * m / p) - 1 := by
    rw [Nat.mul_div_cancel_left m hp.pos]
    exact hpm
  refine S265F3.qUConcl_of_model cfg hF.1 ?_
  intro Eb hEp hEcomm hpE t ht hEt
  exact exists_layer_of_linear_model_prime hp hp2 he1 hK hpe
    (e.trans (CFSG.StandardType.TypeA.recipeEquiv p K)) hβp hβL Eb hEp hEcomm hpE ht hEt

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
