module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3End
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Uni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3UniRec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind FamUni)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedProjEquivPrimeFormP)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem label_eq_of_canon_twA {lab : GLALabel} {k : ℕ}
    (h : canonLabel lab = ⟨.twA, 2, k⟩) : lab = ⟨.twA, 2, k⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  by_cases h3 : rank = 3 <;> by_cases h2 : rank = 2 <;> cases tag <;> simp_all [canonLabel]

theorem qUConcl_of_unitary {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg 3 S B T x b)
    (hF : FieldOn 3 b S) {labK : GLALabel}
    (hkind : FieldKind (PSimple 3 S) labK (indAut 3 S b hF.1)) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hcan : canonLabel labK = ⟨.twA, 2, 3 * m⟩) : QUConcl 3 S B x b := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp3 cfg.comp
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  have hFam : FamUni labK := Or.inl (by rw [label_eq_of_canon_twA hcan])
  obtain ⟨K, _, _, d, τ, hτ, hτq, hKcard, -, -, -, hrank, hnK, A, σ, u, e, hA, heu, hu, hσ⟩ :=
    Y10GFldUniMark.fieldKind_unitary_data hcen hFam hkind
  rw [hcan] at hrank hnK
  have hd : d = 3 := by
    have h : 2 + 1 = d := hrank
    omega
  subst hd
  have hn : labK.n = 3 * m := hnK.symm
  have hf : Odd labK.n := by
    rw [hn]
    exact Nat.odd_mul.2 ⟨⟨1, by norm_num⟩, hm⟩
  have hf1 : labK.n ≠ 1 := by omega
  have hf3 : labK.n ≠ 3 := by omega
  have h : UnitaryFieldData 2 labK.n K :=
    ⟨Nat.prime_two, by omega, by rw [hKcard, ← pow_mul, Nat.mul_comm]⟩
  haveI : CharP K 2 := h.charP
  have hq3 : ¬(3 = 3 ∧ 2 ^ labK.n = 2) := fun h' =>
    hf1 (Nat.pow_right_injective le_rfl (h'.2.trans (pow_one 2).symm))
  have hαD := congr_not_mem_primeFormD h le_rfl hq3 hτq hA hσ e heu hu
  have hinv : chevAut 3 S ⟨b, hF.1⟩ = (indAut 3 S b hF.1)⁻¹ := by
    have h' : indAut 3 S b hF.1 = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h', inv_inv]
  have hβD : MulAut.congr (e.trans (statedProjEquivPrimeFormP h (by norm_num : 1 ≤ 3)))
      (chevAut 3 S ⟨b, hF.1⟩) ∉ primeFormD h (idGram K 3) := by
    rw [hinv, map_inv, inv_mem_iff]
    exact hαD
  have hβ3 : chevAut 3 S ⟨b, hF.1⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 S hF.1 (cfg.elem.2 b cfg.hb)
  refine qUConcl_of_model cfg hF.1 ?_
  intro Eb hE3 hEcomm h9 t ht hEt
  exact exists_layer_of_unitary_model h hf hf1 hf3
    (e.trans (statedProjEquivPrimeFormP h (by norm_num : 1 ≤ 3))) hβ3 hβD Eb hE3 hEcomm
    ((show (9 : ℕ) = 3 ^ 2 by norm_num).trans_le h9) ht hEt

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
