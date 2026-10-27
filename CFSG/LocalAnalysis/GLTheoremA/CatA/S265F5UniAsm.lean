module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3End
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3UniRec
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5Uni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind FamUni)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedProjEquivPrimeFormP)

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem label_eq_of_canon_twA_of_ne {lab : GLALabel} {r k : ℕ} (hr3 : r ≠ 3)
    (h : canonLabel lab = ⟨.twA, r, k⟩) : lab = ⟨.twA, r, k⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  by_cases h3 : rank = 3 <;> by_cases h2 : rank = 2 <;> cases tag <;> simp_all [canonLabel] <;>
    omega

theorem qUConcl_of_unitary_prime {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hF : FieldOn p b S) {labK : GLALabel}
    (hkind : FieldKind (PSimple p S) labK (indAut p S b hF.1)) {m : ℕ} (hm2 : 2 ≤ m)
    (hpm : p ∣ 2 ^ m + 1) (hcan : canonLabel labK = ⟨.twA, p - 1, p * m⟩) : QUConcl p S B x b := by
  classical
  have hp : p.Prime := cfg.prime
  have hp2 : p ≠ 2 := cfg.odd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hp4 : p - 1 ≠ 3 := by
    intro h4
    have h : p = 4 := by omega
    rw [h] at hp
    exact absurd hp (by norm_num)
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp cfg.comp
  have hcen : Subgroup.center (PSimple p S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  have hFam : FamUni labK := Or.inl (by rw [label_eq_of_canon_twA_of_ne hp4 hcan])
  obtain ⟨K, _, _, d, τ, hτ, hτq, hKcard, -, -, -, hrank, hnK, A, σ, u, e, hA, heu, hu, hσ⟩ :=
    Y10GFldUniMark.fieldKind_unitary_data hcen hFam hkind
  rw [hcan] at hrank hnK
  have hd : d = p := by
    have h : p - 1 + 1 = d := hrank
    omega
  clear hrank
  subst d
  have hn : labK.n = p * m := hnK.symm
  have hpm6 : 3 * 2 ≤ p * m := Nat.mul_le_mul hp3 hm2
  have h : UnitaryFieldData 2 labK.n K :=
    ⟨Nat.prime_two, by omega, by rw [hKcard, ← pow_mul, Nat.mul_comm]⟩
  haveI : CharP K 2 := h.charP
  have hq3 : ¬(p = 3 ∧ 2 ^ labK.n = 2) := fun h' => by
    have h1 : labK.n = 1 := Nat.pow_right_injective le_rfl (h'.2.trans (pow_one 2).symm)
    omega
  have hαD := S265F3.congr_not_mem_primeFormD h hp3 hq3 hτq hA hσ e heu hu
  have hinv : chevAut p S ⟨b, hF.1⟩ = (indAut p S b hF.1)⁻¹ := by
    have h' : indAut p S b hF.1 = (chevAut p S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h', inv_inv]
  have hβD : MulAut.congr (e.trans (statedProjEquivPrimeFormP h (by omega : 1 ≤ p)))
      (chevAut p S ⟨b, hF.1⟩) ∉ primeFormD h (idGram K p) := by
    rw [hinv, map_inv, inv_mem_iff]
    exact hαD
  have hβp : chevAut p S ⟨b, hF.1⟩ ^ p = 1 := chevAut_pow_eq_one p S hF.1 (cfg.elem.2 b cfg.hb)
  have hnp : labK.n / p = m := by
    rw [hn]
    exact Nat.mul_div_cancel_left m hp.pos
  have hpe : p ∣ 2 ^ (labK.n / p) + 1 := by
    rw [hnp]
    exact hpm
  have he2 : 2 ≤ labK.n / p := by
    rw [hnp]
    exact hm2
  refine S265F3.qUConcl_of_model cfg hF.1 ?_
  intro Eb hEp hEcomm hpE t ht hEt
  exact exists_layer_of_unitary_model_prime h hp hp2 hpe he2
    (e.trans (statedProjEquivPrimeFormP h (by omega : 1 ≤ p))) hβp hβD Eb hEp hEcomm hpE ht hEt

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
