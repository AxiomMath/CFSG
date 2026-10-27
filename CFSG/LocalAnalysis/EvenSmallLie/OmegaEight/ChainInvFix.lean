module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainInvCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainTransfer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem toVec_colsActAux (C : List ℕ) (z : ℕ) (n : ℕ) :
    toVec 6 (colsActAux C z n) =
      ∑ j ∈ Finset.range n, bz (z.testBit j) • toVec 6 (C.getD j 0) := by
  induction n with
  | zero =>
    ext i
    simp [colsActAux, toVec]
  | succ n ih =>
    rw [colsActAux, toVec_xor, ih, Finset.sum_range_succ]
    congr 1
    by_cases h : z.testBit n
    · simp [h]
    · simp only [h, Bool.false_eq_true, ite_false, bz_false, zero_smul]
      ext i
      simp [toVec]

theorem colsActAux_lt (C : List ℕ) (hC : ∀ j < 6, C.getD j 0 < 64) (z : ℕ) {n : ℕ}
    (hn : n ≤ 6) : colsActAux C z n < 64 := by
  induction n with
  | zero => simp [colsActAux]
  | succ n ih =>
    rw [colsActAux]
    refine Nat.xor_lt_two_pow (n := 6) (ih (by omega)) ?_
    split_ifs
    · exact hC n (by omega)
    · norm_num

theorem bz_testBit_vecBits (v : V6) (j : Fin 6) : bz ((vecBits v).testBit j) = v j := by
  rw [testBit_vecBits, dite_eq_left j.isLt]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (v j) with h | h <;> rw [h] <;> rfl

theorem colsAct_colsF {σ : Equiv.Perm V6} (hσ : σ ∈ linGroup) (v : V6) :
    colsAct (colsF σ) (vecBits v) = vecBits (σ v) := by
  have hC : ∀ j < 6, (colsF σ).getD j 0 < 64 := fun j hj => by
    rw [colsF_getD _ hj]
    exact vecBits_lt _
  refine toVec_injective (colsActAux_lt _ hC _ le_rfl) (vecBits_lt _) ?_
  rw [toVec_vecBits, colsAct, toVec_colsActAux, map_sum_of_mem_linGroup hσ,
    ← Fin.sum_univ_eq_sum_range (fun j => bz ((vecBits v).testBit j) •
      toVec 6 ((colsF σ).getD j 0)) 6]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bz_testBit_vecBits, colsF_getD _ j.isLt, toVec_vecBits]

theorem fixCount_eq (C : List ℕ) :
    fixCount C = ((Finset.range 64).filter fun x => (colsAct C x == x) = true).card := by
  rw [fixCount, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.coe_card]
  congr 2

theorem fixCount_colsF {σ : Equiv.Perm V6} (hσ : σ ∈ linGroup) :
    fixCount (colsF σ) = (Finset.univ.filter fun v => σ v = v).card := by
  rw [fixCount_eq, ← card_filter_vecBits]
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, colsAct_colsF hσ, beq_iff_eq]
  exact ⟨fun h => by rw [← toVec_vecBits (σ v), h, toVec_vecBits], fun h => by rw [h]⟩

theorem isInvol_colsF {σ : Equiv.Perm V6} (hσ : σ ∈ linGroup) (h2 : ∀ v, σ (σ v) = v)
    (hne : σ ≠ 1) : isInvol (colsF σ) = true := by
  simp only [isInvol, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq]
  have hlt : ∀ j < 6, 2 ^ j < 64 := fun j hj =>
    calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj
      _ = 64 := by norm_num
  refine ⟨fun j hj => ?_, fun h => hne ?_⟩
  · rw [colsF_getD _ hj, colsAct_colsF hσ, h2, basisVec, vecBits_toVec (hlt j hj)]
  · have h1 : colsOf (1 : Equiv.Perm V6) = (List.range 6).map (2 ^ ·) := by
      simp only [colsOf, colsF, Equiv.Perm.coe_one, id]
      refine List.map_congr_left fun j hj => ?_
      rw [basisVec, vecBits_toVec (hlt j (List.mem_range.1 hj))]
    exact eq_of_colsOf_eq hσ (one_mem _) (h.trans h1.symm)

theorem card_fix_eq_of_invol {ε : Eps} {σ : Equiv.Perm V6}
    (hσ : σ ∈ linGroup) (hO : colsF σ ∈ oCols ε) (hd : dickC (colsF σ) = false)
    (h2 : ∀ v, σ (σ v) = v) (hne : σ ≠ 1) :
    (Finset.univ.filter fun v => σ v = v).card = 16 := by
  have h := invCheck_spec ε
  simp only [invCheck, List.all_eq_true] at h
  have := h _ hO
  rw [hd, isInvol_colsF hσ h2 hne] at this
  simp only [Bool.false_or, Bool.not_true, beq_iff_eq] at this
  rw [← fixCount_colsF hσ]
  exact this

variable {G : Type*} [Group G]
  {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem invFix (hS : Setup ε t L U Q P a ψ p) : InvFix U Q := by
  intro h hU hQ hsq
  have hP : h ∈ P := hS.rad.U_le_P hU
  have hN : h ∈ normalizer (Q : Set G) := hS.rad.P_le_normalizer hP
  set σ := hS.rad.linHom ⟨h, hN⟩ with hσdef
  have hσ : σ ∈ linGroup := hS.rad.linHom_mem_linGroup _
  have hσv : ∀ v, σ v = lin ψ h v := fun v => rfl
  have hO : colsF σ ∈ oCols ε := hS.rad.colsF_lin_mem_oCols hP
  have hd : dickC (colsF σ) = false := hS.rad.dickC_colsF_lin hP
  have h2 : ∀ v, σ (σ v) = v := fun v => by
    rw [hσv, hσv, ← hS.rad.lin_mul hN hN, hS.rad.lin_of_mem_Q hsq]
  have hfix : ∀ v, σ v = v ↔ ψ v * h = h * ψ v := fun v => by
    rw [hσv, hS.rad.lin_eq_iff hN]
    constructor
    · intro e
      calc ψ v * h = h * ψ v * h⁻¹ * h := by rw [e]
        _ = h * ψ v := by group
    · intro e
      rw [← e]
      group
  have hne : σ ≠ 1 := by
    intro h1
    apply hQ
    refine hS.mem_Q_of_mem_P hP (mem_centralizer_iff.2 fun q hq => ?_)
    obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    exact (hfix v).1 (by rw [h1]; rfl)
  rw [← card_fix_eq_of_invol hσ hO hd h2 hne, ← Nat.card_eq_finsetCard]
  let f : {v // v ∈ Finset.univ.filter fun v => σ v = v} → (Q ⊓ centralizer {h} : Subgroup G) :=
    fun v => ⟨ψ v, hS.rad.ψ_mem v, mem_centralizer_singleton_iff.2 ((hfix v).1
      (Finset.mem_filter.1 v.2).2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w e => Subtype.ext (hS.rad.ψ_inj (congrArg Subtype.val e)), fun x => ?_⟩
    obtain ⟨v, hv⟩ := hS.rad.mem_ψ x x.2.1
    have hc := mem_centralizer_singleton_iff.1 x.2.2
    refine ⟨⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hfix v).2 (by rw [hv]; exact hc)⟩⟩,
      Subtype.ext hv⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end CFSG.EvenSmallLie.OmegaEight.Chain
