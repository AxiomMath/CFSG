module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1Data
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.Sporadic.Schreier.Co1LocalOrbit
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.Sporadic.Co1Schreier.Native (decWord decLetter)
open CFSG.Monster.B.Pinned (rowsMat)
open CFSG.HardMathSupport.Foote.E27.OrbitF3 (lmulD lidD rowsMat_lmulD rowsMat_lidD lmulD_length
  lidD_length)
open scoped Matrix

@[expose] def Acts (x : GL24) (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∀ b, x * eProd b * x⁻¹ = eProd (M *ᵥ b)

theorem acts_one : Acts 1 1 := fun b => by
  rw [one_mul, inv_one, mul_one, Matrix.one_mulVec]

theorem acts_mul {x y : GL24} {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hx : Acts x M)
    (hy : Acts y N) : Acts (x * y) (M * N) := fun b => by
  rw [← Matrix.mulVec_mulVec, ← hx, ← hy, mul_inv_rev]
  simp only [mul_assoc]

private theorem acts_inv {x : GL24} {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hx : Acts x M)
    (hMN : M * N = 1) : Acts x⁻¹ N := fun b => by
  have h := hx (N *ᵥ b)
  rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec] at h
  rw [inv_inv, ← h]
  group

theorem E_le_GA : ElemThree.E ≤ GA := fun _ hx =>
  A_le_GA (Subgroup.subset_closure (Set.mem_union_left _ hx))

theorem wG_mem_Qg {w : List ℕ} (hw : w ∈ Co1T.Data.qGenWords) : Co1T.wG w ∈ Co1T.Qg :=
  Subgroup.subset_closure (show Co1T.wG w ∈ Co1T.qG from List.mem_map_of_mem hw)

private theorem a_mem_Qg (i : Fin 6) :
    (⟨ElemThree.a i, E_le_GA (a_mem_E i)⟩ : ↥GA) ∈ Co1T.Qg := by
  have e : (⟨ElemThree.a i, E_le_GA (a_mem_E i)⟩ : ↥GA) = Co1T.wG [2 * i.val + 2] := by
    apply Subtype.ext
    show ElemThree.a i = 1 * letterG Co1T.lG (decLetter (2 * i.val + 2))
    rw [one_mul]
    fin_cases i <;> rfl
  rw [e]
  exact wG_mem_Qg (by fin_cases i <;> decide +kernel)

theorem EG_le_Qg : ElemThree.E.subgroupOf GA ≤ Co1T.Qg := by
  intro x hx
  have hle : ElemThree.E ≤ Co1T.Qg.map GA.subtype := by
    show Subgroup.closure (Set.range ElemThree.a) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, a_mem_Qg i, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle (Subgroup.mem_subgroupOf.1 hx)
  rwa [show y = x from Subtype.ext hyx] at hy

private theorem rowsMat_r0 : rowsMat 3 6 r0Rows = Matrix.of fun k j => conjVec 0 j k := by
  decide +kernel

private theorem rowsMat_r1 : rowsMat 3 6 r1Rows = Matrix.of fun k j => conjVec 1 j k := by
  decide +kernel

private theorem letterG_seven : letterG Co1T.lG 7 = ElemThree.g 0 := by
  rw [letterG, if_pos (by norm_num), Co1T.lG, List.getD_append _ _ _ _ (by simp),
    List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem letterG_eight : letterG Co1T.lG 8 = ElemThree.g 1 := by
  rw [letterG, if_pos (by norm_num), Co1T.lG, List.getD_append _ _ _ _ (by simp),
    List.getD_append_right _ _ _ _ (by simp)]
  simp

section Basis


theorem eProd_injective : Function.Injective eProd := fun b b' h =>
  Multiplicative.ofAdd.injective
    (eHom_injective (show eHom (Multiplicative.ofAdd b) = eHom (Multiplicative.ofAdd b') from h))

theorem acts_unique {x : GL24} {M N : Matrix (Fin 6) (Fin 6) (ZMod 3)} (hM : Acts x M)
    (hN : Acts x N) : M = N :=
  Matrix.ext_iff_mulVec.2 fun b => eProd_injective ((hM b).symm.trans (hN b))

theorem acts_of_mem_E {x : GL24} (hx : x ∈ ElemThree.E) : Acts x 1 := fun b => by
  rw [Matrix.one_mulVec, (E_comm x hx _ (eProd_mem b)).eq, mul_inv_cancel_right]

theorem card_EG : Nat.card (ElemThree.E.subgroupOf GA) = 3 ^ 6 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe E_le_GA).toEquiv, card_E]

end Basis

section Act


private theorem acts_g (i : Fin 3) :
    Acts (ElemThree.g i) (Matrix.of fun k j => conjVec i j k) := fun b => by
  rw [g_conj_eProd]
  congr 1
  ext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem acts_letter {j : ℤ} (h1 : 1 ≤ j) (h8 : j ≤ 8) :
    Acts (letterG Co1T.lG j) (rowsMat 3 6 (letRows j)) := by
  have hE : ∀ i : Fin 6, Acts (ElemThree.a i) (rowsMat 3 6 (lidD 6)) := fun i => by
    rw [rowsMat_lidD]
    exact acts_of_mem_E (a_mem_E i)
  have h0 := acts_g 0
  have h1' := acts_g 1
  rw [← rowsMat_r0] at h0
  rw [← rowsMat_r1] at h1'
  rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hE 0
  · exact hE 1
  · exact hE 2
  · exact hE 3
  · exact hE 4
  · exact hE 5
  · rw [letterG_seven]
    exact h0
  · rw [letterG_eight]
    exact h1'

private theorem acts_foldl : ∀ (w : List ℤ) (L : List (List ℕ)) (x : GL24),
    (∀ j ∈ w, 1 ≤ j ∧ j ≤ 8) → L.length = 6 → Acts x (rowsMat 3 6 L) →
    Acts (w.foldl (fun x j => x * letterG Co1T.lG j) x)
      (rowsMat 3 6 (w.foldl (fun acc j => lmulD 6 acc (letRows j)) L))
  | [], _, _, _, _, hx => hx
  | j :: w, L, x, hw, hL, hx => by
    have hj := hw j List.mem_cons_self
    have hx' : Acts (x * letterG Co1T.lG j) (rowsMat 3 6 (lmulD 6 L (letRows j))) := by
      rw [rowsMat_lmulD hL]
      exact acts_mul hx (acts_letter hj.1 hj.2)
    simp only [List.foldl_cons]
    exact acts_foldl w (lmulD 6 L (letRows j)) (x * letterG Co1T.lG j)
      (fun j' hj' => hw j' (List.mem_cons_of_mem _ hj')) (by rw [lmulD_length, hL]) hx'

theorem acts_wG {w : List ℕ} (hw : ∀ j ∈ decWord w, 1 ≤ j ∧ j ≤ 8) :
    Acts (Co1T.wG w : GL24) (rowsMat 3 6 (wordRows w)) :=
  acts_foldl (decWord w) (lidD 6) 1 hw lidD_length (by rw [rowsMat_lidD]; exact acts_one)

theorem exists_acts {x : ↥GA} (hx : x ∈ Co1T.Qg) :
    ∃ Y ∈ s0Rows, Acts (x : GL24) (rowsMat 3 6 Y) := by
  have gen : ∀ x ∈ {x | x ∈ Co1T.qG}, ∃ G ∈ gensRows, Acts ((x : ↥GA) : GL24) (rowsMat 3 6 G) := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (show x ∈ Co1T.Data.qGenWords.map Co1T.wG from hx)
    exact ⟨wordRows w, (words_check w hw).2, acts_wG (words_check w hw).1⟩
  have hx' : x ∈ Subgroup.closure {x | x ∈ Co1T.qG} := hx
  clear hx
  induction hx' using Subgroup.closure_induction_left with
  | one => exact ⟨lidD 6, s0_check.1, by rw [rowsMat_lidD]; exact acts_one⟩
  | mul_left x hx y _ ih =>
    obtain ⟨Y, hY, hYa⟩ := ih
    obtain ⟨G, hG, hGa⟩ := gen x hx
    obtain ⟨hG6, -, hGY⟩ := gens_check G hG
    refine ⟨lmulD 6 G Y, hGY Y hY, ?_⟩
    rw [Subgroup.coe_mul, rowsMat_lmulD hG6]
    exact acts_mul hGa hYa
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨Y, hY, hYa⟩ := ih
    obtain ⟨G, hG, hGa⟩ := gen x hx
    obtain ⟨hG6, hG3, hGY⟩ := gens_check G hG
    refine ⟨lmulD 6 G (lmulD 6 G Y), hGY _ (hGY Y hY), ?_⟩
    have hMN : rowsMat 3 6 G * (rowsMat 3 6 G * rowsMat 3 6 G) = 1 := by
      rw [← rowsMat_lmulD hG6, ← rowsMat_lmulD hG6, hG3, rowsMat_lidD]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, rowsMat_lmulD hG6, rowsMat_lmulD hG6, ← mul_assoc]
    exact acts_mul (acts_inv hGa hMN) hYa

end Act

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3.Co1Sylow
