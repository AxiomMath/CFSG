module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Defs
public import Certificates.Certificate12680
public import CFSG.Sporadic.Schreier.J4SElevenBase1

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
open CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc CFSG.Sporadic.J4.QT2A

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rep_letterPL {gs : ℕ → J} {G : Array Pair} (hG : ∀ m, Rep Sp φ (gs m) (G.getD m oneP))
    (l : ℤ) :
    Rep Sp φ (if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹) (letterPL G l) := by
  unfold letterPL
  split_ifs
  · exact hG _
  · exact rep_invP (hG _)

theorem rep_wordPL {gs : ℕ → J} {G : Array Pair} (hG : ∀ m, Rep Sp φ (gs m) (G.getD m oneP)) :
    ∀ w : List ℤ, Rep Sp φ (wordProd gs w) (wordPL G w)
  | [] => by
    simp only [wordProd, List.map_nil, List.prod_nil, wordPL]
    exact rep_oneP
  | l :: w => by
    simp only [wordProd, List.map_cons, List.prod_cons, wordPL]
    exact rep_mulP (rep_letterPL hG l) (rep_wordPL hG w)

theorem abGen_coe (m : ℕ) : ((abGen m : J) : GL (Fin 112) (ZMod 2)) = baseGL m := by
  unfold abGen baseGL
  split_ifs
  · exact a_coe
  · exact b_coe
  · rfl

theorem rep_abGen (m : ℕ) :
    Rep Sp φ (abGen m) ((#[An, Bn] : Array Pair).getD m oneP) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · exact rep_a matFacts
    · exact rep_b matFacts
  · have h1 : abGen m = 1 := by
      unfold abGen
      split_ifs <;> first | omega | rfl
    have h2 : (#[An, Bn] : Array Pair).getD m oneP = oneP := by
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_none (by simp; omega)]
      rfl
    rw [h1, h2]
    exact rep_oneP

theorem localWords_length : CFSG.Sporadic.J4.Native.localWords.length = 3 := by decide

theorem xJ_eq (k : ℕ) : xJ k = wordProd abGen (CFSG.Sporadic.J4.Native.localWords.getD k []) := by
  apply Subtype.ext
  have h := wordProd_map J.subtype abGen (CFSG.Sporadic.J4.Native.localWords.getD k [])
  simp only [Subgroup.coe_subtype] at h
  rw [h]
  show locGL k = _
  unfold locGL
  rw [List.getD_eq_getElem?_getD]
  congr 1
  funext m
  exact (abGen_coe m).symm

theorem rep_xJn (k : ℕ) : Rep Sp φ (xJ k) (xJn k) := by
  rw [xJ_eq]
  exact rep_wordPL rep_abGen _

theorem rep_xJns (m : ℕ) : Rep Sp φ (xJ m) (xJns.getD m oneP) := by
  rcases Nat.lt_or_ge m 3 with hm | hm
  · interval_cases m
    · exact rep_xJn 0
    · exact rep_xJn 1
    · exact rep_xJn 2
  · have h1 : xJ m = 1 := by
      rw [xJ_eq, List.getD_eq_default _ _ (by rw [localWords_length]; exact hm)]
      rfl
    have h2 : xJns.getD m oneP = oneP := by
      unfold xJns
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_none (by simp; omega)]
      rfl
    rw [h1, h2]
    exact rep_oneP

theorem rep_gen5 (m : ℕ) : Rep Sp φ (gen5 m) (gen5n.getD m oneP) := by
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · exact rep_xJn 0
    · exact rep_xJn 1
    · exact rep_xJn 2
    · exact rep_a matFacts
    · exact rep_b matFacts
  · have h1 : gen5 m = 1 := by
      unfold gen5
      split_ifs <;> first | omega | rfl
    have h2 : gen5n.getD m oneP = oneP := by
      unfold gen5n
      simp only [Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_eq_none (by simp; omega)]
      rfl
    rw [h1, h2]
    exact rep_oneP

theorem rep_gE (n : ℕ) : Rep Sp φ (gE n) (gEn n) :=
  rep_wordPL rep_gen5 (genWord n)

theorem rep_uJ (j : ℕ) :
    Rep Sp φ (CFSG.Sporadic.J4.QT.uJ j) (uJn j) :=
  rep_wordPL rep_xJns (CFSG.Sporadic.J4.QT.uWord j)

theorem rep_eta_foldl (c : ℕ) :
    ∀ (L : List ℕ) (g : J) (P : Pair), Rep Sp φ g P →
      Rep Sp φ (L.foldl (fun acc j => if c.testBit j then acc * CFSG.Sporadic.J4.QT.uJ j else acc) g)
        (L.foldl (fun acc j => if c.testBit j then mulP acc (uJn j) else acc) P)
  | [], _, _, h => h
  | j :: L, g, P, h => by
    simp only [List.foldl_cons]
    refine rep_eta_foldl c L _ _ ?_
    split_ifs
    · exact rep_mulP h (rep_uJ j)
    · exact h

theorem rep_z0 : Rep Sp φ z0 z0n :=
  rep_eta_foldl 1131 (List.range 11) 1 oneP rep_oneP

theorem rep_hW : Rep Sp φ hW hWn :=
  rep_wordPL rep_abGen hWordN

theorem rep_jInv :
    Rep Sp φ jInv jn :=
  rep_powP rep_nrm₂ 20

theorem rep_gam :
    Rep Sp φ gam gamN :=
  rep_mulP (rep_powP (rep_mulP rep_z0 (rep_mulP (rep_mulP rep_hW rep_jInv) (rep_invP rep_hW))) 6)
    rep_hW

@[expose] def xElt (i : ℕ) : J := if h : i < 7 then rRep ⟨i, h⟩ else mElt

theorem rep_xElt (i : ℕ) (hi : i < 8) :
    Rep Sp φ (xElt i) (xN.getD i oneP) := by
  interval_cases i
  · exact rep_gE 0
  · exact rep_gE 1
  · exact rep_mulP (rep_gE 0) (rep_gE 2)
  · exact rep_mulP (rep_gE 1) (rep_gE 2)
  · exact rep_mulP (rep_mulP (rep_gE 0) (rep_gE 1)) (rep_gE 2)
  · exact rep_mulP (rep_gE 1) (rep_gE 3)
  · exact rep_mulP (rep_gE 2) (rep_gE 3)
  · exact rep_mulP (rep_mulP (rep_mulP (rep_mulP (rep_mulP (rep_gE 15) (rep_gE 29)) (rep_gE 1))
      (rep_gE 7)) (rep_gE 9)) (rep_gE 11)

theorem rep_g2 (i : ℕ) (hi : i < 8) :
    Rep Sp φ (nrm₁ * (gam⁻¹ * xElt i * gam)) (g2N (xN.getD i oneP)) :=
  rep_mulP rep_nrm₁ (rep_mulP (rep_mulP (rep_invP rep_gam) (rep_xElt i hi)) rep_gam)

theorem slpCheck_true (i : ℕ) (hi : i < 8) :
    slpLt i = true ∧ slpEq i = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := Certificates.certificate12680
  interval_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem slpK_lt (i : ℕ) (hi : i < 8) : slpK.getD i 0 < slpN.getD i 0 := by
  interval_cases i <;> decide

theorem b_mem_closure
    (i : ℕ) (hi : i < 8) :
    b ∈ Subgroup.closure ({nrm₂, nrm₁ * (gam⁻¹ * xElt i * gam)} : Set J) := by
  obtain ⟨hlt, heq⟩ := slpCheck_true i hi
  unfold slpLt at hlt
  unfold slpEq at heq
  have hrep := regsRep_runProg (slpProg i) hlt (regsRep_initRegs rep_nrm₂ (rep_g2 i hi))
  have hb := eq_of_rep_check (hrep.2 _ (slpK_lt i hi)) (rep_b matFacts) heq
  have hmem := runProg_mem (Subgroup.closure ({nrm₂, nrm₁ * (gam⁻¹ * xElt i * gam)} : Set J))
    (slpProg i) (initRegs_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))) (slpK.getD i 0)
  exact hb ▸ hmem

theorem a_mem_normalizer :
    a ∈ Subgroup.normalizer (Q11 : Set J) := by
  obtain ⟨-, -, -, -, -, -, -, -, hx, hy⟩ := Certificates.certificate12680
  refine mem_normalizer_Q11 ?_ ?_
  · rw [conj_of_rep_check (rep_a matFacts) rep_qx (rep_qWord 10 0 1) hx]
    exact qWord_mem 10 0 1
  · rw [conj_of_rep_check (rep_a matFacts) rep_qy (rep_qWord 0 10 6) hy]
    exact qWord_mem 0 10 6

theorem normalizer_sup_closure_eq_top
    (i : ℕ) (hi : i < 8) :
    Subgroup.normalizer (Q11 : Set J) ⊔ Subgroup.closure {gam⁻¹ * xElt i * gam} = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hN : Subgroup.normalizer (Q11 : Set J) ≤
      Subgroup.normalizer (Q11 : Set J) ⊔ Subgroup.closure {gam⁻¹ * xElt i * gam} := le_sup_left
  have hx : gam⁻¹ * xElt i * gam ∈
      Subgroup.normalizer (Q11 : Set J) ⊔ Subgroup.closure {gam⁻¹ * xElt i * gam} :=
    (le_sup_right : Subgroup.closure {gam⁻¹ * xElt i * gam} ≤ _)
      (Subgroup.subset_closure (Set.mem_singleton _))
  rintro _ (rfl | rfl)
  · exact hN a_mem_normalizer
  · refine (Subgroup.closure_le _).2 ?_ (b_mem_closure i hi)
    rintro _ (rfl | rfl)
    · exact hN nrm₂_mem_normalizer
    · exact Subgroup.mul_mem _ (hN nrm₁_mem_normalizer) hx

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
