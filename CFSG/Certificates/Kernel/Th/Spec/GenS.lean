
module

public import CFSG.Certificates.Kernel.Th.Spec.GenSBase

public import CFSG.Sporadic.Th.Max3.Data
import CFSG.Certificates.Kernel.Th.Max3S.WordsBase

public section

namespace CFSG.KC.Th.Spec.GenS

open CFSG.KC.Th CFSG.KC.Th.Gen CFSG.KC.Th.Spec

section Defs

variable {G : Type} [Group G] (a b : G)

@[expose] def q (i : Fin 8) : G :=
  wordProd a b (CFSG.Sporadic.Th.Max3.qWord i) ^ CFSG.Sporadic.Th.Max3.qExp i
@[expose] def CGen : Prop :=
  GenFact a b CFSG.Sporadic.Th.Kernel.fusionWord0' (q a b 0) ∧
    GenFact a b CFSG.Sporadic.Th.Kernel.fusionWord1' (x a b)

end Defs

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem prod4_mem (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {M : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2))} {L0 L1 L2 L3 : ℕ} (h0 : pkMat L0 ∈ M)
    (h1 : pkMat L1 ∈ M) (h2 : pkMat L2 ∈ M) (h3 : pkMat L3 ∈ M) (w : ℕ) :
    ∀ (n S : ℕ), pkMat S ∈ M → pkMat (OutS.prod4 c rm L0 L1 L2 L3 S w n) ∈ M
  | 0, _, hS => hS
  | n + 1, S, hS => by
    show pkMat (mulB c rm (OutS.prod4 c rm L0 L1 L2 L3 S w n)
      (OutS.sel4 L0 L1 L2 L3 (BigS.bitsN w (Nat.mul 2 n) 2))) ∈ M
    rw [pkMat_mulB hk]
    refine M.mul_mem (prod4_mem hk h0 h1 h2 h3 w n S hS) ?_
    unfold OutS.sel4
    cases Nat.blt (BigS.bitsN w (Nat.mul 2 n) 2) 2 <;>
      cases Nat.beq (BigS.bitsN w (Nat.mul 2 n) 2) 2 <;>
      cases Nat.beq (BigS.bitsN w (Nat.mul 2 n) 2) 0 <;> assumption

section Regs

variable (hk : BigS.constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
variable {G : Type} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))
include hk

end Regs

theorem cGen_of {G : Type} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2))
    (hφ : Function.Injective φ) (a b : G) (D : GenData) (h : genChk D = true)
    (hA' : φ a = CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LA))
    (hB' : φ b = CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LB)) :
    CGen a b := by
  unfold genChk at h
  have L0 := andB_left (andB_left (andB_left (andB_left (andB_left (andB_left h)))))
  have L1 := andB_right (andB_left (andB_left (andB_left (andB_left (andB_left h)))))
  have L2 := andB_left (andB_right (andB_left (andB_left (andB_left (andB_left h)))))
  have L3 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h))))))
  have L4 := andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_left h))))))
  have L5 := andB_left (andB_left (andB_right (andB_left (andB_left (andB_left h)))))
  have L6 := andB_right (andB_left (andB_right (andB_left (andB_left (andB_left h)))))
  have L7 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_left h)))))
  have L8 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h))))))
  have L9 := andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_left h))))))
  have L10 := andB_left (andB_left (andB_left (andB_right (andB_left (andB_left h)))))
  have L11 := andB_right (andB_left (andB_left (andB_right (andB_left (andB_left h)))))
  have L12 := andB_left (andB_right (andB_left (andB_right (andB_left (andB_left h)))))
  have L13 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h))))))
  have L14 := andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_left h))))))
  have L15 := andB_left (andB_left (andB_right (andB_right (andB_left (andB_left h)))))
  have L16 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h))))))
  have L17 := andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_left h))))))
  have L18 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_left h)))))
  have L19 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h))))))
  have L20 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_left h))))))
  have L21 := andB_left (andB_left (andB_left (andB_left (andB_right (andB_left h)))))
  have L22 := andB_right (andB_left (andB_left (andB_left (andB_right (andB_left h)))))
  have L23 := andB_left (andB_right (andB_left (andB_left (andB_right (andB_left h)))))
  have L24 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h))))))
  have L25 := andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_left h))))))
  have L26 := andB_left (andB_left (andB_right (andB_left (andB_right (andB_left h)))))
  have L27 := andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h))))))
  have L28 := andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_left h))))))
  have L29 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_left h)))))
  have L30 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h))))))
  have L31 := andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_left h))))))
  have L32 := andB_left (andB_left (andB_left (andB_right (andB_right (andB_left h)))))
  have L33 := andB_right (andB_left (andB_left (andB_right (andB_right (andB_left h)))))
  have L34 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_left h)))))
  have L35 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left h))))))
  have L36 := andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_left h))))))
  have L37 := andB_left (andB_left (andB_right (andB_right (andB_right (andB_left h)))))
  have L38 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left h))))))
  have L39 := andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_left h))))))
  have L40 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_left h)))))
  have L41 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left h))))))
  have L42 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_left h))))))
  have L43 := andB_left (andB_left (andB_left (andB_left (andB_left (andB_right h)))))
  have L44 := andB_right (andB_left (andB_left (andB_left (andB_left (andB_right h)))))
  have L45 := andB_left (andB_right (andB_left (andB_left (andB_left (andB_right h)))))
  have L46 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right h))))))
  have L47 := andB_right (andB_right (andB_right (andB_left (andB_left (andB_left (andB_right h))))))
  have L48 := andB_left (andB_left (andB_right (andB_left (andB_left (andB_right h)))))
  have L49 := andB_right (andB_left (andB_right (andB_left (andB_left (andB_right h)))))
  have L50 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_right h)))))
  have L51 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right h))))))
  have L52 := andB_right (andB_right (andB_right (andB_right (andB_left (andB_left (andB_right h))))))
  have L53 := andB_left (andB_left (andB_left (andB_right (andB_left (andB_right h)))))
  have L54 := andB_right (andB_left (andB_left (andB_right (andB_left (andB_right h)))))
  have L55 := andB_left (andB_right (andB_left (andB_right (andB_left (andB_right h)))))
  have L56 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right h))))))
  have L57 := andB_right (andB_right (andB_right (andB_left (andB_right (andB_left (andB_right h))))))
  have L58 := andB_left (andB_left (andB_right (andB_right (andB_left (andB_right h)))))
  have L59 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right h))))))
  have L60 := andB_right (andB_right (andB_left (andB_right (andB_right (andB_left (andB_right h))))))
  have L61 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_right h)))))
  have L62 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right h))))))
  have L63 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_left (andB_right h))))))
  have L64 := andB_left (andB_left (andB_left (andB_left (andB_right (andB_right h)))))
  have L65 := andB_right (andB_left (andB_left (andB_left (andB_right (andB_right h)))))
  have L66 := andB_left (andB_right (andB_left (andB_left (andB_right (andB_right h)))))
  have L67 := andB_left (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right h))))))
  have L68 := andB_right (andB_right (andB_right (andB_left (andB_left (andB_right (andB_right h))))))
  have L69 := andB_left (andB_left (andB_right (andB_left (andB_right (andB_right h)))))
  have L70 := andB_left (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right h))))))
  have L71 := andB_right (andB_right (andB_left (andB_right (andB_left (andB_right (andB_right h))))))
  have L72 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_right h)))))
  have L73 := andB_left (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right h))))))
  have L74 := andB_right (andB_right (andB_right (andB_right (andB_left (andB_right (andB_right h))))))
  have L75 := andB_left (andB_left (andB_left (andB_right (andB_right (andB_right h)))))
  have L76 := andB_right (andB_left (andB_left (andB_right (andB_right (andB_right h)))))
  have L77 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_right h)))))
  have L78 := andB_left (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right h))))))
  have L79 := andB_right (andB_right (andB_right (andB_left (andB_right (andB_right (andB_right h))))))
  have L80 := andB_left (andB_left (andB_right (andB_right (andB_right (andB_right h)))))
  have L81 := andB_left (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right h))))))
  have L82 := andB_right (andB_right (andB_left (andB_right (andB_right (andB_right (andB_right h))))))
  have L83 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_right h)))))
  have L84 := andB_left (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))
  have L85 := andB_right (andB_right (andB_right (andB_right (andB_right (andB_right (andB_right h))))))
  have hk := L1
  have hA : φ a = pkMat D.ThSeed_SA := by
    rw [hA', (decOK_sound L2).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have hB : φ b = pkMat D.ThSeed_SB := by
    rw [hB', (decOK_sound L3).2, CFSG.Sporadic.Th.rowsMatrix_rowsOf]
  have rA : pkMat (D.ThS_RBf 1) = φ a := by rw [CFSG.KC.Th.Max3S.eq_of_eqN L9, hA]
  have rB : pkMat (D.ThS_RBf 2) = φ b := by rw [CFSG.KC.Th.Max3S.eq_of_eqN L10, hB]
  have r3 : pkMat D.ThO_Gt3 = φ (t3 a b) := mulR hk φ L13 rA rB
  have r4 : pkMat D.ThO_Gt4 = φ (t4 a b) := mulR hk φ L14 r3 rB
  have r5 : pkMat D.ThO_Gt5 = φ (t5 a b) := mulR hk φ L15 r3 r4
  have r6 : pkMat D.ThO_Gt6 = φ (t6 a b) := mulR hk φ L16 r3 r5
  have r7 : pkMat D.ThO_Gt7 = φ (t7 a b) := mulR hk φ L17 rA r6
  have r8 : pkMat D.ThO_Gt8 = φ (t8 a b) := mulR hk φ L18 r6 rA
  have r8i : pkMat D.ThO_Gt8i = φ (t8 a b)⁻¹ := invR hk φ L19 r8
  have ru : pkMat D.ThO_Gu = φ (u a b) := mulR hk φ L20 r8i r7
  have rs8 : pkMat D.ThO_Gs8 = φ (s8 a b) := mulR hk φ L21 r6 r5
  have rs9 : pkMat D.ThO_Gs9 = φ (s9 a b) := mulR hk φ L22 r3 rs8
  have rs10 : pkMat D.ThO_Gs10 = φ (s10 a b) := mulR hk φ L23 rs9 r4
  have rs7 : pkMat D.ThO_Gs7 = φ (s7 a b) := mulR hk φ L24 rA rs10
  have rs8p : pkMat D.ThO_Gs8p = φ (s8' a b) := mulR hk φ L25 rs10 rA
  have rs8pi : pkMat D.ThO_Gs8pi = φ (s8' a b)⁻¹ := invR hk φ L26 rs8p
  have rv : pkMat D.ThO_Gv = φ (v a b) := mulR hk φ L27 rs8pi rs7
  have rx : pkMat D.ThO_Gx = φ (x a b) := powR hk φ L28 (by norm_num) rv
  have ru9 : pkMat D.ThO_Gu9 = φ (u a b ^ 9) := powR hk φ L29 (by norm_num) ru
  have ry : pkMat D.ThO_Gy = φ (y a b) := mulR hk φ L30 r7 ru9
  have rxy : pkMat D.ThO_Gxy = φ (x a b * y a b) := mulR hk φ L31 rx ry
  have rq0 : pkMat D.ThO_Gq0 = φ (q a b 0) := by
    rw [powR hk φ L32 (by norm_num) rxy]
    congr 1
    simp only [q, wordProd, CFSG.Sporadic.Th.Max3.qWord, CFSG.Sporadic.Th.Max3.qExp,
      CFSG.Sporadic.Th.Max3.Gen.eval, Matrix.cons_val_zero, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
  have hword : ∀ (w : List ℕ) (n code : ℕ),
      (List.range n).map (fun i => BigS.bitsN code (2 * i) 2) = w.map (fun i => i - 1) →
      (∀ i ∈ w, i = 1 ∨ i = 2) →
      pkMat (BigS.wordAB D.ThS_c D.ThS_rm D.ThS_ONE (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi code n) =
        φ (abProd a b w) := by
    intro w n code hd hw
    rw [CFSG.KC.Th.Max3S.pkMat_wordAB_range hk, abProd_map]
    have e1 : (List.range n).map (fun i => pkMat (wordLetter (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi
        (BigS.bitsN code (2 * i) 2))) =
        ((List.range n).map fun i => BigS.bitsN code (2 * i) 2).map
          (fun d => pkMat (wordLetter (D.ThS_RBf 1) (D.ThS_RBf 2) D.ThS_Bi d)) := by
      rw [List.map_map]
      rfl
    rw [e1, hd, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rcases hw i hi with rfl | rfl
    · show pkMat (wordLetter _ _ _ 0) = φ a
      rw [wordLetter, if_pos rfl, rA]
    · show pkMat (wordLetter _ _ _ 1) = φ b
      rw [wordLetter, if_neg (by decide), if_pos rfl, rB]
  have rg0 : pkMat D.ThO_Gg0 = φ (abProd a b CFSG.Sporadic.Th.Kernel.fusionWord0') := by
    rw [← CFSG.KC.Th.Max3S.eq_of_eqN L33]
    exact hword _ _ _ digits0 (by decide)
  have rg1 : pkMat D.ThO_Gg1 = φ (abProd a b CFSG.Sporadic.Th.Kernel.fusionWord1') := by
    rw [← CFSG.KC.Th.Max3S.eq_of_eqN L58]
    exact hword _ _ _ digits1 (by decide)
  have fact : ∀ (w : List ℕ) (r : G) {Pg Pgi Pr Pma Pmb Pmc Pmd Pc Pci Pfa Pf Pha Phb Pe Pei
      Pha' Phb' Pe' Pei' : ℕ},
      pkMat Pg = φ (abProd a b w) → pkMat Pr = φ r →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pg Pgi) D.ThS_ONE = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pgi Pr) Pma = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pma Pg) Pmb = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pmb (D.ThS_RBf 1)) Pmc = true →
      Gen.eqN (BigS.powB D.ThS_c D.ThS_rm D.ThS_ONE Pmc 9 4) Pmd = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pmd Pgi) Pc = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pc Pci) D.ThS_ONE = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pc Pr) Pfa = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pfa Pci) Pf = true →
      Gen.eqN Pf (D.ThS_RBf 1) = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm D.ThO_Gx Pc) Pha = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pci Pha) Phb = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm D.ThO_Gx Phb) Pe = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pe Pei) D.ThS_ONE = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm D.ThO_Gy Pc) Pha' = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pci Pha') Phb' = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm D.ThO_Gy Phb') Pe' = true →
      Gen.eqN (mulB D.ThS_c D.ThS_rm Pe' Pei') D.ThS_ONE = true →
      (∀ M : Submonoid (Matrix (Fin 248) (Fin 248) (ZMod 2)), pkMat Pe ∈ M → pkMat Pei ∈ M →
        pkMat Pe' ∈ M → pkMat Pei' ∈ M → pkMat (D.ThS_RBf 1) ∈ M ∧ pkMat (D.ThS_RBf 2) ∈ M) →
      GenFact a b w r := by
    intro w r Pg Pgi Pr Pma Pmb Pmc Pmd Pc Pci Pfa Pf Pha Phb Pe Pei Pha' Phb' Pe' Pei' hg hr l1 l2
      l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 hM
    have rgi := invR hk φ l1 hg
    have rma := mulR hk φ l2 rgi hr
    have rmb := mulR hk φ l3 rma hg
    have rmc := mulR hk φ l4 rmb rA
    have rmd := powR hk φ l5 (by norm_num) rmc
    have rc : pkMat Pc = φ (fusionConj a b w r) := mulR hk φ l6 rmd rgi
    have rci := invR hk φ l7 rc
    have rfa := mulR hk φ l8 rc hr
    have rf := mulR hk φ l9 rfa rci
    have rha := mulR hk φ l11 rx rc
    have rhb := mulR hk φ l12 rci rha
    have re := mulR hk φ l13 rx rhb
    have rei := invR hk φ l14 re
    have rha' := mulR hk φ l15 ry rc
    have rhb' := mulR hk φ l16 rci rha'
    have re' := mulR hk φ l17 ry rhb'
    have rei' := invR hk φ l18 re'
    set K := Subgroup.closure (genPair a b (fusionConj a b w r)) with hK
    have mem : ∀ g ∈ K, φ g ∈ K.toSubmonoid.map φ := fun g hg => ⟨g, hg, rfl⟩
    have e1 : x a b * ((fusionConj a b w r)⁻¹ * (x a b * fusionConj a b w r)) ∈ K :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have e2 : y a b * ((fusionConj a b w r)⁻¹ * (y a b * fusionConj a b w r)) ∈ K :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    obtain ⟨hmA, hmB⟩ := hM (K.toSubmonoid.map φ) (re ▸ mem _ e1) (rei ▸ mem _ (K.inv_mem e1))
      (re' ▸ mem _ e2) (rei' ▸ mem _ (K.inv_mem e2))
    refine ⟨hφ ?_, ?_, ?_⟩
    · rw [← rf, ← rA]
      exact congrArg pkMat (CFSG.KC.Th.Max3S.eq_of_eqN l10)
    · rw [rA] at hmA
      obtain ⟨k, hk', e⟩ := hmA
      have hka : k = a := hφ e
      rw [hka] at hk'
      exact hk'
    · rw [rB] at hmB
      obtain ⟨k, hk', e⟩ := hmB
      have hkb : k = b := hφ e
      rw [hkb] at hk'
      exact hk'
  refine ⟨fact _ _ rg0 rq0 L34 L35 L36 L37 L38 L39 L40 L41 L42 L43 L44 L45 L46 L47 L48 L49 L50 L51
    fun M m1 m2 m3 m4 => ?_, fact _ _ rg1 rx L59 L60 L61 L62 L63 L64 L65 L66 L67 L68 L69 L70 L71 L72
    L73 L74 L75 L76 fun M m1 m2 m3 m4 => ?_⟩
  · have p := prod4_mem hk m1 m2 m3 m4
    refine ⟨?_, ?_⟩
    · rw [← CFSG.KC.Th.Max3S.eq_of_eqN L54]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L53]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L52]
      exact p _ _ _ (by rw [pkMat_one hk]; exact M.one_mem)
    · rw [← CFSG.KC.Th.Max3S.eq_of_eqN L57]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L56]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L55]
      exact p _ _ _ (by rw [pkMat_one hk]; exact M.one_mem)
  · have p := prod4_mem hk m1 m2 m3 m4
    refine ⟨?_, ?_⟩
    · rw [← CFSG.KC.Th.Max3S.eq_of_eqN L81]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L80]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L79]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L78]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L77]
      exact p _ _ _ (by rw [pkMat_one hk]; exact M.one_mem)
    · rw [← CFSG.KC.Th.Max3S.eq_of_eqN L85]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L84]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L83]
      refine p _ _ _ ?_
      rw [← CFSG.KC.Th.Max3S.eq_of_eqN L82]
      exact p _ _ _ (by rw [pkMat_one hk]; exact M.one_mem)

theorem cGen_of_GL {H : Subgroup (GL (Fin 248) (ZMod 2))} (a b : H) (D : GenData)
    (h : genChk D = true)
    (hA : ((a : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LA))
    (hB : ((b : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2)) =
      CFSG.Blueprint.NativeSporadic.decode 2 248 1 (String.ofList D.ThSeed_LB)) :
    CGen a b :=
  cGen_of ((Units.coeHom (Matrix (Fin 248) (Fin 248) (ZMod 2))).comp H.subtype)
    (fun _ _ e => Subtype.ext (Units.ext e)) a b D h hA hB

end CFSG.KC.Th.Spec.GenS

end
