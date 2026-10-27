module

public import Certificates.Data.Kernel.AS91S42
public import CFSG.Certificates.Kernel.HJ12KTSound
public import CFSG.GF2Type.Smith1979.GammaU.NativeBridge
public import CFSG.Quasithin.H13.AS91Sec4TwoInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates.Kernel.AS91S42

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour
open CFSG.Quasithin.H13.AS91.Two

theorem mulR_uA (X Y : ℕ) : mulR (unpackA X) (unpackA Y) = unpackA (mulQ X Y) := by
  simpa only [native_mulR] using mulR_unpackA X Y

theorem appN_uA (X n : ℕ) : appN (unpackA X) n = mvNR (unpackQ X) n := by
  simpa only [native_appN] using appN_unpackA X n

theorem idR_uA : idR = unpackA oneQ := by
  simpa only [native_idR] using idR_eq

theorem viol_invR : @Viol.invR = @CFSG.GammaU.Native.invR := by
  funext r
  simp only [Viol.invR, CFSG.GammaU.Native.invR, native_appN]

theorem viol_okRows : @Viol.okRows = @CFSG.GammaU.Native.okRows := rfl

theorem enumGrp_native : @enumGrp = @CFSG.GammaU.Native.enumGrp := by
  funext gs
  simp only [enumGrp, CFSG.GammaU.Native.enumGrp, native_bfsClosure, native_mulR, native_idR]

theorem enumGrp_uA (gs : List ℕ) :
    enumGrp (gs.map unpackA) = (enumQ gs).map unpackA ∧ ∀ q ∈ enumQ gs, q < 2 ^ 144 := by
  rw [enumGrp_native]
  exact enumGrp_eq gs

theorem okRows_uA (X : ℕ) : Viol.okRows (unpackA X) = true := by
  rw [viol_okRows]
  exact okRows_unpackA X

theorem invR_uA {g r : ℕ} (h : invOKQ g r = true) : Viol.invR (unpackA g) = unpackA r := by
  rw [viol_invR]
  exact invR_unpackA h

theorem beq_uA {X Y : ℕ} (hX : X < 2 ^ 144) (hY : Y < 2 ^ 144) :
    (unpackA X == unpackA Y) = Nat.beq X Y := by
  rw [beq_unpackA hX hY, nat_beq]

theorem hs_contains {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 144) {y : ℕ} (hy : y < 2 ^ 144) :
    (Std.HashSet.ofList (X.map unpackA)).contains (unpackA y) = memP (ofListP X) y := by
  rw [Std.HashSet.contains_ofList, contains_map hX hy, memP_ofListP]

theorem pow256_uA (x : ℕ) : pow256R (unpackA x) = unpackA (pow256Q x) := by
  rw [pow256R]
  have e : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [e]
  simp only [List.foldl_cons, List.foldl_nil, mulR_uA]
  rfl

theorem pow256Q_lt (x : ℕ) : pow256Q x < 2 ^ 144 := mulQ_lt _ _

theorem bnd_eq : bnd = 2 ^ 144 := by decide

theorem pairsOK_mem {G : List (ℕ × ℕ)} (h : pairsOK G = true) {p : ℕ × ℕ} (hp : p ∈ G) :
    p.1 < 2 ^ 144 ∧ p.2 < 2 ^ 144 ∧ invOKQ p.1 p.2 = true := by
  have hq := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, Nat.blt_eq, bnd_eq] at hq
  exact ⟨hq.1.1, hq.1.2, hq.2⟩

theorem gensOKb_of {G : List (ℕ × ℕ)} (h : pairsOK G = true) :
    gensOKb ((G.map Prod.fst).map unpackA) = true := by
  rw [gensOKb, List.all_eq_true]
  intro x hx
  rw [List.map_map] at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨h1, h2, h3⟩ := pairsOK_mem h hp
  rw [Function.comp_apply, invR_uA h3, okRows_uA, okRows_uA, mulR_uA, mulR_uA, idR_uA,
    beq_uA (mulQ_lt _ _) oneQ_lt, beq_uA (mulQ_lt _ _) oneQ_lt]
  rw [invOKQ, Bool.and_eq_true] at h3
  rw [h3.1, h3.2]
  rfl

theorem stab_sound (v : ℕ) (G Pp W : List (ℕ × ℕ)) (nS nP : ℕ) (h : stabQ v G Pp W nS nP = true) :
    stabOK v ((G.map Prod.fst).map unpackA) ((Pp.map Prod.fst).map unpackA)
      (W.map fun w => (unpackA w.1, unpackA w.2)) nS nP = true := by
  obtain ⟨eX, hXb⟩ := enumGrp_uA (G.map Prod.fst)
  obtain ⟨eP, hPb⟩ := enumGrp_uA (Pp.map Prod.fst)
  rw [stabQ, stabAt, stabCore] at h
  generalize enumQ (G.map Prod.fst) = X at eX hXb h
  generalize enumQ (Pp.map Prod.fst) = P at eP hPb h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hG, hPp, hW, hv, hX1, hXc, hXn, hXl, hP1, hPc, hPn, hPl, hPX, hconj, hWX, hall⟩ := h
  rw [CFSG.Quasithin.H13.AS91.Two.stabOK]
  simp only [eX, eP]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨gensOKb_of hG, gensOKb_of hPp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.map_map, List.all_map, List.all_eq_true]
    intro p hp
    rw [Function.comp_apply, Function.comp_apply, appN_uA, nat_beq]
    exact List.all_eq_true.1 hv p hp
  · rw [idR_uA, contains_map hXb oneQ_lt, ← memP_ofListP]
    exact hX1
  · rw [← native_closedCheck, closedCheck_eq _ _ hXb]
    exact hXc
  · rw [dedup_length hXb hXn, nat_beq]
    exact hXl
  · rw [idR_uA, contains_map hPb oneQ_lt, ← memP_ofListP]
    exact hP1
  · rw [← native_closedCheck, closedCheck_eq _ _ hPb]
    exact hPc
  · rw [dedup_length hPb hPn, nat_beq]
    exact hPl
  · rw [List.map_map, List.all_map, List.all_eq_true]
    intro p hp
    rw [Function.comp_apply, Function.comp_apply, hs_contains hXb (pairsOK_mem hPp hp).1]
    exact List.all_eq_true.1 hPX p hp
  · rw [List.map_map, List.all_map, List.all_eq_true]
    intro t ht
    obtain ⟨t1, t2, t3⟩ := pairsOK_mem hG ht
    rw [Function.comp_apply, Function.comp_apply, List.map_map, List.all_map, List.all_eq_true]
    intro p hp
    rw [Function.comp_apply, Function.comp_apply, invR_uA t3, mulR_uA, mulR_uA,
      hs_contains hPb (mulQ_lt _ _)]
    exact List.all_eq_true.1 (List.all_eq_true.1 hconj t ht) p hp
  · rw [List.all_map, List.all_eq_true]
    intro w hw
    obtain ⟨w1, w2, w3⟩ := pairsOK_mem hW hw
    rw [Function.comp_apply, hs_contains hXb w1, okRows_uA, mulR_uA, mulR_uA, idR_uA,
      beq_uA (mulQ_lt _ _) oneQ_lt, beq_uA (mulQ_lt _ _) oneQ_lt]
    rw [invOKQ, Bool.and_eq_true] at w3
    rw [List.all_eq_true.1 hWX w hw, w3.1, w3.2]
    rfl
  · rw [List.all_map, List.all_eq_true]
    intro x hx
    have hx' := List.all_eq_true.1 hall x hx
    rw [Function.comp_apply, pow256_uA, idR_uA, bne, beq_uA (pow256Q_lt x) oneQ_lt,
      hs_contains hPb (hXb x hx), List.any_map]
    rw [twoTest] at hx'
    refine Eq.trans ?_ hx'
    congr 1
    refine congrArg W.any (funext fun w => ?_)
    rw [Function.comp_apply, mulR_uA, mulR_uA, mulR_uA, pow256_uA, bne,
      beq_uA (pow256Q_lt _) oneQ_lt]

theorem wordRows_uA (L : List ℕ) :
    ∀ w : List ℕ, (∀ i ∈ w, i < L.length) → wordRows (L.map unpackA) w = unpackA (wordP L w)
  | [], _ => idR_uA
  | i :: w, hw => by
    have hi : i < L.length := hw i List.mem_cons_self
    have ih := wordRows_uA L w fun j hj => hw j (List.mem_cons_of_mem i hj)
    rw [wordRows, wordP] at ih ⊢
    rw [List.map_cons, List.foldr_cons, ih, List.map_cons, List.foldr_cons,
      getElem!_pos (L.map unpackA) i (by rw [List.length_map]; exact hi), List.getElem_map,
      List.getD_eq_getElem L oneQ hi, mulR_uA]

theorem nGensI_eq : nGensI = nQ.map unpackA := by decide +kernel

theorem words_eq (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ i ∈ w, i < 6) :
    ws.map (wordRows nGensI) = (ws.map (wordP nQ)).map unpackA := by
  rw [List.map_map]
  refine List.map_congr_left fun w hmem => ?_
  rw [Function.comp_apply, nGensI_eq]
  exact wordRows_uA nQ w (hw w hmem)

theorem ch89402_w1 : (stab1Words.map (wordP nQ) == g1Q.map Prod.fst) = true := by quickRfl

theorem ch89402_w2 : (stab2Words.map (wordP nQ) == g2Q.map Prod.fst) = true := by quickRfl

theorem stab1Gens_eq : stab1Gens () = (g1Q.map Prod.fst).map unpackA := by
  rw [stab1Gens, words_eq _ (by decide), eq_of_beq ch89402_w1]

theorem stab2Gens_eq : stab2Gens () = (g2Q.map Prod.fst).map unpackA := by
  rw [stab2Gens, words_eq _ (by decide), eq_of_beq ch89402_w2]

theorem core1_eq : core1Rows = (p1Q.map Prod.fst).map unpackA := by decide +kernel

theorem core2_eq : core2Rows = (p2Q.map Prod.fst).map unpackA := by decide +kernel

theorem wit1_eq : wit1 = w1Q.map fun w => (unpackA w.1, unpackA w.2) := by decide +kernel

theorem wit2_eq : wit2 = w2Q.map fun w => (unpackA w.1, unpackA w.2) := by decide +kernel

theorem stabOK42_of (h1 : stabQ 3 g1Q p1Q w1Q 3840 32 = true)
    (h2 : stabQ 5 g2Q p2Q w2Q 1920 16 = true) : stabOK42 () = true := by
  rw [stabOK42, stab1Gens_eq, stab2Gens_eq, core1_eq, core2_eq, wit1_eq, wit2_eq,
    stab_sound 3 g1Q p1Q w1Q 3840 32 h1, stab_sound 5 g2Q p2Q w2Q 1920 16 h2]
  rfl

end Certificates.Kernel.AS91S42
