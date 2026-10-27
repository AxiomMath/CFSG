module

public import Certificates.Data.Kernel.AS91Coc
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KS.AS91Coc

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
open CFSG.Quasithin.H13.AS91.M24G

@[expose] def RelA (a : Array Nat) (P : Nat) : Prop :=
  ∀ j < 24, a[j]! = pg 5 (mask 5) P j ∧ pg 5 (mask 5) P j < 24

theorem relA_of_letOK {a : Array Nat} {P : Nat} (h : letOK a P = true) : RelA a P := by
  intro j hj
  have := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at this
  exact this

theorem relA_id : RelA idArr (pidn 24 5) := fun j hj =>
  ⟨by rw [idArr_get hj, PF.pg_pidn (by norm_num) (by norm_num) hj],
    by rw [PF.pg_pidn (by norm_num) (by norm_num) hj]; exact hj⟩

theorem relA_cArr {a b : Array Nat} {P Q : Nat} (ha : RelA a P) (hb : RelA b Q) :
    RelA (cArr a b) (pcomp 24 5 (mask 5) P Q) := fun j hj => by
  have hq := hb j hj
  have hp := ha _ hq.2
  rw [PF.pg_pcomp (by norm_num) hj, cArr_get a b hj, hq.1]
  exact hp

theorem permCols_eq {a : Array Nat} {P : Nat} (ha : RelA a P) : permCols a = permColsK P := by
  unfold permCols permColsK
  exact List.map_congr_left fun j hj => by rw [(ha j (List.mem_range.1 hj)).1]

theorem act11_eq {a : Array Nat} {P : Nat} (ha : RelA a P) (m : Nat) : act11 a m = act11K P m := by
  rw [act11, act11K, permM, permCols_eq ha]

theorem xorLin_act11K (P : Nat) : XorLin (act11K P) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

section Fold

variable (hA : RelA cocArrA PA) (hAi : RelA cocArrAi PAi) (hB : RelA cocArrB PB)
  (hBi : RelA cocArrBi PBi)
include hA hAi hB hBi

theorem relA_inv (l : CocL) : RelA (cocInvImg l) (invLetK l) := by
  cases l
  · exact hAi
  · exact hA
  · exact hBi
  · exact hB

theorem relA_img (l : CocL) : RelA (cocImg l) (imgLetK l) := by
  cases l
  · exact hA
  · exact hAi
  · exact hB
  · exact hBi

theorem val_eq (x y : Nat) (l : CocL) : cocVal x y l = valK x y l := by
  cases l
  · rfl
  · exact act11_eq hA x
  · rfl
  · exact act11_eq hB y

theorem fold_twin (x y : Nat) : ∀ w : List CocL,
    RelA (cocInvArrOf x y w) (foldK x y w).1 ∧ cocMaskVal x y w = (foldK x y w).2
  | [] => ⟨relA_id, rfl⟩
  | l :: ls => by
    obtain ⟨h1, h2⟩ := fold_twin x y ls
    refine ⟨relA_cArr h1 (relA_inv hA hAi hB hBi l), ?_⟩
    change act11 (cocInvArrOf x y ls) (cocVal x y l) ^^^ cocMaskVal x y ls =
      act11K (foldK x y ls).1 (valK x y l) ^^^ (foldK x y ls).2
    rw [act11_eq h1, val_eq hA hAi hB hBi, h2]

theorem rel_twin : ∀ w : List CocL, RelA (cocRelArr w) (relK w)
  | [] => relA_id
  | l :: ls => relA_cArr (relA_img hA hAi hB hBi l) (rel_twin ls)

end Fold

theorem foldK_fst (x y : Nat) : ∀ w : List CocL, (foldK x y w).1 = (foldK 0 0 w).1
  | [] => rfl
  | l :: ls => by
    change pcomp 24 5 (mask 5) (foldK x y ls).1 (invLetK l) =
      pcomp 24 5 (mask 5) (foldK 0 0 ls).1 (invLetK l)
    rw [foldK_fst x y ls]

theorem valK_xor (x₁ x₂ y₁ y₂ : Nat) (l : CocL) :
    valK (x₁ ^^^ x₂) (y₁ ^^^ y₂) l = valK x₁ y₁ l ^^^ valK x₂ y₂ l := by
  cases l
  · rfl
  · exact xorLin_act11K PA x₁ x₂
  · rfl
  · exact xorLin_act11K PB y₁ y₂

theorem xor4 (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b, Nat.xor_comm b c, Nat.xor_assoc, ← Nat.xor_assoc]

theorem foldK_xor (x₁ x₂ y₁ y₂ : Nat) : ∀ w : List CocL,
    (foldK (x₁ ^^^ x₂) (y₁ ^^^ y₂) w).2 = (foldK x₁ y₁ w).2 ^^^ (foldK x₂ y₂ w).2
  | [] => (Nat.xor_self 0).symm
  | l :: ls => by
    change act11K (foldK (x₁ ^^^ x₂) (y₁ ^^^ y₂) ls).1 (valK (x₁ ^^^ x₂) (y₁ ^^^ y₂) l) ^^^
        (foldK (x₁ ^^^ x₂) (y₁ ^^^ y₂) ls).2 =
      (act11K (foldK x₁ y₁ ls).1 (valK x₁ y₁ l) ^^^ (foldK x₁ y₁ ls).2) ^^^
        (act11K (foldK x₂ y₂ ls).1 (valK x₂ y₂ l) ^^^ (foldK x₂ y₂ ls).2)
    rw [foldK_fst _ _ ls, foldK_fst x₁ y₁ ls, foldK_fst x₂ y₂ ls, foldK_xor x₁ x₂ y₁ y₂ ls,
      valK_xor, xorLin_act11K, xor4]

theorem xorLin_x (w : List CocL) : XorLin fun x => (foldK x 0 w).2 := fun a b => by
  have := foldK_xor a b 0 0 w
  rwa [Nat.zero_xor] at this

theorem xorLin_y (w : List CocL) : XorLin fun y => (foldK 0 y w).2 := fun a b => by
  have := foldK_xor 0 0 a b w
  rwa [Nat.zero_xor] at this

theorem cocWalk_spec {g : Nat → Nat → Bool} : ∀ (L : List Nat) (i : Nat), cocWalk g L i = true →
    ∀ k < L.length, g (i + k) (L.getD k 0) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | t :: L, i, h, k, hk => by
    change (g i t && cocWalk g L (Nat.succ i)) = true at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := cocWalk_spec L (Nat.succ i) h.2 k (by simpa using hk)
      rw [List.getD_cons_succ]
      rwa [show i + (k + 1) = Nat.succ i + k by omega]

theorem arr_getD (a : Array Nat) (i : Nat) : a.getD i 0 = a.toList.getD i 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem mw_eq (hM : ∀ c < 5, mwChunk c = true) :
    cocRelWords.map (fun w => matOf 11 (fun y => (foldK 0 y w).2)) = cocMW := by
  have hl1 : cocRelWords.length = 25 := by decide +kernel
  have hl2 : cocMW.length = 25 := by decide +kernel
  apply List.ext_getElem (by rw [List.length_map, hl1, hl2])
  intro j h1 h2
  have hj : j < 25 := by rwa [hl2] at h2
  have hc := List.all_eq_true.1 (hM (j / 5) (by omega)) (j % 5)
    (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rw [Nat.div_add_mod, beq_iff_eq] at hc
  rw [List.getElem_map, ← List.getD_eq_getElem cocRelWords [] (by rw [hl1]; exact hj),
    ← List.getD_eq_getElem cocMW [] h2]
  exact hc

section Checks

variable (hA : RelA cocArrA PA) (hAi : RelA cocArrAi PAi) (hB : RelA cocArrB PB)
  (hBi : RelA cocArrBi PBi)
include hA hAi hB hBi

theorem cocRelCheck_of (h : relOKK = true) : cocRelCheck = true := by
  rw [cocRelCheck, List.all_eq_true]
  intro w hw
  have hr := rel_twin hA hAi hB hBi w
  have hj := List.all_eq_true.1 h w hw
  have hsz : (cocRelArr w).size = 24 := by
    cases w with
    | nil => rfl
    | cons l ls => simp [cocRelArr, cArr]
  have he : cocRelArr w = idArr := by
    apply Array.ext (by rw [hsz]; rfl)
    intro j hj1 hj2
    have hj24 : j < 24 := hsz ▸ hj1
    have e1 := (hr j hj24).1
    have e2 := List.all_eq_true.1 hj j (List.mem_range.2 hj24)
    rw [beq_iff_eq] at e2
    rw [← getElem!_pos (cocRelArr w) j hj1, ← getElem!_pos idArr j hj2, e1, e2, idArr_get hj24]
  rw [he]
  exact beq_self_eq_true _

theorem maskVal_x {x : Nat} (hx : x < 2048) (hM : matOf 11 (fun x => (foldK x 0 cocAFive).2) = cocMA) :
    cocMaskVal x 0 cocAFive = actM cocMA x := by
  rw [(fold_twin hA hAi hB hBi x 0 cocAFive).2, ← hM, actM_matOf (xorLin_x cocAFive) 11 x hx]

theorem cocCertA_of (hM : (matOf 11 (fun x => (foldK x 0 cocAFive).2) == cocMA) = true)
    (hW : cocWalk cocGA cocTabA.toList 0 = true) : cocCertA () = true := by
  rw [cocCertA, List.all_eq_true]
  intro x hx
  have hx' := List.mem_range.1 hx
  have hlen : cocTabA.toList.length = 2048 := by decide +kernel
  have h := cocWalk_spec _ 0 hW x (by rw [hlen]; exact hx')
  rw [Nat.zero_add] at h
  rw [maskVal_x hA hAi hB hBi hx' (beq_iff_eq.1 hM), cocCobMask, act11_eq hAi, arr_getD]
  exact h

theorem cocCertB_of (hM : ∀ c < 5, mwChunk c = true)
    (hW : cocWalk cocGB cocTabB.toList 0 = true) : cocCertB () = true := by
  rw [cocCertB, List.all_eq_true]
  intro y hy
  have hy' := List.mem_range.1 hy
  have hlen : cocTabB.toList.length = 2048 := by decide +kernel
  have h := cocWalk_spec _ 0 hW y (by rw [hlen]; exact hy')
  rw [Nat.zero_add] at h
  have hrel : (cocRelWords.all fun w => cocMaskVal 0 y w == 0) =
      (cocMW.all fun M => actM M y == 0) := by
    rw [← mw_eq hM, List.all_map]
    apply List.all_congr rfl
    intro w
    simp only [Function.comp_apply]
    rw [(fold_twin hA hAi hB hBi 0 y w).2, actM_matOf (xorLin_y w) 11 y hy']
  rw [hrel, cocCobMask, cocCobMask, act11_eq hAi, act11_eq hBi, cocWitW, cocWitAlpha, cocWitBeta,
    arr_getD]
  rw [cocGB] at h
  simpa only [decide_eq_true_eq] using h

theorem cert664013Check_of (h1 : InvPairOK 24 cocArrA cocArrAi = true)
    (h2 : InvPairOK 24 cocArrB cocArrBi = true) (h3 : relOKK = true)
    (h4 : (matOf 11 (fun x => (foldK x 0 cocAFive).2) == cocMA) = true)
    (h5 : ∀ c < 5, mwChunk c = true)
    (h6 : cocWalk cocGA cocTabA.toList 0 = true) (h7 : cocWalk cocGB cocTabB.toList 0 = true) :
    cert664013Check () = true := by
  rw [cert664013Check, h1, h2, cocRelCheck_of hA hAi hB hBi h3, cocCertA_of hA hAi hB hBi h4 h6,
    cocCertB_of hA hAi hB hBi h5 h7]
  rfl

end Checks

end CFSG.KS.AS91Coc

end
