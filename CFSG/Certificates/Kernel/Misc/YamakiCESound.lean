module

public import Certificates.Data.Kernel.Misc.YamakiCE
public import CFSG.Certificates.Kernel.Misc.YamakiRepSound
public import CFSG.Certificates.Kernel.Misc.YamakiGenPosSound
public import CFSG.Certificates.Kernel.Misc.YamakiRepFSound

public section

namespace CFSG.KC.YamakiCE

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec CFSG.KD.YamakiCE
  CFSG.KD.YamakiA0 CFSG.KD.YamakiGenPos CFSG.KD.BfsK CFSG.KC.BfsEnum CFSG.KC.YamakiS0
  CFSG.KC.YamakiA0 CFSG.KC.YamakiGenPos CFSG.KC.YamakiRep CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

variable {R : ℕ → ℕ} {o n : ℕ}

theorem numPosK_sound : ∀ {xs ps : List ℕ}, numPosK R o n xs ps = true →
    ∀ x ∈ xs, ∃ p < n, recX R o p = x
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [numPosK] at h
  | x :: xs, p :: ps, h => by
    simp only [numPosK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hp, he⟩, hr⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨p, hp, he⟩
    · exact numPosK_sound hr y hy

theorem memK_sound {x : ℕ} (h : memK R o n x = true) : ∃ p < n, recX R o p = x := by
  unfold memK at h
  obtain ⟨p, hp, he⟩ := List.any_eq_true.1 h
  exact ⟨p, List.mem_range.1 hp, Nat.eq_of_beq_eq_true he⟩

theorem isSome_of_rec {PA PB : ℕ → ℕ} {E : Enum}
    (hE : BInvE (fun t => arrN (recX R o t)) PA PB n E) {x : ℕ} (h : ∃ p < n, recX R o p = x) :
    (E.lookup (arrN x)).isSome = true := by
  obtain ⟨p, hp, rfl⟩ := h
  have hl : E.lookup (arrN (recX R o p)) = some p := lookup_of_inv hE hp
  rw [hl]
  rfl

theorem size_gV0 : (gV0 ()).size = 5 := by
  simp [gV0]

theorem gV0_get {j : ℕ} (hj : j < 5) : (gV0 ())[j]! =(genA ())[v0Idx.getD j 0]! := by
  simp only [gV0]
  rw [getElem!_ofFn_nat _ hj]

theorem wordG_eq {gs : Array (Array ℕ)} {g : ℕ → ℕ} :
    ∀ w : List ℕ, (∀ k ∈ w, gs[k]! = arrN (g k)) → wordA gs w = arrN (wordG g w)
  | [], _ => by rw [wordA, wordG, arrN_one]
  | k :: w, h => by
    rw [wordA, wordG, h k List.mem_cons_self,
      wordG_eq w fun j hj => h j (List.mem_cons_of_mem _ hj), arrN_mul]

theorem all_arrN (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) :
    ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ i ∈ w, i < 12) → ∀ {x : ℕ}, x < 2 ^ 36 →
      fixedBy (ws.map (wordA (genA ()))) (arrN x) = fixK R ws x
  | [], _, _, _ => rfl
  | w :: ws, h, x, hx => by
    have ih := all_arrN hG ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) hx
    unfold fixedBy fixK at ih ⊢
    rw [List.map_cons, List.all_cons, List.all_cons, ih, wordA_eq hG w (h w List.mem_cons_self),
      arrN_mul, arrN_mul, decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _)]

theorem ceEnumCheck_of
    (hE : enumOK (enumE ()) (gE ()) = true ∧ (enumE ()).elems.size = 11520)
    (hV : enumOK (enumV0 ()) (gV0 ()) = true ∧ (enumV0 ()).elems.size = 32) :
    ceEnumCheck () = true := by
  simp only [ceEnumCheck]
  rw [hE.1, hE.2, hV.1, hV.2]
  decide

theorem v0Check_of {RE PAE PBE PAV PBV : ℕ → ℕ}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) PAE PBE 11520 (enumE ()))
    (hV : BInvE (fun t => arrN (recX R o t)) PAV PBV 32 (enumV0 ()))
    (hGE : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (RE j.val))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {ps : List ℕ}
    (hp : genPosK RE 14 11520 v0Idx ps = true) (hsq : sqK R o 32 = true)
    (hc : v0ConjK R o = true) : v0Check () = true := by
  have h1 := lookups_of_pos hE hGE (by decide) hp
  have hm : ∀ j < 5, v0Idx.getD j 0 ∈ v0Idx := by decide
  have hm12 : ∀ j < 5, v0Idx.getD j 0 < 12 := by decide
  have hH12 : ∀ s ∈ idxHhat, s < 12 := by decide
  have hV' := hV
  obtain ⟨e1, -, -, e4, -⟩ := hV'
  simp only [v0Check, Bool.and_eq_true, allLt_iff, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨fun j hj => ?_, fun i hi => ?_⟩, fun s hs j hj => ?_⟩
  · rw [size_gV0] at hj
    rw [gV0_get hj]
    exact List.all_eq_true.1 h1 _ (hm j hj)
  · rw [e1] at hi
    rw [e4 i hi, arrN_mul, ← arrN_one]
    unfold sqK at hsq
    rw [Nat.eq_of_beq_eq_true (List.all_eq_true.1 hsq i (List.mem_range.2 hi))]
  · rw [size_gV0] at hj
    rw [gV0_get hj, genA_eq12 hG (hH12 s hs), genA_eq12 hG (hm12 j hj), arrN_mul, arrN_mul]
    unfold v0ConjK at hc
    exact isSome_of_rec hV (memK_sound (List.all_eq_true.1 (List.all_eq_true.1 hc s hs) _
      (hm j hj)))

theorem gE_get (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {j : ℕ} (hj : j < 2) :
    (gE ())[j]! = arrN (wordN R (e0Words.getD j [])) := by
  have hw : ∀ j < 2, ∀ i ∈ e0Words.getD j [], i < 12 := by decide
  rw [gE, wordsA_get _ _ (by simpa [e0Words] using hj), wordA_eq hG _ (hw j hj)]

theorem commOK_gE (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) (x : ℕ) :
    commOK (gE ()) (arrN x) =
      (Nat.beq (MULF x (wordN R (e0Words.getD 0 []))) (MULF (wordN R (e0Words.getD 0 [])) x) &&
        Nat.beq (MULF x (wordN R (e0Words.getD 1 []))) (MULF (wordN R (e0Words.getD 1 [])) x)) := by
  have hs : (gE ()).size = 2 := by simp [gE, wordsA, e0Words]
  apply Bool.eq_iff_iff.2
  unfold commOK
  rw [allLt_iff, hs, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  have key : ∀ j < 2, (decide (compA (arrN x) (gE ())[j]! = compA (gE ())[j]! (arrN x)) = true ↔
      MULF x (wordN R (e0Words.getD j [])) = MULF (wordN R (e0Words.getD j [])) x) := by
    intro j hj
    rw [gE_get hG hj, arrN_mul, arrN_mul, decide_eq_true_eq]
    exact ⟨arrN_inj (CFSG.KC.Sp62.MULF_lt _ _) (CFSG.KC.Sp62.MULF_lt _ _), fun h => by rw [h]⟩
  constructor
  · intro h
    exact ⟨(key 0 (by norm_num)).1 (h 0 (by norm_num)), (key 1 (by norm_num)).1 (h 1 (by norm_num))⟩
  · rintro ⟨a, b⟩ j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact (key 0 (by norm_num)).2 a
    · exact (key 1 (by norm_num)).2 b

theorem centE0Check_of {PA PB : ℕ → ℕ}
    (hH : BInvE (fun t => arrN (recX R o t)) PA PB 23040 (enumH ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hlt : ∀ t < 23040, recX R o t < 2 ^ 36) (h5 : R 5 < 2 ^ 36)
    (hc : ∀ q < 45, centChunk R o 23040 512 q 5 = true) : centE0Check () = true := by
  obtain ⟨e1, -, -, e4, -⟩ := hH
  simp only [centE0Check, allLt_iff]
  intro i hi
  rw [e1] at hi
  have hq : i / 512 < 45 := by omega
  have hcq := hc _ hq
  simp only [centChunk, CFSG.KC.YamakiRepF.strictY_eq] at hcq
  have hlo : Nat.mul 512 (i / 512) ≤ i := Nat.mul_div_le i 512
  have hhi : i < Nat.mul 512 (i / 512) + 512 := by
    change i < 512 * (i / 512) + 512
    omega
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 hcq i hlo hhi
  rw [Nat.blt_eq.mpr hi, cond_true] at e
  unfold centAt at e
  rw [e4 i hi, commOK_gE hG, ← arrN_one, genA_eq12 hG (by norm_num : 5 < 12),
    decide_arrN (hlt i hi) ONE_lt, decide_arrN (hlt i hi) h5]
  exact e

theorem commMemCheck_of {RE PAE PBE PAV PBV : ℕ → ℕ}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) PAE PBE 11520 (enumE ()))
    (hV : BInvE (fun t => arrN (recX R o t)) PAV PBV 32 (enumV0 ()))
    (hGE : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (RE j.val))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val)) {ps : List ℕ}
    (hpW : numPosK RE 14 11520 ((commFixers ++ commConjs ++ commTriple).map (wordN RE)) ps = true)
    (hgk : commGkK R o = true) : commMemCheck () = true := by
  have hws : ∀ w ∈ commFixers ++ commConjs ++ commTriple, ∀ i ∈ w, i < 12 := by decide
  have hgw : ∀ k < 5, ∀ i ∈ commGWords.getD k [], i < 12 := by decide
  have hsz : (commGk ()).size = 5 := by simp [commGk, wordsA, commGWords, commConjs]
  simp only [commMemCheck, Bool.and_eq_true, List.all_eq_true, allLt_iff]
  refine ⟨⟨by decide, fun w hw => ?_⟩, fun k hk => ?_⟩
  · rw [wordA_eq hGE w (hws w hw)]
    exact isSome_of_rec hE (numPosK_sound hpW _ (List.mem_map_of_mem hw))
  · rw [hsz] at hk
    rw [commGk, wordsA_get _ _ (by simpa [commGWords, commConjs] using hk),
      wordA_eq hG _ (hgw k hk)]
    unfold commGkK at hgk
    exact isSome_of_rec hV (memK_sound (List.all_eq_true.1 hgk k (List.mem_range.2 hk)))

theorem commFixCheck_of {PA PB : ℕ → ℕ}
    (hV : BInvE (fun t => arrN (recX R o t)) PA PB 32 (enumV0 ()))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hlt : ∀ t < 32, recX R o t < 2 ^ 36) (h5 : R 5 < 2 ^ 36)
    (hfx : commFixK R o commFixers = true) : commFixCheck () = true := by
  have hw : ∀ w ∈ commFixers, ∀ i ∈ w, i < 12 := by decide
  obtain ⟨e1, -, -, e4, -⟩ := hV
  unfold commFixK at hfx
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hfx
  simp only [commFixCheck, Bool.and_eq_true, allLt_iff]
  rw [wordA_eq hG commV1 (by decide), genA_eq12 hG (by norm_num : 5 < 12), arrN_mul,
    all_arrN hG _ hw (wordN_lt _)]
  refine ⟨hfx.1, fun i hi => ?_⟩
  rw [e1] at hi
  rw [e4 i hi, all_arrN hG _ hw (hlt i hi), ← arrN_one, decide_arrN (hlt i hi) ONE_lt,
    decide_arrN (hlt i hi) (wordN_lt _), decide_arrN (hlt i hi) h5,
    decide_arrN (hlt i hi) (CFSG.KC.Sp62.MULF_lt _ _)]
  exact hfx.2 i hi

theorem commTripleCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (h5 : R 5 < 2 ^ 36) (htr : commTripleK R = true) : commTripleCheck () = true := by
  simp only [commTripleCheck]
  rw [wordA_eq hG _ (by decide : ∀ i ∈ commV1, i < 12),
    wordA_eq hG _ (by decide : ∀ i ∈ conjWord (commTriple.getD 0 []) commV1, i < 12),
    wordA_eq hG _ (by decide : ∀ i ∈ conjWord (commTriple.getD 1 []) commV1, i < 12),
    wordA_eq hG _ (by decide : ∀ i ∈ conjWord (commTriple.getD 2 []) commV1, i < 12),
    genA_eq12 hG (by norm_num : 5 < 12), ← arrN_one, arrN_mul, decide_arrN (wordN_lt _) ONE_lt,
    decide_arrN h5 ONE_lt, decide_arrN (wordN_lt _) (wordN_lt _),
    decide_arrN (CFSG.KC.Sp62.MULF_lt _ _) (wordN_lt _)]
  exact htr

theorem commExprCheck_of (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hex : commExprK R = true) : commExprCheck () = true := by
  have hgw : ∀ k < 5, ∀ i ∈ commGWords.getD k [], i < 12 := by decide
  have hgk : ∀ k < 5, (commGk ())[k]! = arrN (wordN R (commGWords.getD k [])) := fun k hk => by
    rw [commGk, wordsA_get _ _ (by simpa [commGWords, commConjs] using hk),
      wordA_eq hG _ (hgw k hk)]
  have hm12 : ∀ i < 5, v0Idx.getD i 0 < 12 := by decide
  unfold commExprK at hex
  simp only [commExprCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hex ⊢
  intro i hi
  obtain ⟨h1, h2⟩ := hex i hi
  refine ⟨h1, ?_⟩
  rw [wordG_eq (g := fun k => wordN R (commGWords.getD k [])) _ fun k hk => hgk k (h1 k hk),
    genA_eq12 hG (hm12 i hi), Nat.eq_of_beq_eq_true h2]

theorem commCheck_of {RE PAE PBE PAV PBV : ℕ → ℕ}
    (hE : BInvE (fun t => arrN (recX RE 14 t)) PAE PBE 11520 (enumE ()))
    (hV : BInvE (fun t => arrN (recX R o t)) PAV PBV 32 (enumV0 ()))
    (hGE : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (RE j.val))
    (hG : ∀ j : Fin 12, yamakiMat6 j = pkMat 6 (R j.val))
    (hlt : ∀ t < 32, recX R o t < 2 ^ 36) (h5 : R 5 < 2 ^ 36) {ps : List ℕ}
    (hpW : numPosK RE 14 11520 ((commFixers ++ commConjs ++ commTriple).map (wordN RE)) ps = true)
    (hgk : commGkK R o = true) (hfx : commFixK R o commFixers = true)
    (htr : commTripleK R = true) (hex : commExprK R = true) : commCheck () = true := by
  unfold commCheck
  rw [commMemCheck_of hE hV hGE hG hpW hgk, commFixCheck_of hV hG hlt h5 hfx,
    commTripleCheck_of hG h5 htr, commExprCheck_of hG hex]
  rfl

end CFSG.KC.YamakiCE

end
