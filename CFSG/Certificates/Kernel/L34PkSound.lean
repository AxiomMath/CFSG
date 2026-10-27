
module

public import Certificates.Data.Kernel.L34Pk
public import CFSG.Certificates.Kernel.WittCntSound

public section

namespace CFSG.KC.L34

open CFSG.KS.PK CFSG.KC.Enum CFSG.KC.WCnt CFSG.KS.PCnt CFSG.Quasithin.L34Amalgam
  CFSG.Quasithin.Asc94 CFSG.ComponentClassification.WittDesign

@[expose] def encT (T : Array (Fin 22)) : Nat := enc 5 (fun i => (T.getD i 0).val) 22

@[expose] def V (T : Array (Fin 22)) : Prop := T.size = 22

theorem pt_eq_fd (x i : Nat) : pt x i = fd 5 x i := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  change (x >>> (5 * i)) &&& 31 = x / 2 ^ (5 * i) % 2 ^ 5
  rw [Nat.shiftRight_eq_div_pow, h31, Nat.and_two_pow_sub_one_eq_mod]

theorem fd_encT (T : Array (Fin 22)) {i : Nat} (hi : i < 22) :
    fd 5 (encT T) i = (T.getD i 0).val :=
  fd_enc (fun j _ => lt_trans (T.getD j 0).isLt (by norm_num)) hi

theorem pt_encT (T : Array (Fin 22)) {i : Nat} (hi : i < 22) :
    pt (encT T) i = (T.getD i 0).val := by
  rw [pt_eq_fd, fd_encT T hi]

theorem encT_lt (T : Array (Fin 22)) : encT T < 2 ^ (5 * 22) :=
  enc_lt (fun j _ => lt_trans (T.getD j 0).isLt (by norm_num))

theorem encT_inj {s t : Array (Fin 22)} (hs : V s) (ht : V t) (h : encT s = encT t) : s = t := by
  have hs' : s.size = 22 := hs
  have ht' : t.size = 22 := ht
  refine Array.ext (hs'.trans ht'.symm) fun i h1 h2 => ?_
  have hi : i < 22 := hs' ▸ h1
  have e := congrArg (fun x => fd 5 x i) h
  simp only [fd_encT _ hi] at e
  rw [Array.getElem_eq_getD 0, Array.getElem_eq_getD 0]
  exact Fin.ext e

theorem encT_eq_iff {s t : Array (Fin 22)} (hs : V s) (ht : V t) : encT s = encT t ↔ s = t :=
  ⟨encT_inj hs ht, fun h => h ▸ rfl⟩

theorem V_tmul (s t : Array (Fin 22)) : V (tmul s t) := Array.size_ofFn

theorem V_tid : V tid := Array.size_ofFn

theorem getD_tmul (s t : Array (Fin 22)) {i : Nat} (hi : i < 22) :
    (tmul s t).getD i 0 = s.getD (t.getD i 0).val 0 := by
  have hs : (tmul s t).size = 22 := V_tmul s t
  rw [← Array.getElem_eq_getD (h := hs.symm ▸ hi)]
  unfold tmul
  rw [Array.getElem_ofFn]

theorem encT_tmul (s t : Array (Fin 22)) : encT (tmul s t) = pm (encT s) (encT t) := by
  refine eq_of_fd_eq (encT_lt _) (pcomp_lt (by norm_num) 5 _ _) fun i hi => ?_
  have h := fd_pcomp (n := 22) (by norm_num) 5 (encT s) (encT t) hi
  rw [mask_five] at h
  unfold pm
  rw [h, fd_encT _ hi, fd_encT _ hi, fd_encT _ (t.getD i 0).isLt, getD_tmul _ _ hi]

theorem fd_pI : ∀ i < 22, fd 5 pI i = i := by decide

theorem encT_tid : encT tid = pI := by
  refine eq_of_fd_eq (encT_lt _) (by unfold pI; norm_num) fun i hi => ?_
  have hs : tid.size = 22 := V_tid
  rw [fd_encT _ hi, fd_pI i hi, ← Array.getElem_eq_getD (h := hs.symm ▸ hi)]
  unfold tid
  rw [Array.getElem_ofFn]
  rfl

theorem V_evalT (f g : Fin 5 → Array (Fin 22)) : ∀ w, V (evalT f g w)
  | [] => V_tid
  | _ :: _ => V_tmul _ _

theorem pevT_cons (f g : Fin 5 → Nat) (x : Fin 5 × Bool) (w : List (Fin 5 × Bool)) :
    pevT f g (x :: w) = pm (cond x.2 (f x.1) (g x.1)) (pevT f g w) :=
  strictN_eq' _ _

theorem evalT_nil (f g : Fin 5 → Array (Fin 22)) : evalT f g [] = tid := rfl

theorem evalT_cons (f g : Fin 5 → Array (Fin 22)) (x : Fin 5 × Bool) (w : List (Fin 5 × Bool)) :
    evalT f g (x :: w) = tmul (cond x.2 (f x.1) (g x.1)) (evalT f g w) := rfl

theorem pevT_nil (f g : Fin 5 → Nat) : pevT f g [] = pI := rfl

theorem encT_cond (b : Bool) (s t : Array (Fin 22)) :
    encT (cond b s t) = cond b (encT s) (encT t) := by
  cases b
  · rw [cond_false, cond_false]
  · rw [cond_true, cond_true]

theorem encT_evalT (f g : Fin 5 → Array (Fin 22)) : ∀ w,
    encT (evalT f g w) = pevT (fun i => encT (f i)) (fun i => encT (g i)) w
  | [] => by rw [evalT_nil, pevT_nil, encT_tid]
  | x :: w => by
    rw [pevT_cons, ← encT_evalT f g w, evalT_cons, encT_tmul, encT_cond]

theorem encT_getD (l : List (Array (Fin 22))) (i : Nat) :
    encT (l.getD i tid) = (l.map encT).getD i pI := by
  rw [← encT_tid, List.getD_map]

theorem V_getD {l : List (Array (Fin 22))} (h : ∀ T ∈ l, V T) (i : Nat) : V (l.getD i tid) := by
  induction l generalizing i with
  | nil => exact V_tid
  | cons T l ih =>
    cases i with
    | zero => exact h T List.mem_cons_self
    | succ i => exact ih (fun U hU => h U (List.mem_cons_of_mem _ hU)) i

theorem encT_wtab (gT gTi : List (Array (Fin 22))) (s : String) :
    encT (wtab gT gTi s) = pwtab (gT.map encT) (gTi.map encT) s := by
  unfold wtab pwtab
  rw [encT_evalT]
  simp only [encT_getD]

theorem encT_wtabI (gT gTi : List (Array (Fin 22))) (s : String) :
    encT (wtabI gT gTi s) = pwtabI (gT.map encT) (gTi.map encT) s := by
  unfold wtabI pwtabI
  rw [encT_evalT]
  simp only [encT_getD]

theorem V_wtab (gT gTi : List (Array (Fin 22))) (s : String) : V (wtab gT gTi s) := V_evalT _ _ _

theorem fixesF_eq (T : Array (Fin 22)) : fixesF T = pfixes (encT T) := by
  unfold fixesF pfixes
  refine List.all_congr rfl fun y => ?_
  rw [pt_encT T y.isLt, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, Fin.ext_iff]

theorem presF_eq (T : Array (Fin 22)) : presF T = ppres (encT T) := by
  unfold presF ppres
  refine List.all_congr rfl fun y => ?_
  rw [pt_encT T y.isLt, Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem,
    List.mem_map]
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨a, ha, e⟩
    rwa [Fin.ext e] at ha

theorem beq_eq {T U : Array (Fin 22)} (hT : V T) (hU : V U) :
    (T == U) = Nat.beq (encT T) (encT U) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, encT_eq_iff hT hU]

theorem contains_eq {l : List (Array (Fin 22))} (hl : ∀ U ∈ l, V U) {T : Array (Fin 22)}
    (hT : V T) : l.contains T = (l.map encT).contains (encT T) := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · exact fun h => ⟨_, h, rfl⟩
  · rintro ⟨a, ha, e⟩
    rwa [encT_inj (hl a ha) hT e] at ha

theorem getD_one_eq (T : Array (Fin 22)) : (T.getD 1 0 == 1) = Nat.beq (pt (encT T) 1) 1 := by
  rw [pt_encT T (by norm_num), Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq, Fin.ext_iff]
  rfl

theorem nodup_map_encT {l : List (Array (Fin 22))} (hl : ∀ T ∈ l, V T) :
    (l.map encT).Nodup ↔ l.Nodup := by
  constructor
  · exact List.Nodup.of_map _
  · exact fun h => h.map_on fun a ha b hb e => encT_inj (hl a ha) (hl b hb) e

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem a2Check_eq (gT gTi : List (Array (Fin 22))) :
    a2Check gT gTi = a2CheckP (gT.map encT) (gTi.map encT) := by
  unfold a2Check a2CheckP
  have hn : (a2W.map (wtab gT gTi)).Nodup ↔ (a2W.map (pwtab (gT.map encT) (gTi.map encT))).Nodup := by
    rw [← nodup_map_encT (fun T hT => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hT
      exact V_wtab gT gTi s), List.map_map]
    simp only [Function.comp_def, encT_wtab]
  simp only [hn, fixesF_eq, encT_wtab]

theorem pqCheck_eq {gT gTi crdT : List (Array (Fin 22))} (hc : ∀ T ∈ crdT, V T)
    (hg : ∀ T ∈ gT, V T) :
    pqCheck gT gTi crdT = pqCheckP (gT.map encT) (gTi.map encT) (crdT.map encT) := by
  unfold pqCheck pqCheckP
  simp only [fixesF_eq, presF_eq, getD_one_eq, contains_eq hc (V_getD hg 0),
    contains_eq hc (V_getD hg 1), encT_tmul, encT_getD]

theorem invCheck_eq {gT gTi crdT : List (Array (Fin 22))} (hc : ∀ T ∈ crdT, V T) :
    invCheck gT gTi crdT = invCheckP (gT.map encT) (gTi.map encT) (crdT.map encT) := by
  unfold invCheck invCheckP
  simp only [strictB_eq', beq_eq, contains_eq hc, fixesF_eq, encT_tmul, encT_tid, encT_wtab,
    V_tmul, V_tid, V_wtab]

theorem conjCheck_eq {gT gTi : List (Array (Fin 22))} (hg : ∀ T ∈ gT, V T)
    (hgi : ∀ T ∈ gTi, V T) :
    conjCheck gT gTi = conjCheckP (gT.map encT) (gTi.map encT) := by
  unfold conjCheck conjCheckP
  simp only [strictB_eq', beq_eq, encT_tmul, encT_tid, encT_wtab, encT_wtabI, encT_getD, V_tmul,
    V_tid, V_wtab, V_getD hg, V_getD hgi]

theorem fun5 (f : Fin 5 → Nat) : f = fun i => [f 0, f 1, f 2, f 3, f 4].getD i.val pI := by
  funext i
  fin_cases i <;> rfl

theorem s1Check_eq (gT gTi : List (Array (Fin 22))) :
    s1Check gT gTi = s1CheckP (gT.map encT) (gTi.map encT) := by
  unfold s1Check s1CheckP
  refine List.all_congr rfl fun σ => ?_
  simp only [strictB_eq', presF_eq, beq_eq, encT_evalT, encT_tid, encT_wtab, encT_wtabI,
    V_evalT, V_tid]
  rw [fun5 (fun i : Fin 5 => pwtab (gT.map encT) (gTi.map encT) (σ.getD i.val "")),
    fun5 (fun i : Fin 5 => pwtabI (gT.map encT) (gTi.map encT) (σ.getD i.val ""))]
  rfl

theorem rhCheck_eq {gT gTi : List (Array (Fin 22))} (hg : ∀ T ∈ gT, V T) :
    rhCheck gT gTi = rhCheckP (gT.map encT) (gTi.map encT) := by
  unfold rhCheck rhCheckP
  simp only [getD_one_eq, beq_eq, encT_evalT, encT_tid, encT_getD, encT_wtab, encT_wtabI,
    V_evalT, V_tid, V_getD hg]

theorem encT_ite (c : Prop) [Decidable c] (s t : Array (Fin 22)) :
    encT (if c then s else t) = if c then encT s else encT t := by
  split <;> rfl

theorem encT_candT (T₀ T₁ T₂ : Array (Fin 22)) (i : Fin 5) :
    encT (candT T₀ T₁ T₂ i) = pcandT (encT T₀) (encT T₁) (encT T₂) i := by
  unfold candT pcandT
  rw [encT_getD]
  rfl

theorem glueCheck_eq {gT gTi crdT : List (Array (Fin 22))} (hc : ∀ T ∈ crdT, V T)
    (hg : ∀ T ∈ gT, V T) :
    glueCheck gT gTi crdT = glueCheckP (gT.map encT) (gTi.map encT) (crdT.map encT) := by
  unfold glueCheck glueCheckP
  simp only [strictB_eq', contains_eq hc, fixesF_eq, beq_eq, encT_evalT, encT_candT, encT_ite,
    encT_wtab, encT_getD, V_wtab, V_evalT]

theorem encT_tab (g : M22) : encT (tab g) = pkw 5 (g : Equiv.Perm (Fin 22)) := by
  unfold encT pkw
  refine enc_congr fun i hi => ?_
  rw [← Array.getElem_eq_getD (h := by unfold tab; rw [Array.size_ofFn]; exact hi)]
  unfold tab
  rw [Array.getElem_ofFn]
  simp [pv, hi]

theorem V_tab (g : M22) : V (tab g) := Array.size_ofFn

end CFSG.KC.L34

end
