module

public import Certificates.Data.Kernel.SmithEKFp
public import CFSG.Certificates.Kernel.SmithEK.CdSound

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

theorem recAll_congr (f : Nat → Bool → Bool) (p : Nat → Bool) (hf : ∀ k b, f k b = (b && p k))
    (n : Nat) : Nat.rec (motive := fun _ => Bool) true f n = true ↔ ∀ k < n, p k = true := by
  have e : f = fun k b => b && p k := funext fun k => funext fun b => hf k b
  subst e
  exact recAll_iff p n

theorem fpWts_eq (WT : List Nat) : ∀ PI : List Nat, fpWts WT PI = PI.map fun i => WT.getD i 0
  | [] => rfl
  | i :: PI => congrArg (WT.getD i 0 :: ·) (fpWts_eq WT PI)

theorem fpPairsK_sound {TP : Nat → Nat} {W : List Nat} {L a : Nat} {PL : List (List Nat)}
    {PM PI PJ : List Nat} (h : fpPairsK TP W L a PL PM PI PJ = true) :
    ∀ k < 20, cdPlK TP W L a PL PM (PI.getD k 0) (PJ.getD k 0) = true :=
  (recAll_iff (fun k => cdPlK TP W L a PL PM (PI.getD k 0) (PJ.getD k 0)) 20).1 h

theorem fpUnitK_sound {WT PI UM : List Nat} (h : fpUnitK WT PI UM = true) :
    ∀ t < 20, xorSel (PI.map fun i => WT.getD i 0) (UM.getD t 0) = 2 ^ t := by
  have h1 := (recAll_iff (fun t => Nat.beq (cdSel (fpWts WT PI) (UM.getD t 0)) (Nat.pow 2 t)) 20).1 h
  intro t ht
  have h2 := Nat.eq_of_beq_eq_true (h1 t ht)
  rwa [cdSel_eq, fpWts_eq] at h2

theorem fpBsK_sound {WT PI PJ BS BM : List Nat} (h : fpBsK WT PI PJ BS BM = true) :
    BS.length ≤ 8 ∧ ∀ k < 20,
      xorSel BS (BM.getD k 0) = WT.getD (PJ.getD k 0) 0 ^^^ WT.getD (PI.getD k 0) 0 := by
  unfold fpBsK at h
  rw [Bool.and_eq_true, Nat.ble_eq, lenK_eq] at h
  have h1 := (recAll_iff (fun k => Nat.beq (cdSel BS (BM.getD k 0))
    (Nat.xor (WT.getD (PJ.getD k 0) 0) (WT.getD (PI.getD k 0) 0))) 20).1 h.2
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := Nat.eq_of_beq_eq_true (h1 k hk)
  rwa [cdSel_eq] at h2

theorem fpFixK_sound {TP : Nat → Nat} {W : List Nat} {L a : Nat} {FX : List Nat}
    (h : fpFixK TP W L a (maskK FX) = true) : ∀ x < 693, cdImg TP W L a x = x → x ∈ FX := by
  have h1 := (recAll_iff (fun x => bif Nat.beq (cdImg TP W L a x) x then bitK (maskK FX) x
    else true) 693).1 h
  intro x hx he
  have h2 := h1 x hx
  rw [show Nat.beq (cdImg TP W L a x) x = true from Nat.beq_eq_true_eq _ _ ▸ he, cond_true,
    bitK_eq, maskK_testBit] at h2
  exact h2

theorem fpAllK_sound {TP : Nat → Nat} {W : List Nat} {L a : Nat} :
    ∀ {FX : List Nat}, fpAllK TP W L a FX = true →
      FX.Nodup ∧ ∀ y ∈ FX, y < 693 ∧ cdImg TP W L a y = y
  | [], _ => ⟨List.nodup_nil, fun _ hy => absurd hy List.not_mem_nil⟩
  | y :: ys, h => by
    have e : fpAllK TP W L a (y :: ys) = (Nat.blt y 693 && Nat.beq (cdImg TP W L a y) y &&
        !memK y ys && fpAllK TP W L a ys) := rfl
    rw [e, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
      Bool.not_eq_true', ← Bool.not_eq_true, memK_iff] at h
    obtain ⟨⟨⟨hy, hfix⟩, hnm⟩, hrest⟩ := h
    obtain ⟨hnd, hall⟩ := fpAllK_sound hrest
    exact ⟨List.nodup_cons.2 ⟨hnm, hnd⟩, List.forall_mem_cons.2 ⟨⟨hy, hfix⟩, hall⟩⟩

theorem fpCodeK_sound {PC FX FC : List Nat} (h : fpCodeK PC FX FC = true) :
    FC.length = FX.length ∧ ∀ k < FX.length, FC.getD k 0 = PC.getD (FX.getD k 0) 0 := by
  unfold fpCodeK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenK_eq, lenK_eq] at h
  have h1 := (recAll_iff (fun k => Nat.beq (FC.getD k 0) (PC.getD (FX.getD k 0) 0))
    FX.length).1 (lenK_eq FX ▸ h.2)
  exact ⟨h.1, fun k hk => Nat.eq_of_beq_eq_true (h1 k hk)⟩

theorem fpTreeK_sound {TP : Nat → Nat} {FX FE : List Nat} (h : fpTreeK TP FX FE = true) :
    FE.length + 1 = FX.length ∧ ∀ k < FE.length, ∃ g < FX.length, ∃ m ≤ k,
      at' 10 (TP (FX.getD g 0)) (FX.getD m 0) = FX.getD (k + 1) 0 := by
  unfold fpTreeK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenK_eq, lenK_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := (recAll_congr _ (fun k => Nat.blt (Nat.mod (FE.getD k 0) 64) FX.length &&
      Nat.ble (Nat.div (FE.getD k 0) 64) k &&
      Nat.beq (at' 10 (TP (FX.getD (Nat.mod (FE.getD k 0) 64) 0))
        (FX.getD (Nat.div (FE.getD k 0) 64) 0)) (FX.getD (Nat.succ k) 0))
    (fun k b => by simp only [Bool.and_assoc]) FE.length).1 h.2 k hk
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h2
  exact ⟨_, h2.1.1, _, h2.1.2, h2.2⟩

theorem fpTree_induct {TP : Nat → Nat} {FX FE : List Nat} (h : fpTreeK TP FX FE = true)
    (Q : Nat → Prop) (h0 : Q (FX.getD 0 0))
    (hstep : ∀ g < FX.length, ∀ u ∈ FX, Q u → Q (at' 10 (TP (FX.getD g 0)) u)) :
    ∀ v ∈ FX, Q v := by
  obtain ⟨hlen, he⟩ := fpTreeK_sound h
  have key : ∀ k < FX.length, Q (FX.getD k 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact h0
      | succ k =>
        obtain ⟨g, hg, m, hm, e⟩ := he k (by omega)
        rw [← e]
        refine hstep g hg _ ?_ (ih m (by omega) (by omega))
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  rw [← List.getD_eq_getElem _ 0 hk]
  exact key k hk

theorem fpLineK_sound {FC FL : List Nat} (h : fpLineK FC FL = true) :
    FL.length + 1 = FC.length ∧ ∀ k < FL.length, ∃ m ≤ k, ∃ n < FC.length, ∃ l u : Nat,
      0 < l ∧ l < 4 ∧ 0 < u ∧ u < 4 ∧
      FC.getD n 0 = fpScale l (FC.getD m 0) ^^^ fpScale u (FC.getD (k + 1) 0) := by
  unfold fpLineK at h
  rw [Bool.and_eq_true, Nat.beq_eq, lenK_eq, lenK_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  have h2 := (recAll_congr _ (fun k => Nat.ble (Nat.mod (FL.getD k 0) 64) k &&
      Nat.blt (Nat.mod (Nat.div (FL.getD k 0) 64) 64) FC.length &&
      Nat.blt 0 (Nat.mod (Nat.div (FL.getD k 0) 4096) 4) &&
      Nat.blt 0 (Nat.div (FL.getD k 0) 16384) && Nat.blt (Nat.div (FL.getD k 0) 16384) 4 &&
      Nat.beq (FC.getD (Nat.mod (Nat.div (FL.getD k 0) 64) 64) 0)
        (Nat.xor (fpScale (Nat.mod (Nat.div (FL.getD k 0) 4096) 4) (FC.getD (Nat.mod (FL.getD k 0) 64) 0))
          (fpScale (Nat.div (FL.getD k 0) 16384) (FC.getD (Nat.succ k) 0))))
    (fun k b => by simp only [Bool.and_assoc]) FL.length).1 h.2 k hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h2
  obtain ⟨⟨⟨⟨⟨hm, hn⟩, hl⟩, hu⟩, hu4⟩, he⟩ := h2
  exact ⟨_, hm, _, hn, _, _, hl, Nat.mod_lt _ (by omega), hu, hu4, he⟩

theorem fpEntries_iff (n : Nat) : ∀ S : List Nat,
    List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Nat.blt (Nat.mod e 64) n && Nat.blt (Nat.div e 64) 4 && ih) S = true ↔
      ∀ e ∈ S, e % 64 < n ∧ e / 64 < 4
  | [] => by simp
  | e :: S => by
    have h := fpEntries_iff n S
    simp only [Bool.and_eq_true, Nat.blt_eq, List.forall_mem_cons] at h ⊢
    rw [h]
    rfl

theorem fpSpanK_sound {FC : List Nat} {SP : List (List Nat)} (h : fpSpanK FC SP = true) :
    ∀ t < 6, fpComb FC (SP.getD t []) = 4 ^ t ∧ ∀ e ∈ SP.getD t [], e % 64 < FC.length ∧ e / 64 < 4 := by
  have h1 := (cdRecAll2_iff (fun t => Nat.beq (fpComb FC (SP.getD t [])) (Nat.pow 4 t))
    (fun t => List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Nat.blt (Nat.mod e 64) (lenK FC) && Nat.blt (Nat.div e 64) 4 && ih)
      (SP.getD t [])) 6).1 h
  intro t ht
  obtain ⟨h2, h3⟩ := h1 t ht
  rw [fpEntries_iff, lenK_eq] at h3
  exact ⟨Nat.eq_of_beq_eq_true h2, h3⟩

theorem fpRepK_sound {TP : Nat → Nat} {W : List Nat} {L a : Nat} {PL : List (List Nat)}
    {PM WT PC PI PJ UM BS BM FX FC FE FL : List Nat} {SP : List (List Nat)}
    (h : fpRepK TP W L a PL PM WT PC PI PJ UM BS BM FX FC FE FL SP = true) :
    PI.length = 20 ∧ PJ.length = 20 ∧
      (∀ k < 20, cdPlK TP W L a PL PM (PI.getD k 0) (PJ.getD k 0) = true) ∧
      (∀ t < 20, xorSel (PI.map fun i => WT.getD i 0) (UM.getD t 0) = 2 ^ t) ∧
      BS.length ≤ 8 ∧
      (∀ k < 20, xorSel BS (BM.getD k 0) = WT.getD (PJ.getD k 0) 0 ^^^ WT.getD (PI.getD k 0) 0) ∧
      (∀ x < 693, cdImg TP W L a x = x → x ∈ FX) ∧ FX.Nodup ∧
      (∀ y ∈ FX, y < 693 ∧ cdImg TP W L a y = y) ∧ FX.length % 2 = 1 ∧ FX.length ≤ 64 ∧
      fpCodeK PC FX FC = true ∧ fpTreeK TP FX FE = true ∧ fpLineK FC FL = true ∧
      fpSpanK FC SP = true := by
  unfold fpRepK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, lenK_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hPI, hPJ⟩, hpairs⟩, hunit⟩, hbs⟩, hfix⟩, hall⟩, hodd⟩, h64⟩, hcode⟩,
    htree⟩, hline⟩, hspan⟩ := h
  obtain ⟨hnd, hfx⟩ := fpAllK_sound hall
  obtain ⟨hb8, hbm⟩ := fpBsK_sound hbs
  exact ⟨hPI, hPJ, fpPairsK_sound hpairs, fpUnitK_sound hunit, hb8, hbm, fpFixK_sound hfix, hnd,
    hfx, hodd, h64, hcode, htree, hline, hspan⟩

end CFSG.SmithE.K
