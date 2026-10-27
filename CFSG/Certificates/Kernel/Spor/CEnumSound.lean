module

public import Certificates.Data.Kernel.Spor.CEnum
public import CFSG.Certificates.Kernel.Spor.KEnumSound
public import CFSG.Sporadic.SuzRecog.ModelGroupsKit

public section

namespace CFSG.KS.CEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KS.KeyBfsG
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo

local notation "cj" => CFSG.Sporadic.SuzRecog.ModelGroupsCheck.conjA

theorem fp_eq_fpOf (a : Array Nat) : fp a = fpOf (fun i => a[i]!) := rfl

theorem fpOf_congr {f g : Nat → Nat} (h : ∀ i < 1782, f i = g i) : fpOf f = fpOf g := by
  unfold fpOf
  rw [h 17 (by norm_num), h 333 (by norm_num), h 901 (by norm_num), h 1500 (by norm_num),
    h 1234 (by norm_num), h 77 (by norm_num)]

theorem invCand_comp_get {a ai b bi : Array Nat} (ha : isInvA 1782 a ai = true)
    (hb : isInvA 1782 b bi = true) {x : Nat} (hx : x < 1782) :
    (invCand 1782 (compA 1782 a b))[x]! = bi[ai[x]!]! := by
  obtain ⟨ra, rai⟩ := rep_permOfArr ha
  obtain ⟨rb, rbi⟩ := rep_permOfArr hb
  have hr := CFSG.Sporadic.SuzRecog.ModelGroups.rep_invCand (rep_compA ra rb)
  rw [hr.apply hx, rai.apply hx, rbi.apply (Fin.isLt _), mul_inv_rev, Equiv.Perm.mul_apply]

theorem key_T {T TI Rho : Nat} (hTI : canonK 1782 11 (mask 11) (1782 * 11) TI = true)
    (hR : canonK 1782 11 (mask 11) (1782 * 11) Rho = true)
    (hi : invCand 1782 (unpack 1782 11 T) = unpack 1782 11 TI) :
    fp (cj (unpack 1782 11 T) (unpack 1782 11 Rho)) = cKey 11 (mask 11) Rho T TI := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.conjA cKey
  rw [fp_eq_fpOf, hi]
  refine fpOf_congr fun x hx => ?_
  rw [FpBfs.compA_get hx, FpBfs.compA_get hx, unpack_get hx, unpack_get (canon_lt hTI hx),
    unpack_get (canon_lt hR (canon_lt hTI hx))]

theorem key_S {G GI T TI Rho : Nat} (hGI : canonK 1782 11 (mask 11) (1782 * 11) GI = true)
    (hT : canonK 1782 11 (mask 11) (1782 * 11) T = true)
    (hTI : canonK 1782 11 (mask 11) (1782 * 11) TI = true)
    (hR : canonK 1782 11 (mask 11) (1782 * 11) Rho = true)
    (hgi : isInvA 1782 (unpack 1782 11 G) (unpack 1782 11 GI) = true)
    (hti : isInvA 1782 (unpack 1782 11 T) (unpack 1782 11 TI) = true) :
    fp (cj (compA 1782 (unpack 1782 11 G) (unpack 1782 11 T)) (unpack 1782 11 Rho)) =
      cKeyS 11 (mask 11) Rho G GI T TI := by
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.conjA cKeyS
  rw [fp_eq_fpOf]
  refine fpOf_congr fun x hx => ?_
  have h1 : pg 11 (mask 11) GI x < 1782 := canon_lt hGI hx
  have h2 : pg 11 (mask 11) TI (pg 11 (mask 11) GI x) < 1782 := canon_lt hTI h1
  have h3 := canon_lt hR h2
  rw [FpBfs.compA_get hx, FpBfs.compA_get hx, invCand_comp_get hgi hti hx, unpack_get hx,
    unpack_get h1, unpack_get h2, FpBfs.compA_get h3, unpack_get h3, unpack_get (canon_lt hT h3)]

theorem cenumK_sound {k cnt cap R Rho : Nat} {G GI T TI PL POS FP SRT SRI : Nat → Nat}
    {gens : Array (Array Nat)} {root rho : Array Nat}
    (hg : ∀ s < k, gens[s]! = unpack 1782 11 (G s)) (hr : root = unpack 1782 11 R)
    (hrho : rho = unpack 1782 11 Rho)
    (hh : cenumHdK 1782 11 (mask 11) (1782 * 11) k cnt R Rho G GI T FP = true)
    (hp : ∀ i < cnt,
      cenumPtK 1782 11 (mask 11) (1782 * 11) k cnt Rho G GI T TI PL POS FP SRT SRI i = true)
    (hcap : cnt ≤ cap) :
    keyBfsG (fun g => fp (cj g rho)) (fun s x => compA 1782 gens[s]! x) k root (fp rho) cap =
        (Array.ofFn (n := cnt) fun i => unpack 1782 11 (T i.val),
          Array.ofFn (n := cnt) fun i => if i.val = 0 then 0 else PL i.val / k,
          Array.ofFn (n := cnt) fun i => if i.val = 0 then 0 else PL i.val % k) ∧
      (∀ i < cnt, invCand 1782 (unpack 1782 11 (T i)) = unpack 1782 11 (TI i) ∧
        isInvA 1782 (unpack 1782 11 (T i)) (unpack 1782 11 (TI i)) = true) ∧
      (∀ a < cnt, ∀ b < cnt, fp (cj (unpack 1782 11 (T a)) rho) =
        fp (cj (unpack 1782 11 (T b)) rho) → a = b) ∧
      (∀ i < cnt, 0 < i → PL i / k < i ∧ PL i % k < k ∧
        compA 1782 gens[PL i % k]! (unpack 1782 11 (T (PL i / k))) = unpack 1782 11 (T i)) ∧
      (∀ i < cnt, canonK 1782 11 (mask 11) (1782 * 11) (T i) = true) := by
  unfold cenumHdK at hh
  simp only [bAnd_iff] at hh
  obtain ⟨hk0, hc0, hT0, hcR, hFP0, hG⟩ := hh
  have hk0 := blt_true hk0
  have hc0 := blt_true hc0
  have hT0 : T 0 = R := Nat.eq_of_beq_eq_true hT0
  have hFP0 : FP 0 = fpK 11 (mask 11) Rho := Nat.eq_of_beq_eq_true hFP0
  have hG : ∀ s < k, canonK 1782 11 (mask 11) (1782 * 11) (G s) = true ∧
      canonK 1782 11 (mask 11) (1782 * 11) (GI s) = true ∧
      invCand 1782 (unpack 1782 11 (G s)) = unpack 1782 11 (GI s) ∧
      isInvA 1782 (unpack 1782 11 (G s)) (unpack 1782 11 (GI s)) = true := by
    intro s hs
    have h := allN_spec hG s hs
    simp only [bAnd_iff] at h
    exact ⟨h.1, h.2.1, invEqK_sound h.2.2⟩
  have sp : ∀ i < cnt, canonK 1782 11 (mask 11) (1782 * 11) (T i) = true ∧
      canonK 1782 11 (mask 11) (1782 * 11) (TI i) = true ∧
      permOK 1782 11 (mask 11) (1782 * 11) (T i) (TI i) = true ∧
      FP i = cKey 11 (mask 11) Rho (T i) (TI i) ∧
      (i ≠ 0 → PL i / k < i ∧ T i = pcomp 1782 11 (mask 11) (G (PL i % k)) (T (PL i / k)) ∧
        (i + 1 < cnt → PL i < PL (i + 1))) ∧
      (∀ s < k, POS (k * i + s) < cnt ∧
        FP (POS (k * i + s)) = cKeyS 11 (mask 11) Rho (G s) (GI s) (T i) (TI i) ∧
        (POS (k * i + s) = 0 ∨ PL (POS (k * i + s)) ≤ k * i + s)) ∧
      (SRI i < cnt ∧ SRT (SRI i) = i) ∧
      (SRT i < cnt ∧ (i + 1 < cnt → FP (SRT i) < FP (SRT (i + 1)))) := by
    intro i hi
    have h := hp i hi
    unfold cenumPtK at h
    simp only [strictB_eq, bAnd_iff] at h
    obtain ⟨c1, c2, a2, a3, a4, a5, ⟨a6, a7⟩, a8, -, a9⟩ := h
    refine ⟨c1, c2, a2, Nat.eq_of_beq_eq_true a3, fun h0 => ?_, fun s hs => ?_,
      ⟨blt_true a6, Nat.eq_of_beq_eq_true a7⟩, blt_true a8, fun h1 => ?_⟩
    · have hz : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hz] at a4
      simp only [bAnd_iff] at a4
      obtain ⟨b1, b2, b3⟩ := a4
      refine ⟨blt_true b1, Nat.eq_of_beq_eq_true b2, fun h1 => ?_⟩
      have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using h1
      rw [hb] at b3
      exact blt_true b3
    · have h := allN_spec a5 s hs
      simp only [bAnd_iff] at h
      obtain ⟨b1, b2, b3⟩ := h
      refine ⟨blt_true b1, Nat.eq_of_beq_eq_true b2, ?_⟩
      by_cases hz : POS (k * i + s) = 0
      · exact Or.inl hz
      · have hz' : Nat.beq (POS (Nat.add (Nat.mul k i) s)) 0 = false :=
          Bool.eq_false_iff.2 fun e => hz (Nat.eq_of_beq_eq_true e)
        rw [hz'] at b3
        exact Or.inr (by simpa [Nat.ble_eq] using b3)
    · have hb : Nat.blt (Nat.succ i) cnt = true := by simpa [Nat.blt_eq] using h1
      rw [hb] at a9
      exact blt_true a9
  have hinv : ∀ i < cnt, invCand 1782 (unpack 1782 11 (T i)) = unpack 1782 11 (TI i) ∧
      isInvA 1782 (unpack 1782 11 (T i)) (unpack 1782 11 (TI i)) = true :=
    fun i hi => invEqK_sound (sp i hi).2.2.1
  have hkey : ∀ i < cnt, fp (cj (unpack 1782 11 (T i)) rho) = FP i := by
    intro i hi
    rw [hrho, key_T (sp i hi).2.1 hcR (hinv i hi).1, (sp i hi).2.2.2.1]
  have hsort : ∀ j j', j < j' → j' < cnt → FP (SRT j) < FP (SRT j') := by
    intro j j' hj hj'
    induction j' with
    | zero => omega
    | succ j' ih =>
      rcases Nat.lt_or_ge j j' with a | a
      · exact Nat.lt_trans (ih a (by omega)) ((sp j' (by omega)).2.2.2.2.2.2.2.2 hj')
      · have e : j = j' := by omega
        subst e
        exact (sp j (by omega)).2.2.2.2.2.2.2.2 hj'
  have hinj : ∀ a < cnt, ∀ b < cnt, fp (cj (unpack 1782 11 (T a)) rho) =
      fp (cj (unpack 1782 11 (T b)) rho) → a = b := by
    intro a ha b hb e
    rw [hkey a ha, hkey b hb] at e
    obtain ⟨ra, ea⟩ := (sp a ha).2.2.2.2.2.2.1
    obtain ⟨rb, eb⟩ := (sp b hb).2.2.2.2.2.2.1
    rw [← ea, ← eb] at e
    rcases Nat.lt_trichotomy (SRI a) (SRI b) with c | c | c
    · exact absurd e (Nat.ne_of_lt (hsort _ _ c rb))
    · rw [← ea, ← eb, c]
    · exact absurd e (Nat.ne_of_gt (hsort _ _ c ra))
  have htree : ∀ i < cnt, 0 < i → PL i / k < i ∧ PL i % k < k ∧
      compA 1782 gens[PL i % k]! (unpack 1782 11 (T (PL i / k))) = unpack 1782 11 (T i) := by
    intro i hi h0
    obtain ⟨b1, b2, -⟩ := (sp i hi).2.2.2.2.1 (by omega)
    have hs : PL i % k < k := Nat.mod_lt _ hk0
    refine ⟨b1, hs, ?_⟩
    rw [hg _ hs, b2, CFSG.KC.BfsPin.compA_unpack (hG _ hs).1 (sp _ (by omega)).1]
  have hstep : ∀ i < cnt, ∀ s < k, fp (cj (compA 1782 gens[s]! (unpack 1782 11 (T i))) rho) =
      cKeyS 11 (mask 11) Rho (G s) (GI s) (T i) (TI i) := by
    intro i hi s hs
    rw [hg s hs, hrho]
    exact key_S (hG s hs).2.1 (sp i hi).1 (sp i hi).2.1 hcR (hG s hs).2.2.2
      (hinv i hi).2
  have hdm : ∀ c, k * (c / k) + c % k = c := fun c => Nat.div_add_mod c k
  have Rec : GRec (fun g => fp (cj g rho)) (fun s x => compA 1782 gens[s]! x) k root (fp rho) cnt
      (k * cnt) (fun i => unpack 1782 11 (T i)) (fun i => if i = 0 then 0 else PL i / k)
      (fun i => if i = 0 then 0 else PL i % k) POS := by
    refine ⟨hk0, hc0, by rw [hT0, hr], ?_, by simp, by simp, hinj, fun i h0 hi => ?_,
      fun i h0 hi => ?_, ?_, fun e he => ?_⟩
    · have := hkey 0 hc0
      rw [hFP0, ← fp_unpack, ← hrho, hT0, ← hr] at this
      exact this.symm
    · simp only [Nat.pos_iff_ne_zero.1 h0, ↓reduceIte]
      obtain ⟨a1, a2, a3⟩ := htree i hi h0
      exact ⟨a1, a2, a3.symm⟩
    · have h1 : i + 1 ≠ 0 := by omega
      simp only [Nat.pos_iff_ne_zero.1 h0, h1, ↓reduceIte, hdm]
      exact ((sp i (by omega)).2.2.2.2.1 (by omega)).2.2 hi
    · by_cases h1 : cnt - 1 = 0
      · simp only [h1, ↓reduceIte]
        have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hc0)
        omega
      · simp only [h1, ↓reduceIte]
        exact CFSG.KS.KEnum.mul_add_lt
          (((sp (cnt - 1) (by omega)).2.2.2.2.1 h1).1.trans (by omega)) (Nat.mod_lt _ hk0)
    · have hed : e / k < cnt := (Nat.div_lt_iff_lt_mul hk0).2 (by rw [Nat.mul_comm]; exact he)
      have hek : e % k < k := Nat.mod_lt _ hk0
      obtain ⟨c1, c2, c3⟩ := (sp (e / k) hed).2.2.2.2.2.1 (e % k) hek
      rw [hdm e] at c1 c2 c3
      refine ⟨c1, (hstep _ hed _ hek).trans ?_, ?_⟩
      · rw [hkey _ c1, c2]
      · rcases c3 with z | z
        · exact Or.inl z
        · by_cases hz : POS e = 0
          · exact Or.inl hz
          · right
            simp only [hz, ↓reduceIte, hdm]
            exact z
  have hcap' : (if cnt - 1 = 0 then 0 else PL (cnt - 1) / k) < cap := by
    by_cases h1 : cnt - 1 = 0
    · simp only [h1, ↓reduceIte]
      omega
    · simp only [h1, ↓reduceIte]
      have := ((sp (cnt - 1) (by omega)).2.2.2.2.1 h1).1
      omega
  obtain ⟨-, r2, r3, r4, r5⟩ := keyBfsG_rec Rec hcap'
  have hsz := r3 (Nat.le_refl _)
  have ext : ∀ {α : Type} [Inhabited α] (a : Array α) (f : Nat → α), a.size = cnt →
      (∀ i < cnt, a[i]! = f i) → a = Array.ofFn (n := cnt) fun i => f i.val :=
    fun a f ha hf => by
      apply Array.ext
      · simp [ha]
      · intro i h1 h2
        rw [Array.getElem_ofFn, ← getElem!_pos a i h1, hf i (by omega)]
  refine ⟨?_, hinv, hinj, htree, fun i hi => (sp i hi).1⟩
  generalize keyBfsG (fun g => fp (cj g rho)) (fun s x => compA 1782 gens[s]! x) k root (fp rho)
    cap = S at hsz r2 r4 r5
  obtain ⟨S1, S2, S3⟩ := S
  simp only at hsz r2 r4 r5
  rw [ext S1 _ hsz fun i hi => (r2 i hi).1, ext S2 _ (r4.trans hsz) fun i hi => (r2 i hi).2.1,
    ext S3 _ (r5.trans hsz) fun i hi => (r2 i hi).2.2]

end CFSG.KS.CEnum

end
