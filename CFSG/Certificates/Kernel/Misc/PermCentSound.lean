module

public import Certificates.Data.Kernel.Misc.PermCent
public import CFSG.Certificates.Kernel.Misc.PermClosWSound
public import Mathlib.GroupTheory.OrderOfElement
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.Cent

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW

section CentDfsSound

open CFSG.KC.Ord (andB notB)

private def csPts (O : ℕ → List ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | k, m + 1 => O k ++ csPts O (k + 1) m

private theorem csPts_add (O : ℕ → List ℕ) :
    ∀ a k b, csPts O k (a + b) = csPts O k a ++ csPts O (k + a) b
  | 0, k, b => by simp [csPts]
  | a + 1, k, b => by
    rw [Nat.add_right_comm, csPts, csPts, csPts_add O a (k + 1) b, List.append_assoc,
      Nat.add_right_comm k 1 a, Nat.add_assoc]

private theorem csPts_succ (O : ℕ → List ℕ) (k : ℕ) : csPts O 0 (k + 1) = csPts O 0 k ++ O k := by
  rw [csPts_add O k 0 1]
  simp [csPts]

private theorem csMem_pts {O : ℕ → List ℕ} {nO k q : ℕ} (hk : k < nO) (hq : q ∈ O k) :
    q ∈ csPts O 0 nO := by
  obtain ⟨m, rfl⟩ : ∃ m, nO = k + (m + 1) := ⟨nO - k - 1, by omega⟩
  rw [csPts_add O k 0 (m + 1)]
  simp [csPts, hq]

private noncomputable def csCov (n w : ℕ) (R : ℕ → ℕ) (O : ℕ → List ℕ) (U : ℕ → ℕ) (m : ℕ) :
    ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
    (fun _ used => Nat.beq used (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)))
    (fun _ ih k used =>
      List.rec (motive := fun _ => ℕ → Bool) (fun u => ih (Nat.succ k) u)
        (fun q _ ihl u => andB (Nat.blt q n) (andB (notB (bitB u q))
          (andB (Nat.beq (pg w (mask w) (U q) (R k)) q)
            (ihl (Nat.lor u (Nat.shiftLeft (nat_lit 1) q)))))) (O k) used)
    m

private noncomputable def csDfs (n w : ℕ) (G : ℕ → ℕ) (nG : ℕ) (O : ℕ → List ℕ) (U : ℕ → ℕ)
    (f : ℕ → Bool) (m : ℕ) : ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool) (fun _ X _ => f X)
    (fun _ ih k X used => CFSG.KC.LQT.P.allN n fun t =>
      Bool.rec (motive := fun _ => Bool) true
        (CFSG.KC.LQT.P.letB (assignX w U (O k) t X) fun X' =>
          Bool.rec (motive := fun _ => Bool) true (ih (Nat.succ k) X' (assignU w U (O k) t used))
            (commAt w G nG (O k) X'))
        (assignOK w U (O k) t used))
    m

private theorem csBit (u v : ℕ) : bitB u v = u.testBit v := CFSG.KC.LQT.P.bit_eq u v

private theorem csLor (u v : ℕ) : Nat.lor u (Nat.shiftLeft (nat_lit 1) v) = u ||| 2 ^ v :=
  CFSG.KC.LQT.P.lor_eq u v

private theorem csCov_list (n w : ℕ) (R U : ℕ → ℕ) (k : ℕ) (c : ℕ → Bool) :
    ∀ (L : List ℕ) (u : ℕ),
      List.rec (motive := fun _ => ℕ → Bool) (fun u => c u)
        (fun q _ ihl u => andB (Nat.blt q n) (andB (notB (bitB u q))
          (andB (Nat.beq (pg w (mask w) (U q) (R k)) q)
            (ihl (Nat.lor u (Nat.shiftLeft (nat_lit 1) q)))))) L u = true →
      (∀ q ∈ L, q < n ∧ pg w (mask w) (U q) (R k) = q) ∧ L.Nodup ∧
        (∀ q ∈ L, u.testBit q = false) ∧
        ∃ u', c u' = true ∧ ∀ v, u'.testBit v = true ↔ u.testBit v = true ∨ v ∈ L
  | [], u, h => ⟨by simp, List.nodup_nil, by simp, u, h, by simp⟩
  | q :: L, u, h => by
    change andB (Nat.blt q n) (andB (notB (bitB u q))
      (andB (Nat.beq (pg w (mask w) (U q) (R k)) q) (List.rec (motive := fun _ => ℕ → Bool)
        (fun u => c u) (fun q _ ihl u => andB (Nat.blt q n) (andB (notB (bitB u q))
          (andB (Nat.beq (pg w (mask w) (U q) (R k)) q)
            (ihl (Nat.lor u (Nat.shiftLeft (nat_lit 1) q)))))) L
        (Nat.lor u (Nat.shiftLeft (nat_lit 1) q))))) = true at h
    obtain ⟨hq, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
    obtain ⟨hb, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
    obtain ⟨hU, hL⟩ := CFSG.KC.LQT.P.andB_iff.1 h
    rw [CFSG.KC.LQT.P.blt_iff] at hq
    rw [CFSG.KC.LQT.P.notB_iff, csBit] at hb
    rw [CFSG.KC.LQT.P.beq_iff] at hU
    obtain ⟨h1, h2, h3, u', hc, hu'⟩ := csCov_list n w R U k c L _ hL
    rw [csLor] at h3 hu'
    have hb' : u.testBit q = false := by simpa using hb
    have h3' : ∀ q' ∈ L, q' ≠ q ∧ u.testBit q' = false := fun q' hq' => by
      have := h3 q' hq'
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_false_iff] at this
      exact ⟨fun e => by rw [e] at this; simp at this, this.1⟩
    refine ⟨?_, ?_, ?_, u', hc, fun v => ?_⟩
    · intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      exacts [⟨hq, hU⟩, h1 q' hq']
    · exact List.nodup_cons.2 ⟨fun hm => (h3' q hm).1 rfl, h2⟩
    · intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      exacts [hb', (h3' q' hq').2]
    · rw [hu', Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_cons]
      constructor
      · rintro ((h | rfl) | h)
        exacts [Or.inl h, Or.inr (Or.inl rfl), Or.inr (Or.inr h)]
      · rintro (h | rfl | h)
        exacts [Or.inl (Or.inl h), Or.inl (Or.inr rfl), Or.inr h]

private theorem csCov_spec (n w : ℕ) (R : ℕ → ℕ) (O : ℕ → List ℕ) (U : ℕ → ℕ) :
    ∀ m k used, csCov n w R O U m k used = true →
      (∀ q ∈ csPts O k m, q < n) ∧ (csPts O k m).Nodup ∧
        (∀ q ∈ csPts O k m, used.testBit q = false) ∧
        (∀ i < m, ∀ q ∈ O (k + i), pg w (mask w) (U q) (R (k + i)) = q) ∧
        (∀ v < n, used.testBit v = true ∨ v ∈ csPts O k m)
  | 0, k, used, h => by
    change Nat.beq used (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)) = true at h
    rw [CFSG.KC.LQT.P.beq_iff] at h
    have e : used = 2 ^ n - 1 := by
      rw [h]
      change (1 <<< n) - 1 = 2 ^ n - 1
      rw [Nat.one_shiftLeft]
    refine ⟨by simp [csPts], List.nodup_nil, by simp [csPts], by simp, fun v hv => Or.inl ?_⟩
    rw [e, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hv
  | m + 1, k, used, h => by
    obtain ⟨h1, h2, h3, u', hc, hu'⟩ := csCov_list n w R U k (csCov n w R O U m (k + 1)) (O k)
      used h
    obtain ⟨i1, i2, i3, i4, i5⟩ := csCov_spec n w R O U m (k + 1) u' hc
    have hpts : csPts O k (m + 1) = O k ++ csPts O (k + 1) m := rfl
    rw [hpts]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      exacts [(h1 q hq).1, i1 q hq]
    · refine List.nodup_append.2 ⟨h2, i2, fun a ha b hb e => ?_⟩
      subst e
      have := i3 a hb
      have h' := (hu' a).2 (Or.inr ha)
      rw [this] at h'
      exact Bool.false_ne_true h'
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h3 q hq
      · cases hb : used.testBit q
        · rfl
        · have := (hu' q).2 (Or.inl hb)
          rw [i3 q hq] at this
          exact absurd this Bool.false_ne_true
    · intro i hi q hq
      rcases i with _ | i
      · exact (h1 q hq).2
      · have e : k + (i + 1) = k + 1 + i := by omega
        rw [e] at hq ⊢
        exact i4 i (by omega) q hq
    · intro v hv
      rcases i5 v hv with h | h
      · rcases (hu' v).1 h with h | h
        exacts [Or.inl h, Or.inr (List.mem_append_left _ h)]
      · exact Or.inr (List.mem_append_right _ h)

private theorem csAssignOK {w : ℕ} {U F : ℕ → ℕ} {t : ℕ} :
    ∀ (L : List ℕ) (used : ℕ), (∀ q ∈ L, pg w (mask w) (U q) t = F q) →
      (∀ q ∈ L, used.testBit (F q) = false) → (L.map F).Nodup → assignOK w U L t used = true
  | [], _, _, _, _ => rfl
  | q :: L, used, hU, hb, hnd => by
    change CFSG.KC.LQT.P.letB (pg w (mask w) (U q) t) (fun v => andB (notB (bitB used v))
      (assignOK w U L t (Nat.lor used (Nat.shiftLeft (nat_lit 1) v)))) = true
    rw [CFSG.KC.LQT.P.letB_eq, hU q List.mem_cons_self, CFSG.KC.LQT.P.andB_iff,
      CFSG.KC.LQT.P.notB_iff, csBit, csLor]
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨by simp [hb q List.mem_cons_self], csAssignOK L _
      (fun q' hq' => hU q' (List.mem_cons_of_mem _ hq')) (fun q' hq' => ?_) hnd.2⟩
    rw [Nat.testBit_or, Nat.testBit_two_pow, hb q' (List.mem_cons_of_mem _ hq'), Bool.false_or,
      decide_eq_false_iff_not]
    exact fun e => hnd.1 (e ▸ List.mem_map_of_mem hq')

private theorem csAssignU {w : ℕ} {U F : ℕ → ℕ} {t : ℕ} :
    ∀ (L : List ℕ) (used : ℕ), (∀ q ∈ L, pg w (mask w) (U q) t = F q) →
      ∀ v, (assignU w U L t used).testBit v = true ↔ (∃ q ∈ L, F q = v) ∨ used.testBit v = true
  | [], used, _, v => by
    change used.testBit v = true ↔ _
    simp
  | q :: L, used, hU, v => by
    change (Nat.lor (Nat.shiftLeft (nat_lit 1) (pg w (mask w) (U q) t))
      (assignU w U L t used)).testBit v = true ↔ _
    have e : Nat.shiftLeft (nat_lit 1) (pg w (mask w) (U q) t) = 2 ^ F q := by
      rw [hU q List.mem_cons_self]
      exact Nat.one_shiftLeft _
    change ((Nat.shiftLeft (nat_lit 1) (pg w (mask w) (U q) t)) |||
      (assignU w U L t used)).testBit v = true ↔ _
    rw [e, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
      csAssignU L used (fun q' hq' => hU q' (List.mem_cons_of_mem _ hq')) v]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc.symm

private theorem csAssignX {w : ℕ} {U F : ℕ → ℕ} {t : ℕ} (hF : ∀ i, F i < 2 ^ w) :
    ∀ (L P : List ℕ) (X : ℕ), (∀ q ∈ L, pg w (mask w) (U q) t = F q) →
      CFSG.KS.PF.Fld w X (fun i => if i ∈ P then F i else 0) →
      CFSG.KS.PF.Fld w (assignX w U L t X) (fun i => if i ∈ L ∨ i ∈ P then F i else 0)
  | [], P, X, _, hX => CFSG.KS.PF.fld_congr hX fun i => by simp
  | q :: L, P, X, hU, hX => by
    have ih := csAssignX hF L P X (fun q' hq' => hU q' (List.mem_cons_of_mem _ hq')) hX
    have h1 := CFSG.KS.PF.fld_shl q (CFSG.KS.PF.fld_one (hF q))
    change CFSG.KS.PF.Fld w ((pg w (mask w) (U q) t) <<< (w * q) ||| assignX w U L t X) _
    rw [hU q List.mem_cons_self]
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_or h1 ih) fun i => ?_
    by_cases hi : i = q
    · subst hi
      simp only [le_refl, ↓reduceIte, Nat.sub_self, List.mem_cons, true_or]
      split_ifs <;> simp
    · have h2 : ¬ (q ≤ i ∧ i - q = 0) := by omega
      have h3 : (if q ≤ i then (if i - q = 0 then F q else 0) else 0) = 0 := by
        split_ifs <;> first | rfl | omega
      rw [h3, Nat.zero_or]
      simp [List.mem_cons, hi]

private theorem csDfs_step {n w : ℕ} {G : ℕ → ℕ} {nG : ℕ} {O : ℕ → List ℕ} {U : ℕ → ℕ}
    {f : ℕ → Bool} {m k X used t : ℕ} (h : csDfs n w G nG O U f (m + 1) k X used = true)
    (ht : t < n) (hok : assignOK w U (O k) t used = true)
    (hc : commAt w G nG (O k) (assignX w U (O k) t X) = true) :
    csDfs n w G nG O U f m (k + 1) (assignX w U (O k) t X) (assignU w U (O k) t used) = true := by
  change CFSG.KC.LQT.P.allN n (fun t => Bool.rec (motive := fun _ => Bool) true
    (CFSG.KC.LQT.P.letB (assignX w U (O k) t X) fun X' =>
      Bool.rec (motive := fun _ => Bool) true
        (csDfs n w G nG O U f m (Nat.succ k) X' (assignU w U (O k) t used))
        (commAt w G nG (O k) X'))
    (assignOK w U (O k) t used)) = true at h
  have h1 := (CFSG.KC.LQT.P.allN_iff _ _).1 h t ht
  rw [hok] at h1
  change CFSG.KC.LQT.P.letB (assignX w U (O k) t X) (fun X' =>
      Bool.rec (motive := fun _ => Bool) true
        (csDfs n w G nG O U f m (Nat.succ k) X' (assignU w U (O k) t used))
        (commAt w G nG (O k) X')) = true at h1
  rw [CFSG.KC.LQT.P.letB_eq, hc] at h1
  exact h1

private theorem csImg {n : ℕ} (σ : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    CFSG.KC.Misc.ClosW.img σ i = σ ⟨i, hi⟩ := dif_pos hi

private theorem csImg_lt {n w : ℕ} (hw : n < 2 ^ w) (σ : Perm (Fin n)) (i : ℕ) :
    CFSG.KC.Misc.ClosW.img σ i < 2 ^ w := by
  unfold CFSG.KC.Misc.ClosW.img
  split
  · exact (Fin.isLt _).trans hw
  · exact Nat.two_pow_pos w

private theorem csImg_inj {n : ℕ} (σ : Perm (Fin n)) {i j : ℕ} (hi : i < n) (hj : j < n)
    (e : CFSG.KC.Misc.ClosW.img σ i = CFSG.KC.Misc.ClosW.img σ j) : i = j := by
  rw [csImg σ hi, csImg σ hj] at e
  have := σ.injective (Fin.ext e)
  simpa using this

private theorem csMain {n w nO : ℕ} (hw : n + 1 < 2 ^ w) (gs : List (Perm (Fin n)))
    {G U R : ℕ → ℕ} {O : ℕ → List ℕ} {f : ℕ → Bool}
    (hG : ∀ j < gs.length, G j = wcode w (gs.getD j 1)) (x : Perm (Fin n))
    (hx : ∀ g ∈ gs, x * g = g * x) (hR : ∀ k < nO, R k < n)
    (hU : ∀ k < nO, ∀ q ∈ O k,
      pg w (mask w) (U q) (CFSG.KC.Misc.ClosW.img x (R k)) = CFSG.KC.Misc.ClosW.img x q)
    (hcl : ∀ k < nO, ∀ q ∈ O k, ∀ j < gs.length, pg w (mask w) (G j) q ∈ O k)
    (hlt : ∀ q ∈ csPts O 0 nO, q < n) (hnd : (csPts O 0 nO).Nodup)
    (hcv : ∀ v < n, v ∈ csPts O 0 nO) :
    ∀ m k X used, k + m = nO →
      CFSG.KS.PF.Fld w X (fun i => if i ∈ csPts O 0 k then CFSG.KC.Misc.ClosW.img x i else 0) →
      (∀ v, used.testBit v = true ↔ ∃ q ∈ csPts O 0 k, CFSG.KC.Misc.ClosW.img x q = v) →
      csDfs n w G gs.length O U f m k X used = true → f (wcode w x) = true := by
  have hw' : n < 2 ^ w := by omega
  intro m
  induction m with
  | zero =>
    intro k X used hk hX _ hd
    have hk' : k = nO := by omega
    subst hk'
    change f X = true at hd
    have e : X = wcode w x := by
      refine CFSG.KS.PF.eq_of_fld (CFSG.KS.PF.w_pos hw) hX
        (CFSG.KS.PF.fld_congr (fld_wcode hw' x) fun i => ?_)
      by_cases hi : i < n
      · simp [hi, hcv i hi]
      · have : i ∉ csPts O 0 k := fun hm => hi (hlt i hm)
        simp [hi, this]
    rw [← e]
    exact hd
  | succ m ih =>
    intro k X used hk hX hused hd
    have hkn : k < nO := by omega
    have hRk := hR k hkn
    set t := CFSG.KC.Misc.ClosW.img x (R k) with ht_def
    have ht : t < n := by
      rw [ht_def, csImg x hRk]
      exact Fin.isLt _
    have hsplit : csPts O 0 nO = csPts O 0 k ++ (O k ++ csPts O (k + 1) m) := by
      rw [← hk, csPts_add O k 0 (m + 1)]
      simp [csPts]
    have hOk : ∀ q ∈ O k, q < n := fun q hq => hlt q (csMem_pts hkn hq)
    have hnd' := hnd
    rw [hsplit, List.nodup_append] at hnd'
    obtain ⟨hndP, hndR, hdisj⟩ := hnd'
    have hndO : (O k).Nodup := (List.nodup_append.1 hndR).1
    have hUk := hU k hkn
    have hok : assignOK w U (O k) t used = true := by
      refine csAssignOK (F := CFSG.KC.Misc.ClosW.img x) (O k) used hUk (fun q hq => ?_) ?_
      · cases hb : used.testBit (CFSG.KC.Misc.ClosW.img x q)
        · rfl
        · obtain ⟨q', hq', e⟩ := (hused _).1 hb
          have hq'n : q' < n := hlt q' (by rw [hsplit]; exact List.mem_append_left _ hq')
          have := csImg_inj x hq'n (hOk q hq) e
          subst this
          exact absurd rfl (hdisj q' hq' q' (List.mem_append_left _ hq))
      · refine List.Nodup.map_on (fun a ha b hb e => csImg_inj x (hOk a ha) (hOk b hb) e) hndO
    have hX' := csAssignX (csImg_lt hw' x) (O k) (csPts O 0 k) X hUk hX
    have hmem : ∀ i, (i ∈ O k ∨ i ∈ csPts O 0 k) ↔ i ∈ csPts O 0 (k + 1) := fun i => by
      rw [csPts_succ, List.mem_append]
      tauto
    have hX'' : CFSG.KS.PF.Fld w (assignX w U (O k) t X)
        (fun i => if i ∈ csPts O 0 (k + 1) then CFSG.KC.Misc.ClosW.img x i else 0) :=
      CFSG.KS.PF.fld_congr hX' fun i => by simp only [hmem i]
    have hpgX : ∀ q ∈ O k, pg w (mask w) (assignX w U (O k) t X) q =
        CFSG.KC.Misc.ClosW.img x q := fun q hq => by
      have h := CFSG.KS.PF.pg_of_fld (i := q) hX' (by
        simp only [hq, true_or, ↓reduceIte]
        exact csImg_lt hw' x q)
      simpa [hq] using h
    have hc : commAt w G gs.length (O k) (assignX w U (O k) t X) = true := by
      refine (CFSG.KC.LQT.P.allL_iff _ _).2 fun q hq => (CFSG.KC.LQT.P.allN_iff _ _).2
        fun j hj => (CFSG.KC.LQT.P.beq_iff).2 ?_
      have hqn := hOk q hq
      have hgq := hcl k hkn q hq j hj
      rw [hpgX q hq, hpgX _ hgq]
      have hB : CFSG.KC.Misc.ClosW.img x q = (x ⟨q, hqn⟩ : ℕ) := csImg x hqn
      have hA : pg w (mask w) (G j) q = ((gs.getD j 1) ⟨q, hqn⟩ : ℕ) := by
        rw [hG j hj]
        exact pg_wcode_nat hw' _ hqn
      rw [hB, hA, hG j hj, pg_wcode hw' (gs.getD j 1) (x ⟨q, hqn⟩), csImg x (Fin.isLt _)]
      have hgmem : gs.getD j 1 ∈ gs := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
        exact List.getElem_mem hj
      have := congrArg (fun σ : Perm (Fin n) => (σ ⟨q, hqn⟩ : ℕ)) (hx _ hgmem)
      simpa [Perm.mul_apply] using this
    have hused' : ∀ v, (assignU w U (O k) t used).testBit v = true ↔
        ∃ q ∈ csPts O 0 (k + 1), CFSG.KC.Misc.ClosW.img x q = v := fun v => by
      rw [csAssignU (O k) used hUk v, hused v, csPts_succ]
      simp only [List.mem_append]
      constructor
      · rintro (⟨q, hq, e⟩ | ⟨q, hq, e⟩)
        exacts [⟨q, Or.inr hq, e⟩, ⟨q, Or.inl hq, e⟩]
      · rintro ⟨q, hq | hq, e⟩
        exacts [Or.inr ⟨q, hq, e⟩, Or.inl ⟨q, hq, e⟩]
    exact ih (k + 1) _ _ (by omega) hX'' hused' (csDfs_step hd ht hok hc)

end CentDfsSound

theorem centDfs_sound {n w nO : ℕ} (hw : n + 1 < 2 ^ w) (hn : n < 16777216)
    (gs : List (Perm (Fin n))) {G U R : ℕ → ℕ} {O : ℕ → List ℕ} {UW : ℕ → List ℕ} {f : ℕ → Bool}
    (hG : ∀ j < gs.length, G j = wcode w (gs.getD j 1))
    (hwd : ∀ q < n, wWordAt n w G gs.length UW U q = true)
    (hcov : covOK n w nO R O U = true) (horb : ∀ k < nO, orbOK n w G gs.length R O k = true)
    (hd : centDfs n w G gs.length nO O U f = true) :
    ∀ x : Perm (Fin n), (∀ g ∈ gs, x * g = g * x) → f (wcode w x) = true := by
  intro x hx
  have hw' : n < 2 ^ w := by omega
  obtain ⟨hlt, hnd, -, hpg, hcv⟩ := csCov_spec n w R O U nO 0 0 hcov
  have hcv' : ∀ v < n, v ∈ csPts O 0 nO := fun v hv => by
    simpa using hcv v hv
  have hpg' : ∀ k < nO, ∀ q ∈ O k, pg w (mask w) (U q) (R k) = q := fun k hk q hq => by
    simpa using hpg k hk q (by simpa using hq)
  have horb' : ∀ k < nO, R k < n ∧ ∀ q ∈ O k, ∀ j < gs.length, pg w (mask w) (G j) q ∈ O k :=
    fun k hk => by
      have h := horb k hk
      change CFSG.KC.Ord.andB (Nat.blt (R k) n) (CFSG.KC.LQT.P.allL (O k) fun q =>
        CFSG.KC.LQT.P.allN gs.length fun j => CFSG.KC.LQT.P.anyL (O k) fun q' =>
          Nat.beq (pg w (mask w) (G j) q) q') = true at h
      rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.blt_iff, CFSG.KC.LQT.P.allL_iff] at h
      refine ⟨h.1, fun q hq j hj => ?_⟩
      obtain ⟨q', hq', e⟩ := (CFSG.KC.LQT.P.anyL_iff _ _).1
        ((CFSG.KC.LQT.P.allN_iff _ _).1 (h.2 q hq) j hj)
      rw [CFSG.KC.LQT.P.beq_iff] at e
      rw [e]
      exact hq'
  have hxc : ∀ u ∈ Subgroup.closure {g | g ∈ gs}, x * u = u * x := by
    intro u hu
    have hle : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.centralizer {x} := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hx g hg
    exact (Subgroup.mem_centralizer_iff.1 (hle hu)) x rfl
  have hU : ∀ k < nO, ∀ q ∈ O k,
      pg w (mask w) (U q) (CFSG.KC.Misc.ClosW.img x (R k)) = CFSG.KC.Misc.ClosW.img x q := by
    intro k hk q hq
    have hRk := (horb' k hk).1
    have hqn := hlt q (csMem_pts hk hq)
    have h := hwd q hqn
    change CFSG.KC.Ord.andB (lettersK gs.length (UW q))
      (Nat.beq (wWord n w G gs.length (UW q)) (U q)) = true at h
    rw [CFSG.KC.LQT.P.andB_iff, CFSG.KC.LQT.P.beq_iff] at h
    obtain ⟨u, hu, hwu⟩ := wword_mem hw hn gs hG h.1
    rw [h.2] at hwu
    have huR : (u ⟨R k, hRk⟩ : ℕ) = q := by
      rw [← pg_wcode_nat hw' u hRk, hwu]
      exact hpg' k hk q hq
    rw [← hwu, csImg x hRk, pg_wcode hw' u (x ⟨R k, hRk⟩), csImg x hqn]
    have hq' : (⟨q, hqn⟩ : Fin n) = u ⟨R k, hRk⟩ := Fin.ext huR.symm
    rw [hq']
    have := congrArg (fun σ : Perm (Fin n) => (σ ⟨R k, hRk⟩ : ℕ)) (hxc u hu)
    simpa [Perm.mul_apply] using this.symm
  exact csMain hw gs hG x hx (fun k hk => (horb' k hk).1) hU (fun k hk => (horb' k hk).2) hlt hnd
    hcv' nO 0 0 0 (by omega) (CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero w) fun i => by simp [csPts])
    (fun v => by simp [csPts]) hd

theorem presE_iff {n w : ℕ} (hw : n < 2 ^ w) (A : ℕ → ℕ) (x : Perm (Fin n)) :
    presE n w A (wcode w x) = true ↔ ∀ a b : Fin n, bitB (A a) b = true →
      bitB (A (x a)) (x b) = true := by
  unfold presE
  simp only [CFSG.KC.LQT.P.allN_fin, CFSG.KC.LQT.P.impB_iff, pg_wcode hw]

@[expose] def Pres {n : ℕ} (A : ℕ → ℕ) (x : Perm (Fin n)) : Prop :=
  ∀ a b : Fin n, bitB (A a) b = true → bitB (A (x a)) (x b) = true

theorem pres_closure {n : ℕ} (A : ℕ → ℕ) {s : Set (Perm (Fin n))} (hs : ∀ g ∈ s, Pres A g) :
    ∀ x ∈ Subgroup.closure s, Pres A x := by
  intro x hx
  have hx' : x ∈ Submonoid.closure s := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  clear hx
  induction hx' using Submonoid.closure_induction with
  | mem g hg => exact hs g hg
  | one => exact fun a b h => h
  | mul x y _ _ hx hy => exact fun a b h => hx _ _ (hy a b h)

end CFSG.KC.Misc.Cent

end
