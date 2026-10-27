module

public import Certificates.Data.Kernel.Misc.Sp6
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataSylow
import CFSG.Certificates.Kernel.Misc.Sp6SndQuad
import CFSG.Certificates.Kernel.Misc.Sp6SndList
import CFSG.Certificates.Kernel.Misc.Sp6SndSearch
public import Mathlib.Data.List.GetD

public section

namespace CFSG.KC.Misc.Sp6

open CFSG.KC.Misc CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6.Snd

@[expose] def pListG (G : List (List ℕ)) : List (List ℕ) :=
  (bfsAux G 40 [(idT, [])] [(idT, [])]).map Prod.fst

@[expose] def eaListG (G : List (List ℕ)) : List (List (List ℕ)) :=
  eaClose (pListG G) 10 [[idT]] [[idT]]

@[expose] def pCheckG (u : Bool) (G : List (List ℕ)) : Bool :=
  let P := pListG G
  P.length == 128 && decide (P.map codeT).Nodup && P.contains idT &&
    P.all (validT u) && P.all fun a => P.all fun b => P.contains (compT a b)

@[expose] def eaCheckG (G : List (List ℕ)) : Bool :=
  let P := pListG G
  let EL := eaListG G
  EL.contains [idT] && EL.all fun A =>
    A.all P.contains && decide (A.map codeT).Nodup && A.contains idT &&
      (extenders P A).all fun x => EL.contains (adjoin x A) && A.length < (adjoin x A).length

@[expose] def boundCheckG (u : Bool) (G : List (List ℕ)) : Bool :=
  let EL := eaListG G
  EL.all fun A => A == [idT] ||
    let Bs := A.map (bOf u)
    A.length * ((List.range 512).filter fun e => Bs.all fun B => evalE B e == e).length *
      ((List.range 64).filter fun v => qOf u v == 0 && A.all fun a => evalV a v == v).length <
      2 ^ (if u then 9 else 12)

theorem pCheck_eq (u : Bool) : pCheck u = pCheckG u (pGens u) := rfl

theorem eaCheck_eq (u : Bool) : eaCheck u = eaCheckG (pGens u) := rfl

theorem boundCheck_eq (u : Bool) : boundCheck u = boundCheckG u (pGens u) := rfl


private theorem reach_mono {G : List (List ℕ)} {x : List ℕ} :
    ∀ {n N : ℕ}, Snd.reach G n x → n ≤ N → Snd.reach G N x
  | n, 0, h, hn => by rwa [Nat.le_zero.1 hn] at h
  | n, N + 1, h, hn => by
    rcases Nat.lt_or_ge n (N + 1) with h' | h'
    · exact Or.inl (reach_mono h (by omega))
    · rwa [show n = N + 1 by omega] at h

private theorem dec_compK (A B : ℕ) : Snd.dec (compK A B) = compT (Snd.dec A) (Snd.dec B) := by
  rw [Snd.compK_eq, Snd.dec_codeL (Snd.compT_tup (Snd.dec_tup A).2 (Snd.dec_tup B))]

private theorem popN_filter {M n : ℕ} {p : ℕ → Bool} :
    (∀ i < n, M.testBit i = p i) → popN M n = ((List.range n).filter p).length := by
  intro h
  rw [Snd.popN_eq]
  congr 1
  exact List.filter_congr fun i hi => h i (List.mem_range.1 hi)

private theorem recAndL_testBit (s : ℕ) (y F : ℕ → ℕ) (c : ℕ → Bool) (n e : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) s (fun i acc => Bool.rec (motive := fun _ => ℕ) acc
      (letN (y i) fun a => Nat.land acc (F a)) (c i)) n).testBit e = true ↔
      s.testBit e = true ∧ ∀ i < n, c i = true → (F (y i)).testBit e = true := by
  have h : (fun i acc => Bool.rec (motive := fun _ => ℕ) acc
      (letN (y i) fun a => Nat.land acc (F a)) (c i)) =
      fun i acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.land acc (F (y i))) (c i) := by
    funext i acc
    rw [letN_eq]
  rw [h]
  exact Snd.recAnd_testBit s (fun i => F (y i)) c n e

private theorem eq_single_of_nodup {A : List (List ℕ)} {a : List ℕ} (hA : A.Nodup) (ha : a ∈ A)
    (h : ∀ c ∈ A, c = a) : A = [a] := by
  match A, hA, ha, h with
  | [b], _, _, h => rw [h b (by simp)]
  | b :: c :: l, hA, _, h =>
    have := List.nodup_cons.1 hA
    exact absurd (by rw [h b (by simp), h c (by simp)]; exact List.mem_cons_self) this.1

theorem sp6_sound {u : Bool} {G : List (List ℕ)}
    {Pl IV IVI CM EL par ext ppar gen dep XEL XVL : List Nat} {PQ Q0 nc : Nat}
    (ht : treeK (if u then 1 else 0) G Pl PQ ppar gen dep = true)
    (hc : ∀ c < 8, closK PQ (16 * c) 16 = true)
    (hi : invChk Pl PQ IV IVI CM = true)
    (hx : tabsK (if u then 1 else 0) (nthN XEL) (nthN XVL) Q0 = true)
    (hl : 0 < lenN EL ∧ lenN EL ≤ 16 * nc)
    (he : ∀ c < nc, eaChunk (if u then 1 else 0) (if u then 9 else 12) (nthN XEL) (nthN XVL) Q0 PQ
      IV IVI CM EL par ext (16 * c) 16 = true) :
    pCheckG u G = true ∧ eaCheckG G = true ∧ boundCheckG u G = true := by
  have h36 : Nat.shiftLeft 1 36 = 2 ^ 36 := rfl
  simp only [treeK, andB_eq_true, allLL_eq_true, allL_eq_true, allN_eq_true, Nat.beq_eq,
    Nat.blt_eq, Nat.ble_eq, orB_eq_true, notB_eq_true, letB_eq, tupOK_iff, lenN_eq, gensK_eq,
    nthN_eq, h36] at ht
  obtain ⟨hG, hPl, hPlt, hPQ, hcnt, h0, htree, hgm, hdist, hval⟩ := ht
  subst hPQ
  have hat : ∀ i (hi : i < 128), qlAt (qlOfL Pl) i = Pl[i] := fun i hi =>
    Snd.qlAt_qlOfL hPlt (by omega) (by omega)
  have hE : ∀ i < 128, qlAt (qlOfL Pl) i < 2 ^ 36 := fun i hi => by
    rw [hat i hi]; exact hPlt _ (List.getElem_mem _)
  have hinj : ∀ i < 128, ∀ j < 128, qlAt (qlOfL Pl) i = qlAt (qlOfL Pl) j → i = j := by
    intro i hi j hj h
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd h.symm (Nat.ne_of_beq_eq_false (hdist j hj i hij))
    · exact hij
    · exact absurd h (Nat.ne_of_beq_eq_false (hdist i hi j hij))
  have hcl : ∀ i < 128, ∀ j < 128, ∃ l < 128,
      qlAt (qlOfL Pl) l = compK (qlAt (qlOfL Pl) i) (qlAt (qlOfL Pl) j) := by
    intro i hi j hj
    have h := hc (i / 16) (by omega)
    simp only [closK, allN_eq_true, letB_eq, Snd.qlMem_iff, hcnt] at h
    obtain ⟨l, hl, hl'⟩ := h (i % 16) (Nat.mod_lt _ (by omega)) j hj
    rw [show Nat.add (16 * (i / 16)) (i % 16) = i by simp only [Nat.add_eq]; omega] at hl'
    exact ⟨l, hl, hl'⟩
  have hcodeE : ∀ i < 128, codeL (Snd.dec (qlAt (qlOfL Pl) i)) = qlAt (qlOfL Pl) i :=
    fun i hi => Snd.codeL_dec (hE i hi)
  have hE0 : Snd.dec (qlAt (qlOfL Pl) 0) = idT := by rw [h0, Snd.dec_idK]
  have hEinj : ∀ i < 128, ∀ j < 128,
      Snd.dec (qlAt (qlOfL Pl) i) = Snd.dec (qlAt (qlOfL Pl) j) → i = j := fun i hi j hj h =>
    hinj i hi j hj (by rw [← hcodeE i hi, ← hcodeE j hj, h])
  have hEcl : ∀ i < 128, ∀ j < 128, ∃ l < 128, Snd.dec (qlAt (qlOfL Pl) l) =
      compT (Snd.dec (qlAt (qlOfL Pl) i)) (Snd.dec (qlAt (qlOfL Pl) j)) := fun i hi j hj => by
    obtain ⟨l, hl, h⟩ := hcl i hi j hj
    exact ⟨l, hl, by rw [h, dec_compK]⟩
  have hgen : ∀ g ∈ G, ∃ l < 128, Snd.dec (qlAt (qlOfL Pl) l) = g := fun g hg => by
    have h := hgm _ (List.mem_map_of_mem hg)
    rw [Snd.qlMem_iff, hcnt] at h
    obtain ⟨l, hl, h⟩ := h
    exact ⟨l, hl, by rw [h, Snd.dec_codeL (hG g hg)]⟩
  have hPS : ∀ x ∈ pListG G, ∃ i < 128, x = Snd.dec (qlAt (qlOfL Pl) i) :=
    Snd.pListG_sound G _ ⟨0, by omega, hE0.symm⟩ fun x ⟨i, hi, hx⟩ g hg => by
      obtain ⟨l, hl, rfl⟩ := hgen g hg
      obtain ⟨l', hl', h⟩ := hEcl i hi l hl
      exact ⟨l', hl', by rw [h, hx]⟩
  have hreach : ∀ k < 128, Snd.reach G (dep.getD k 0 - dep.getD 0 0)
      (Snd.dec (qlAt (qlOfL Pl) k)) ∧ dep.getD 0 0 ≤ dep.getD k 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases htree k hk with rfl | ⟨hpk, hgk, hdk, -, hk'⟩
      · exact ⟨by simpa [Snd.reach] using hE0, le_rfl⟩
      · obtain ⟨ih1, ih2⟩ := ih _ hpk (by omega)
        rw [List.length_map] at hgk
        rw [List.getD_eq_getElem (G.map codeL) 0 (by simpa using hgk), List.getElem_map] at hk'
        refine ⟨?_, by omega⟩
        rw [show dep.getD k 0 - dep.getD 0 0 = (dep.getD (ppar.getD k 0) 0 - dep.getD 0 0) + 1
          by simp only [Nat.succ_eq_add_one] at hdk; omega]
        refine Or.inr ⟨_, ih1, _, List.getElem_mem hgk, ?_⟩
        rw [hk', dec_compK, Snd.dec_codeL (hG _ (List.getElem_mem hgk))]
  have hPc : ∀ k < 128, Snd.dec (qlAt (qlOfL Pl) k) ∈ pListG G := fun k hk => by
    refine Snd.pListG_complete G (reach_mono (hreach k hk).1 ?_)
    rcases htree k hk with rfl | ⟨-, -, -, hd, -⟩
    · omega
    · omega
  have hPnd : (pListG G).Nodup := Snd.pListG_nodup G
  have hPT : ∀ x ∈ pListG G, Snd.IsTup x := fun x hx => by
    obtain ⟨i, -, rfl⟩ := hPS x hx; exact Snd.dec_tup _
  have hPcl : ∀ a ∈ pListG G, ∀ b ∈ pListG G, compT a b ∈ pListG G := fun a ha b hb => by
    obtain ⟨i, hi, rfl⟩ := hPS a ha
    obtain ⟨j, hj, rfl⟩ := hPS b hb
    obtain ⟨l, hl, h⟩ := hEcl i hi j hj
    rw [← h]; exact hPc l hl
  have hPid : idT ∈ pListG G := hE0 ▸ hPc 0 (by omega)
  have hcodeinj : ∀ x ∈ pListG G, ∀ y ∈ pListG G, codeL x = codeL y → x = y :=
    fun x hx y hy h => Snd.codeL_inj (hPT x hx) (hPT y hy) h
  have hPlen : (pListG G).length = 128 := by
    have h1 : ((pListG G).map codeL).Nodup := hPnd.map_on hcodeinj
    have h2 : ((List.range 128).map (qlAt (qlOfL Pl))).Nodup :=
      (List.nodup_range).map_on fun i hi j hj h =>
        hinj i (List.mem_range.1 hi) j (List.mem_range.1 hj) h
    have hperm := (List.perm_ext_iff_of_nodup h1 h2).2 fun c => by
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, hi, rfl⟩ := hPS x hx
        exact ⟨i, hi, (hcodeE i hi).symm⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨_, hPc i hi, hcodeE i hi⟩
    simpa using hperm.length_eq
  have hcodeT : codeT = codeL := funext fun l => (Snd.codeL_eq_codeT l).symm
  have hEA := Snd.eaClose_isEA hPT hPcl hPid
  have hEAcl := Snd.eaClose_closed hPT hPcl hPid hPnd hPlen.le
  refine ⟨?_, ?_, ?_⟩
  · simp only [pCheckG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem,
      List.all_eq_true]
    refine ⟨⟨⟨⟨hPlen, ?_⟩, hPid⟩, ?_⟩, fun a ha b hb => hPcl a ha b hb⟩
    · rw [hcodeT]; exact hPnd.map_on hcodeinj
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := hPS x hx
      rw [← Snd.validK_eq]; exact hval i hi
  · simp only [eaCheckG, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem,
      List.all_eq_true]
    refine ⟨Snd.mem_eaClose_of_mem _ _ _ _ _ (by simp), fun A hA => ?_⟩
    obtain ⟨hA1, hAP, -, -, -, hAs⟩ := hEA A hA
    refine ⟨⟨⟨fun a ha => hAP a ha, ?_⟩, hA1⟩, fun x hx => ⟨hEAcl A hA x hx, ?_⟩⟩
    · rw [hcodeT, ← hcodeT]; exact hAs.imp (ne_of_lt)
    · rw [Snd.length_adjoin hPT hPcl (hEA A hA) hx]
      have : 0 < A.length := List.length_pos_of_mem hA1
      omega
  · obtain ⟨hl0, hl1⟩ := hl
    rw [lenN_eq] at hl0 hl1
    simp only [invChk, andB_eq_true, eqLN_eq_true, Nat.beq_eq, lenN_eq, allN_eq_true, letB_eq,
      Nat.blt_eq, nthN_eq, invsL_eq] at hi
    obtain ⟨hIV, -, -, hiv⟩ := hi
    simp only [tabsK, andB_eq_true, allN_eq_true, Nat.beq_eq] at hx
    obtain ⟨hXE, hXV, hQ0⟩ := hx
    have hek : ∀ k < EL.length, eaK (if u then 1 else 0) (if u then 9 else 12) (nthN XEL)
        (nthN XVL) Q0 (qlOfL Pl) IV IVI CM EL par ext k = true := by
      intro k hk
      have h := he (k / 16) (by omega)
      simp only [eaChunk, allN_eq_true, impB_eq_true, Nat.blt_eq, lenN_eq, Nat.add_eq] at h
      have h2 := h (k % 16) (Nat.mod_lt _ (by omega))
      rw [show 16 * (k / 16) + k % 16 = k by omega] at h2
      exact h2 hk
    have h128 : Nat.shiftLeft 1 128 = 2 ^ 128 := rfl
    have hek' : ∀ k < EL.length, nthN EL k < 2 ^ 128 ∧
        (∀ t < IV.length, extOK (qlOfL Pl) (nthN EL k) IVI CM EL (nthN IV t) t = true) ∧
        boundK (if u then 1 else 0) (if u then 9 else 12) (nthN XEL) (nthN XVL) Q0 (qlOfL Pl)
          (nthN EL k) = true ∧ (k = 0 → nthN EL k = 1) := by
      intro k hk
      have h := hek k hk
      simp only [eaK, letB_eq, andB_eq_true, lenN_eq, allN_eq_true, Nat.blt_eq, h128] at h
      obtain ⟨h1, h2, -, h4, h5⟩ := h
      refine ⟨h2, h4, h5, ?_⟩
      rintro rfl
      exact Nat.eq_of_beq_eq_true h1
    have hlt128 : ∀ k < EL.length, ∀ i, (nthN EL k).testBit i = true → i < 128 :=
      fun k hk i hi => by
        by_contra h
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hek' k hk).1
          (Nat.pow_le_pow_right (by omega) (by omega)))] at hi
        exact absurd hi (by simp)
    have hrep : ∀ A ∈ eaListG G, ∃ k < EL.length, ∀ c, c ∈ A ↔
        ∃ i < 128, (nthN EL k).testBit i = true ∧ c = Snd.dec (qlAt (qlOfL Pl) i) := by
      refine Snd.eaClose_induct (pListG G) _ ?_ 10 [[idT]] [[idT]] ?_ (fun A h => h)
      · rintro A ⟨k, hk, hA⟩ x hx
        obtain ⟨hMlt, hext, -, -⟩ := hek' k hk
        simp only [extenders, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
          List.all_eq_true, beq_iff_eq] at hx
        obtain ⟨hxP, ⟨hxinv, hxA⟩, hxc⟩ := hx
        have hxA' : x ∉ A := by simpa using hxA
        obtain ⟨j, hj, rfl⟩ := hPS x hxP
        have hmem : qlAt (qlOfL Pl) j ∈ IV := by
          rw [← hIV, List.mem_filter, Snd.invK_eq (hE j hj)]
          exact ⟨by rw [hat j hj]; exact List.getElem_mem _, hxinv⟩
        obtain ⟨t, ht, hIVt⟩ := List.getElem_of_mem hmem
        obtain ⟨hti, htx, htc⟩ := hiv t ht
        have hIVt' : IV.getD t 0 = qlAt (qlOfL Pl) j := by
          rw [List.getD_eq_getElem _ _ ht, hIVt]
        have hIVIj : IVI.getD t 0 = j := hinj _ hti _ hj (by rw [htx, hIVt'])
        have hx := hext t ht
        simp only [extOK, impB_eq_true, andB_eq_true, notB_eq_true, Nat.beq_eq, letB_eq,
          memN_eq_true, hasB_eq, nthN_eq, hIVt', hIVIj] at hx
        have hnot : (EL.getD k 0).testBit j = false := by
          rcases h : (EL.getD k 0).testBit j
          · rfl
          · exact absurd ((hA _).2 ⟨j, hj, by rw [nthN_eq]; exact h, rfl⟩) hxA'
        have hmask : Nat.land (EL.getD k 0) (Nat.xor (CM.getD t 0)
            340282366920938463463374607431768211455) = 0 := by
          rw [← nthN_eq, Snd.land_mask_eq_zero_iff hMlt, htc, hIVt']
          intro i hi
          have hi128 := hlt128 k hk i hi
          rw [Snd.commMask_testBit, hcnt]
          refine ⟨hi128, ?_⟩
          rw [Snd.compK_eq, Snd.compK_eq, hxc _ ((hA _).2 ⟨i, hi128, hi, rfl⟩)]
        obtain ⟨hB, -⟩ := hx ⟨hnot, hmask⟩
        obtain ⟨k', hk', hk'eq⟩ := List.getElem_of_mem hB
        have hAT : ∀ a ∈ A, Snd.IsTup a := fun a ha => by
          obtain ⟨i, -, -, rfl⟩ := (hA a).1 ha; exact Snd.dec_tup _
        refine ⟨k', hk', fun c => ?_⟩
        rw [Snd.mem_adjoin (Snd.dec_tup _) hAT c, nthN_eq EL k',
          List.getD_eq_getElem _ _ hk', hk'eq, ← nthN_eq]
        simp only [Snd.adjK_testBit]
        constructor
        · rintro (hc | ⟨a, ha, rfl⟩)
          · obtain ⟨i, hi, hb, rfl⟩ := (hA c).1 hc
            exact ⟨i, hi, Or.inl hb, rfl⟩
          · obtain ⟨i, hi, hb, rfl⟩ := (hA a).1 ha
            obtain ⟨l, hl, hle⟩ := hcl j hj i hi
            have hq := Snd.qlIdx_spec (Q := qlOfL Pl) ⟨l, by rw [hcnt]; exact hl, hle⟩
            rw [hcnt] at hq
            refine ⟨_, hq.1, Or.inr ⟨i, hi, hb, rfl⟩, ?_⟩
            rw [hq.2, dec_compK]
        · rintro ⟨i, hi, hb | ⟨i', hi', hb', rfl⟩, rfl⟩
          · exact Or.inl ((hA _).2 ⟨i, hi, hb, rfl⟩)
          · refine Or.inr ⟨_, (hA _).2 ⟨i', hi', hb', rfl⟩, ?_⟩
            obtain ⟨l, hl, hle⟩ := hcl j hj i' hi'
            have hq := Snd.qlIdx_spec (Q := qlOfL Pl) ⟨l, by rw [hcnt]; exact hl, hle⟩
            rw [hq.2, dec_compK]
      · intro A hA
        rw [List.mem_singleton] at hA
        subst hA
        refine ⟨0, hl0, fun c => ?_⟩
        rw [(hek' 0 hl0).2.2.2 rfl, List.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨0, by omega, rfl, hE0.symm⟩
        · rintro ⟨i, hi, hb, rfl⟩
          rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hb
          subst hb
          exact hE0
    have hXE' : ∀ j < 9, nthN XEL j = xeK j := hXE
    have hXV' : ∀ j < 6, nthN XVL j = xvK j := hXV
    simp only [boundCheckG, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    intro A hA
    by_cases h1 : A = [idT]
    · exact Or.inl h1
    right
    obtain ⟨k, hk, hAk⟩ := hrep A hA
    obtain ⟨-, -, hbd, -⟩ := hek' k hk
    obtain ⟨hA1, -, -, -, -, hAs⟩ := hEA A hA
    have hAnd : A.Nodup := List.Nodup.of_map codeT (hAs.imp ne_of_lt)
    have hall : ∀ Pr : List ℕ → Prop, (∀ a ∈ A, Pr a) ↔ ∀ i < 128,
        (nthN EL k).testBit i = true → Pr (Snd.dec (qlAt (qlOfL Pl) i)) := fun Pr =>
      ⟨fun h i hi hb => h _ ((hAk _).2 ⟨i, hi, hb, rfl⟩), fun h a ha => by
        obtain ⟨i, hi, hb, rfl⟩ := (hAk a).1 ha; exact h i hi hb⟩
    have hM1 : nthN EL k ≠ 1 := by
      intro hM
      refine h1 (eq_single_of_nodup hAnd hA1 fun c hc => ?_)
      obtain ⟨i, hi, hb, rfl⟩ := (hAk c).1 hc
      rw [hM, Nat.testBit_one_eq_true_iff_self_eq_zero] at hb
      subst hb
      exact hE0
    have hlenA : A.length = popN (nthN EL k) 128 := by
      rw [Snd.popN_eq]
      have h1 : (((List.range 128).filter fun i => (nthN EL k).testBit i).map
          fun i => Snd.dec (qlAt (qlOfL Pl) i)).Nodup :=
        (List.nodup_range.filter _).map_on fun i hi j hj h =>
          hEinj i (by simp at hi; omega) j (by simp at hj; omega) h
      have hperm := (List.perm_ext_iff_of_nodup hAnd h1).2 fun c => by
        rw [hAk c]
        simp only [List.mem_map, List.mem_filter, List.mem_range]
        constructor
        · rintro ⟨i, hi, hb, rfl⟩; exact ⟨i, ⟨hi, hb⟩, rfl⟩
        · rintro ⟨i, ⟨hi, hb⟩, rfl⟩; exact ⟨i, hi, hb, rfl⟩
      rw [hperm.length_eq, List.length_map]
    have hs : ∀ n e, e < n → (Nat.sub (Nat.shiftLeft 1 n) 1).testBit e = true := fun n e he => by
      rw [show Nat.sub (Nat.shiftLeft 1 n) 1 = 2 ^ n - 1 by simp [Nat.shiftLeft_eq],
        Nat.testBit_two_pow_sub_one]
      simpa using he
    unfold boundK at hbd
    rw [orB_eq_true] at hbd
    replace hbd := hbd.resolve_left fun h => hM1 (Nat.eq_of_beq_eq_true h)
    rw [letB_eq, letB_eq, Nat.blt_eq] at hbd
    rw [Nat.mul_eq, Nat.mul_eq, show Nat.shiftLeft 1 (if u then 9 else 12) =
      2 ^ (if u then 9 else 12) by simp [Nat.shiftLeft_eq]] at hbd
    refine lt_of_eq_of_lt ?_ hbd
    rw [hlenA]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) ?_
    · symm
      rw [popN_filter]
      intro e he
      rw [Bool.eq_iff_iff]
      refine (recAndL_testBit _ (qlAt (qlOfL Pl)) (fun a => fixE (nthN XEL)
        (bTabK (if u then 1 else 0) (tLo a) (tHi a))) (hasB (nthN EL k)) 128 e).trans ?_
      simp only [List.all_eq_true, List.mem_map, beq_iff_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, hasB_eq, Snd.fixE_testBit hXE', Snd.evalEK_eq,
        Bool.and_eq_true, decide_eq_true_eq, he, true_and, hs 512 e he]
      exact (hall fun a => evalE (bOf u a) e = e).symm
    · symm
      rw [popN_filter]
      intro v hv
      rw [Bool.eq_iff_iff]
      refine (Snd.recAnd_testBit Q0 (fun i => fixV (nthN XVL) (qlAt (qlOfL Pl) i))
        (hasB (nthN EL k)) 128 v).trans ?_
      rw [hQ0, Snd.q0K_testBit]
      simp only [List.all_eq_true, beq_iff_eq, hasB_eq, Snd.fixV_testBit hXV',
        Bool.and_eq_true, decide_eq_true_eq, hv, true_and]
      exact and_congr_right fun _ => (hall fun a => evalV a v = v).symm

end CFSG.KC.Misc.Sp6

end
