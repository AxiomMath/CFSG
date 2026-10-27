module

public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Sporadic.Schreier.TitsBasic

public section

namespace CFSG.KC.LQT.Cov.T

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KS.Mathieu (icode)
open CFSG.Sporadic.Schreier.Tits

private theorem compA_getElem {n i : Nat} {t u : Array Nat} (h : i < (compA n t u).size) :
    (compA n t u)[i] = t[u[i]!]! := by
  simp [compA]

private theorem unpack_getElem {n w p i : Nat} (h : i < (unpack n w p).size) :
    (unpack n w p)[i] = CFSG.KC.Enum.pg w (mask w) p i := by
  rw [← getElem!_pos _ i h]
  exact CFSG.KS.Raw.Orb.unpack_get (by simpa [unpack] using h)

private theorem foldl_scatter {n : Nat} {t : Array Nat} {R : Nat → Nat}
    (ht : ∀ i < n, t[i]! < n ∧ R t[i]! = i) : ∀ k ≤ n,
    (List.foldl (fun b a => b.setIfInBounds t[a]! a) (Array.replicate n 0) (List.range' 0 k)).size = n ∧
    ∀ i < k, (List.foldl (fun b a => b.setIfInBounds t[a]! a) (Array.replicate n 0)
      (List.range' 0 k))[t[i]!]! = i := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨hs, hv⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    refine ⟨by simp [hs], fun i hi => ?_⟩
    have htk := ht k (by omega)
    have hti := ht i (by omega)
    rw [getElem!_pos _ _ (by simp [hs]; exact hti.1),
      Array.getElem_setIfInBounds (by rw [hs]; exact hti.1)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · have hne : t[k]! ≠ t[i]! := by
        intro e
        have := htk.2
        rw [e, hti.2] at this
        omega
      simp only [hne, ↓reduceIte]
      rw [← getElem!_pos _ _ (by rw [hs]; exact hti.1)]
      exact hv i h
    · subst h
      simp

theorem compA_unpack {n w p q : Nat} (hn : n < 2 ^ 32)
    (hq : ∀ i < n, CFSG.KC.Enum.pg w (mask w) q i < n) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) := by
  apply Array.ext
  · simp [compA, unpack]
  · intro i h1 _
    have hi : i < n := by simpa [compA] using h1
    rw [compA_getElem, CFSG.KS.Raw.Orb.unpack_get hi,
      CFSG.KS.Raw.Orb.unpack_get (hq i hi), unpack_getElem, CFSG.KS.PF.pg_pcomp hn hi]

theorem unpack_pidn {n w : Nat} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    unpack n w (pidn n w) = idA n := by
  apply Array.ext
  · simp [unpack, idA]
  · intro i h1 _
    have hi : i < n := by simpa [unpack] using h1
    rw [unpack_getElem, show (idA n)[i] = i from by simp [idA],
      CFSG.KS.PF.pg_pidn hn hw hi]

theorem perm_facts {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    (∀ i < n, CFSG.KC.Enum.pg w (mask w) p i < n ∧
      CFSG.KC.Enum.pg w (mask w) r (CFSG.KC.Enum.pg w (mask w) p i) = i) ∧
      ∀ j < n, ∃ i < n, CFSG.KC.Enum.pg w (mask w) p i = j := by
  unfold permOK at h
  simp only [bAnd_iff] at h
  obtain ⟨-, -, ha⟩ := h
  have hpr : ∀ i < n, CFSG.KC.Enum.pg w (mask w) p i < n ∧
      CFSG.KC.Enum.pg w (mask w) r (CFSG.KC.Enum.pg w (mask w) p i) = i := by
    intro i hi
    have := allN_spec ha i hi
    rw [CFSG.KS.PF.strictB_eqP] at this
    simp only [bAnd_iff] at this
    exact ⟨by simpa [Nat.blt_eq] using this.1, Nat.eq_of_beq_eq_true this.2⟩
  refine ⟨hpr, fun j hj => ?_⟩
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n) (t := Finset.range n)
    (fun a _ => CFSG.KC.Enum.pg w (mask w) p a) (fun a ha => by simpa using (hpr a (by simpa using ha)).1)
    (fun a₁ a₂ h₁ h₂ e => by
      have e1 := (hpr a₁ (by simpa using h₁)).2
      have e2 := (hpr a₂ (by simpa using h₂)).2
      have e' : CFSG.KC.Enum.pg w (mask w) p a₁ = CFSG.KC.Enum.pg w (mask w) p a₂ := e
      rw [e'] at e1
      omega) le_rfl
  obtain ⟨i, hi, e⟩ := hsurj j (by simpa using hj)
  exact ⟨i, by simpa using hi, e.symm⟩

private theorem perm_inv_lt {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    ∀ j < n, CFSG.KC.Enum.pg w (mask w) r j < n := by
  obtain ⟨hpr, hs⟩ := perm_facts h
  intro j hj
  obtain ⟨i, hi, e⟩ := hs j hj
  rw [← e, (hpr i hi).2]
  exact hi

theorem invCand_unpack {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) :
    invCand n (unpack n w p) = unpack n w r := by
  obtain ⟨hpr, hsurj⟩ := perm_facts h
  have hsize : (unpack n w p).size = n := by simp [unpack]
  have hsizeR : (unpack n w r).size = n := by simp [unpack]
  have ht : ∀ i < n, (unpack n w p)[i]! < n ∧
      CFSG.KC.Enum.pg w (mask w) r (unpack n w p)[i]! = i := by
    intro i hi
    rw [CFSG.KS.Raw.Orb.unpack_get hi]
    exact hpr i hi
  obtain ⟨hs, hv⟩ := foldl_scatter ht n le_rfl
  have e : invCand n (unpack n w p) = List.foldl (fun b a => b.setIfInBounds (unpack n w p)[a]! a)
      (Array.replicate n 0) (List.range' 0 n) := by
    simp [invCand, Id.run]
    rfl
  rw [e]
  apply Array.ext
  · rw [hs]; simp [unpack]
  · intro j h1 h2
    have hj : j < n := by simpa [hsizeR] using h2
    obtain ⟨i, hi', e⟩ := hsurj j hj
    have := hv i hi'
    rw [CFSG.KS.Raw.Orb.unpack_get hi', e, getElem!_pos _ _ (by rw [hs]; exact hj)] at this
    rw [this, unpack_getElem (by rw [hsizeR]; exact hj), ← e, (hpr i hi').2]

@[expose] noncomputable def letK (S SI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0), S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
    SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))

private theorem letK_even {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 0) :
    letK S SI c = S (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, CFSG.KS.PF.shr_eq, Nat.pow_one]
  rfl

private theorem letK_odd {S SI : Nat → Nat} {c : Nat} (hc : c % 2 = 1) :
    letK S SI c = SI (c / 2 - 1) := by
  have e : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  unfold letK
  rw [e, hc, CFSG.KS.PF.shr_eq, Nat.pow_one]
  rfl

private theorem icode_ofNat (k : Nat) : icode (Int.ofNat k) = k + k := rfl

private theorem icode_negSucc (k : Nat) : icode (Int.negSucc k) = k + 1 + (k + 1) + 1 := rfl

private theorem map_get! {S : Array (Array Nat)} {f : Array Nat → Array Nat} {k : Nat}
    (hk : k < S.size) : (S.map f)[k]! = f S[k]! := by
  rw [getElem!_pos (S.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos S k hk]

theorem letter_sound {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hperm : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) {z : Int}
    (h1 : Nat.blt (nat_lit 0) (icode z) = true)
    (h2 : Nat.ble (Nat.shiftRight (icode z) (nat_lit 1)) kS = true) :
    unpack n w (letK PS PSI (icode z)) = letterA S (rawInvs n S) z ∧
      ∀ i < n, CFSG.KC.Enum.pg w (mask w) (letK PS PSI (icode z)) i < n := by
  have h1' := Nat.blt_eq.mp h1
  have h2' := Nat.ble_eq.mp h2
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_one] at h2'
  cases z with
  | ofNat k =>
    rw [icode_ofNat] at h1' h2'
    have hk : k + k = icode (Int.ofNat k) := rfl
    have hL : letK PS PSI (icode (Int.ofNat k)) = PS (k - 1) := by
      rw [← hk, letK_even (by omega)]
      congr 1
      omega
    have hj : k - 1 < kS := by omega
    have hk0 : 0 < k := by omega
    have h0 : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk0
    have et : (Int.ofNat k).toNat = k := rfl
    rw [hL]
    refine ⟨?_, fun i hi => ((perm_facts (hperm _ hj)).1 i hi).1⟩
    unfold letterA
    rw [iteT h0, et, hS.2 _ hj]
  | negSucc k =>
    rw [icode_negSucc] at h2'
    have hk : k + 1 + (k + 1) + 1 = icode (Int.negSucc k) := rfl
    have hL : letK PS PSI (icode (Int.negSucc k)) = PSI k := by
      rw [← hk, letK_odd (by omega)]
      congr 1
      omega
    have hj : k < kS := by omega
    have h0 : ¬ (0 : Int) < Int.negSucc k := Int.not_lt.mpr (Int.le_of_lt (Int.negSucc_lt_zero k))
    have et : (-Int.negSucc k).toNat = k + 1 := rfl
    rw [hL]
    refine ⟨?_, perm_inv_lt (hperm _ hj)⟩
    unfold letterA
    rw [iteF h0, et, Nat.add_sub_cancel, rawInvs, map_get! (by rw [hS.1]; exact hj), hS.2 _ hj,
      invCand_unpack (hperm _ hj)]

end CFSG.KC.LQT.Cov.T

end
