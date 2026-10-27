module

public import CFSG.Certificates.Kernel.LocalQTLatCCheckSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem getK_getD' : ∀ (l : List ℕ) (i : ℕ), getK l i = l.getD i 0
  | [], _ => rfl
  | x :: l, i => by
    change Bool.rec (motive := fun _ => ℕ) (getK l (Nat.sub i 1)) x (Nat.beq i 0) = _
    cases i with
    | zero => rfl
    | succ i =>
      rw [beq_false (Nat.succ_ne_zero i), getK_getD' l]
      rfl

theorem memAt {C : List Lvl} {F d : ℕ} {T : List (Perm (Fin n))} {lat : List (List (Perm (Fin n)))}
    {ms : List Mem} (hms : ms.map Prod.fst = (T :: lat).map (List.map P.code)) (j : ℕ)
    {p : Mem × SetX} (hp : (membersX n C F d ms)[j]? = some p) :
    ∃ L, (T :: lat)[j]? = some L ∧ p.2 = mkX n C F d p.1 ∧ p.1.1 = L.map P.code := by
  rw [membersX_eq, List.getElem?_map] at hp
  cases hm : ms[j]? with
  | none =>
    rw [hm] at hp
    exact absurd hp (by simp)
  | some m =>
    rw [hm, Option.map_some, Option.some.injEq] at hp
    subst hp
    have := congrArg (fun l => l[j]?) hms
    simp only [List.getElem?_map, hm, Option.map_some] at this
    cases hL : (T :: lat)[j]? with
    | none =>
      rw [hL] at this
      exact absurd this (by simp)
    | some L =>
      rw [hL, Option.map_some, Option.some.injEq] at this
      exact ⟨L, rfl, rfl, this⟩

theorem containsC_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true) (ms : List Mem)
    (c : LatCert (Perm (Fin n))) (A : List (Perm (Fin n))) {d k s : ℕ}
    (h : containsC n C d (c.tGens.map P.code) (c.lat.map (List.map P.code)) ms c.sizes
      (A.map P.code) k s = true) :
    (List.range k).all (fun j => c.sizes.getD j 0 != s ||
      A.all fun g => (elts (RN.enc : Perm (Fin n) → RN n) d ((c.tGens :: c.lat).getD j [])).contains
        (RN.enc g)) = true := by
  unfold containsC at h
  rw [P.andB_iff, P.andB_iff, P.allN_iff] at h
  obtain ⟨h0, hok, hall⟩ := h
  have hms := memsOK_iff h0
  have hlen : (membersX n C (chainF C) d ms).length = (c.tGens :: c.lat).length := by
    rw [membersX_eq, List.length_map]
    have := congrArg List.length hms
    simpa using this
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have hj' := hall j hj
  rw [P.orB_iff, P.notB_iff, P.beq_iff, LK.getO_eq, getK_getD'] at hj'
  rw [Bool.or_eq_true]
  rcases hj' with e | e
  · left
    rw [bne_iff_ne]
    exact e
  · right
    rw [List.all_eq_true]
    intro g hg
    rw [Std.HashSet.contains_iff_mem]
    cases hp : (membersX n C (chainF C) d ms)[j]? with
    | none =>
      rw [hp] at e
      change P.allL (A.map P.code) (fun g => Nat.beq g (P.one n)) = true at e
      rw [P.allL_map] at e
      have hg1 := e g hg
      rw [P.beq_iff, P.code_one, P.code_eq_iff hn] at hg1
      subst hg1
      have hL : (c.tGens :: c.lat).getD j [] = [] := by
        rw [List.getElem?_eq_none_iff] at hp
        exact List.getD_eq_default _ _ (by omega)
      rw [hL]
      have := mem_bfsSet_prod (G := Perm (Fin n)) RN.enc_mul RN.enc_one [] d []
        (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _)
      rw [List.prod_nil] at this
      exact this
    | some p =>
      rw [hp] at e
      obtain ⟨L, hL, hp2, hp1⟩ := memAt hms j hp
      obtain ⟨hc, hA⟩ := P.andB_iff.1 e
      rw [hp2] at hc hA
      have hR := mem_rel hn hok hI hp1 hc
      rw [P.allL_map] at hA
      have hgd : (c.tGens :: c.lat).getD j [] = L := by
        rw [List.getD_eq_getElem?_getD, hL]
        rfl
      rw [hgd]
      exact (hR.2.1 g).1 (hA g hg)

end CFSG.KC.LQT.CM

end
