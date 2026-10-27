module

public import Certificates.Data.Kernel.G24Rigid
public import CFSG.Certificates.Kernel.G24KeySound

public section

namespace CFSG.KC.G24Rigid

open CFSG.KC.Enum CFSG.KC.Pack CFSG.KC.G24Key

theorem nif_beq' (c k t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t (Nat.beq c k) = if c = k then t else e := by
  cases h : Nat.beq c k
  · rw [if_neg fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

theorem bif_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c =
    (if c = true then t else e) := by
  cases c <;> rfl

theorem tlet_eq (Z B : ℕ → ℕ) (c q : ℕ) :
    tlet Z B c q = if c = 0 then Z q else ap (B (c - 1)) q := by
  unfold tlet
  rw [nif_beq']
  rfl

variable {F : ℕ → ℕ → ℕ} {g : ℕ → Pm}

theorem wG_eq : ∀ (w : List ℕ), (∀ c ∈ w, ∀ x : Fin 1365, F c x = (g c x : ℕ)) →
    ∀ x : Fin 1365, wG F w x = ((w.map g).prod x : ℕ)
  | [], _, _ => rfl
  | c :: w, h, x => by
    change strictN (wG F w x) (F c) = _
    rw [strictN_eq, wG_eq w (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) x,
      h c List.mem_cons_self, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem itN_eq {f : ℕ → ℕ} {u : Pm} (hf : ∀ x : Fin 1365, f x = (u x : ℕ)) :
    ∀ (e : ℕ) (x : Fin 1365), itN f e x = ((u ^ e) x : ℕ)
  | 0, x => by
    change (x : ℕ) = _
    simp
  | e + 1, x => by
    change strictN (itN f e x) f = _
    rw [strictN_eq, itN_eq hf e x, hf, pow_succ', Equiv.Perm.mul_apply]

theorem fixN_iff {f : ℕ → ℕ} {u : Pm} (hf : ∀ x : Fin 1365, f x = (u x : ℕ)) (e : ℕ) :
    fixN f e = true ↔ ∀ x : Fin 1365, (x : ℕ) < 3 → (u ^ e) x = x := by
  unfold fixN
  constructor
  · intro h x hx
    have := Nat.eq_of_beq_eq_true (allN_spec h x hx)
    rw [itN_eq hf] at this
    exact Fin.ext this
  · intro h
    refine CFSG.KS.PackFld.allN_of_forall fun b hb => ?_
    have hb' : b < 3 := hb
    have e1 := itN_eq hf e ⟨b, by omega⟩
    rw [h ⟨b, by omega⟩ hb'] at e1
    change Nat.beq (itN f e b) b = true
    rw [e1]
    exact Nat.beq_refl _

variable {H : Subgroup Pm}

theorem pow_eq_one_of_fixN {w : List ℕ} (hF : ∀ c ∈ w, ∀ x : Fin 1365, F c x = (g c x : ℕ))
    (hg : ∀ c ∈ w, g c ∈ H)
    (hsep : ∀ u ∈ H, (∀ x : Fin 1365, (x : ℕ) < 3 → u x = x) → u = 1) {e : ℕ}
    (h : fixN (wG F w) e = true) : (w.map g).prod ^ e = 1 := by
  have hm : ∀ w' : List ℕ, (∀ c ∈ w', g c ∈ H) → (w'.map g).prod ∈ H := by
    intro w' h'
    induction w' with
    | nil => exact one_mem H
    | cons c w' ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_mem (h' c List.mem_cons_self) (ih fun c' hc' => h' c' (List.mem_cons_of_mem _ hc'))
  exact hsep _ (pow_mem (hm w hg) e) ((fixN_iff (wG_eq w hF) e).1 h)

theorem ordK_spec {w : List ℕ} {v : ℕ} (hF : ∀ c ∈ w, ∀ x : Fin 1365, F c x = (g c x : ℕ))
    (hg : ∀ c ∈ w, g c ∈ H)
    (hsep : ∀ u ∈ H, (∀ x : Fin 1365, (x : ℕ) < 3 → u x = x) → u = 1) (hv : 0 < v)
    (h : ordK F w v = true) : orderOf (w.map g).prod = v := by
  unfold ordK at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  rw [orderOf_eq_iff hv]
  refine ⟨pow_eq_one_of_fixN hF hg hsep h1, fun m hm hm0 e => ?_⟩
  have := allN_spec h2 m hm
  simp only [bif_eq] at this
  rw [if_neg (by rw [Nat.beq_eq]; omega)] at this
  have hfx : fixN (wG F w) m = true := (fixN_iff (wG_eq w hF) m).2 fun x _ => by rw [e]; rfl
  rw [if_pos hfx] at this
  exact Bool.false_ne_true this

theorem ownK_spec : ∀ {T : List (List ℕ × ℕ)}, ownK F T = true → ∀ t ∈ T, ordK F t.1 t.2 = true
  | [], _, t, ht => absurd ht List.not_mem_nil
  | s :: T, h, t, ht => by
    change bAnd(ordK F s.1 s.2, ownK F T) = true at h
    obtain ⟨h1, h2⟩ := band_iff.1 h
    rcases List.mem_cons.1 ht with rfl | ht
    · exact h1
    · exact ownK_spec h2 t ht

theorem refK_spec {T : List (List ℕ × ℕ)} {r : ℕ}
    (hF : ∀ t ∈ T, ∀ c ∈ t.1, ∀ x : Fin 1365, F c x = (g c x : ℕ))
    (hg : ∀ t ∈ T, ∀ c ∈ t.1, g c ∈ H)
    (hsep : ∀ u ∈ H, (∀ x : Fin 1365, (x : ℕ) < 3 → u x = x) → u = 1)
    (h : refK F T r = true) : ∃ t ∈ T, orderOf (t.1.map g).prod ≠ t.2 := by
  unfold refK at h
  simp only [strictB_eq] at h
  generalize Nat.land (Nat.sub r (nat_lit 1)) (nat_lit 31) = t at h
  generalize Nat.shiftRight (Nat.sub r (nat_lit 1)) (nat_lit 5) = m at h
  obtain ⟨hlt, h⟩ := band_iff.1 h
  have hlt' : t < T.length := Nat.le_of_ble_eq_true hlt
  have hget : T.getD t ([], 0) = T[t] := by
    rw [List.getD_eq_getElem _ _ hlt']
  rw [hget] at h
  refine ⟨T[t], List.getElem_mem hlt', fun ho => ?_⟩
  have hFt := hF _ (List.getElem_mem hlt')
  have hgt := hg _ (List.getElem_mem hlt')
  rw [bif_eq] at h
  by_cases hm : Nat.blt m 3 = true
  · rw [if_pos hm, bif_eq] at h
    have hm3 : m < 3 := Nat.le_of_ble_eq_true hm
    by_cases hb : Nat.beq (itN (wG F T[t].1) T[t].2 m) m = true
    · rw [if_pos hb] at h
      exact Bool.false_ne_true h
    · apply hb
      have hp1 : (T[t].1.map g).prod ^ T[t].2 = 1 := by
        rw [← ho]
        exact pow_orderOf_eq_one _
      have e2 : itN (wG F T[t].1) T[t].2 m = m := by
        have e1 := itN_eq (wG_eq _ hFt) T[t].2 ⟨m, by omega⟩
        rw [hp1] at e1
        simpa using e1
      rw [e2]
      exact Nat.beq_refl _
  · rw [if_neg hm] at h
    obtain ⟨hd, hfx⟩ := band_iff.1 h
    have hd' : Nat.sub m 2 < T[t].2 := Nat.le_of_ble_eq_true hd
    have hm3 : 3 ≤ m := by
      by_contra hc
      exact hm (by rw [Nat.blt_eq]; omega)
    have hpow := pow_eq_one_of_fixN hFt hgt hsep hfx
    have h0 : 0 < Nat.sub m 2 := by change 0 < m - 2; omega
    have := orderOf_le_of_pow_eq_one h0 hpow
    change m - 2 < T[t].2 at hd'
    change orderOf _ ≤ m - 2 at this
    omega

theorem levK_spec {G : ℕ → ℕ → ℕ → ℕ} {T : List (List ℕ × ℕ)} {R SK : ℕ → ℕ} {n : ℕ}
    (h : levK G T R SK n = true) :
    ∀ k < n, R k ≠ 0 → SK k = 0 → refK (G k) T (R k) = true := by
  intro k hk hr hs
  have := allN_spec h k hk
  simp only [strictB_eq, bif_eq] at this
  rw [if_neg (by rw [Nat.beq_eq]; exact hr), if_pos (by rw [Nat.beq_eq]; exact hs)] at this
  exact this

theorem cntK_eq (R SK : ℕ → ℕ) (n : ℕ) :
    cntK R SK n = (List.range n).countP (fun k => decide (R k = 0 ∧ SK k = 0)) := by
  unfold cntK
  rw [foldN_eq]
  generalize List.range n = l
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.foldr_cons, ih, List.countP_cons]
    by_cases hp : R k = 0 ∧ SK k = 0
    · rw [nif_true (by rw [band_iff, Nat.beq_eq, Nat.beq_eq]; exact hp)]
      simp [hp]
    · rw [nif_false (Bool.eq_false_iff.2 fun e => hp (by
        rw [band_iff, Nat.beq_eq, Nat.beq_eq] at e
        exact e))]
      simp [hp]

theorem slpK_spec {S A : ℕ → ℕ} {n : ℕ} (h : slpK S A n = true) :
    ∀ j, 2 ≤ j → j < n → Nat.land (A j) 15 < j ∧ Nat.shiftRight (A j) 4 < j ∧
      ∀ p < 1365, ap (S j) p = ap (S (Nat.land (A j) 15)) (ap (S (Nat.shiftRight (A j) 4)) p) := by
  intro j hj2 hjn
  have := allN_spec h (j - 2) (by change j - 2 < n - 2; omega)
  simp only [strictB_eq] at this
  have ej : Nat.add (j - 2) 2 = j := by change j - 2 + 2 = j; omega
  rw [ej] at this
  obtain ⟨ha, this⟩ := band_iff.1 this
  obtain ⟨hb, this⟩ := band_iff.1 this
  exact ⟨Nat.le_of_ble_eq_true ha, Nat.le_of_ble_eq_true hb, fun p hp =>
    Nat.eq_of_beq_eq_true (allN_spec this p hp)⟩

theorem invK_spec {S SI : ℕ → ℕ} {n : ℕ} (h : invK S SI n = true) :
    ∀ j < n, ∀ p < 1365, ap (SI j) (ap (S j) p) = p := fun j hj p hp =>
  Nat.eq_of_beq_eq_true (allN_spec (allN_spec h j hj) p hp)

theorem ptEqK_spec {P : ℕ} {f : ℕ → ℕ} (h : ptEqK P f = true) : ∀ p < 1365, ap P p = f p :=
  fun p hp => Nat.eq_of_beq_eq_true (allN_spec h p hp)

@[expose] noncomputable def wordB (b : ℕ → Pm) (W : ℕ → ℕ) : ℕ → Pm
  | 0 => 1
  | i + 1 => b (Nat.land (tw 4 15 W i) 3) * wordB b W i

theorem land3_lt (l : ℕ) : Nat.land l 3 < 4 := by
  change l &&& (2 ^ 2 - 1) < 4
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

theorem wpB_eq {B W : ℕ → ℕ} {b : ℕ → Pm} (hB : ∀ j < 4, PtRep (B j) (b j)) :
    ∀ (L : ℕ) (x : Fin 1365), wpB B W L x = (wordB b W L x : ℕ)
  | 0, _ => rfl
  | L + 1, x => by
    change strictN (wpB B W L x) (ap (B (Nat.land (tw 4 15 W L) 3))) = _
    rw [strictN_eq, wpB_eq hB L x]
    simp only [wordB, Equiv.Perm.mul_apply]
    exact hB _ (land3_lt _) _

theorem wordB_mem {G : Type*} [SetLike G Pm] [SubgroupClass G Pm] {K : G} {b : ℕ → Pm}
    (hb : ∀ j < 4, b j ∈ K) (W : ℕ → ℕ) : ∀ L, wordB b W L ∈ K
  | 0 => one_mem K
  | L + 1 => mul_mem (hb _ (land3_lt _)) (wordB_mem hb W L)

end CFSG.KC.G24Rigid

end
