module

public import Certificates.Data.Kernel.Co2I301.Six
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option exponentiation.threshold 600

namespace CFSG.KS.Co2I301

open CFSG.KC.Enum CFSG.KC.Co2I301 CFSG.KS CFSG.KS.Raw.Orb

@[expose] def R7 (P : ℕ) (g : Equiv.Perm (Fin 63)) : Prop := PRep 63 7 P g

theorem mask7 : CFSG.KS.mask 7 = 127 := by decide

theorem bIf_true {c t e : Bool} (h : bIf(c, t, e) = true) : (c = true → t = true) ∧
    (c = false → e = true) := by
  cases c <;> simp_all

theorem beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by rwa [Nat.blt_eq] at h

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (beq_true e) h

theorem pt_eq (p i : ℕ) : pt p i = pg 7 (CFSG.KS.mask 7) p i := by rw [mask7]; rfl

theorem cp_eq (p q : ℕ) : cp p q = pcomp 63 7 (CFSG.KS.mask 7) p q := by rw [mask7]; rfl

theorem r7_apply {P : ℕ} {g : Equiv.Perm (Fin 63)} (h : R7 P g) (x : Fin 63) :
    pt P x = g x := by
  rw [pt_eq]
  exact h x

theorem r7_cp {P Q : ℕ} {g h : Equiv.Perm (Fin 63)} (hP : R7 P g) (hQ : R7 Q h) :
    R7 (cp P Q) (g * h) := by
  rw [cp_eq]
  exact prep_pcomp (by norm_num) hP hQ

theorem r7_idc : R7 idc 1 := prep_pidn (by norm_num) (by norm_num)

theorem r7_cj {G GI X : ℕ} {g x : Equiv.Perm (Fin 63)} (hG : R7 G g) (hGI : R7 GI g⁻¹)
    (hX : R7 X x) : R7 (cj G GI X) (g * x * g⁻¹) :=
  r7_cp (r7_cp hG hX) hGI

theorem r7_inv {P Q : ℕ} {g : Equiv.Perm (Fin 63)} (hP : R7 P g) (h : inv63 P Q = true) :
    R7 Q g⁻¹ := by
  have h' : permOK 63 7 (CFSG.KS.mask 7) (63 * 7) P Q = true := by rw [mask7]; exact h
  obtain ⟨-, -, h3⟩ := permOK_facts h'
  intro x
  have e := (h3 (g⁻¹ x) (g⁻¹ x).2).2
  have hx : g (g⁻¹ x) = x := by simp
  rw [hP (g⁻¹ x), hx] at e
  exact e

theorem cd_shr (r : ℕ) : cd r >>> (63 * 7) = 0 := by
  have hlt : cd r < 2 ^ 441 := by
    unfold cd
    have e : CM = 2 ^ 441 - 1 := by decide
    rw [e]
    change r &&& (2 ^ 441 - 1) < 2 ^ 441
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by positivity)
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt hlt

theorem cd_eq_of_r7 {r s : ℕ} {g : Equiv.Perm (Fin 63)} (hr : R7 (cd r) g) (hs : R7 (cd s) g) :
    cd r = cd s :=
  PF.eq_of_fields (n := 63) (w := 7) (by norm_num) (cd_shr r) (cd_shr s)
    fun i hi => by rw [hr ⟨i, hi⟩, hs ⟨i, hi⟩]

theorem r7_unique {P : ℕ} {g h : Equiv.Perm (Fin 63)} (hg : R7 P g) (hh : R7 P h) : g = h :=
  Equiv.ext fun x => Fin.ext (by rw [← hg x, ← hh x])

theorem eq_of_r7 {P Q : ℕ} {g : Equiv.Perm (Fin 63)} (hP : P >>> (63 * 7) = 0)
    (hQ : Q >>> (63 * 7) = 0) (h1 : R7 P g) (h2 : R7 Q g) : P = Q :=
  PF.eq_of_fields (n := 63) (w := 7) (by norm_num) hP hQ
    fun i hi => by rw [h1 ⟨i, hi⟩, h2 ⟨i, hi⟩]

theorem cp_shr (p q : ℕ) : cp p q >>> (63 * 7) = 0 := by
  rw [cp_eq]
  exact PF.pcomp_shr p q (by norm_num) (by norm_num)

theorem idc_shr : idc >>> (63 * 7) = 0 := PF.pidn_shr (by norm_num) (by norm_num)

theorem incr_lt {R : ℕ → ℕ} {N : ℕ} (h : ∀ j < N, incr R N j = true) :
    ∀ i j, i < j → j < N → cd (R i) < cd (R j) := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := h j (by omega)
    unfold incr at hs
    have hb : Nat.blt (Nat.succ j) N = true := by rw [Nat.blt_eq]; exact hj
    rw [hb] at hs
    have hjj : cd (R j) < cd (R (j + 1)) := blt_true hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hl | rfl
    · exact (ih hl (by omega)).trans hjj
    · exact hjj

theorem incr_inj {R : ℕ → ℕ} {N : ℕ} (h : ∀ j < N, incr R N j = true) {i j : ℕ} (hi : i < N)
    (hj : j < N) (e : cd (R i) = cd (R j)) : i = j := by
  rcases lt_trichotomy i j with hl | rfl | hl
  · exact absurd e (incr_lt h i j hl hj).ne
  · rfl
  · exact absurd e (incr_lt h j i hl hi).ne'

theorem incr_perm_inj {R : ℕ → ℕ} {N : ℕ} (h : ∀ j < N, incr R N j = true) {i j : ℕ}
    (hi : i < N) (hj : j < N) {g : Equiv.Perm (Fin 63)} (hgi : R7 (cd (R i)) g)
    (hgj : R7 (cd (R j)) g) : i = j :=
  incr_inj h hi hj (cd_eq_of_r7 hgi hgj)

theorem dep_ind {N : ℕ} (dep par : ℕ → ℕ) (Q : ℕ → Prop) (h0 : ∀ j < N, dep j = 0 → Q j)
    (hs : ∀ j < N, dep j ≠ 0 → par j < N ∧ dep (par j) + 1 = dep j ∧ (Q (par j) → Q j)) :
    ∀ j < N, Q j := by
  suffices ∀ d, ∀ j < N, dep j = d → Q j from fun j hj => this _ j hj rfl
  intro d
  induction d with
  | zero => exact fun j hj e => h0 j hj e
  | succ d ih =>
    intro j hj e
    obtain ⟨hp, hd, hq⟩ := hs j hj (by omega)
    exact hq (ih _ hp (by omega))

theorem oRec_spec {O : ℕ → ℕ} {N X : ℕ} {PI PII : ℕ → ℕ} {j : ℕ}
    (h : oRec O N X PI PII j = true) :
    (oDep (O j) = 0 → cd (O j) = X) ∧
    (oDep (O j) ≠ 0 → oPar (O j) < N ∧ oDep (O (oPar (O j))) + 1 = oDep (O j) ∧
      cd (O j) = cj (PI (oLet (O j))) (PII (oLet (O j))) (cd (O (oPar (O j))))) ∧
    incr O N j = true := by
  unfold oRec at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨ht, he⟩ := bIf_true h1
  refine ⟨fun e => beq_true (ht (by rw [e]; rfl)), fun e => ?_, h2⟩
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (he (beq_false e))
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
  exact ⟨blt_true a, beq_true b, beq_true c⟩

theorem kRec_spec {K : ℕ → ℕ} {N : ℕ} {FK : ℕ → ℕ} {j : ℕ} (h : kRec K N FK j = true) :
    (kDep (K j) = 0 → cd (K j) = idc) ∧
    (kDep (K j) ≠ 0 → kPar (K j) < N ∧ kDep (K (kPar (K j))) + 1 = kDep (K j) ∧
      cd (K j) = cp (cd (K (kPar (K j)))) (FK (kLet (K j)))) := by
  unfold kRec at h
  obtain ⟨ht, he⟩ := bIf_true h
  refine ⟨fun e => beq_true (ht (by rw [e]; rfl)), fun e => ?_⟩
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (he (beq_false e))
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
  exact ⟨blt_true a, beq_true b, beq_true c⟩

theorem lRec_spec {L : ℕ → ℕ} {N : ℕ} {K : ℕ → ℕ} {NK : ℕ} {A : ℕ → ℕ} {F1 F2 j : ℕ}
    (h : lRec L N K NK A F1 F2 j = true) :
    lK (L j) < NK ∧ lU (L j) < 6 ∧ cd (L j) = cp (cd (K (lK (L j)))) (A (lU (L j))) ∧
    incr L N j = true ∧
    (cm (cd (L j)) F1 = true → cm (cd (L j)) F2 = true →
      cd (L j) = A 0 ∨ cd (L j) = A 1 ∨ cd (L j) = A 2) := by
  unfold lRec at h
  obtain ⟨a, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨c, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨d, h⟩ := (bAnd_iff _ _).1 h
  refine ⟨blt_true a, blt_true b, beq_true c, d, fun h1 h2 => ?_⟩
  have hc := (bIf_true h).1 (by rw [h1, h2])
  cases e0 : Nat.beq (cd (L j)) (A 0)
  · rw [e0] at hc
    cases e1 : Nat.beq (cd (L j)) (A 1)
    · rw [e1] at hc
      exact Or.inr (Or.inr (beq_true hc))
    · exact Or.inr (Or.inl (beq_true e1))
  · exact Or.inl (beq_true e0)

theorem tRec_spec {T : ℕ → ℕ} {N : ℕ} {TG S : ℕ → ℕ} {NS j : ℕ}
    (h : tRec T N TG S NS j = true) :
    (tDep (T j) = 0 → cd (T j) = idc) ∧
    (tDep (T j) ≠ 0 → tPar (T j) < N ∧ tLet (T j) < 4 ∧
      tDep (T (tPar (T j))) + 1 = tDep (T j) ∧ cd (T j) = cp (cd (T (tPar (T j)))) (TG (tLet (T j)))) ∧
    incr T N j = true ∧
    (∀ g < 4, tTgt (T j) g < N ∧ cd (T (tTgt (T j) g)) = cp (cd (T j)) (TG g)) ∧
    (cp (cd (T j)) (cd (T j)) = idc → cd (T j) ≠ idc →
      tInv (T j) < NS ∧ cd (S (tInv (T j))) = cd (T j)) := by
  unfold tRec at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  obtain ⟨ht, he⟩ := bIf_true h1
  refine ⟨fun e => beq_true (ht (by rw [e]; rfl)), fun e => ?_, h2, fun g hg => ?_,
    fun e1 e2 => ?_⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (he (beq_false e))
    obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
    obtain ⟨c, d⟩ := (bAnd_iff _ _).1 c
    exact ⟨blt_true a, blt_true b, beq_true c, beq_true d⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h3 g hg)
    exact ⟨blt_true a, beq_true b⟩
  · have hc : bAnd(Nat.beq (cp (cd (T j)) (cd (T j))) idc, Bool.not (Nat.beq (cd (T j)) idc)) =
        true := by
      rw [show Nat.beq (cp (cd (T j)) (cd (T j))) idc = true by rw [e1]; exact Nat.beq_refl _,
        beq_false e2]
      rfl
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 ((bIf_true h4).1 hc)
    exact ⟨blt_true a, beq_true b⟩

theorem sRec_spec {S : ℕ → ℕ} {N : ℕ} {PI PII HL HLI : ℕ → ℕ} {j : ℕ}
    (h : sRec S N PI PII HL HLI j = true) :
    (∀ g < 2, sTgt (S j) g < N ∧ cd (S (sTgt (S j) g)) = cj (PI g) (PII g) (cd (S j))) ∧
    sWd (S j) < 3 ∧ sPt (S j) < 63 ∧
    pt (cd (S j)) (ysy HL HLI (sWd (S j)) (cd (S j)) (sPt (S j))) ≠
      ysy HL HLI (sWd (S j)) (cd (S j)) (pt (cd (S j)) (sPt (S j))) := by
  unfold sRec at h
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun g hg => ?_, blt_true h3, blt_true h4, fun e => ?_⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h2 g hg)
    exact ⟨blt_true a, beq_true b⟩
  · rw [e, Nat.beq_refl] at h5
    exact Bool.noConfusion h5

theorem wP_cons (PI PII : ℕ → ℕ) (c : ℕ) (w : List ℕ) :
    wP PI PII (c :: w) = cp (wL PI PII c) (wP PI PII w) := rfl

@[expose] def letterPerm (π : ℕ → Equiv.Perm (Fin 63)) (c : ℕ) : Equiv.Perm (Fin 63) :=
  if c % 2 = 0 then π (c / 2) else (π (c / 2))⁻¹

@[expose] def wordPerm (π : ℕ → Equiv.Perm (Fin 63)) : List ℕ → Equiv.Perm (Fin 63)
  | [] => 1
  | c :: w => letterPerm π c * wordPerm π w

theorem r7_wL {PI PII : ℕ → ℕ} {π : ℕ → Equiv.Perm (Fin 63)} (hPI : ∀ g < 2, R7 (PI g) (π g))
    (hPII : ∀ g < 2, R7 (PII g) (π g)⁻¹) {c : ℕ} (hc : c < 4) :
    R7 (wL PI PII c) (letterPerm π c) := by
  have e1 : Nat.land c 1 = c % 2 := by
    change c &&& (2 ^ 1 - 1) = c % 2 ^ 1
    exact Nat.and_two_pow_sub_one_eq_mod c 1
  have e2 : Nat.shiftRight c 1 = c / 2 := by
    change c >>> 1 = c / 2 ^ 1
    exact Nat.shiftRight_eq_div_pow c 1
  unfold wL letterPerm
  rw [e1, e2]
  by_cases h : c % 2 = 0
  · rw [if_pos h, show Nat.beq (c % 2) 0 = true by rw [h]; rfl]
    exact hPI _ (by omega)
  · rw [if_neg h, show Nat.beq (c % 2) 0 = false from beq_false h]
    exact hPII _ (by omega)

theorem r7_wP {PI PII : ℕ → ℕ} {π : ℕ → Equiv.Perm (Fin 63)} (hPI : ∀ g < 2, R7 (PI g) (π g))
    (hPII : ∀ g < 2, R7 (PII g) (π g)⁻¹) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 4) → R7 (wP PI PII w) (wordPerm π w)
  | [], _ => r7_idc
  | c :: w, hw => by
    rw [wP_cons, wordPerm]
    exact r7_cp (r7_wL hPI hPII (hw c List.mem_cons_self))
      (r7_wP hPI hPII w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))

theorem wordPerm_mem {π : ℕ → Equiv.Perm (Fin 63)} {G : Subgroup (Equiv.Perm (Fin 63))}
    (hπ : ∀ g < 2, π g ∈ G) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 4) → wordPerm π w ∈ G
  | [], _ => G.one_mem
  | c :: w, hw => by
    rw [wordPerm]
    refine G.mul_mem ?_ (wordPerm_mem hπ w fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))
    have hc := hw c List.mem_cons_self
    unfold letterPerm
    split_ifs
    · exact hπ _ (by omega)
    · exact G.inv_mem (hπ _ (by omega))

theorem r7_pw {P : ℕ} {g : Equiv.Perm (Fin 63)} (hP : R7 P g) : ∀ e, R7 (pw P e) (g ^ e)
  | 0 => by rw [pow_zero]; exact r7_idc
  | e + 1 => by
    rw [pow_succ]
    exact r7_cp (r7_pw hP e) hP

end CFSG.KS.Co2I301

end
