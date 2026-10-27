module

public import Certificates.Data.Kernel.SporCov.Census
public import CFSG.Certificates.Kernel.SporCov.Cover
public import CFSG.Certificates.Kernel.SporCov.P3Cover
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

public section

namespace CFSG.KD.SporCov

open CFSG.KC.SporCov CFSG.StandardType.SporadicShape
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

theorem lt_of_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem nthN_cons_succ (a : ℕ) (l : List ℕ) (i : ℕ) : nthN (a :: l) (i + 1) = nthN l i := rfl

theorem lenN_eq : ∀ l : List ℕ, lenN l = l.length
  | [] => rfl
  | a :: l => by
    change lenN l + 1 = _
    rw [lenN_eq l, List.length_cons]

theorem lenW_eq : ∀ l : List (List ℕ), lenW l = l.length
  | [] => rfl
  | a :: l => by
    change lenW l + 1 = _
    rw [lenW_eq l, List.length_cons]

theorem nthW_mem {l : List (List ℕ)} {i : ℕ} (hi : i < l.length) : nthW l i ∈ l := by
  induction l generalizing i with
  | nil => exact absurd hi (by simp)
  | cons w l ih =>
    cases i with
    | zero => exact List.mem_cons_self
    | succ i =>
      rw [nthW_cons_succ]
      exact List.mem_cons_of_mem _ (ih (by simp at hi; omega))

theorem nfW_succ (H : List (List ℕ)) (e : ℕ → ℕ) (n i : ℕ) :
    nfW H e (n + 1) i = nfW H e n (i + 1) ++ repW (nthW H i) (e i) := rfl

theorem zeroTo_eq {e : ℕ → ℕ} {i : ℕ} (h : zeroTo e i = true) : ∀ t ≤ i, e t = 0 := by
  have key : ∀ n, Nat.rec (motive := fun _ => Bool) true
      (fun t ih => Nat.beq (e t) 0 && ih) n = true → ∀ t < n, e t = 0 := by
    intro n
    induction n with
    | zero => intro _ t ht; exact absurd ht (Nat.not_lt_zero t)
    | succ n ih =>
      intro hn t ht
      change (Nat.beq (e n) 0 && _) = true at hn
      rw [Bool.and_eq_true] at hn
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact ih hn.2 t ht
      · exact Nat.eq_of_beq_eq_true hn.1
  intro t ht
  exact key (i + 1) h t (Nat.lt_succ_of_le ht)

theorem neA_mem {E : List ℕ → List ℕ → Bool} {W : List (List ℕ)} (h : neA E W = true) :
    ∀ w ∈ W, neOK E w = true := by
  induction W with
  | nil => intro w hw; exact absurd hw List.not_mem_nil
  | cons v W ih =>
    change (neOK E v && neA E W) = true at h
    rw [Bool.and_eq_true] at h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.1
    · exact ih h.2 w hw

section Keys

variable (K : List ℕ → ℕ) (H : List (List ℕ)) (k p : ℕ)

theorem keyFrom_cons (m : ℕ) (P : List ℕ) (prev : ℕ) :
    keyFrom K H k p (m :: P) prev =
      (Nat.blt prev (K (cw H k p m)) && keyFrom K H k p P (K (cw H k p m))) := rfl

theorem keyFrom_lt : ∀ (P : List ℕ) (prev : ℕ), keyFrom K H k p P prev = true →
    ∀ n < P.length, prev < K (cw H k p (nthN P n))
  | [], _, _, n, hn => absurd hn (by simp)
  | m :: P, prev, h, n, hn => by
    rw [keyFrom_cons, Bool.and_eq_true] at h
    have h1 := lt_of_blt h.1
    cases n with
    | zero => exact h1
    | succ n =>
      rw [nthN_cons_succ]
      exact h1.trans (keyFrom_lt P _ h.2 n (by simp at hn; omega))

theorem keyFrom_mono : ∀ (P : List ℕ) (prev : ℕ), keyFrom K H k p P prev = true →
    ∀ a b, a < b → b < P.length → K (cw H k p (nthN P a)) < K (cw H k p (nthN P b))
  | [], _, _, a, b, _, hb => absurd hb (by simp)
  | m :: P, prev, h, a, b, hab, hb => by
    rw [keyFrom_cons, Bool.and_eq_true] at h
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [nthN_cons_succ]
    cases a with
    | zero => exact keyFrom_lt K H k p P _ h.2 b (by simp at hb; omega)
    | succ a =>
      rw [nthN_cons_succ]
      exact keyFrom_mono P _ h.2 a b (by omega) (by simp at hb; omega)

theorem keyInc_mono {P : List ℕ} (h : keyInc K H k p P = true) :
    ∀ a b, a < b → b < P.length → K (cw H k p (nthN P a)) < K (cw H k p (nthN P b)) := by
  cases P with
  | nil => intro a b _ hb; exact absurd hb (by simp)
  | cons m P =>
    change keyFrom K H k p P (K (cw H k p m)) = true at h
    intro a b hab hb
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [nthN_cons_succ]
    cases a with
    | zero => exact keyFrom_lt K H k p P _ h b (by simp at hb; omega)
    | succ a =>
      rw [nthN_cons_succ]
      exact keyFrom_mono K H k p P _ h a b (by omega) (by simp at hb; omega)

end Keys

variable {G : Type} [Group G]

@[expose] def nfG (g : ℕ → G) (e : ℕ → ℕ) : ℕ → ℕ → G
  | 0, _ => 1
  | n + 1, i => g i ^ e i * nfG g e n (i + 1)

theorem nfG_mem {k : ℕ} (g : ℕ → G) (e : ℕ → ℕ) (s : ℕ) :
    ∀ n i, i + n ≤ k → (∀ t, i ≤ t → t < i + n → e t = 0 ∨ s ≤ t) →
      nfG g e n i ∈ pcSub (fun t : Fin k => (g t)⁻¹) s
  | 0, _, _, _ => Subgroup.one_mem _
  | n + 1, i, hk, he => by
    refine Subgroup.mul_mem _ ?_
      (nfG_mem g e s n (i + 1) (by omega) fun t h1 h2 => he t (by omega) (by omega))
    rcases he i le_rfl (by omega) with h0 | hs
    · rw [h0, pow_zero]
      exact Subgroup.one_mem _
    · have hm : (g i)⁻¹ ∈ pcSub (fun t : Fin k => (g t)⁻¹) s :=
        Subgroup.subset_closure ⟨⟨i, by omega⟩, hs, rfl⟩
      exact Subgroup.pow_mem _ (by simpa using Subgroup.inv_mem _ hm) _

theorem nfG_mem_after {k : ℕ} (g : ℕ → G) {e : ℕ → ℕ} {i : ℕ} (he : ∀ t ≤ i, e t = 0) :
    nfG g e k 0 ∈ pcSub (fun t : Fin k => (g t)⁻¹) (i + 1) :=
  nfG_mem g e (i + 1) k 0 (by omega) fun t _ _ => by
    by_cases ht : t ≤ i
    · exact Or.inl (he t ht)
    · exact Or.inr (by omega)

theorem pc_card [Finite G] {p k : ℕ} (hp : 0 < p) (g : ℕ → G)
    (hpow : ∀ i < k, ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧ g i ^ p = nfG g e k 0)
    (hconj : ∀ i j, i < j → j < k → ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧
      g j * g i = g i * nfG g e k 0) :
    Nat.card (pcSub (fun t : Fin k => (g t)⁻¹) 0) ≤ p ^ k := by
  set q : Fin k → G := fun t => (g t)⁻¹ with hq
  have hp' : ∀ i : Fin k, q i ^ p ∈ pcSub q (i.val + 1) := by
    intro i
    obtain ⟨e, he, h⟩ := hpow i i.isLt
    rw [hq, inv_pow, h]
    exact Subgroup.inv_mem _ (nfG_mem_after g he)
  have hc : ∀ i j : Fin k, i < j → q i * q j * (q i)⁻¹ ∈ pcSub q (i.val + 1) := by
    intro i j hij
    obtain ⟨e, he, h⟩ := hconj i j hij j.isLt
    have e1 : q i * q j * (q i)⁻¹ = ((g i)⁻¹ * g j * g i)⁻¹ := by
      rw [hq]
      group
    have e2 : (g i)⁻¹ * g j * g i = nfG g e k 0 := by
      rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e1, e2]
    exact Subgroup.inv_mem _ (nfG_mem_after g he)
  have key : ∀ m : ℕ, m ≤ k → Nat.card (pcSub q (k - m)) ≤ p ^ m := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.sub_zero, pcSub_n, pow_zero]
      simp
    | succ m ih =>
      intro hm
      have hi : k - (m + 1) < k := by omega
      have e : (k - (m + 1)) + 1 = k - m := by omega
      have hf' : Finite (pcSub q (k - (m + 1) + 1)) := inferInstance
      have h := pcSub_card_step hp q ⟨k - (m + 1), hi⟩ hf' (hp' ⟨k - (m + 1), hi⟩)
        (fun j hj => hc ⟨k - (m + 1), hi⟩ j hj)
      have h3 : Nat.card (pcSub q (k - (m + 1))) ≤ p * Nat.card (pcSub q (k - (m + 1) + 1)) := h.2
      rw [e] at h3
      calc Nat.card (pcSub q (k - (m + 1))) ≤ p * Nat.card (pcSub q (k - m)) := h3
        _ ≤ p * p ^ m := Nat.mul_le_mul_left _ (ih (by omega))
        _ = p ^ (m + 1) := by ring
  have := key k le_rfl
  rwa [Nat.sub_self] at this

theorem cover_of_census [Finite G] {p : ℕ} (hp : p.Prime) (S : Subgroup G)
    (hS : Nat.card S = p ^ (Nat.card G).factorization p)
    (hcen : ∀ x ∈ S, x ^ p = 1 → x ≠ 1 → ∃ y ∈ Subgroup.zpowers x, y ≠ 1 ∧
      ∀ w, IsConj y w → SporKRestGenerating p w) :
    SporKRestCover p G := by
  have : Fact p.Prime := ⟨hp⟩
  intro E hE hcard
  let Sy : Sylow p G := Sylow.ofCard S hS
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Sy P
  have : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    nlinarith [hp.two_le]
  obtain ⟨e, heE, he1⟩ := Subgroup.exists_ne_one_of_nontrivial E
  have hxS : g⁻¹ * e * g ∈ S := by
    have hxP : e ∈ (P : Subgroup G) := hEP heE
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
    obtain ⟨t, ht, et⟩ := hxP
    have e2 : g⁻¹ * e * g = t := by
      rw [← et]
      simp [MulAut.conj_apply]
      group
    rw [e2]
    exact ht
  have hinv : g⁻¹ * e * g = g⁻¹ * e * g⁻¹⁻¹ := by rw [inv_inv]
  have hxp : (g⁻¹ * e * g) ^ p = 1 := by
    rw [hinv, conj_pow, hE.2 e heE, mul_one, mul_inv_cancel]
  have hx1 : g⁻¹ * e * g ≠ 1 := by
    rw [hinv]
    exact conj_ne_one he1
  obtain ⟨y, hy, hy1, hyg⟩ := hcen _ hxS hxp hx1
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨g * (g⁻¹ * e * g) ^ m * g⁻¹, ?_, conj_ne_one hy1, hyg _ (isConj_iff.2 ⟨g, rfl⟩)⟩
  have e3 : g * (g⁻¹ * e * g) * g⁻¹ = e := by group
  rw [← conj_zpow, e3]
  exact zpow_mem heE m

namespace Model

variable {L : ℕ → Bool} {E : List ℕ → List ℕ → Bool} {ev : List ℕ → G} (hM : Model L E ev)

theorem chW_nfW {H : List (List ℕ)} (hH : chA L H = true) (e : ℕ → ℕ) :
    ∀ n i, chW L (nfW H e n i) = true
  | 0, _ => chW_nil L
  | n + 1, i => by
    rw [nfW_succ]
    exact chW_append_of (chW_nfW hH e n (i + 1)) (chW_repW (chW_nthW hH i) _)

include hM

theorem ev_nfW (H : List (List ℕ)) (e : ℕ → ℕ) :
    ∀ n i, ev (nfW H e n i) = nfG (fun t => ev (nthW H t)) e n i
  | 0, _ => hM.nil
  | n + 1, i => by
    rw [nfW_succ, hM.append, hM.repW_eq, ev_nfW H e n (i + 1)]
    rfl

theorem pcR_facts {p k : ℕ} {H R : List (List ℕ)} (hH : chA L H = true)
    (hR : ∀ i < k, ∀ j < k, i ≤ j → pcR E p H R k i j = true) :
    (∀ i < k, ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧
        ev (nthW H i) ^ p = nfG (fun t => ev (nthW H t)) e k 0) ∧
      ∀ i j, i < j → j < k → ∃ e : ℕ → ℕ, (∀ t ≤ i, e t = 0) ∧
        ev (nthW H j) * ev (nthW H i) = ev (nthW H i) * nfG (fun t => ev (nthW H t)) e k 0 := by
  have oH := chW_nthW hH
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_⟩
  · have h := hR i hi i hi le_rfl
    unfold pcR at h
    rw [Bool.and_eq_true, Nat.beq_refl, cond_true] at h
    refine ⟨_, zeroTo_eq h.1, ?_⟩
    rw [← hM.repW_eq, ← hM.ev_nfW]
    exact hM.eq (chW_repW (oH i) p) (chW_nfW hH _ _ _) h.2
  · have h := hR i (by omega) j hj hij.le
    unfold pcR at h
    have hb : Nat.beq i j = false :=
      Bool.eq_false_iff.2 fun hb => hij.ne (Nat.eq_of_beq_eq_true hb)
    rw [Bool.and_eq_true, hb, cond_false] at h
    refine ⟨_, zeroTo_eq h.1, ?_⟩
    rw [← hM.ev_nfW]
    have e := hM.eq (chW_append_of (oH i) (oH j)) (chW_append_of (chW_nfW hH _ _ _) (oH i)) h.2
    rwa [hM.append, hM.append] at e

theorem cenOK_cases {p k N n : ℕ} {H Rp Gs T : List (List ℕ)} {P : List ℕ}
    (h : cenOK E p H k Rp Gs P T N n = true) :
    E (cw H k p (nthN P n)) [] = true ∨ neOK E (repW (cw H k p (nthN P n)) p) = true ∨
      (nthN (nthW T n) 1 < Rp.length ∧
        cjOK E (nthW Rp (nthN (nthW T n) 1)) (nthW Gs (nthN (nthW T n) 2))
          (cw H k p (nthN P n)) = true) ∨
      (nthN (nthW T n) 1 < N ∧ nthN (nthW T (nthN (nthW T n) 1)) 0 = 2 ∧
        E (repW (cw H k p (nthN P n)) (nthN (nthW T n) 2))
          (cw H k p (nthN P (nthN (nthW T n) 1))) = true) := by
  unfold cenOK at h
  cases h0 : Nat.beq (nthN (nthW T n) 0) 0
  · rw [h0, cond_false] at h
    cases h1 : Nat.beq (nthN (nthW T n) 0) 1
    · rw [h1, cond_false] at h
      cases h2 : Nat.beq (nthN (nthW T n) 0) 2
      · rw [h2, cond_false] at h
        cases h3 : Nat.beq (nthN (nthW T n) 0) 3
        · rw [h3, cond_false] at h
          exact absurd h Bool.false_ne_true
        · rw [h3, cond_true, Bool.and_eq_true, Bool.and_eq_true] at h
          exact Or.inr (Or.inr (Or.inr ⟨lt_of_blt h.1.1,
            Nat.eq_of_beq_eq_true h.1.2, h.2⟩))
      · rw [h2, cond_true, Bool.and_eq_true, lenW_eq] at h
        exact Or.inr (Or.inr (Or.inl ⟨lt_of_blt h.1, h.2⟩))
    · rw [h1, cond_true] at h
      exact Or.inr (Or.inl h)
  · rw [h0, cond_true] at h
    exact Or.inl h

theorem cenOK_two {p k N n : ℕ} {H Rp Gs T : List (List ℕ)} {P : List ℕ}
    (h : cenOK E p H k Rp Gs P T N n = true) (h2 : nthN (nthW T n) 0 = 2) :
    nthN (nthW T n) 1 < Rp.length ∧
      cjOK E (nthW Rp (nthN (nthW T n) 1)) (nthW Gs (nthN (nthW T n) 2))
        (cw H k p (nthN P n)) = true := by
  unfold cenOK at h
  rw [h2] at h
  change (cond false _ (cond false _ (cond true _ _))) = true at h
  rw [cond_false, cond_false, cond_true, Bool.and_eq_true, lenW_eq] at h
  exact ⟨lt_of_blt h.1, h.2⟩

theorem cover_of_cen [Finite G] {p k : ℕ} (hp : p.Prime) (hval : (Nat.card G).factorization p = k)
    (hc : ∀ u, chW L u = true → ev u = 1 → E u [] = true) (K : List ℕ → ℕ)
    (hK : ∀ u v, chW L u = true → chW L v = true → ev u = ev v → K u = K v)
    {H R Rp Gs T : List (List ℕ)} {P : List ℕ}
    (hR : ∀ i < k, ∀ j < k, i ≤ j → pcR E p H R k i j = true)
    (hH : cenH E L H Rp Gs P (p ^ k) = true) (hI : keyInc K H k p P = true)
    (hT : ∀ n < p ^ k, cenOK E p H k Rp Gs P T (p ^ k) n = true)
    (hgen : ∀ r ∈ Rp, ∀ y, IsConj (ev r) y → SporKRestGenerating p y) : SporKRestCover p G := by
  unfold cenH at hH
  simp only [Bool.and_eq_true] at hH
  obtain ⟨⟨⟨⟨oH, oR⟩, oG⟩, hne⟩, hlen⟩ := hH
  rw [lenN_eq] at hlen
  have hlen' : P.length = p ^ k := Nat.eq_of_beq_eq_true hlen
  set g : ℕ → G := fun t => ev (nthW H t) with hg
  set S := pcSub (fun t : Fin k => (g t)⁻¹) 0 with hSdef
  set w : ℕ → List ℕ := fun n => cw H k p (nthN P n) with hw
  have ow : ∀ n, chW L (w n) = true := fun n => chW_nfW oH _ _ _
  have hwS : ∀ n, ev (w n) ∈ S := fun n => by
    rw [hw]
    unfold cw
    rw [hM.ev_nfW]
    exact nfG_mem g _ 0 k 0 (by omega) fun t _ _ => Or.inr (Nat.zero_le t)
  obtain ⟨hpow, hconj⟩ := hM.pcR_facts oH hR
  have hle : Nat.card S ≤ p ^ k := pc_card hp.pos g hpow hconj
  let f : Fin (p ^ k) → S := fun n => ⟨ev (w n), hwS n⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : ev (w a) = ev (w b) := congrArg Subtype.val hab
    have eK := hK _ _ (ow a) (ow b) e
    by_contra hne'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · exact absurd eK (keyInc_mono K H k p hI a b h (by rw [hlen']; exact b.isLt)).ne
    · exact absurd eK (keyInc_mono K H k p hI b a h (by rw [hlen']; exact a.isLt)).ne'
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by simpa using hle)
  have hcard : Nat.card S = p ^ (Nat.card G).factorization p := by
    rw [hval]
    refine le_antisymm hle ?_
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hrep : ∀ n < p ^ k, nthN (nthW T n) 0 = 2 → ev (w n) ≠ 1 ∧
      ∀ y, IsConj (ev (w n)) y → SporKRestGenerating p y := by
    intro n hn h2
    obtain ⟨ht, hcj⟩ := hM.cenOK_two (hT n hn) h2
    have hmem := nthW_mem ht
    have oRt : chW L (nthW Rp (nthN (nthW T n) 1)) = true := (chA_iff L Rp).1 oR _ hmem
    have oGt := chW_nthW oG (nthN (nthW T n) 2)
    have hcon := isConj_of_conj (hM.conj oRt oGt (ow n) hcj)
    refine ⟨fun e1 => ?_, fun y hy => hgen _ hmem y (hcon.trans hy)⟩
    rw [e1, isConj_comm, isConj_one_right] at hcon
    exact hM.ne_one hc oRt ((neA_mem hne) _ hmem) hcon
  refine cover_of_census hp S hcard fun x hxS hxp hx1 => ?_
  obtain ⟨n, hn⟩ := hbij.2 ⟨x, hxS⟩
  have hx : ev (w n) = x := congrArg Subtype.val hn
  rcases hM.cenOK_cases (hT n n.isLt) with h0 | h1 | ⟨ht, hcj⟩ | ⟨hn', h2, hj⟩
  · exact absurd (by rw [← hx, ← hM.nil]; exact hM.eq (ow n) (chW_nil L) h0) hx1
  · refine absurd ?_ (hM.ne_one hc (chW_repW (ow n) p) h1)
    rw [hM.repW_eq, hx, hxp]
  · have hmem := nthW_mem ht
    have oRt : chW L (nthW Rp (nthN (nthW T n) 1)) = true := (chA_iff L Rp).1 oR _ hmem
    have hcon := isConj_of_conj
      (hM.conj oRt (chW_nthW oG (nthN (nthW T n) 2)) (ow n) hcj)
    rw [hx] at hcon
    exact ⟨x, Subgroup.mem_zpowers x, hx1, fun y hy => hgen _ hmem y (hcon.trans hy)⟩
  · obtain ⟨hne1, hgw⟩ := hrep _ hn' h2
    have e := hM.eq (chW_repW (ow n) _) (ow _) hj
    rw [hM.repW_eq, hx] at e
    refine ⟨x ^ nthN (nthW T n) 2, Subgroup.npow_mem_zpowers x _, ?_, ?_⟩
    · rw [e]
      exact hne1
    · rw [e]
      exact hgw

end Model

end CFSG.KD.SporCov

end
