module

public import Certificates.Data.Kernel.SporSch.HS2272K
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.Certificates.Kernel.SporSch.PairClProof
public import CFSG.Certificates.Kernel.Spor.PointChainCard
import CFSG.Certificates.Kernel.SporSch.MathieuBTSplit

public section

namespace CFSG.KS.HS2272

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

variable {n : Nat}

@[expose] def wordVal (g : Nat → Equiv.Perm (Fin n)) (w : List Nat) : Equiv.Perm (Fin n) :=
  (w.map g).prod

theorem wordVal_nil (g : Nat → Equiv.Perm (Fin n)) : wordVal g [] = 1 := rfl

theorem wordVal_cons (g : Nat → Equiv.Perm (Fin n)) (k : Nat) (w : List Nat) :
    wordVal g (k :: w) = g k * wordVal g w := by
  simp [wordVal]

theorem wordVal_append (g : Nat → Equiv.Perm (Fin n)) (v w : List Nat) :
    wordVal g (v ++ w) = wordVal g v * wordVal g w := by
  simp [wordVal]

theorem wordVal_mem {H : Subgroup (Equiv.Perm (Fin n))} {g : Nat → Equiv.Perm (Fin n)}
    (h : ∀ k, g k ∈ H) : ∀ w, wordVal g w ∈ H
  | [] => H.one_mem
  | k :: w => by
    rw [wordVal_cons]
    exact H.mul_mem (h k) (wordVal_mem h w)

variable {L : Nat → Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}

theorem ivL_eq (k : Nat) : ivL k = if k % 2 = 0 then k + 1 else k - 1 := by
  unfold ivL
  by_cases h : k % 2 = 0
  · have e : Nat.beq (Nat.mod k 2) 0 = true := Nat.beq_eq.mpr h
    rw [e, if_pos h]
  · have e : Nat.beq (Nat.mod k 2) 0 = false := by
      cases e' : Nat.beq (Nat.mod k 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e') h
    rw [e, if_neg h]
    rfl

theorem wv_rep (hL : ∀ k, RepF n (L k) (g k)) : ∀ w, RepF n (wv L w) (wordVal g w)
  | [] => RepF.one
  | k :: w => by
    rw [wordVal_cons]
    exact (hL k).comp (wv_rep hL w)

theorem wvI_rep (hL : ∀ k, RepF n (L k) (g k)) (hi : ∀ k, g (ivL k) = (g k)⁻¹) :
    ∀ w, RepF n (wvI L w) (wordVal g w)⁻¹
  | [] => by
    rw [wordVal_nil, inv_one]
    exact RepF.one
  | k :: w => by
    have e : wvI L (k :: w) = fun x => wvI L w (L (ivL k) x) := by
      funext x
      change strictN (L (ivL k) x) (wvI L w) = _
      rw [strictN_val]
    rw [e, wordVal_cons, mul_inv_rev, ← hi k]
    exact (wvI_rep hL hi w).comp (hL _)

theorem cjv_rep (hL : ∀ k, RepF n (L k) (g k)) (hi : ∀ k, g (ivL k) = (g k)⁻¹)
    {f : Nat → Nat} {t : Equiv.Perm (Fin n)} (hf : RepF n f t) (w : List Nat) :
    RepF n (cjv L w f) (wordVal g w * t * (wordVal g w)⁻¹) := by
  rw [mul_assoc]
  exact (wv_rep hL w).comp (hf.comp (wvI_rep hL hi w))

theorem conjProd_rep (hL : ∀ k, RepF n (L k) (g k)) (hi : ∀ k, g (ivL k) = (g k)⁻¹)
    (x y : List Nat) :
    RepF n (conjProd L x y)
      (wordVal g x * (wordVal g y * wordVal g x * (wordVal g y)⁻¹)) := by
  have h := (wv_rep hL x).comp ((wv_rep hL y).comp ((wv_rep hL x).comp (wvI_rep hL hi y)))
  unfold conjProd
  simpa only [mul_assoc] using h

theorem eqBlk_spec {lo len : Nat} {f g' : Nat → Nat} (h : eqBlk lo len f g' = true) :
    ∀ x, lo ≤ x → x < lo + len → f x = g' x := by
  intro x h1 h2
  have := allBlk_spec h (x - lo) (by omega)
  rw [show Nat.add lo (x - lo) = x by change lo + (x - lo) = x; omega] at this
  exact Nat.eq_of_beq_eq_true this

theorem neL_spec {bs : List Nat} {f g' : Nat → Nat} (h : neL bs f g' = true) :
    ¬ ∀ b ∈ bs, f b = g' b := by
  intro h2
  have h3 := (eqOnL_iff bs f g').2 h2
  unfold neL at h
  rw [h3] at h
  exact Bool.false_ne_true h

theorem fixG_spec {ws : List (List Nat)} {bs : List Nat} (h : fixG L ws bs = true) :
    ∀ w ∈ ws, ∀ b ∈ bs, wv L w b = b := by
  induction ws with
  | nil => intro w hw; simp at hw
  | cons v ws ih =>
    have h' : Bool.rec (motive := fun _ => Bool) false (fixG L ws bs)
        (eqOnL bs (wv L v) (fun x => x)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact (eqOnL_iff _ _ _).1 h1
    · exact ih h2 w hw

theorem cntFix_eq (f : Nat → Nat) :
    cntFix n f = ((Finset.range n).filter fun x => f x = x).card := by
  unfold cntFix
  rw [MBT.foldN_add' (g := fun x => if f x = x then 1 else 0), Nat.zero_add, Finset.card_filter]
  intro i s
  by_cases h : f i = i
  · have : Nat.beq (f i) i = true := Nat.beq_eq.mpr h
    rw [this, if_pos h]
  · have : Nat.beq (f i) i = false := by
      cases e : Nat.beq (f i) i
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [this, if_neg h]
    rfl

theorem cntFix_card {f : Nat → Nat} {t : Equiv.Perm (Fin n)} (hf : RepF n f t) :
    cntFix n f = (Finset.univ.filter fun x : Fin n => t x = x).card := by
  rw [cntFix_eq]
  refine (Finset.card_bij (fun (x : Fin n) _ => (x : Nat)) ?_ ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Finset.mem_range, x.2, true_and]
    rw [hf x x.2]
    exact congrArg Fin.val hx
  · intro x _ y _ h
    exact Fin.ext h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext ((hf y hy.1).symm.trans hy.2)

theorem keyL_congr (m : Nat) {f f' : Nat → Nat} : ∀ {bs : List Nat}, (∀ b ∈ bs, f b = f' b) →
    keyL m f bs = keyL m f' bs
  | bs, h => by
    rw [ClP.keyL_eq, ClP.keyL_eq, List.map_congr_left h]

theorem cfL_go (hL : ∀ k, RepF n (L k) (g k)) (hi : ∀ k, g (ivL k) = (g k)⁻¹)
    (h0 : 0 < n) (h3 : 3 < n) {f : Nat → Nat} {t : Equiv.Perm (Fin n)} (hf : RepF n f t) :
    ∀ (ws : List (List Nat)) (k : Nat), cfL n L f ws k = true →
      (∀ w ∈ ws, (wordVal g w * t * (wordVal g w)⁻¹) ⟨0, h0⟩ = ⟨0, h0⟩ ∧
        k < keyL n (cjv L w f) [1, 2, 3]) ∧
      ws.Pairwise (fun v w => keyL n (cjv L v f) [1, 2, 3] < keyL n (cjv L w f) [1, 2, 3])
  | [], _, _ => by simp
  | w :: ws, k, h => by
    have h' : strictB (keyL n (cjv L w f) [nat_lit 1, nat_lit 2, nat_lit 3]) (fun k' =>
        bAnd(Nat.beq (cjv L w f (nat_lit 0)) (nat_lit 0), bAnd(Nat.blt k k', cfL n L f ws k'))) =
        true := h
    rw [strictB_val] at h'
    obtain ⟨ha, hb⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨hc, hd⟩ := (bAnd_iff _ _).1 hb
    obtain ⟨ih1, ih2⟩ := cfL_go hL hi h0 h3 hf ws _ hd
    have hk : k < keyL n (cjv L w f) [1, 2, 3] := Nat.blt_eq.mp hc
    refine ⟨fun v hv => ?_, List.pairwise_cons.2 ⟨fun v hv => (ih1 v hv).2, ih2⟩⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · refine ⟨Fin.ext ?_, hk⟩
      rw [← cjv_rep hL hi hf v 0 h0]
      exact Nat.eq_of_beq_eq_true ha
    · exact ⟨(ih1 v hv).1, lt_trans hk (ih1 v hv).2⟩

theorem cfL_spec (hL : ∀ k, RepF n (L k) (g k)) (hi : ∀ k, g (ivL k) = (g k)⁻¹)
    (h0 : 0 < n) (h3 : 3 < n) {f : Nat → Nat} {t : Equiv.Perm (Fin n)} (hf : RepF n f t)
    {ws : List (List Nat)} {k : Nat} (h : cfL n L f ws k = true) :
    (∀ w ∈ ws, (wordVal g w * t * (wordVal g w)⁻¹) ⟨0, h0⟩ = ⟨0, h0⟩) ∧
      (ws.map fun w => wordVal g w * t * (wordVal g w)⁻¹).Nodup := by
  obtain ⟨h1, h2⟩ := cfL_go hL hi h0 h3 hf ws k h
  refine ⟨fun w hw => (h1 w hw).1, ?_⟩
  rw [List.Nodup, List.pairwise_map]
  refine h2.imp fun {v w} hvw he => ?_
  have e : keyL n (cjv L v f) [1, 2, 3] = keyL n (cjv L w f) [1, 2, 3] := by
    refine keyL_congr n fun b hb => ?_
    have hbn : b < n := by simp at hb; omega
    rw [cjv_rep hL hi hf v b hbn, cjv_rep hL hi hf w b hbn, he]
  omega

theorem hasBit_iff (m p : Nat) : hasBit m p = true ↔ m.testBit p = true := by
  unfold hasBit
  rw [Nat.beq_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  change (m >>> p) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem hasBit_lor (m p q : Nat) :
    hasBit (Nat.lor m (Nat.shiftLeft 1 p)) q = true ↔ hasBit m q = true ∨ q = p := by
  rw [hasBit_iff, hasBit_iff]
  change (m ||| (1 <<< p)).testBit q = true ↔ _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr_right eq_comm

theorem hasBit_one (p q : Nat) : hasBit (Nat.shiftLeft 1 p) q = true ↔ q = p := by
  rw [hasBit_iff]
  change (1 <<< p).testBit q = true ↔ _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  exact eq_comm

section Orbits

variable (hL : ∀ k, RepF n (L k) (g k)) {H : Subgroup (Equiv.Perm (Fin n))} {x₀ : Fin n}
include hL

theorem orbL_go {gs : List (List Nat)} (hgs : ∀ j, wordVal g (gs.getD j []) ∈ H) :
    ∀ (es : List (Nat × Nat × Nat)) (m : Nat), orbL n L gs es m = true →
      (∀ q, hasBit m q = true → ∃ hq : q < n, (⟨q, hq⟩ : Fin n) ∈ MulAction.orbit H x₀) →
      (∀ p ∈ es.map (·.1), (∃ hp : p < n, (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit H x₀) ∧
        hasBit m p = false) ∧ (es.map (·.1)).Nodup
  | [], _, _, _ => by simp
  | e :: es, m, h, hm => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
          (orbL n L gs es (Nat.lor m (Nat.shiftLeft (nat_lit 1) e.1)))
          (Nat.beq (wv L (gs.getD e.2.2 []) e.2.1) e.1)) (Nat.blt e.1 n))
        (bIf(hasBit m e.1, false, true))) (hasBit m e.2.1) = true := h
    obtain ⟨hq, h1⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨hp, h2⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨hpn, h3⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨hw, h4⟩ := (bAnd_iff _ _).1 h3
    have hpn' : e.1 < n := Nat.blt_eq.mp hpn
    have hpf : hasBit m e.1 = false := by
      cases e' : hasBit m e.1
      · rfl
      · rw [e'] at hp
        exact absurd hp Bool.false_ne_true
    obtain ⟨hqn, hqo⟩ := hm _ hq
    have hpo : (⟨e.1, hpn'⟩ : Fin n) ∈ MulAction.orbit H x₀ := by
      obtain ⟨⟨c, hc⟩, hc'⟩ := hqo
      refine ⟨⟨wordVal g (gs.getD e.2.2 []) * c, H.mul_mem (hgs _) hc⟩, Fin.ext ?_⟩
      have e1 := wv_rep hL (gs.getD e.2.2 []) e.2.1 hqn
      rw [Nat.eq_of_beq_eq_true hw] at e1
      have hc2 : c x₀ = ⟨e.2.1, hqn⟩ := hc'
      change ((wordVal g (gs.getD e.2.2 []) * c) x₀ : Nat) = e.1
      rw [Equiv.Perm.mul_apply, hc2]
      exact e1.symm
    have hm' : ∀ q, hasBit (Nat.lor m (Nat.shiftLeft 1 e.1)) q = true →
        ∃ hq : q < n, (⟨q, hq⟩ : Fin n) ∈ MulAction.orbit H x₀ := by
      intro q hq'
      rcases (hasBit_lor m e.1 q).1 hq' with hq' | rfl
      · exact hm q hq'
      · exact ⟨hpn', hpo⟩
    obtain ⟨ih1, ih2⟩ := orbL_go hgs es _ h4 hm'
    refine ⟨fun p hp' => ?_, ?_⟩
    · rcases List.mem_cons.1 hp' with rfl | hp'
      · exact ⟨⟨hpn', hpo⟩, hpf⟩
      · refine ⟨(ih1 p hp').1, ?_⟩
        cases e' : hasBit m p
        · rfl
        · have h5 := (hasBit_lor m e.1 p).2 (Or.inl e')
          have h6 := (ih1 p hp').2
          rw [h5] at h6
          exact absurd h6 (by decide)
    · refine List.nodup_cons.2 ⟨fun hin => ?_, ih2⟩
      have := (ih1 _ hin).2
      rw [(hasBit_lor m e.1 e.1).2 (Or.inr rfl)] at this
      exact absurd this (by decide)

theorem orbL_card {gs : List (List Nat)} (hgs : ∀ j, wordVal g (gs.getD j []) ∈ H)
    {es : List (Nat × Nat × Nat)} {β : Nat} (hβ : β < n)
    (h : orbL n L gs es (Nat.shiftLeft 1 β) = true) :
    es.length + 1 ≤ (MulAction.orbit H (⟨β, hβ⟩ : Fin n)).ncard := by
  obtain ⟨h1, h2⟩ := orbL_go hL (x₀ := ⟨β, hβ⟩) hgs es _ h (fun q hq => by
    rw [hasBit_one] at hq
    subst hq
    exact ⟨hβ, MulAction.mem_orbit_self _⟩)
  have hnd : (β :: es.map (·.1)).Nodup := by
    refine List.nodup_cons.2 ⟨fun hin => ?_, h2⟩
    have := (h1 β hin).2
    rw [(hasBit_one β β).2 rfl] at this
    exact absurd this (by decide)
  have hsub : ∀ p ∈ β :: es.map (·.1), ∃ hp : p < n,
      (⟨p, hp⟩ : Fin n) ∈ MulAction.orbit H (⟨β, hβ⟩ : Fin n) := by
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hβ, MulAction.mem_orbit_self _⟩
    · exact (h1 p hp).1
  classical
  let F : Finset (Fin n) := Finset.univ.filter fun x => (x : Nat) ∈ β :: es.map (·.1)
  have hF : F.card = es.length + 1 := by
    have : F.card = (β :: es.map (·.1)).toFinset.card := by
      refine Finset.card_bij (fun x _ => (x : Nat)) ?_ ?_ ?_
      · intro x hx
        simpa [F] using hx
      · intro x _ y _ hxy
        exact Fin.ext hxy
      · intro y hy
        obtain ⟨hyn, -⟩ := hsub y (List.mem_toFinset.1 hy)
        exact ⟨⟨y, hyn⟩, by simpa [F] using List.mem_toFinset.1 hy, rfl⟩
    rw [this, List.toFinset_card_of_nodup hnd]
    simp
  rw [← hF, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro x hx
  have hx' : (x : Nat) ∈ β :: es.map (·.1) := by simpa [F] using hx
  obtain ⟨_, hxo⟩ := hsub _ hx'
  exact hxo

end Orbits

theorem chainL_go (h0 : 0 < n) :
    ∀ (levs : List (Nat × List (List Nat) × List (Nat × Nat × Nat))) (prev : List Nat),
      chainL n L levs prev = true → ∀ l < levs.length,
        (∀ w ∈ (levs.getD l (0, [], [])).2.1, ∀ b ∈ prev ++ (levs.take l).map (·.1),
          wv L w b = b) ∧ (levs.getD l (0, [], [])).1 < n ∧
        orbL n L (levs.getD l (0, [], [])).2.1 (levs.getD l (0, [], [])).2.2
          (Nat.shiftLeft 1 (levs.getD l (0, [], [])).1) = true
  | [], _, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | v :: levs, prev, h, l, hl => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (chainL n L levs (v.1 :: prev))
          (orbL n L v.2.1 v.2.2 (Nat.shiftLeft (nat_lit 1) v.1))) (Nat.blt v.1 n))
        (fixG L v.2.1 prev) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
    rcases l with _ | l
    · refine ⟨fun w hw b hb => ?_, Nat.blt_eq.mp h3, h5⟩
      simp only [List.take_zero, List.map_nil, List.append_nil] at hb
      exact fixG_spec h1 w hw b hb
    · have ih := chainL_go h0 levs (v.1 :: prev) h6 l (by simpa using hl)
      simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons] at ih ⊢
      refine ⟨fun w hw b hb => ih.1 w hw b ?_, ih.2⟩
      simp only [List.mem_append, List.mem_cons] at hb ⊢
      tauto

theorem prod_map_eq_range {α : Type} (f : α → Nat) (d : α) :
    ∀ l : List α, (l.map f).prod = ∏ i ∈ Finset.range l.length, f (l.getD i d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, List.length_cons, Finset.prod_range_succ',
      prod_map_eq_range f d l]
    simp [mul_comm]

theorem chainL_card (hL : ∀ k, RepF n (L k) (g k)) (h0 : 0 < n) {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : ∀ k, g k ∈ G) {levs : List (Nat × List (List Nat) × List (Nat × Nat × Nat))}
    (h : chainL n L levs [] = true) :
    (levs.map fun v => v.2.2.length + 1).prod ≤ Nat.card G := by
  have hc := chainL_go h0 levs [] h
  let B : Nat → Fin n := fun l => if hl : (levs.getD l (0, [], [])).1 < n then
    ⟨(levs.getD l (0, [], [])).1, hl⟩ else ⟨0, h0⟩
  have hB : ∀ l < levs.length, (B l : Nat) = (levs.getD l (0, [], [])).1 := by
    intro l hl
    simp only [B, dif_pos (hc l hl).2.1]
  rw [PCC.card_chain G B levs.length]
  have hmem : ∀ l < levs.length, ∀ j,
      wordVal g (((levs.getD l (0, [], [])).2.1).getD j []) ∈ PCC.Gs G B l := by
    intro l hl j
    rw [PCC.mem_Gs]
    refine ⟨wordVal_mem hG _, fun k hk => ?_⟩
    by_cases hj : j < ((levs.getD l (0, [], [])).2.1).length
    · have hjm : ((levs.getD l (0, [], [])).2.1).getD j [] ∈ (levs.getD l (0, [], [])).2.1 := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hw := (hc l hl).1 _ hjm (B k) ?_
      · exact Fin.ext ((wv_rep hL _ (B k) (B k).2).symm.trans hw)
      · rw [hB k (by omega), List.nil_append, List.mem_map]
        refine ⟨levs.getD k (0, [], []), ?_, rfl⟩
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp [List.getElem_take]⟩
    · rw [List.getD_eq_default _ _ (by omega), wordVal_nil]
      rfl
  have hle : ∀ l < levs.length, (levs.getD l (0, [], [])).2.2.length + 1 ≤
      (MulAction.orbit (PCC.Gs G B l) (B l)).ncard := by
    intro l hl
    have hBl : B l = ⟨(levs.getD l (0, [], [])).1, (hc l hl).2.1⟩ := Fin.ext (hB l hl)
    rw [hBl]
    exact orbL_card hL (hmem l hl) (hc l hl).2.1 (hc l hl).2.2
  have hpos : 0 < Nat.card (PCC.Gs G B levs.length) := Nat.card_pos
  calc (levs.map fun v => v.2.2.length + 1).prod
      = ∏ l ∈ Finset.range levs.length, ((levs.getD l (0, [], [])).2.2.length + 1) :=
        prod_map_eq_range _ _ levs
    _ ≤ ∏ l ∈ Finset.range levs.length, (MulAction.orbit (PCC.Gs G B l) (B l)).ncard :=
        Finset.prod_le_prod' fun l hl => hle l (Finset.mem_range.1 hl)
    _ ≤ _ := Nat.le_mul_of_pos_right _ hpos

section Order

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}

theorem evenOrd_spec (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hf : RepF n f z) (hz : z ∈ H) {m : Nat}
    (h : evenOrd bs f m = true) : 2 ∣ orderOf z := by
  unfold evenOrd at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  have hm2 : m % 2 = 0 := Nat.eq_of_beq_eq_true h1
  have hzm : z ^ m = 1 := (fixL_iff hH hbs (hf.powF m) (H.pow_mem hz m)).1 h5
  have hzm2 : z ^ (m / 2) ≠ 1 := by
    intro he
    exact neL_spec h6 ((eqOnL_iff _ _ _).1
      ((fixL_iff hH hbs (hf.powF (m / 2)) (H.pow_mem hz _)).2 he))
  by_contra hodd
  apply hzm2
  have hd : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
  have hco : Nat.Coprime (orderOf z) 2 :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd))
  have : orderOf z ∣ m / 2 := by
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hm2
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hc] at hd
    exact hco.dvd_of_dvd_mul_left hd
  exact orderOf_dvd_iff_pow_eq_one.1 this

theorem ord6L_spec (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hf : RepF n f z) (hz : z ∈ H) (h : ord6L bs f = true) :
    orderOf z = 6 := by
  unfold ord6L at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  have hz6 : z ^ 6 = 1 := (fixL_iff hH hbs (hf.powF 6) (H.pow_mem hz 6)).1 h1
  have hne : ∀ e, neL bs (powF f e) (fun x => x) = true → z ^ e ≠ 1 := fun e he he1 =>
    neL_spec he ((eqOnL_iff _ _ _).1 ((fixL_iff hH hbs (hf.powF e) (H.pow_mem hz e)).2 he1))
  have hd : orderOf z ∣ 6 := orderOf_dvd_of_pow_eq_one hz6
  have h3' : ¬ orderOf z ∣ 3 := fun h => hne 3 h3 (orderOf_dvd_iff_pow_eq_one.1 h)
  have h2' : ¬ orderOf z ∣ 2 := fun h => hne 2 h4 (orderOf_dvd_iff_pow_eq_one.1 h)
  have hle : orderOf z ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  interval_cases hz' : orderOf z <;> simp_all

end Order

theorem sortK_inj {N : Nat} {K S SI : Nat → Nat} (h : sortK N K S SI = true) :
    ∀ i < N, ∀ j < N, K i = K j → i = j := by
  unfold sortK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hS : ∀ i < N, SI i < N ∧ S i < N ∧ S (SI i) = i := by
    intro i hi
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h1 i hi)
    obtain ⟨c, d⟩ := (bAnd_iff _ _).1 b
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp c, Nat.eq_of_beq_eq_true d⟩
  have hmono : ∀ a b, a < b → b < N → K (S a) < K (S b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hstep : K (S b) < K (S (b + 1)) :=
        Nat.blt_eq.mp (allN_spec h2 b (by change b < N - 1; omega))
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
      · exact lt_trans (ih hab (by omega)) hstep
      · exact hstep
  intro i hi j hj hK
  obtain ⟨hi1, -, hi3⟩ := hS i hi
  obtain ⟨hj1, -, hj3⟩ := hS j hj
  rw [← hi3, ← hj3] at hK ⊢
  rcases lt_trichotomy (SI i) (SI j) with hlt | heq | hgt
  · exact absurd hK (ne_of_lt (hmono _ _ hlt hj1))
  · rw [heq]
  · exact absurd hK.symm (ne_of_lt (hmono _ _ hgt hi1))

end CFSG.KS.HS2272

end
