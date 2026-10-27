
module

public import Certificates.Data.Kernel.T75M23.N7K
public import CFSG.Certificates.Kernel.TabWordSound
public import CFSG.Certificates.Kernel.Misc.O62SoundBits
public import CFSG.CGT.T75M23.N7ModelBase
public import CFSG.CGT.T75M23.L2FInputs7

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23 CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

abbrev LetterRd (L : Int → Nat) : Prop :=
  ∀ z, ∀ x < 23, ap (n7L z) x = fd 5 (L z) x ∧ fd 5 (L z) x < 23

theorem sB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem iteL (f : Int → Nat) (c z : Int) (r : Nat) :
    (if z = c then f c else r) = if z = c then f z else r := by
  by_cases h : z = c
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

theorem withL_eq (L : Int → Nat) (k : (Int → Nat) → Bool) : withL L k = k L := by
  unfold withL
  simp only [sB_eq]
  refine congrArg k (funext fun z => ?_)
  simp only [iteL L, ite_self]

theorem hid : ∀ x < 23, fd 5 idn x = x := fun _ hx => fd_pidn (by norm_num) (by norm_num) hx

theorem fd_wordK_lt {L : Int → Nat} (hL : LetterRd L) (u : List Int) {x : Nat} (hx : x < 23) :
    ap (wordT 23 n7L u) x = fd 5 (wordK 23 5 idn L u) x ∧ fd 5 (wordK 23 5 idn L u) x < 23 :=
  (wordT_fd (by norm_num) hid hL u).2 x hx

noncomputable abbrev img (w : List (Fin 6 × Bool)) : NativeSporadic.M23 :=
  FreeGroup.lift n7Gen (FreeGroup.mk w)

theorem img_append (w w' : List (Fin 6 × Bool)) : img (w ++ w') = img w * img w' := by
  rw [img, img, img, ← FreeGroup.mul_mk, map_mul]

theorem rep_img (h1 : n7InvCheck = true) (w : List (Fin 6 × Bool)) : Rep 23 (n7Tab w) (img w) := by
  rw [img, ← evalWord7_m23Gen]
  exact rep_n7Tab h1 w

theorem idx_img (h1 : n7InvCheck = true) {L : Int → Nat} (hL : LetterRd L)
    (w : List (Fin 6 × Bool)) {x : Nat} (hx : x < 23) :
    idx 23 (img w) x = fd 5 (wordK 23 5 idn L (lw w)) x :=
  ((rep_img h1 w) x hx).symm.trans (fd_wordK_lt hL _ hx).1

theorem lw_a7W (a : Nat) : lw (a7W a) = (a7Words.getD a []).map a7Z := by
  unfold lw a7W liftWord7
  simp only [List.map_map]
  congr 1
  funext i
  unfold a7Z
  by_cases h : i = 0 <;> simp [h, m23LetterZ]

theorem lw_tw : ∀ k < 16, lw (tw7 k) = twZ k := by decide +kernel

theorem idx_ak (h1 : n7InvCheck = true) {L : Int → Nat} (hL : LetterRd L) (a : Nat) {x : Nat}
    (hx : x < 23) : idx 23 (img (a7W a)) x = fd 5 (ak L a) x := by
  rw [idx_img h1 hL _ hx, lw_a7W]; rfl

theorem idx_tk (h1 : n7InvCheck = true) {L : Int → Nat} (hL : LetterRd L) {k : Nat} (hk : k < 16)
    {x : Nat} (hx : x < 23) : idx 23 (img (tw7 k)) x = fd 5 (tk L k) x := by
  rw [idx_img h1 hL _ hx, lw_tw k hk]; rfl

theorem idx_elem (h1 : n7InvCheck = true) {L : Int → Nat} (hL : LetterRd L) (a : Nat) {k : Nat}
    (hk : k < 16) {x : Nat} (hx : x < 23) :
    idx 23 (img (a7W a ++ tw7 k)) x = fd 5 (pcomp 23 5 (mask 5) (ak L a) (tk L k)) x := by
  rw [img_append, idx_mul, fd_pcomp (by norm_num) _ _ _ hx, ← idx_tk h1 hL hk hx,
    idx_ak h1 hL a (idx_lt _ hx)]

theorem keyP_congr : ∀ (pts : List Nat) {g h : Nat → Nat}, (∀ p ∈ pts, g p = h p) →
    keyP pts g = keyP pts h
  | [], _, _, _ => rfl
  | q :: t, g, h, e => by
    have c : ∀ f : Nat → Nat, keyP (q :: t) f = f q + 32 * keyP t f := fun _ => rfl
    rw [c, c, e q List.mem_cons_self, keyP_congr t fun p hp => e p (List.mem_cons_of_mem _ hp)]

theorem ptW_foldr (L : Int → Nat) : ∀ (u : List Int) (x : Nat),
    ptW L u x = u.foldr (fun z y => fd 5 (L z) y) x
  | [], _ => rfl
  | z :: u, x => by
    have e : ptW L (z :: u) x = strictN (ptW L u x) fun y => fdN 5 (L z) y := rfl
    rw [e, strictN_eq', ptW_foldr L u x, List.foldr_cons]
    rfl

theorem ptW_eq (L : Int → Nat) (u : List Int) {x : Nat} (hx : x < 23) :
    ptW L u x = fd 5 (wordK 23 5 idn L u) x := by
  rw [ptW_foldr, fd_wordK (by norm_num) hid L u hx]

theorem eq_of_nodupN {f : Nat → Nat} {n : Nat} (h : nodupN ((List.range n).map f) = true)
    {a b : Nat} (ha : a < n) (hb : b < n) (e : f a = f b) : a = b := by
  rw [O62.nodupN_eq, decide_eq_true_iff] at h
  exact List.inj_on_of_nodup_map h (List.mem_range.2 ha) (List.mem_range.2 hb) e

theorem hep_lt : ∀ i < 7, hep.getD i 0 < 23 := by decide

theorem hep_mem : ∀ i < 7, hep.getD i 0 ∈ hep := by decide

theorem hep_inj : ∀ i < 7, ∀ j < 7, hep.getD i 0 = hep.getD j 0 → i = j := by decide

theorem a7x_getD : ∀ i : Fin 7, (a7x i).val = axL.getD i.val 0 := by decide +kernel

theorem a7y_getD : ∀ i : Fin 7, (a7y i).val = ayL.getD i.val 0 := by decide +kernel

theorem hepOk_spec {L : Int → Nat} (h : hepOk L = true) {i : Nat} (hi : i < 7) :
    fd 5 (L 1) (hep.getD i 0) = hep.getD (axL.getD i 0) 0 ∧
      fd 5 (L 2) (hep.getD i 0) = hep.getD (ayL.getD i 0) 0 := by
  unfold hepOk at h
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem ptW_hep {L : Int → Nat}
    (hx : ∀ i : Fin 7, fd 5 (L 1) (hep.getD i 0) = hep.getD (a7x i).val 0)
    (hy : ∀ i : Fin 7, fd 5 (L 2) (hep.getD i 0) = hep.getD (a7y i).val 0) :
    ∀ (u : List Nat) (i : Fin 7),
      ptW L (u.map a7Z) (hep.getD i 0) = hep.getD (evalG a7x a7y u i).val 0
  | [], _ => rfl
  | l :: u, i => by
    have e : ptW L ((l :: u).map a7Z) (hep.getD i 0) =
        fd 5 (L (a7Z l)) (ptW L (u.map a7Z) (hep.getD i 0)) := by
      rw [List.map_cons]
      exact strictN_eq' _ _
    rw [e, ptW_hep hx hy u i, evalG, Equiv.Perm.mul_apply]
    unfold a7Z
    by_cases hl : l = 0
    · rw [if_pos hl, if_pos hl]
      exact hx _
    · rw [if_neg hl, if_neg hl]
      exact hy _

theorem a7Words_getD {a : Nat} (ha : a < 2520) :
    a7Words.getD a [] = a7Words[a]'(by rw [a7Words_length]; exact ha) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem eq_of_evalG (hn : A7Nodup) {a b : Nat} (ha : a < 2520) (hb : b < 2520)
    (e : evalG a7x a7y (a7Words.getD a []) = evalG a7x a7y (a7Words.getD b [])) : a = b := by
  have h := hn.values
  rw [a7Words_getD ha, a7Words_getD hb] at e
  exact (h.getElem_inj_iff (i := a) (j := b) (hi := by simp [a7Words_length, ha])
    (hj := by simp [a7Words_length, hb])).1 (by simpa using e)

theorem allW_spec {g : Nat → List Nat → Bool} : ∀ {ws : List (List Nat)} {i : Nat},
    allW ws g i = true → ∀ j (hj : j < ws.length), g (i + j) ws[j] = true
  | [], _, _, j, hj => absurd hj (by simp)
  | u :: ws, i, h, j, hj => by
    have e : allW (u :: ws) g i = (g i u && allW ws g (Nat.succ i)) := rfl
    rw [e, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := allW_spec h.2 j (by simpa using hj)
      rw [show i + (j + 1) = Nat.succ i + j by omega]
      simpa using this

theorem n7kOk_parts {L : Int → Nat} (h : n7kOk L = true) :
    (∀ k < 16, ∀ p ∈ hep, fd 5 (tk L k) p = p) ∧ hepOk L = true ∧ tKeyOk L = true := by
  unfold n7kOk at h
  rw [withL_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hf, hh⟩, ht⟩ := h
  refine ⟨fun k hk p hp => ?_, hh, ht⟩
  unfold fixOk at hf
  have := List.all_eq_true.1 hf k (List.mem_range.2 hk)
  rw [sB_eq] at this
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 this p hp)

theorem img_injective {L : Int → Nat} (hL : LetterRd L) (h1 : n7InvCheck = true)
    (hA : A7Nodup) (hok : n7kOk L = true) :
    Function.Injective fun p : Fin 2520 × Fin 16 => img (a7W p.1 ++ tw7 p.2) := by
  obtain ⟨hfix, hh, ht⟩ := n7kOk_parts hok
  have hx : ∀ i : Fin 7, fd 5 (L 1) (hep.getD i 0) = hep.getD (a7x i).val 0 := fun i => by
    rw [a7x_getD]
    exact (hepOk_spec hh i.isLt).1
  have hy : ∀ i : Fin 7, fd 5 (L 2) (hep.getD i 0) = hep.getD (a7y i).val 0 := fun i => by
    rw [a7y_getD]
    exact (hepOk_spec hh i.isLt).2
  rintro ⟨a, k⟩ ⟨b, l⟩ hab
  have e : img (a7W a) * img (tw7 k) = img (a7W b) * img (tw7 l) := by
    rw [← img_append, ← img_append]
    exact hab
  have hH : ∀ i : Fin 7, hep.getD (evalG a7x a7y (a7Words.getD a.val []) i).val 0 =
      hep.getD (evalG a7x a7y (a7Words.getD b.val []) i).val 0 := by
    intro i
    have hp := hep_lt i i.isLt
    have hm := hep_mem i i.isLt
    have := congrArg (fun g => idx 23 g (hep.getD i 0)) e
    simp only [idx_mul] at this
    rw [idx_tk h1 hL k.isLt hp, hfix k k.isLt _ hm, idx_tk h1 hL l.isLt hp, hfix l l.isLt _ hm,
      idx_ak h1 hL a hp, idx_ak h1 hL b hp] at this
    rw [← ptW_hep hx hy, ← ptW_hep hx hy, ptW_eq L _ hp, ptW_eq L _ hp]
    exact this
  have hE : evalG a7x a7y (a7Words.getD a.val []) = evalG a7x a7y (a7Words.getD b.val []) :=
    Equiv.ext fun i => Fin.ext (hep_inj _ (Fin.isLt _) _ (Fin.isLt _) (hH i))
  have hA' : a = b := Fin.ext (eq_of_evalG hA a.isLt b.isLt hE)
  subst hA'
  have e' := mul_left_cancel e
  have hT : ∀ p ∈ List.range 23, fd 5 (tk L k) p = fd 5 (tk L l) p := by
    intro p hp
    have hp23 := List.mem_range.1 hp
    rw [← idx_tk h1 hL k.isLt hp23, ← idx_tk h1 hL l.isLt hp23, e']
  have hk : keyL (List.range 23) (tk L k) = keyL (List.range 23) (tk L l) := keyP_congr _ hT
  exact Prod.ext rfl (Fin.ext (eq_of_nodupN ht k.isLt l.isLt hk))

noncomputable def phiK (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) :
    N7 →* NativeSporadic.M23 :=
  PresentedGroup.toGroup (lift_n7Gen_eq_one h1 h2)

theorem phiK_n7 {h1 : n7InvCheck = true} {h2 : n7RelCheck = true} (w : List (Fin 6 × Bool)) :
    phiK h1 h2 (n7 w) = img w := by
  have hcomp : (phiK h1 h2).comp (PresentedGroup.mk _) = FreeGroup.lift n7Gen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem n7K_injective {L : Int → Nat} (hL : LetterRd L) (h1 : n7InvCheck = true)
    (h2 : n7RelCheck = true) (hA : A7Nodup) (hok : n7kOk L = true) :
    Function.Injective fun p : Fin 2520 × Fin 16 => n7 (a7W p.1 ++ tw7 p.2) := by
  intro p q e
  refine img_injective hL h1 hA hok ?_
  have := congrArg (phiK h1 h2) e
  rw [phiK_n7, phiK_n7] at this
  exact this

theorem n7K_surj {L : Int → Nat} (hL : LetterRd L)
    (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) (hok : n7kOk L = true) (g : N7) :
    ∃ a < 2520, ∃ k < 16, g = n7 (a7W a ++ tw7 k) := by
  obtain ⟨hfin, hle⟩ := Certificates.certificate271010.2.2
  have hbij := (n7K_injective hL h1 h2 Certificates.certificate271010.2.1
    hok).bijective_of_nat_card_le (by
    simp only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hle.trans (by norm_num))
  obtain ⟨⟨a, k⟩, hak⟩ := hbij.2 g
  exact ⟨a, a.isLt, k, k.isLt, hak.symm⟩

theorem n7K_forall {L : Int → Nat} (hL : LetterRd L)
    (h1 : n7InvCheck = true) (h2 : n7RelCheck = true) (hok : n7kOk L = true) (P : N7 → Prop)
    (h : ∀ a < 2520, ∀ k < 16, P (n7 (a7W a ++ tw7 k))) (g : N7) : P g := by
  obtain ⟨a, ha, k, hk, rfl⟩ := n7K_surj hL h1 h2 hok g
  exact h a ha k hk

end CFSG.KC.N7K

end
