
module

public import Certificates.Data.Kernel.T75JM.N0K
public import CFSG.Certificates.Kernel.TabWordSound
public import CFSG.Certificates.Kernel.Misc.O62SoundBits
public import CFSG.CGT.T75JM.N0ModelBase
public import CFSG.CGT.T75JM.L2FInputs
public import Certificates.Certificate14984

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Blueprint

abbrev LetterRd (L : Int → Nat) : Prop :=
  ∀ z, ∀ x < 22, ap (m22L z) x = fd 5 (L z) x ∧ fd 5 (L z) x < 22

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

theorem hid : ∀ x < 22, fd 5 idn x = x := fun _ hx => fd_pidn (by norm_num) (by norm_num) hx

theorem fd_wordK_lt {L : Int → Nat} (hL : LetterRd L) (u : List Int) {x : Nat} (hx : x < 22) :
    ap (wordT 22 m22L u) x = fd 5 (wordK 22 5 idn L u) x ∧ fd 5 (wordK 22 5 idn L u) x < 22 :=
  (wordT_fd (by norm_num) hid hL u).2 x hx

theorem n0RelCheck_of {L : Int → Nat} (hL : LetterRd L) (h : relOk L = true) :
    n0RelCheck = true := by
  unfold relOk at h
  unfold n0RelCheck
  exact List.all_eq_true.2 fun r hr =>
    wordT_beq_idT (by norm_num) hid hL (List.all_eq_true.1 h r hr)

noncomputable def phiK (h1 : n0InvCheck = true) (h2 : n0RelCheck = true) :
    N0 →* NativeSporadic.M22 :=
  PresentedGroup.toGroup (lift_n0Gen_eq_one h1 h2)

variable {h1 : n0InvCheck = true} {h2 : n0RelCheck = true}

theorem phiK_n0 (w : List (Fin 6 × Bool)) :
    phiK h1 h2 (n0 w) = FreeGroup.lift n0Gen (FreeGroup.mk w) := by
  have hcomp : (phiK h1 h2).comp (PresentedGroup.mk _) = FreeGroup.lift n0Gen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem rep_phiK (w : List (Fin 6 × Bool)) : Rep 22 (n0Tab w) (phiK h1 h2 (n0 w)) := by
  rw [phiK_n0, ← evalWord7_m22Gen]
  exact rep_n0Tab h1 w

theorem idx_phiK {L : Int → Nat} (hL : LetterRd L) (w : List (Fin 6 × Bool)) {x : Nat}
    (hx : x < 22) : idx 22 (phiK h1 h2 (n0 w)) x = fd 5 (wordK 22 5 idn L (lw w)) x :=
  ((rep_phiK w) x hx).symm.trans (fd_wordK_lt hL _ hx).1

theorem lw_a6W (a : Nat) : lw (a6W a) = (a6Words.getD a []).map a6Z := by
  unfold lw a6W liftWord
  simp only [List.map_map]
  congr 1
  funext i
  unfold a6Z
  by_cases h : i = 0 <;> simp [h, m22LetterZ]

theorem lw_tw : ∀ k < 16, lw (tw k) = twZ k := by decide +kernel

theorem idx_ak {L : Int → Nat} (hL : LetterRd L) (a : Nat) {x : Nat} (hx : x < 22) :
    idx 22 (phiK h1 h2 (n0 (a6W a))) x = fd 5 (ak L a) x := by
  rw [idx_phiK hL _ hx, lw_a6W]; rfl

theorem idx_tk {L : Int → Nat} (hL : LetterRd L) {k : Nat} (hk : k < 16) {x : Nat}
    (hx : x < 22) : idx 22 (phiK h1 h2 (n0 (tw k))) x = fd 5 (tk L k) x := by
  rw [idx_phiK hL _ hx, lw_tw k hk]; rfl

theorem idx_phiK_elem {L : Int → Nat} (hL : LetterRd L) (a : Nat) {k : Nat} (hk : k < 16)
    {x : Nat} (hx : x < 22) :
    idx 22 (phiK h1 h2 (n0 (a6W a ++ tw k))) x = fd 5 (pcomp 22 5 (mask 5) (ak L a) (tk L k)) x := by
  rw [n0_append, map_mul, idx_mul, fd_pcomp (by norm_num) _ _ _ hx, ← idx_tk hL hk hx,
    idx_ak hL a (idx_lt _ hx)]

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

theorem ptW_eq (L : Int → Nat) (u : List Int) {x : Nat} (hx : x < 22) :
    ptW L u x = fd 5 (wordK 22 5 idn L u) x := by
  rw [ptW_foldr, fd_wordK (by norm_num) hid L u hx]

theorem eq_of_nodupN {f : Nat → Nat} {n : Nat} (h : nodupN ((List.range n).map f) = true)
    {a b : Nat} (ha : a < n) (hb : b < n) (e : f a = f b) : a = b := by
  rw [O62.nodupN_eq, decide_eq_true_iff] at h
  exact List.inj_on_of_nodup_map h (List.mem_range.2 ha) (List.mem_range.2 hb) e

theorem a6Words_getD {a : Nat} (ha : a < 360) :
    a6Words.getD a [] = a6Words[a]'(by rw [a6Words_length]; exact ha) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem eq_of_nodupA {f : List Nat → Nat} (h : nodupN (a6Words.map f) = true) {a b : Nat}
    (ha : a < 360) (hb : b < 360) (e : f (a6Words.getD a []) = f (a6Words.getD b [])) :
    a = b := by
  rw [O62.nodupN_eq, decide_eq_true_iff] at h
  rw [a6Words_getD ha, a6Words_getD hb] at e
  exact (h.getElem_inj_iff (i := a) (j := b) (hi := by simp [a6Words_length, ha])
    (hj := by simp [a6Words_length, hb])).1 (by simpa using e)

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

theorem n0kOk_parts {L : Int → Nat} (h : n0kOk L = true) :
    relOk L = true ∧ (∀ k < 16, ∀ p ∈ hexad, fd 5 (tk L k) p = p) ∧ a6KeyOk L = true ∧
      tKeyOk L = true := by
  unfold n0kOk at h
  rw [withL_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hr, hf⟩, ha⟩, ht⟩ := h
  refine ⟨hr, fun k hk p hp => ?_, ha, ht⟩
  unfold fixOk at hf
  have := List.all_eq_true.1 hf k (List.mem_range.2 hk)
  rw [sB_eq] at this
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 this p hp)

theorem eq_of_idx {g h : NativeSporadic.M22} (e : ∀ x < 22, idx 22 g x = idx 22 h x) : g = h := by
  refine Subtype.ext (Equiv.ext fun i => Fin.ext ?_)
  have := e i.val i.isLt
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at this

theorem n0K_injective {L : Int → Nat} (hL : LetterRd L) (h1 : n0InvCheck = true)
    (hok : n0kOk L = true) :
    Function.Injective fun p : Fin 360 × Fin 16 => n0 (a6W p.1 ++ tw p.2) := by
  obtain ⟨hr, hfix, ha, ht⟩ := n0kOk_parts hok
  have h2 := n0RelCheck_of hL hr
  rintro ⟨a, k⟩ ⟨b, l⟩ hab
  have e := congrArg (phiK h1 h2) hab
  simp only [n0_append, map_mul] at e
  have hH : ∀ p ∈ hexad, fd 5 (ak L a) p = fd 5 (ak L b) p := by
    intro p hp
    have hp22 : p < 22 := by simp [hexad] at hp; omega
    have := congrArg (fun g => idx 22 g p) e
    simp only [idx_mul] at this
    rw [idx_tk hL k.isLt hp22, hfix k k.isLt p hp, idx_tk hL l.isLt hp22, hfix l l.isLt p hp,
      idx_ak hL a hp22, idx_ak hL b hp22] at this
    exact this
  have hab' : a.val = b.val := by
    refine eq_of_nodupA (f := fun u => keyP hexad (ptW L (u.map a6Z))) ha a.isLt b.isLt
      (keyP_congr hexad fun p hp => ?_)
    have hp22 : p < 22 := by simp [hexad] at hp; omega
    rw [ptW_eq L _ hp22, ptW_eq L _ hp22]
    exact hH p hp
  have hA : a = b := Fin.ext hab'
  subst hA
  have e' := mul_left_cancel e
  have hT : ∀ p ∈ List.range 22, fd 5 (tk L k) p = fd 5 (tk L l) p := by
    intro p hp
    have hp22 := List.mem_range.1 hp
    rw [← idx_tk (h1 := h1) (h2 := h2) hL k.isLt hp22, ← idx_tk (h1 := h1) (h2 := h2) hL l.isLt hp22,
      e']
  have hk : keyL (List.range 22) (tk L k) = keyL (List.range 22) (tk L l) := keyP_congr _ hT
  exact Prod.ext rfl (Fin.ext (eq_of_nodupN ht k.isLt l.isLt hk))

theorem n0K_surj {L : Int → Nat} (hL : LetterRd L)
    (h1 : n0InvCheck = true) (hok : n0kOk L = true) (g : N0) :
    ∃ a < 360, ∃ k < 16, g = n0 (a6W a ++ tw k) := by
  obtain ⟨hfin, hle⟩ := Certificates.certificate14984.2.2.1
  have hbij := (n0K_injective hL h1 hok).bijective_of_nat_card_le (by
    simp only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hle.trans (by norm_num))
  obtain ⟨⟨a, k⟩, hak⟩ := hbij.2 g
  exact ⟨a, a.isLt, k, k.isLt, hak.symm⟩

theorem n0K_forall {L : Int → Nat} (hL : LetterRd L)
    (h1 : n0InvCheck = true) (hok : n0kOk L = true) (P : N0 → Prop)
    (h : ∀ a < 360, ∀ k < 16, P (n0 (a6W a ++ tw k))) (g : N0) : P g := by
  obtain ⟨a, ha, k, hk, rfl⟩ := n0K_surj hL h1 hok g
  exact h a ha k hk

end CFSG.KC.N0K

end
