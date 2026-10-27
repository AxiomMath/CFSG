module

public import Certificates.Data.Kernel.EvenBN.Thm49EF6
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PrimSound

public section

namespace CFSG.KD.T49

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim
open CFSG.Sporadic.Schreier.Tits

abbrev PR (P : Nat) (g : Equiv.Perm (Fin 1755)) : Prop := PRep 1755 11 P g

theorem ap_eq {P : Nat} {g : Equiv.Perm (Fin 1755)} (h : PR P g) (x : Fin 1755) :
    ap P x = g x := h x

theorem ap_eq' {P : Nat} {g : Equiv.Perm (Fin 1755)} (h : PR P g) {x : Nat} (hx : x < 1755) :
    ap P x = g ⟨x, hx⟩ := h ⟨x, hx⟩

theorem ap_lt {P : Nat} {g : Equiv.Perm (Fin 1755)} (h : PR P g) {x : Nat} (hx : x < 1755) :
    ap P x < 1755 := by
  rw [ap_eq' h hx]
  exact (g _).2

theorem prep_pmul {P Q : Nat} {g h : Equiv.Perm (Fin 1755)} (hP : PR P g) (hQ : PR Q h) :
    PR (pmul P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

theorem prep_idP : PR idP 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_inv {P Q : Nat} {g : Equiv.Perm (Fin 1755)} (hP : PR P g) (h : isPerm P Q = true) :
    PR Q g⁻¹ := by
  obtain ⟨-, -, h3⟩ := permOK_facts (n := 1755) (w := 11) (P := P) (Q := Q) h
  intro x
  have hy := (h3 (g⁻¹ x) (g⁻¹ x).2).2
  have hgx : g (g⁻¹ x) = x := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  have e : pg 11 (mask 11) P (g⁻¹ x) = x := by
    have := hP (g⁻¹ x)
    rw [hgx] at this
    exact this
  rw [e] at hy
  exact hy

theorem eq_of_prep {P Q : Nat} {g h : Equiv.Perm (Fin 1755)} (hP : PR P g) (hQ : PR Q h)
    (e : P = Q) : g = h := by
  subst e
  exact Equiv.ext fun x => Fin.ext ((hP x).symm.trans (hQ x))

theorem prep_wd {k : Nat} {S SI : Nat → Nat} {gs : Nat → Equiv.Perm (Fin 1755)}
    (hS : ∀ j < k, PR (S j) (gs j)) (hSI : ∀ j < k, PR (SI j) (gs j)⁻¹) {w : List Int}
    (hl : lettersK k w = true) : PR (wd S SI w) (wordIn k gs w) :=
  (prep_wordK (n := 1755) (w := 11) (by norm_num) (by norm_num) hS hSI w hl).1

theorem mul_eq_of {P Q R T : Nat} {p q r t : Equiv.Perm (Fin 1755)} (hP : PR P p) (hQ : PR Q q)
    (hR : PR R r) (hT : PR T t) (e : pmul P Q = pmul R T) : p * q = r * t :=
  eq_of_prep (prep_pmul hP hQ) (prep_pmul hR hT) e

theorem bitK_iff (S x : Nat) : bitK S x = true ↔ S.testBit x = true := by
  unfold bitK
  rw [Nat.beq_eq]
  change S >>> x &&& 1 = 1 ↔ _
  rw [Nat.testBit, Nat.one_and_eq_mod_two, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (S >>> x) with h | h <;> simp [h]

theorem bitK_setK (S x y : Nat) : bitK (setK S x) y = true ↔ bitK S y = true ∨ y = x := by
  rw [bitK_iff, bitK_iff]
  unfold setK
  change (S ||| 1 <<< x).testBit y = true ↔ _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr h.symm

theorem bitK_zero (y : Nat) : bitK 0 y = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [bitK_iff] at h
  simp at h

theorem bitK_root (r y : Nat) : bitK (setK 0 r) y = true ↔ y = r := by
  rw [bitK_setK, bitK_zero]
  simp

theorem orbOK_cons (G0 G1 r : Nat) (rs : List Nat) (S : Nat) :
    orbOK G0 G1 (r :: rs) S = true ↔ recG r < 2 ∧ bitK S (recP r) = true ∧
      bitK S (recY r) = false ∧ ap (pick2 G0 G1 (recG r)) (recP r) = recY r ∧
      orbOK G0 G1 rs (setK S (recY r)) = true := by
  have e : orbOK G0 G1 (r :: rs) S = (Nat.blt (recG r) 2 && (bitK S (recP r) &&
      (!bitK S (recY r) && (Nat.beq (ap (pick2 G0 G1 (recG r)) (recP r)) (recY r) &&
        orbOK G0 G1 rs (setK S (recY r)))))) := by
    dsimp only [orbOK]
    rw [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bIf_eq]
    cases bitK S (recY r) <;> rfl
  rw [e]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true']

theorem orbMask_cons (r : Nat) (rs : List Nat) (S : Nat) :
    orbMask (r :: rs) S = orbMask rs (setK S (recY r)) := rfl

theorem pick2_prep {G0 G1 : Nat} {u0 u1 : Equiv.Perm (Fin 1755)} (h0 : PR G0 u0) (h1 : PR G1 u1)
    {g : Nat} (hg : g < 2) : PR (pick2 G0 G1 g) (if g = 0 then u0 else u1) := by
  unfold pick2
  rw [CFSG.KS.Raw.Orb.nIf_eq]
  rcases g with _ | _ | g
  · simpa using h0
  · simpa using h1
  · omega

theorem orb_reach {G0 G1 : Nat} {u0 u1 : Equiv.Perm (Fin 1755)} (h0 : PR G0 u0) (h1 : PR G1 u1)
    {K : Subgroup (Equiv.Perm (Fin 1755))} (hu0 : u0 ∈ K) (hu1 : u1 ∈ K) (r : Fin 1755) :
    ∀ (rs : List Nat) (S : Nat), orbOK G0 G1 rs S = true →
      (∀ y, bitK S y = true → ∃ c ∈ K, ((c r : Fin 1755) : Nat) = y) →
      ∀ y, bitK (orbMask rs S) y = true → ∃ c ∈ K, ((c r : Fin 1755) : Nat) = y
  | [], S, _, hS, y, hy => hS y hy
  | x :: rs, S, h, hS, y, hy => by
    rw [orbOK_cons] at h
    obtain ⟨hg, hp, -, he, hrest⟩ := h
    rw [orbMask_cons] at hy
    refine orb_reach h0 h1 hu0 hu1 r rs _ hrest (fun t ht => ?_) y hy
    rcases (bitK_setK _ _ _).1 ht with ht | rfl
    · exact hS t ht
    · obtain ⟨c, hc, hcp⟩ := hS _ hp
      have hpl : recP x < 1755 := by
        rw [← hcp]
        exact (c r).2
      have hcr : c r = ⟨recP x, hpl⟩ := Fin.ext hcp
      refine ⟨(if recG x = 0 then u0 else u1) * c, K.mul_mem ?_ hc, ?_⟩
      · split_ifs
        · exact hu0
        · exact hu1
      · rw [← he, ap_eq' (pick2_prep h0 h1 hg) hpl, Equiv.Perm.mul_apply, hcr]

theorem orbMask_mono : ∀ (rs : List Nat) (S y : Nat), bitK S y = true →
    bitK (orbMask rs S) y = true
  | [], _, _, h => h
  | _ :: rs, _, y, h => orbMask_mono rs _ y ((bitK_setK _ _ _).2 (Or.inl h))

theorem orbMask_mem : ∀ (rs : List Nat) (S y : Nat), y ∈ rs.map recY →
    bitK (orbMask rs S) y = true
  | [], _, _, h => by simp at h
  | r :: rs, S, y, h => by
    rw [List.map_cons, List.mem_cons] at h
    rw [orbMask_cons]
    rcases h with rfl | h
    · exact orbMask_mono rs _ _ ((bitK_setK _ _ _).2 (Or.inr rfl))
    · exact orbMask_mem rs _ y h

theorem mem_fixed {P : Nat} {g : Equiv.Perm (Fin 1755)} {L : List Nat} (hP : PR P g)
    (h : fixedK 1755 11 (mask 11) P L = true) (x : Fin 1755) : (x : Nat) ∈ L ↔ g x = x := by
  rw [← fixedK_sound h, CFSG.Certificates.Native.fixedList, List.mem_filter, List.mem_range,
    unpack_get x.2, beq_iff_eq, hP x]
  constructor
  · rintro ⟨-, h⟩
    exact Fin.ext h
  · intro h
    exact ⟨x.2, congrArg Fin.val h⟩

theorem length_fixed {P : Nat} {g : Equiv.Perm (Fin 1755)} {L : List Nat} (hP : PR P g)
    (h : fixedK 1755 11 (mask 11) P L = true) :
    L.length = (Finset.univ.filter (fun x : Fin 1755 => g x = x)).card := by
  have hnd : L.Nodup := by
    rw [← fixedK_sound h, CFSG.Certificates.Native.fixedList]
    exact List.nodup_range.filter _
  have hlt : ∀ y ∈ L, y < 1755 := by
    intro y hy
    rw [← fixedK_sound h, CFSG.Certificates.Native.fixedList, List.mem_filter,
      List.mem_range] at hy
    exact hy.1
  rw [← List.toFinset_card_of_nodup hnd]
  symm
  refine Finset.card_bij (fun x _ => (x : Nat)) (fun x hx => ?_)
    (fun a _ b _ hab => Fin.ext hab) (fun y hy => ?_)
  · rw [Finset.mem_filter] at hx
    exact List.mem_toFinset.2 ((mem_fixed hP h x).2 hx.2)
  · have hy' := List.mem_toFinset.1 hy
    refine ⟨⟨y, hlt y hy'⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (mem_fixed hP h ⟨y, hlt y hy'⟩).1 hy'⟩

theorem orb_nodup {G0 G1 : Nat} : ∀ (rs : List Nat) (S : Nat) (pre : List Nat),
    orbOK G0 G1 rs S = true → pre.Nodup → (∀ y ∈ pre, bitK S y = true) →
      (pre ++ rs.map recY).Nodup
  | [], _, pre, _, hn, _ => by simpa using hn
  | x :: rs, S, pre, h, hn, hS => by
    rw [orbOK_cons] at h
    obtain ⟨-, -, hy, -, hrest⟩ := h
    have e : pre ++ (x :: rs).map recY = (pre ++ [recY x]) ++ rs.map recY := by simp
    rw [e]
    have hnot : recY x ∉ pre := fun hm => by
      rw [hS _ hm] at hy
      exact Bool.noConfusion hy
    refine orb_nodup rs _ _ hrest ?_ (fun t ht => ?_)
    · rw [List.nodup_append_comm, List.singleton_append]
      exact List.nodup_cons.2 ⟨hnot, hn⟩
    · rw [List.mem_append, List.mem_singleton] at ht
      rw [bitK_setK]
      rcases ht with ht | rfl
      · exact Or.inl (hS t ht)
      · exact Or.inr rfl

theorem lenK_eq {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l]
    rfl

theorem allK_iff {α : Type} (f : α → Bool) : ∀ l : List α, allK f l = true ↔ ∀ x ∈ l, f x = true
  | [] => by simp [allK]
  | x :: l => by
    change Bool.rec (motive := fun _ => Bool) false (allK f l) (f x) = true ↔ _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, allK_iff f l]
    simp

structure CoreSpec (W : F6W) (zp y0 u1 u2 e e1 e1i f : Nat) : Prop where
  zpComm : pmul zp W.Z = pmul W.Z zp
  q0lt : W.q0 < 1755
  q0ne : ap zp W.q0 ≠ ap W.Z W.q0
  eZ : pmul e W.Z = pmul zp e
  e0 : ap e 0 = W.yp
  y0z : pmul y0 W.Z = pmul zp y0
  y0zp : pmul y0 zp = pmul W.Z y0
  fixZ : fixedK 1755 11 (mask 11) W.Z W.fz = true
  fixZZ : fixedK 1755 11 (mask 11) (pmul W.Z zp) W.fzz = true
  lenNe : W.fz.length ≠ W.fzz.length
  u10 : ap u1 0 = 0
  u20 : ap u2 0 = 0
  u1Z : pmul u1 W.Z = pmul W.Z u1
  u2Z : pmul u2 W.Z = pmul W.Z u2
  e10 : ap e1 0 = W.r2
  e1inv : pmul e1 e1i = idP
  fRel : pmul (pmul (pmul W.Z (pmul e1 W.Z)) e1i) f = pmul f W.Z
  o1ok : orbOK u1 u2 W.o1 (setK 0 W.yp) = true
  o2ok : orbOK u1 u2 W.o2 (setK 0 W.r2) = true
  o1len : W.o1.length = 79
  cover : ∀ y ∈ W.fz, y = 0 ∨ bitK (orbMask W.o1 (setK 0 W.yp)) y = true ∨
    bitK (orbMask W.o2 (setK 0 W.r2)) y = true

theorem coreSpec_of {W : F6W} {zp y0 u1 u2 e e1 e1i f : Nat}
    (h : f6Core W zp y0 u1 u2 e e1 e1i f = true) : CoreSpec W zp y0 u1 u2 e e1 e1i f := by
  unfold f6Core commP at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20⟩ := h
  have hne : ∀ {a b : Nat}, Bool.rec (motive := fun _ => Bool) true false (Nat.beq a b) = true →
      a ≠ b := by
    intro a b hab e
    subst e
    rw [Nat.beq_refl] at hab
    exact Bool.noConfusion hab
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.blt_eq.mp h0, hne h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6, h7, h8, ?_, Nat.eq_of_beq_eq_true h10,
    Nat.eq_of_beq_eq_true h11, Nat.eq_of_beq_eq_true h12, Nat.eq_of_beq_eq_true h13,
    Nat.eq_of_beq_eq_true h14, Nat.eq_of_beq_eq_true h15, Nat.eq_of_beq_eq_true h16, h17, h18,
    by rw [← lenK_eq]; exact Nat.eq_of_beq_eq_true h19, fun y hy => ?_⟩
  · rw [← lenK_eq, ← lenK_eq]
    exact hne h9
  · have := (allK_iff _ _).1 h20 y hy
    simp only [CFSG.KS.Raw.Orb.bIf_eq, Nat.beq_eq] at this
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    · right
      by_cases hb : bitK (orbMask W.o1 (setK 0 W.yp)) y = true
      · exact Or.inl hb
      · right
        simpa [hy0, hb] using this

structure F6Spec (W : F6W) : Prop where
  permF : ∀ j < 4, isPerm (W.F j) (W.FI j) = true
  permD : ∀ j < 2, isPerm (W.D j) (W.DI j) = true
  permZ : isPerm W.Z W.Z = true
  lzp : lettersK 4 Certificates.Thm49E.zpWord = true
  ly0 : lettersK 4 Certificates.Thm49E.y0Word = true
  lu1 : lettersK 4 Certificates.Thm49E.u1Word = true
  lu2 : lettersK 4 Certificates.Thm49E.u2Word = true
  le : lettersK 2 W.ew = true
  le1 : lettersK 2 W.e1w = true
  le1i : lettersK 2 W.e1iw = true
  lf : lettersK 2 W.fw = true
  core : CoreSpec W (wd W.F W.FI Certificates.Thm49E.zpWord) (wd W.F W.FI Certificates.Thm49E.y0Word)
    (wd W.F W.FI Certificates.Thm49E.u1Word) (wd W.F W.FI Certificates.Thm49E.u2Word)
    (wd W.D W.DI W.ew) (wd W.D W.DI W.e1w) (wd W.D W.DI W.e1iw) (wd W.D W.DI W.fw)

theorem f6K_spec {W : F6W} (h : f6K W = true) : F6Spec W := by
  unfold f6K at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.strictB_eq, Bool.and_eq_true,
    CFSG.KS.Raw.Orb.allN_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, coreSpec_of h12⟩

end CFSG.KD.T49

end
