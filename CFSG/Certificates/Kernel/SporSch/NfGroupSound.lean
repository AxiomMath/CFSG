module

public import Certificates.Data.Kernel.SporSch.NfGroup
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Schreier

variable {n : Nat} {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}
  {ev : Nat → Nat → Nat} {vld : Nat → Bool} {E : Nat → Equiv.Perm (Fin n)}

@[expose] def Codes (H : Subgroup (Equiv.Perm (Fin n))) (ev : Nat → Nat → Nat) (vld : Nat → Bool)
    (E : Nat → Equiv.Perm (Fin n)) : Prop :=
  ∀ a, vld a = true → RepF n (ev a) (E a) ∧ E a ∈ H

theorem mulL_sound (hH : BaseFaithful H bs) (hC : Codes H ev vld E) {a b c : Nat}
    (ha : vld a = true) (hb : vld b = true) (hc : vld c = true)
    (h : mulL ev bs a b c = true) : E a * E b = E c :=
  eq_of_eqOnL hH ((hC a ha).1.comp (hC b hb).1) (hC c hc).1
    (H.mul_mem (hC a ha).2 (hC b hb).2) (hC c hc).2 h

theorem comL_sound (hH : BaseFaithful H bs) (hC : Codes H ev vld E) {X : Nat → Nat}
    {x : Equiv.Perm (Fin n)} (hX : RepF n X x) (hx : x ∈ H) {a : Nat} (ha : vld a = true)
    (h : comL ev bs X a = true) : E a * x = x * E a :=
  eq_of_eqOnL hH ((hC a ha).1.comp hX) (hX.comp (hC a ha).1)
    (H.mul_mem (hC a ha).2 hx) (H.mul_mem hx (hC a ha).2) h

theorem wtL_sound (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) (hC : Codes H ev vld E)
    {s u v e : Nat} (hs : vld s = true) (hu : vld u = true) (hv : vld v = true)
    (h : wtL ev bs s u v e = true) : E u * E v = 1 ∧ (E s * E u * E s * E v) ^ e ≠ 1 := by
  unfold wtL at h
  rw [bAnd_iff, bNot_iff] at h
  have hUV := (hC u hu).1.comp (hC v hv).1
  refine ⟨(fixL_iff hH hbs hUV (H.mul_mem (hC u hu).2 (hC v hv).2)).1 h.1, fun h1 => h.2 ?_⟩
  have hz : RepF n (fun x => ev s (ev u (ev s (ev v x)))) (E s * E u * E s * E v) := by
    have := (hC s hs).1.comp ((hC u hu).1.comp ((hC s hs).1.comp (hC v hv).1))
    simpa only [mul_assoc] using this
  have hzH : E s * E u * E s * E v ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hC s hs).2 (hC u hu).2) (hC s hs).2) (hC v hv).2
  exact (fixL_iff hH hbs (hz.powF e) (H.pow_mem hzH e)).2 h1

@[expose] noncomputable def wElt (E : Nat → Equiv.Perm (Fin n)) (G : Nat → Nat) :
    Nat → Nat → Equiv.Perm (Fin n)
  | 0, _ => 1
  | f + 1, w => if w = 0 then 1 else E (G (w % 4 - 1)) * wElt E G f (w / 4)

theorem wev_succ (G : Nat → Nat) (f w x : Nat) : wev ev G (f + 1) w x =
    Bool.rec (motive := fun _ => Nat) (ev (G (Nat.sub (Nat.mod w 4) 1)) (wev ev G f (Nat.div w 4) x))
      x (Nat.beq w 0) := rfl

theorem wev_rep (hC : Codes H ev vld E) {G : Nat → Nat} (hG : ∀ j, vld (G j) = true) :
    ∀ f w, RepF n (wev ev G f w) (wElt E G f w)
  | 0, _ => fun _ _ => rfl
  | f + 1, w => by
    intro x hx
    rw [wev_succ]
    by_cases hw : w = 0
    · subst hw
      rfl
    · have hb : Nat.beq w 0 = false := by
        cases h : Nat.beq w 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hw
      rw [hb]
      simp only [wElt, ite_eq_right hw]
      exact ((hC _ (hG _)).1.comp (wev_rep hC hG f (w / 4))) x hx

theorem wElt_mem {G : Nat → Nat} (S : Subgroup (Equiv.Perm (Fin n))) (hS : ∀ j, E (G j) ∈ S) :
    ∀ f w, wElt E G f w ∈ S
  | 0, _ => S.one_mem
  | f + 1, w => by
    simp only [wElt]
    split_ifs
    · exact S.one_mem
    · exact S.mul_mem (hS _) (wElt_mem S hS f _)

theorem wordsOK_sound (hH : BaseFaithful H bs) (hC : Codes H ev vld E) {G L W : Nat → Nat}
    {m : Nat} (hG : ∀ j, vld (G j) = true) (hv : ∀ i < m, vld (L i) = true)
    (h : wordsOK ev bs G L W m = true) : ∀ i < m, E (L i) = wElt E G 40 (W i) := fun i hi =>
  eq_of_eqOnL hH (hC _ (hv i hi)).1 (wev_rep hC hG 40 (W i)) (hC _ (hv i hi)).2
    (wElt_mem H (fun j => (hC _ (hG j)).2) 40 _) (allN_spec h i hi)

section ListGroup

variable {L T I : Nat → Nat} {m : Nat}

theorem lgOK_parts (h : lgOK ev vld bs L T I m = true) :
    (∀ i < m, vld (L i) = true) ∧ eqOnL bs (ev (L 0)) (fun x => x) = true ∧
      (∀ i < m, ∀ j < m, T (m * i + j) < m ∧ mulL ev bs (L i) (L j) (L (T (m * i + j))) = true) ∧
      (∀ i < m, I i < m ∧ mulL ev bs (L i) (L (I i)) (L 0) = true) ∧
      (∀ i < m, ∀ j < i, eqOnL bs (ev (L i)) (ev (L j)) ≠ true) := by
  unfold lgOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨allN_spec h1, h2, fun i hi j hj => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · have := allN_spec (allN_spec h3 i hi) j hj
    rw [strictB_val, bAnd_iff, Nat.blt_eq] at this
    exact this
  · have := allN_spec h4 i hi
    rw [strictB_val, bAnd_iff, Nat.blt_eq] at this
    exact this
  · have := allN_spec (allN_spec h5 i hi) j hj
    exact (bNot_iff _).1 this

variable (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) (hC : Codes H ev vld E)
  (h : lgOK ev vld bs L T I m = true) (hm : 0 < m)
include hH hbs hC h hm

theorem lg_one : E (L 0) = 1 :=
  (fixL_iff hH hbs (hC _ ((lgOK_parts h).1 0 hm)).1 (hC _ ((lgOK_parts h).1 0 hm)).2).1
    (lgOK_parts h).2.1

@[expose] noncomputable def lgSub : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∃ i < m, E (L i) = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    obtain ⟨hv, -, hT, -, -⟩ := lgOK_parts h
    obtain ⟨hk, hmul⟩ := hT i hi j hj
    exact ⟨_, hk, (mulL_sound hH hC (hv i hi) (hv j hj) (hv _ hk) hmul).symm⟩
  one_mem' := ⟨0, hm, lg_one hH hbs hC h hm⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨hv, -, -, hI, -⟩ := lgOK_parts h
    obtain ⟨hk, hmul⟩ := hI i hi
    refine ⟨I i, hk, ?_⟩
    have e := mulL_sound hH hC (hv i hi) (hv _ hk) (hv 0 hm) hmul
    rw [lg_one hH hbs hC h hm] at e
    exact (eq_inv_of_mul_eq_one_right e)

theorem lgSub_le : lgSub hH hbs hC h hm ≤ H := by
  rintro _ ⟨i, hi, rfl⟩
  exact (hC _ ((lgOK_parts h).1 i hi)).2

theorem card_lgSub : Nat.card (lgSub hH hbs hC h hm) = m := by
  obtain ⟨hv, -, -, -, hd⟩ := lgOK_parts h
  have hinj : ∀ i < m, ∀ j < m, E (L i) = E (L j) → i = j := by
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hij
    · exact hd j hj i hij (eqOnL_of_eq hbs (hC _ (hv j hj)).1 (e ▸ (hC _ (hv i hi)).1))
    · exact hd i hi j hij (eqOnL_of_eq hbs (hC _ (hv i hi)).1 (e.symm ▸ (hC _ (hv j hj)).1))
  let f : Fin m → lgSub hH hbs hC h hm := fun i => ⟨E (L i), i.val, i.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨_, i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end ListGroup

section GenClosure

open Subgroup

variable {L G T : Nat → Nat} {m k z : Nat}

theorem keyBL_congr (hbs : ∀ b ∈ bs, b < n) {a c : Nat} {u : Equiv.Perm (Fin n)}
    (hf : RepF n (ev a) u) (hg : RepF n (ev c) u) : keyBL n ev bs a = keyBL n ev bs c := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change Nat.add (Nat.mod (Nat.add (ev a b) (Nat.sub n b)) n) (Nat.mul n (keyBL n ev bs a)) =
      Nat.add (Nat.mod (Nat.add (ev c b) (Nat.sub n b)) n) (Nat.mul n (keyBL n ev bs c))
    rw [ih fun x hx => hbs x (List.mem_cons_of_mem _ hx), hf b (hbs b List.mem_cons_self),
      hg b (hbs b List.mem_cons_self)]

theorem gcOK_parts (h : gcOK n ev vld bs L G T m k z = true) :
    (∀ i < m, vld (L i) = true) ∧ (∀ t < k, vld (G t) = true) ∧
      (z < m ∧ eqOnL bs (ev (L z)) (fun x => x) = true) ∧
      (∀ i < m, ∀ t < k, T (k * i + t) < m ∧ mulL ev bs (G t) (L i) (L (T (k * i + t))) = true) ∧
      (∀ i < m - 1, keyBL n ev bs (L i) < keyBL n ev bs (L (i + 1))) := by
  unfold gcOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, ⟨hz, h3⟩, h4, h5⟩ := h
  rw [Nat.blt_eq] at hz
  refine ⟨allN_spec h1, allN_spec h2, ⟨hz, h3⟩, fun i hi t ht => ?_, fun i hi => ?_⟩
  · have := allN_spec (allN_spec h4 i hi) t ht
    rw [strictB_val, bAnd_iff, Nat.blt_eq] at this
    exact this
  · have := allN_spec h5 i hi
    rw [Nat.blt_eq] at this
    exact this

variable (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) (hC : Codes H ev vld E)
  (h : gcOK n ev vld bs L G T m k z = true)
include hH hbs hC h

omit hH hbs in
theorem gc_closure_le :
    closure {g | ∃ t < k, E (G t) = g} ≤ H := by
  refine (closure_le _).2 ?_
  rintro _ ⟨t, ht, rfl⟩
  exact (hC _ ((gcOK_parts h).2.1 t ht)).2

theorem gc_mem_iff (hw : ∀ i < m, E (L i) ∈ closure {g | ∃ t < k, E (G t) = g}) (g) :
    g ∈ closure {g | ∃ t < k, E (G t) = g} ↔ ∃ i < m, E (L i) = g := by
  obtain ⟨hv, hgv, ⟨hz, h1⟩, hT, -⟩ := gcOK_parts h
  have hone : E (L z) = 1 :=
    (fixL_iff hH hbs (hC _ (hv z hz)).1 (hC _ (hv z hz)).2).1 h1
  let S : Set (Equiv.Perm (Fin n)) := {g | ∃ i < m, E (L i) = g}
  have hmulS : ∀ x : Equiv.Perm (Fin n), (∀ s ∈ S, x * s ∈ S) → ∀ e : ℕ, ∀ s ∈ S, x ^ e * s ∈ S := by
    intro x hx e
    induction e with
    | zero => simp
    | succ e ih =>
      intro s hs
      rw [pow_succ', mul_assoc]
      exact hx _ (ih s hs)
  let P : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {x | ∀ s ∈ S, x * s ∈ S}
      mul_mem' := fun {x y} hx hy s hs => by
        rw [Set.mem_ofPred_eq] at hx hy
        rw [mul_assoc]
        exact hx _ (hy s hs)
      one_mem' := fun s hs => by simpa using hs
      inv_mem' := fun {x} hx s hs => by
        have hpos := orderOf_pos x
        have e : x⁻¹ = x ^ (orderOf x - 1) := by
          refine (eq_inv_of_mul_eq_one_left ?_).symm
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [e]
        exact hmulS x hx _ s hs }
  have hle : closure {g | ∃ t < k, E (G t) = g} ≤ P := by
    refine (closure_le _).2 ?_
    rintro _ ⟨t, ht, rfl⟩ _ ⟨i, hi, rfl⟩
    obtain ⟨hj, hmul⟩ := hT i hi t ht
    exact ⟨_, hj, (mulL_sound hH hC (hgv t ht) (hv i hi) (hv _ hj) hmul).symm⟩
  constructor
  · intro hg
    obtain ⟨i, hi, e⟩ := hle hg _ ⟨z, hz, hone⟩
    exact ⟨i, hi, by rw [e, mul_one]⟩
  · rintro ⟨i, hi, rfl⟩
    exact hw i hi

theorem gc_card (hw : ∀ i < m, E (L i) ∈ closure {g | ∃ t < k, E (G t) = g}) :
    Nat.card (closure {g | ∃ t < k, E (G t) = g}) = m := by
  obtain ⟨hv, -, -, -, hkey⟩ := gcOK_parts h
  have hmono : ∀ i j, i < j → j < m → keyBL n ev bs (L i) < keyBL n ev bs (L j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := hkey j (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
      · exact (ih hlt (by omega)).trans hs
      · exact hs
  have hinj : ∀ i < m, ∀ j < m, E (L i) = E (L j) → i = j := by
    intro i hi j hj e
    have hk := keyBL_congr hbs (hC _ (hv i hi)).1 (e ▸ (hC _ (hv j hj)).1)
    rcases Nat.lt_trichotomy i j with hij | rfl | hij
    · exact absurd hk (hmono i j hij hj).ne
    · rfl
    · exact absurd hk (hmono j i hij hi).ne'
  let f : Fin m → closure {g | ∃ t < k, E (G t) = g} := fun i =>
    ⟨E (L i), hw i i.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨i, hi, rfl⟩ := (gc_mem_iff hH hbs hC h hw g).1 hg
    exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end GenClosure

section Words

variable {w NR : Nat} {LT : Nat → Nat} {kk : Nat}

theorem wEvK_succ (w NR : Nat) (LT : Nat → Nat) (kk f P x : Nat) :
    wEvK w NR LT kk (f + 1) P x = if P = 0 then x else
      if (P % 32 - 1) < kk then lptK w NR LT (P % 32 - 1) (wEvK w NR LT kk f (P / 32) x)
      else wEvK w NR LT kk f (P / 32) x := by
  have e1 : Nat.shiftRight P 5 = P / 32 := Nat.shiftRight_eq_div_pow P 5
  have e2 : Nat.land P 31 = P % 32 := Nat.and_two_pow_sub_one_eq_mod P 5
  change nIf(Nat.beq P 0, x, strictN (wEvK w NR LT kk f (Nat.shiftRight P 5) x) (fun y =>
        strictN (Nat.sub (Nat.land P 31) 1) (fun l => nIf(Nat.blt l kk, lptK w NR LT l y, y)))) = _
  rw [e1, e2]
  by_cases hP : P = 0
  · subst hP
    rfl
  · have hb : Nat.beq P 0 = false := by
      cases P with
      | zero => exact absurd rfl hP
      | succ _ => rfl
    rw [hb]
    simp only [hP, ↓reduceIte]
    generalize wEvK w NR LT kk f (P / 32) x = y
    generalize hl : P % 32 - 1 = l
    have : Nat.sub (P % 32) 1 = l := hl
    have sN : ∀ (y : Nat) (k : Nat → Nat), strictN y k = k y := fun y k => by cases y <;> rfl
    rw [this, sN, sN]
    by_cases hk : l < kk
    · rw [Nat.blt_eq.mpr hk, ite_eq_left_of_eq_true _ _ (eq_true hk)]
    · rw [Bool.eq_false_iff.2 (fun h => hk (Nat.blt_eq.mp h)),
        ite_eq_right_of_eq_false _ _ (eq_false hk)]

theorem wEvK_rep (hL : ∀ l < kk, ∃ g ∈ H, RepF n (lptK w NR LT l) g) :
    ∀ f P, ∃ g ∈ H, RepF n (wEvK w NR LT kk f P) g
  | 0, _ => ⟨1, H.one_mem, fun _ _ => rfl⟩
  | f + 1, P => by
    obtain ⟨g, hg, hr⟩ := wEvK_rep hL f (P / 32)
    by_cases hP : P = 0
    · refine ⟨1, H.one_mem, fun x hx => ?_⟩
      rw [wEvK_succ]
      simp only [hP, ↓reduceIte]
      rfl
    by_cases hk : P % 32 - 1 < kk
    · obtain ⟨u, hu, hur⟩ := hL _ hk
      refine ⟨u * g, H.mul_mem hu hg, fun x hx => ?_⟩
      rw [wEvK_succ]
      simp only [hP, hk, ↓reduceIte]
      exact (hur.comp hr) x hx
    · refine ⟨g, hg, fun x hx => ?_⟩
      rw [wEvK_succ]
      simp only [hP, hk, ↓reduceIte]
      exact hr x hx

theorem wEvK_codes (hH : BaseFaithful H bs) (hC : Codes H ev vld E)
    (hL : ∀ l < kk, ∃ g ∈ H, RepF n (lptK w NR LT l) g) {a f P : Nat} (ha : vld a = true)
    (h : eqOnL bs (wEvK w NR LT kk f P) (ev a) = true) : RepF n (wEvK w NR LT kk f P) (E a) := by
  obtain ⟨g, hg, hr⟩ := wEvK_rep hL f P
  exact hr.congr (eq_of_eqOnL hH hr (hC a ha).1 hg (hC a ha).2 h)

end Words

end CFSG.KS.SporSch

end
