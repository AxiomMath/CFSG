module

public import CFSG.Certificates.Kernel.U43Mod.WordSound

public section

namespace CFSG.KS.U43Mod

open CFSG.KC.Enum CFSG.KC.U43Mod

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (beq_iff.1 hb) h

theorem keyIs_iff {w m r : ℕ} : ∀ (bs : List ℕ) (t0 : ℕ), keyIs w m bs r t0 = true ↔
    ∀ t (ht : t < bs.length), fld(r, Nat.mul w (t0 + t), m) = bs[t]
  | [], t0 => by simp [keyIs]
  | p :: bs, t0 => by
    change Bool.rec (motive := fun _ => Bool) false (keyIs w m bs r (Nat.succ t0))
      (Nat.beq fld(r, Nat.mul w t0, m) p) = true ↔ _
    rw [bAnd_iff, keyIs_iff bs, beq_iff]
    constructor
    · rintro ⟨h0, h1⟩ t ht
      cases t with
      | zero => simpa using h0
      | succ t =>
        have h2 := h1 t (by simpa using ht)
        have e : Nat.succ t0 + t = t0 + (t + 1) := by omega
        rw [e] at h2
        simpa using h2
    · intro h
      have h3 := h 0 (by simp)
      rw [Nat.add_zero] at h3
      refine ⟨h3, fun t ht => ?_⟩
      have h2 := h (t + 1) (by simpa using ht)
      have e : t0 + (t + 1) = Nat.succ t0 + t := by omega
      rw [e] at h2
      simpa using h2

theorem keyMap_iff {w m r r' : ℕ} {f : ℕ → ℕ} : ∀ (bs : List ℕ) (t0 : ℕ),
    keyMap w m bs f r r' t0 = true ↔
      ∀ t < bs.length, fld(r', Nat.mul w (t0 + t), m) = f fld(r, Nat.mul w (t0 + t), m)
  | [], t0 => by simp [keyMap]
  | _ :: bs, t0 => by
    change Bool.rec (motive := fun _ => Bool) false (keyMap w m bs f r r' (Nat.succ t0))
      (Nat.beq fld(r', Nat.mul w t0, m) (f fld(r, Nat.mul w t0, m))) = true ↔ _
    rw [bAnd_iff, keyMap_iff bs, beq_iff]
    constructor
    · rintro ⟨h0, h1⟩ t ht
      cases t with
      | zero => simpa using h0
      | succ t =>
        have h2 := h1 t (by simpa using ht)
        have e : Nat.succ t0 + t = t0 + (t + 1) := by omega
        rw [e] at h2
        exact h2
    · intro h
      refine ⟨by simpa using h 0 (by simp), fun t ht => ?_⟩
      have h2 := h (t + 1) (by simpa using ht)
      have e : t0 + (t + 1) = Nat.succ t0 + t := by omega
      rw [e] at h2
      exact h2

theorem kClos_iff {T : ℕ → ℕ} {w m iw im N r oc : ℕ} {bs : List ℕ} {G : ℕ → ℕ → ℕ} :
    ∀ k, kClos T w m iw im bs N G r oc k = true ↔ ∀ j < k,
      fld(r, Nat.add oc (Nat.mul iw j), im) < N ∧
        keyMap w m bs (G j) r (T fld(r, Nat.add oc (Nat.mul iw j), im)) (nat_lit 0) = true
  | 0 => by simp [kClos]
  | k + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (kClos T w m iw im bs N G r oc k)
      (strictB fld(r, Nat.add oc (Nat.mul iw k), im) (fun c =>
        bAnd(Nat.blt c N, strictB (T c) (fun rc => keyMap w m bs (G k) r rc (nat_lit 0))))) =
          true ↔ _
    rw [bAnd_iff, kClos_iff k, strictB_eq, bAnd_iff, strictB_eq, blt_iff]
    constructor
    · rintro ⟨h0, h1⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h1 j hj
      · exact h0
    · intro h
      exact ⟨h k (Nat.lt_succ_self k), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

@[expose] def dOf (kb iw r : ℕ) : ℕ := fld(r, Nat.add kb (Nat.add iw (nat_lit 4)), nat_lit 255)

@[expose] def pOf (kb im r : ℕ) : ℕ := fld(r, kb, im)

@[expose] def lOf (kb iw r : ℕ) : ℕ := fld(r, Nat.add kb iw, nat_lit 15)

theorem bIf_spec {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => Bool.noConfusion h', fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => Bool.noConfusion h'⟩

theorem kRec_spec {T : ℕ → ℕ} {w m iw im N k kb km i : ℕ} {bs : List ℕ} {G : ℕ → ℕ → ℕ}
    (h : kRec T w m iw im bs N k G kb km i = true) :
    (i = 0 ∨ Nat.land (T (i - 1)) km < Nat.land (T i) km) ∧
    (dOf kb iw (T i) = 0 → keyIs w m bs (T i) (nat_lit 0) = true) ∧
    (dOf kb iw (T i) ≠ 0 → pOf kb im (T i) < N ∧ lOf kb iw (T i) < k ∧
      dOf kb iw (T (pOf kb im (T i))) = dOf kb iw (T i) - 1 ∧
      keyMap w m bs (G (lOf kb iw (T i))) (T (pOf kb im (T i))) (T i) (nat_lit 0) = true) ∧
    kClos T w m iw im bs N G (T i) (Nat.add kb (Nat.add iw (nat_lit 12))) k = true := by
  unfold kRec at h
  simp only [strictB_eq] at h
  rw [bAnd_iff, bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, h3⟩
  · obtain ⟨h1a, h1b⟩ := bIf_spec h1
    cases hi : Nat.beq i (nat_lit 0)
    · exact Or.inr (blt_iff.1 (h1b hi))
    · exact Or.inl (Nat.eq_of_beq_eq_true hi)
  · intro hd
    exact (bIf_spec h2).1 (beq_iff.2 hd)
  · intro hd
    have h4 := (bIf_spec h2).2 (beq_false hd)
    rw [bAnd_iff, bAnd_iff] at h4
    obtain ⟨h5, h6, h7⟩ := h4
    rw [bAnd_iff] at h7
    exact ⟨blt_iff.1 h5, blt_iff.1 h6, beq_iff.1 h7.1, h7.2⟩

theorem fld_eq' (x o w : ℕ) : fld(x, o, 2 ^ w - 1) = x / 2 ^ o % 2 ^ w := by
  change (x >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem mod_eq_of_flds {a b w : ℕ} : ∀ L : ℕ,
    (∀ t < L, fld(a, Nat.mul w t, 2 ^ w - 1) = fld(b, Nat.mul w t, 2 ^ w - 1)) →
      a % 2 ^ (w * L) = b % 2 ^ (w * L)
  | 0, _ => by simp [Nat.mod_one]
  | L + 1, h => by
    have ih := mod_eq_of_flds L fun t ht => h t (Nat.lt_succ_of_lt ht)
    have hL := h L (Nat.lt_succ_self L)
    rw [fld_eq', fld_eq'] at hL
    change a / 2 ^ (w * L) % 2 ^ w = b / 2 ^ (w * L) % 2 ^ w at hL
    have e : w * (L + 1) = w * L + w := by ring
    rw [e, pow_add, Nat.mod_mul, Nat.mod_mul, ih, hL]

variable {n : ℕ} {S : ℕ → Equiv.Perm (Fin n)}

theorem card_of_kTree {T : ℕ → ℕ} {w m iw im N k : ℕ} {bs : List ℕ} {G : ℕ → ℕ → ℕ}
    (hm : m = 2 ^ w - 1) (hbs : ∀ p ∈ bs, p < n)
    (hG : ∀ j < k, ∀ q (hq : q < n), G j q = (S j ⟨q, hq⟩ : ℕ))
    (hsep : ∀ x ∈ Subgroup.closure (S '' Set.Iio k), ∀ y ∈ Subgroup.closure (S '' Set.Iio k),
      (∀ p (hp : p ∈ bs), x ⟨p, hbs p hp⟩ = y ⟨p, hbs p hp⟩) → x = y)
    (h : kTree T w m iw im bs N k G = true) :
    Nat.card (Subgroup.closure (S '' Set.Iio k)) = N := by
  set H := Subgroup.closure (S '' Set.Iio k) with hH
  unfold kTree at h
  rw [strictB_eq, bAnd_iff] at h
  obtain ⟨hN, hall⟩ := h
  have hN' : 0 < N := blt_iff.1 hN
  have hR := allN_spec hall
  generalize hkb : Nat.mul w (List.length bs) = kb at hR
  have hS : ∀ j < k, S j ∈ H := fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hbs' : ∀ t (ht : t < bs.length), bs[t] < n := fun t ht => hbs _ (List.getElem_mem ht)
  let KeyOf : ℕ → Equiv.Perm (Fin n) → Prop := fun i x =>
    ∀ t (ht : t < bs.length), fld(T i, Nat.mul w t, m) = (x ⟨bs[t], hbs' t ht⟩ : ℕ)
  have huniq : ∀ i x y, x ∈ H → y ∈ H → KeyOf i x → KeyOf i y → x = y := by
    intro i x y hx hy kx ky
    refine hsep x hx y hy fun p hp => ?_
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hp
    exact Fin.ext ((kx t ht).symm.trans (ky t ht))
  have hone : ∀ i < N, dOf kb iw (T i) = 0 → KeyOf i 1 := by
    intro i hi hd t ht
    have h1 := (keyIs_iff bs 0).1 ((kRec_spec (hR i hi)).2.1 hd) t ht
    rw [Nat.zero_add] at h1
    rw [h1]
    rfl
  have hex : ∀ d i, i < N → dOf kb iw (T i) = d → ∃ x ∈ H, KeyOf i x := by
    intro d
    induction d with
    | zero => exact fun i hi hd => ⟨1, H.one_mem, hone i hi hd⟩
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, hl, hdp, hkm⟩ := (kRec_spec (hR i hi)).2.2.1 (by omega)
      obtain ⟨x, hx, kx⟩ := ih _ hp (by omega)
      refine ⟨S (lOf kb iw (T i)) * x, H.mul_mem (hS _ hl) hx, fun t ht => ?_⟩
      have h1 := (keyMap_iff bs 0).1 hkm t ht
      rw [Nat.zero_add] at h1
      rw [h1, kx t ht, hG _ hl _ (Fin.is_lt _), Equiv.Perm.mul_apply]
  have hex' : ∀ i, i < N → ∃ x, x ∈ H ∧ KeyOf i x := fun i hi =>
    let ⟨x, hx, kx⟩ := hex _ i hi rfl
    ⟨x, hx, kx⟩
  choose! e heH heK using hex'
  have hinc : ∀ i i', i < i' → i' < N →
      Nat.land (T i) (Nat.sub (Nat.shiftLeft 1 kb) 1) <
        Nat.land (T i') (Nat.sub (Nat.shiftLeft 1 kb) 1) := by
    intro i i' hii' hi'
    induction i' with
    | zero => omega
    | succ i' ih =>
      rcases (kRec_spec (hR (i' + 1) hi')).1 with h1 | h1
      · omega
      rw [Nat.add_sub_cancel] at h1
      rcases Nat.lt_succ_iff_lt_or_eq.1 hii' with h2 | rfl
      · exact (ih h2 (by omega)).trans h1
      · exact h1
  have hland : ∀ x, Nat.land x (Nat.sub (Nat.shiftLeft 1 kb) 1) = x % 2 ^ (w * bs.length) := by
    intro x
    change x &&& ((1 <<< kb) - 1) = _
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, ← hkb]
    rfl
  have hinj : ∀ i i', i < N → i' < N → e i = e i' → i = i' := by
    have key : ∀ i i', i < i' → i' < N → e i ≠ e i' := by
      intro i i' hii' hi' he
      have hi : i < N := by omega
      have hf : ∀ t < bs.length, fld(T i, Nat.mul w t, 2 ^ w - 1) =
          fld(T i', Nat.mul w t, 2 ^ w - 1) := by
        intro t ht
        rw [← hm, heK i hi t ht, heK i' hi' t ht, he]
      have h1 := mod_eq_of_flds _ hf
      have h2 := hinc i i' hii' hi'
      rw [hland, hland, h1] at h2
      exact lt_irrefl _ h2
    intro i i' hi hi' he
    rcases lt_trichotomy i i' with h | h | h
    · exact absurd he (key i i' h hi')
    · exact h
    · exact absurd he.symm (key i' i h hi)
  have hcl : ∀ i < N, ∀ j < k, ∃ c < N, e c = S j * e i := by
    intro i hi j hj
    obtain ⟨hc, hkm⟩ := (kClos_iff k).1 (kRec_spec (hR i hi)).2.2.2 j hj
    refine ⟨_, hc, huniq _ _ _ (heH _ hc) (H.mul_mem (hS j hj) (heH i hi)) (heK _ hc) ?_⟩
    intro t ht
    have h1 := (keyMap_iff bs 0).1 hkm t ht
    rw [Nat.zero_add] at h1
    rw [h1, heK i hi t ht, hG j hj _ (Fin.is_lt _), Equiv.Perm.mul_apply]
  have hdesc : ∀ d i, i < N → dOf kb iw (T i) = d → ∃ i0 < N, dOf kb iw (T i0) = 0 := by
    intro d
    induction d with
    | zero => exact fun i hi hd => ⟨i, hi, hd⟩
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, -, hdp, -⟩ := (kRec_spec (hR i hi)).2.2.1 (by omega)
      exact ih _ hp (by omega)
  have h1mem : ∃ i0 < N, e i0 = 1 := by
    obtain ⟨i0, hi0, hd⟩ := hdesc _ 0 hN' rfl
    exact ⟨i0, hi0, huniq _ _ _ (heH i0 hi0) H.one_mem (heK i0 hi0) (hone i0 hi0 hd)⟩
  have hcov : ∀ y ∈ H, ∃ i < N, e i = y := by
    intro y hy
    refine Subgroup.closure_induction_left (p := fun y _ => ∃ i < N, e i = y) h1mem ?_ ?_ hy
    · rintro _ ⟨j, hj, rfl⟩ y _ ⟨i, hi, rfl⟩
      exact hcl i hi j hj
    · rintro _ ⟨j, hj, rfl⟩ y _ ⟨i, hi, rfl⟩
      have hpow : ∀ a : ℕ, ∃ c < N, e c = S j ^ a * e i := by
        intro a
        induction a with
        | zero => exact ⟨i, hi, by simp⟩
        | succ a ih =>
          obtain ⟨c, hc, he⟩ := ih
          obtain ⟨c', hc', he'⟩ := hcl c hc j hj
          exact ⟨c', hc', by rw [he', he, pow_succ', mul_assoc]⟩
      have hinv : (S j)⁻¹ = S j ^ (orderOf (S j) - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]
      obtain ⟨c, hc, he⟩ := hpow (orderOf (S j) - 1)
      exact ⟨c, hc, by rw [he, hinv]⟩
  let f : Fin N → H := fun i => ⟨e i, heH i i.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Fin.ext (hinj a b a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨i, hi, he⟩ := hcov y hy
    exact ⟨⟨i, hi⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.KS.U43Mod

end
