module

public import Certificates.Data.Kernel.Spor.CommBase
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBase

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.ComponentClassification.M12Cover

variable {n w nL : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

theorem bIf_eqC (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (if c = true then t else e) := by
  cases c <;> rfl

theorem notB_true {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem allL_iff {α : Type} {f : α → Bool} {l : List α} :
    allL f l = true ↔ ∀ a ∈ l, f a = true := by
  induction l with
  | nil => exact ⟨fun _ a ha => absurd ha List.not_mem_nil, fun _ => rfl⟩
  | cons a l ih =>
    change bAnd(f a, allL f l) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyL_iff {α : Type} {f : α → Bool} {l : List α} :
    anyL f l = true ↔ ∃ a ∈ l, f a = true := by
  induction l with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨a, ha, _⟩ => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    change bIf(f a, true, anyL f l) = true ↔ _
    rw [bIf_eqC]
    by_cases h : f a = true
    · simp [h]
    · simp [h, ih]

theorem lettersOK_iff {W : List ℕ} : lettersOK nL W = true ↔ ∀ z ∈ W, z < nL := by
  rw [lettersOK, allL_iff]
  exact forall₂_congr fun z _ => by rw [Nat.blt_eq]

theorem prep_unique {P : ℕ} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g) (hh : PRep n w P h) :
    g = h :=
  Equiv.ext fun y => Fin.ext (by rw [← hg y, ← hh y])

theorem prep_inv_of_permOK {P Q : ℕ} {g : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (h : permOK n w (mask w) (n * w) P Q = true) : PRep n w Q g⁻¹ := by
  intro y
  have e := ((permOK_facts h).2.2 (g⁻¹ y) (g⁻¹ y).2).2
  have hy : g (g⁻¹ y) = y := by simp
  rw [hg (g⁻¹ y), hy] at e
  exact e

@[expose] def word (ℓ : ℕ → Equiv.Perm (Fin n)) (W : List ℕ) : Equiv.Perm (Fin n) :=
  (W.map ℓ).prod

theorem wapp_eq (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) :
    ∀ {W : List ℕ}, (∀ z ∈ W, z < nL) → ∀ y : Fin n, wapp w (mask w) L W y = word ℓ W y
  | [], _, y => rfl
  | z :: W, hW, y => by
    change strictN (wapp w (mask w) L W y) (fun v => pg w (mask w) (L z) v) = _
    rw [strictN_eq, wapp_eq hL (fun a ha => hW a (List.mem_cons_of_mem z ha)) y,
      hL z (hW z List.mem_cons_self)]
    simp only [word, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem commute_word {x : Equiv.Perm (Fin n)} (hx : ∀ z < nL, Commute x (ℓ z)) {W : List ℕ}
    (hW : ∀ z ∈ W, z < nL) : Commute x (word ℓ W) :=
  Commute.list_prod_right _ _ fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hx z (hW z hz)

theorem comm_apply {x g : Equiv.Perm (Fin n)} (h : Commute x g) (y : Fin n) : x (g y) = g (x y) := by
  rw [← Equiv.Perm.mul_apply, h.eq, Equiv.Perm.mul_apply]

theorem allowed_cases {b pr y : ℕ} {ex : List (ℕ × ℕ)} {sw : List (ℕ × List ℕ)}
    (h : allowed b ex sw pr y = true) :
    y = b ∨ (pr = b ∧ ((∃ e ∈ ex, e.1 = y) ∨ ∃ t ∈ sw, t.1 = y)) ∨ (pr ≠ b ∧ y = pr) := by
  unfold allowed at h
  rw [bIf_eqC, bIf_eqC, bIf_eqC] at h
  by_cases h1 : y = b
  · exact Or.inl h1
  rw [if_neg (by rwa [Nat.beq_eq])] at h
  by_cases h2 : pr = b
  · rw [if_pos (by rwa [Nat.beq_eq])] at h
    refine Or.inr (Or.inl ⟨h2, ?_⟩)
    split_ifs at h with h3
    · exact Or.inl (by simpa [Nat.beq_eq] using anyL_iff.1 h3)
    · exact Or.inr (by simpa [Nat.beq_eq] using anyL_iff.1 h)
  · rw [if_neg (by rwa [Nat.beq_eq])] at h
    exact Or.inr (Or.inr ⟨h2, Nat.eq_of_beq_eq_true h⟩)

theorem sq_fix_of_baseOK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {r : BaseRec} (h : baseOK n w (mask w) L nL r = true) :
    ∃ hb : r.1 < n, x (x ⟨r.1, hb⟩) = ⟨r.1, hb⟩ := by
  obtain ⟨b, ss, ex, sw, pr⟩ := r
  change baseOKc n w (mask w) L nL b ss ex sw pr = true at h
  unfold baseOKc at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hb, -, hss, hsb, hex, hsw, hall⟩ := h
  rw [Nat.blt_eq] at hb
  rw [allL_iff] at hss hsb hex hsw
  rw [allN_iff] at hall
  replace hss : ∀ s ∈ ss, ∀ z ∈ s, z < nL := fun s hs => lettersOK_iff.1 (hss s hs)
  replace hsb : ∀ s ∈ ss, wapp w (mask w) L s b = b := fun s hs =>
    Nat.eq_of_beq_eq_true (hsb s hs)
  replace hex : ∀ e ∈ ex, e.2 < nL ∧ pg w (mask w) (L e.2) b ≠ b ∧
      pg w (mask w) (L e.2) e.1 = e.1 := fun e he => by
    have := hex e he
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.ne_of_beq_eq_false (notB_true this.2.1),
      Nat.eq_of_beq_eq_true this.2.2⟩
  replace hsw : ∀ t ∈ sw, (∀ z ∈ t.2, z < nL) ∧ wapp w (mask w) L t.2 b = t.1 ∧
      wapp w (mask w) L t.2 t.1 = b := fun t ht => by
    have := hsw t ht
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, lettersOK_iff] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2.1, Nat.eq_of_beq_eq_true this.2.2⟩
  replace hall : ∀ y < n, fixAll w (mask w) L ss y = true → allowed b ex sw pr y = true :=
    fun y hy hf => by
      have := hall y hy
      rwa [bIf_eqC, if_pos hf] at this
  refine ⟨hb, ?_⟩
  set B : Fin n := ⟨b, hb⟩
  have hS : ∀ s ∈ ss, word ℓ s B = B := fun s hs =>
    Fin.ext (by rw [← wapp_eq hL (hss s hs)]; exact hsb s hs)
  have hSc : ∀ s ∈ ss, Commute x (word ℓ s) := fun s hs => commute_word hx (hss s hs)
  have hfix : ∀ y : Fin n, (∀ s ∈ ss, word ℓ s y = y) →
      allowed b ex sw pr y = true := by
    intro y hy
    have hf : fixAll w (mask w) L ss y = true := by
      rw [fixAll, allL_iff]
      intro s hs
      rw [Nat.beq_eq, wapp_eq hL (hss s hs), hy s hs]
    exact hall y y.2 hf
  have hxfix : ∀ y : Fin n, (∀ s ∈ ss, word ℓ s y = y) → ∀ s ∈ ss, word ℓ s (x y) = x y :=
    fun y hy s hs => by rw [← comm_apply (hSc s hs), hy s hs]
  have hc : ∀ s ∈ ss, word ℓ s (x B) = x B := hxfix B hS
  rcases allowed_cases (hfix (x B) hc) with h1 | ⟨-, ⟨e, he, he1⟩ | ⟨t, ht, ht1⟩⟩ | ⟨hne, h1⟩
  · have e : x B = B := Fin.ext h1
    rw [e, e]
  · exfalso
    obtain ⟨hz, hmove, hfixe⟩ := hex e he
    have hmove' : ℓ e.2 B ≠ B := fun hc => hmove ((hL e.2 hz B).trans (congrArg Fin.val hc))
    have hfix' : ℓ e.2 (x B) = x B := Fin.ext (by rw [← hL e.2 hz, ← he1]; exact hfixe)
    apply hmove'
    apply x.injective
    rw [comm_apply (hx e.2 hz), hfix']
  · obtain ⟨htl, htb, htc⟩ := hsw t ht
    have hT : word ℓ t.2 B = x B := Fin.ext (by rw [← wapp_eq hL htl, ← ht1]; exact htb)
    have hT' : word ℓ t.2 (x B) = B := Fin.ext (by
      rw [← wapp_eq hL htl]
      change wapp w (mask w) L t.2 (x B : ℕ) = b
      rw [← ht1]
      exact htc)
    calc x (x B) = x (word ℓ t.2 B) := by rw [hT]
      _ = word ℓ t.2 (x B) := comm_apply (commute_word hx htl) B
      _ = B := hT'
  · rcases allowed_cases (hfix (x (x B)) (hxfix _ hc)) with h2 | ⟨h2, -⟩ | ⟨-, h2⟩
    · exact Fin.ext h2
    · exact absurd h2 hne
    · exfalso
      have e : x (x B) = x B := Fin.ext (by rw [h2, h1])
      have := congrArg Fin.val (x.injective e)
      exact hne (h1.symm.trans this)

theorem eq_one_of_forestOK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {X : Equiv.Perm (Fin n)}
    (hX : ∀ z < nL, Commute X (ℓ z)) {B : List BaseRec} {PF ZF DF : ℕ}
    (h : forestOK n w (mask w) L nL B PF ZF DF = true)
    (hB : ∀ r ∈ B, ∀ hb : r.1 < n, X ⟨r.1, hb⟩ = ⟨r.1, hb⟩) : X = 1 := by
  rw [forestOK, allN_iff] at h
  have key : ∀ d, ∀ p : Fin n, pg w (mask w) DF p = d → X p = p := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp
      have hq := h p p.2
      rw [strictB_eq, bIf_eqC] at hq
      by_cases hqp : Nat.beq (pg w (mask w) PF p) p = true
      · rw [if_pos hqp, anyL_iff] at hq
        obtain ⟨r, hr, hr1⟩ := hq
        have e : r.1 = p := Nat.eq_of_beq_eq_true hr1
        have := hB r hr (e ▸ p.2)
        have hp' : (⟨r.1, e ▸ p.2⟩ : Fin n) = p := Fin.ext e
        rwa [hp'] at this
      · rw [if_neg hqp, bAnd_eq, Bool.and_eq_true, strictB_eq, bAnd_eq, bAnd_eq,
          Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hq
        obtain ⟨hqn, hz, hd, hl⟩ := hq
        replace hl := Nat.eq_of_beq_eq_true hl
        set q : Fin n := ⟨pg w (mask w) PF p, hqn⟩
        have hlq : ℓ (pg w (mask w) ZF p) q = p := Fin.ext (by rw [← hL _ hz]; exact hl)
        have hXq : X q = q := ih _ (hp ▸ hd) q rfl
        rw [← hlq, comm_apply (hX _ hz), hXq]
  exact Equiv.ext fun p => key _ p rfl

theorem sq_eq_one_of_commBaseOK (hL : ∀ z < nL, PRep n w (L z) (ℓ z)) {x : Equiv.Perm (Fin n)}
    (hx : ∀ z < nL, Commute x (ℓ z)) {B : List BaseRec} {PF ZF DF : ℕ}
    (h : commBaseOK n w (mask w) L nL B PF ZF DF = true) : x ^ 2 = 1 := by
  rw [commBaseOK, bAnd_eq, Bool.and_eq_true, allL_iff] at h
  refine eq_one_of_forestOK hL (fun z hz => (hx z hz).pow_left 2) h.2 fun r hr hb => ?_
  obtain ⟨hb', e⟩ := sq_fix_of_baseOK hL hx (h.1 r hr)
  rw [pow_two, Equiv.Perm.mul_apply]
  exact e

theorem fourClassesLarge_of_commBase (K : Subgroup (Equiv.Perm (Fin n)))
    (hL : ∀ z < nL, PRep n w (L z) (ℓ z))
    (hK : ∀ z < nL, (ℓ z ∈ K ∧ ℓ z ^ 5 = 1) ∨ ∀ k ∈ K, Commute k (ℓ z))
    {B : List BaseRec} {PF ZF DF : ℕ} (h : commBaseOK n w (mask w) L nL B PF ZF DF = true) :
    FourClassesLarge K := by
  intro x _ hx2
  by_contra hlt
  have hle : Nat.card {y : K // IsConj x y} ≤ 4 := by omega
  have hx : ∀ z < nL, Commute (x : Equiv.Perm (Fin n)) (ℓ z) := by
    intro z hz
    rcases hK z hz with ⟨hm, h5⟩ | hc
    · have := CFSG.EvenSporadicStandard.TwoRu.HypOne.commute_of_card_isConj_le
        (x := x) (h := ⟨ℓ z, hm⟩) Nat.prime_five le_rfl (Subtype.ext (by simpa using h5)) hle
      exact (congrArg Subtype.val this).symm
    · exact hc x x.2
  exact hx2 (Subtype.ext (by simpa using sq_eq_one_of_commBaseOK hL hx h))

end CFSG.KC.CommBase

end
