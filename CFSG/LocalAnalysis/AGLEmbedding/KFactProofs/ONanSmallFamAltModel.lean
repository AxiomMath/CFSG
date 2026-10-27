module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm

variable {p : ℕ} [Fact p.Prime]

@[expose] def altTr (i j : ZMod p) : Perm (ZMod p × Fin 2) where
  toFun w := (w.1 + ![i, j] w.2, w.2)
  invFun w := (w.1 - ![i, j] w.2, w.2)
  left_inv w := by simp
  right_inv w := by simp

theorem altTr_apply (i j k : ZMod p) (s : Fin 2) : altTr i j (k, s) = (k + ![i, j] s, s) := rfl

theorem altTr_mul (i j i' j' : ZMod p) : altTr i j * altTr i' j' = altTr (i + i') (j + j') := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altTr_apply, Perm.mul_apply] <;> ring

theorem altTr_zero : altTr (0 : ZMod p) 0 = 1 := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altTr_apply]

theorem altTr_injective {i j i' j' : ZMod p} (h : altTr i j = altTr i' j') : i = i' ∧ j = j' := by
  have h0 := congrArg (fun f : Perm (ZMod p × Fin 2) => (f (0, 0)).1) h
  have h1 := congrArg (fun f : Perm (ZMod p × Fin 2) => (f (0, 1)).1) h
  simp [altTr_apply] at h0 h1
  exact ⟨h0, h1⟩

theorem altTr_pow (i j : ZMod p) (n : ℕ) :
    altTr i j ^ n = altTr ((n : ZMod p) * i) ((n : ZMod p) * j) := by
  induction n with
  | zero => simp [altTr_zero]
  | succ n ih =>
    rw [pow_succ, ih, altTr_mul]
    push_cast
    ring_nf

@[expose] def altMulPerm (l : (ZMod p)ˣ) : Perm (ZMod p) := Units.mulLeft l

theorem altMulPerm_apply (l : (ZMod p)ˣ) (x : ZMod p) : altMulPerm l x = l * x := rfl

theorem altMulPerm_one : altMulPerm (1 : (ZMod p)ˣ) = 1 := by
  refine Equiv.ext fun x => ?_
  simp [altMulPerm_apply]

theorem altMulPerm_mul (l m : (ZMod p)ˣ) : altMulPerm (l * m) = altMulPerm l * altMulPerm m := by
  refine Equiv.ext fun x => ?_
  simp [altMulPerm_apply, mul_assoc]

theorem altMulPerm_inv (l : (ZMod p)ˣ) : altMulPerm l⁻¹ = (altMulPerm l)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← altMulPerm_mul, inv_mul_cancel]
  refine Equiv.ext fun x => ?_
  simp [altMulPerm_apply]

@[expose] def altDg (l m : (ZMod p)ˣ) : Perm (ZMod p × Fin 2) :=
  prodCongrLeft fun s => altMulPerm (![l, m] s)

theorem altDg_apply (l m : (ZMod p)ˣ) (k : ZMod p) (s : Fin 2) :
    altDg l m (k, s) = ((![l, m] s : (ZMod p)ˣ) * k, s) := rfl

theorem altDg_mul_altTr (l m : (ZMod p)ˣ) (i j : ZMod p) :
    altDg l m * altTr i j = altTr ((l : ZMod p) * i) ((m : ZMod p) * j) * altDg l m := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altDg_apply, altTr_apply, Perm.mul_apply, mul_add]

@[expose] def altSwp : Perm (ZMod p × Fin 2) := prodCongrRight fun _ => Equiv.swap 0 1

theorem altSwp_mul_altTr (i j : ZMod p) : altSwp * altTr i j = altTr j i * altSwp := by
  refine Equiv.ext fun ⟨k, s⟩ => ?_
  fin_cases s <;> simp [altSwp, altTr_apply, Perm.mul_apply, prodCongrRight_apply]

theorem sign_altSwp (hp2 : p ≠ 2) : Perm.sign (altSwp : Perm (ZMod p × Fin 2)) = -1 := by
  rw [altSwp, Perm.sign_prodCongrRight, Finset.prod_const, Perm.sign_swap (by decide),
    Finset.card_univ, ZMod.card]
  exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).neg_one_pow

theorem sign_altDg (l m : (ZMod p)ˣ) :
    Perm.sign (altDg l m) = Perm.sign (altMulPerm l) * Perm.sign (altMulPerm m) := by
  rw [altDg, Perm.sign_prodCongrLeft, Fin.prod_univ_two]
  simp

theorem sign_mulLeft₀_of_orderOf' (hp2 : p ≠ 2) {g : ZMod p}
    (hg : orderOf g = p - 1) (hg0 : g ≠ 0) : Perm.sign (Equiv.mulLeft₀ g hg0) = -1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  set f := Equiv.mulLeft₀ g hg0 with hf
  have hfapp : ∀ y, f y = g * y := fun y => rfl
  have hsupp : f.support = Finset.univ.erase 0 := by
    ext y
    rw [Perm.mem_support, hfapp]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy h0
      apply hy
      rw [h0, mul_zero]
    · intro hy h
      have : (g - 1) * y = 0 := by rw [sub_mul, h, one_mul, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact hg1 (sub_eq_zero.mp h')
      · exact hy h'
  have hpow : ∀ n : ℕ, (f ^ n) 1 = g ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hfapp, pow_succ']
  have hcyc : f.IsCycle := by
    refine ⟨1, ?_, fun y hy => ?_⟩
    · rw [hfapp, mul_one]
      exact hg1
    · have hy0 : y ≠ 0 := by
        intro h0
        apply hy
        rw [hfapp, h0, mul_zero]
      let u : (ZMod p)ˣ := Units.mk0 g hg0
      have hu : orderOf u = p - 1 := by rw [← hg, ← orderOf_units]; rfl
      have hcard : Nat.card (Subgroup.zpowers u) = Nat.card (ZMod p)ˣ := by
        rw [Nat.card_zpowers, hu, Nat.card_eq_fintype_card, ZMod.card_units]
      have htop : Subgroup.zpowers u = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
      have hmem : Units.mk0 y hy0 ∈ Subgroup.zpowers u := by rw [htop]; exact Subgroup.mem_top _
      rw [← mem_powers_iff_mem_zpowers] at hmem
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, ?_⟩
      rw [zpow_natCast, hpow]
      have := congrArg Units.val hn
      simpa [u] using this
  rw [hcyc.sign, hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card]
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  have : p - 1 = 2 * k := by omega
  rw [this, pow_mul]
  simp


theorem exists_sign_altMulPerm_eq_neg_one (hp2 : p ≠ 2) :
    ∃ g : (ZMod p)ˣ, Perm.sign (altMulPerm g) = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_zmod]
  refine ⟨g, ?_⟩
  have := sign_mulLeft₀_of_orderOf' hp2 (g := (g : ZMod p)) (by rw [orderOf_units, hord]) g.ne_zero
  have h2 : altMulPerm g = Equiv.mulLeft₀ (g : ZMod p) g.ne_zero := Equiv.ext fun x => rfl
  rw [h2]
  exact this

theorem altTr_inv (i j : ZMod p) : (altTr i j)⁻¹ = altTr (-i) (-j) := by
  apply inv_eq_of_mul_eq_one_right
  rw [altTr_mul, add_neg_cancel, add_neg_cancel, altTr_zero]

@[expose] def altEtr : Subgroup (Perm (ZMod p × Fin 2)) where
  carrier := {x | ∃ i j : ZMod p, x = altTr i j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    exact ⟨i + i', j + j', altTr_mul i j i' j'⟩
  one_mem' := ⟨0, 0, altTr_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨-i, -j, altTr_inv i j⟩

theorem mem_altEtr {x : Perm (ZMod p × Fin 2)} : x ∈ (altEtr : Subgroup (Perm (ZMod p × Fin 2))) ↔
    ∃ i j : ZMod p, x = altTr i j := Iff.rfl

theorem altDg_conj (l m : (ZMod p)ˣ) (i j : ZMod p) :
    altDg l m * altTr i j * (altDg l m)⁻¹ = altTr ((l : ZMod p) * i) ((m : ZMod p) * j) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact altDg_mul_altTr l m i j

theorem altSwp_conj (i j : ZMod p) :
    (altSwp : Perm (ZMod p × Fin 2)) * altTr i j * altSwp⁻¹ = altTr j i := by
  rw [mul_inv_eq_iff_eq_mul]
  exact altSwp_mul_altTr i j

theorem altDg_mem_normalizer (l m : (ZMod p)ˣ) :
    altDg l m ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
      Set (Perm (ZMod p × Fin 2))) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨i, j, rfl⟩
  exact ⟨_, _, altDg_conj l m i j⟩

theorem altSwp_mem_normalizer :
    (altSwp : Perm (ZMod p × Fin 2)) ∈
      Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
        Set (Perm (ZMod p × Fin 2))) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨i, j, rfl⟩
  exact ⟨_, _, altSwp_conj i j⟩

theorem exists_odd_centralizer_altTr (hp2 : p ≠ 2) (i j : ZMod p) :
    ∃ h ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
      Set (Perm (ZMod p × Fin 2))), Perm.sign h = -1 ∧ h * altTr i j = altTr i j * h := by
  obtain ⟨g, hg⟩ := exists_sign_altMulPerm_eq_neg_one (p := p) hp2
  by_cases hj : j = 0
  · refine ⟨altDg 1 g, altDg_mem_normalizer 1 g, ?_, ?_⟩
    · rw [sign_altDg, hg, altMulPerm_one, map_one]
      simp
    · rw [altDg_mul_altTr, hj]
      simp
  by_cases hi : i = 0
  · refine ⟨altDg g 1, altDg_mem_normalizer g 1, ?_, ?_⟩
    · rw [sign_altDg, hg, altMulPerm_one, map_one]
      simp
    · rw [altDg_mul_altTr, hi]
      simp
  · let κ : (ZMod p)ˣ := Units.mk0 (i / j) (div_ne_zero hi hj)
    refine ⟨altDg κ κ⁻¹ * altSwp, mul_mem (altDg_mem_normalizer _ _) altSwp_mem_normalizer, ?_, ?_⟩
    · rw [map_mul, sign_altSwp hp2, sign_altDg, altMulPerm_inv, Perm.sign_inv]
      simp [Int.units_mul_self]
    · rw [mul_assoc, altSwp_mul_altTr, ← mul_assoc, altDg_mul_altTr, mul_assoc]
      have h1 : (κ : ZMod p) * j = i := by simp [κ, div_mul_cancel₀ _ hj]
      have h2 : ((κ⁻¹ : (ZMod p)ˣ) : ZMod p) * i = j := by
        simp [κ, inv_div, div_mul_cancel₀ _ hi]
      rw [h1, h2]

theorem exists_even_conj_altTr (hp2 : p ≠ 2) (i j : ZMod p) {σ : Perm (ZMod p × Fin 2)}
    (hσ : σ ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
      Set (Perm (ZMod p × Fin 2)))) :
    ∃ g ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
      Set (Perm (ZMod p × Fin 2))), Perm.sign g = 1 ∧
      g * altTr i j * g⁻¹ = σ * altTr i j * σ⁻¹ := by
  obtain ⟨h, hh, hsh, hcomm⟩ := exists_odd_centralizer_altTr hp2 i j
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact ⟨σ, hσ, h1, rfl⟩
  · refine ⟨σ * h, mul_mem hσ hh, by rw [map_mul, h1, hsh]; simp, ?_⟩
    have h2 : h * altTr i j * h⁻¹ = altTr i j := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    calc σ * h * altTr i j * (σ * h)⁻¹ = σ * (h * altTr i j * h⁻¹) * σ⁻¹ := by group
      _ = σ * altTr i j * σ⁻¹ := by rw [h2]

section Count

theorem ncard_zmod_nonzero : (({0}ᶜ : Set (ZMod p))).ncard = p - 1 := by
  rw [Set.compl_eq_univ_sdiff, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
    Nat.card_zmod]

theorem ncard_zmod_pairs :
    ((({0} : Set (ZMod p)) ×ˢ ({0}ᶜ : Set (ZMod p)) ∪ ({0}ᶜ : Set (ZMod p)) ×ˢ {0}).ncard =
      2 * (p - 1)) ∧
    ((({0}ᶜ : Set (ZMod p)) ×ˢ ({0}ᶜ : Set (ZMod p))).ncard = (p - 1) ^ 2) := by
  have hZ := ncard_zmod_nonzero (p := p)
  refine ⟨?_, ?_⟩
  · rw [Set.ncard_union_eq, Set.ncard_prod, Set.ncard_prod, hZ]
    · simp [two_mul]
    rw [Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨ha', hb'⟩
    exact ha' ha
  · rw [Set.ncard_prod, hZ, sq]

theorem ncard_altEtr_of_invariant (hp2 : p ≠ 2) (P : Set (Perm (ZMod p × Fin 2)))
    (hP : P ⊆ ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) : Set (Perm (ZMod p × Fin 2))) \ {1})
    (hinv : ∀ g : Perm (ZMod p × Fin 2), Perm.sign g = 1 →
      g ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod p × Fin 2))) :
        Set (Perm (ZMod p × Fin 2))) → ∀ t ∈ P, g * t * g⁻¹ ∈ P) :
    P.ncard = 0 ∨ P.ncard = p ^ 2 - 1 ∨ P.ncard = 2 * (p - 1) ∨ P.ncard = (p - 1) ^ 2 := by
  have hp : p.Prime := Fact.out
  set Q : Set (ZMod p × ZMod p) := {x | altTr x.1 x.2 ∈ P} with hQ
  have hQ0 : ((0 : ZMod p), (0 : ZMod p)) ∉ Q := by
    intro h
    have h1 : altTr (0 : ZMod p) 0 ∈ P := h
    rw [altTr_zero] at h1
    exact (hP h1).2 rfl
  have hinjtr : Function.Injective (fun x : ZMod p × ZMod p => altTr x.1 x.2) := by
    intro x y h
    obtain ⟨h1, h2⟩ := altTr_injective h
    exact Prod.ext h1 h2
  have hPQ : P = (fun x : ZMod p × ZMod p => altTr x.1 x.2) '' Q := by
    ext t
    constructor
    · intro ht
      obtain ⟨i, j, rfl⟩ := (hP ht).1
      exact ⟨(i, j), ht, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hPQcard : P.ncard = Q.ncard := by rw [hPQ, Set.ncard_image_of_injective _ hinjtr]
  have hQD : ∀ x ∈ Q, ∀ l m : (ZMod p)ˣ, ((l : ZMod p) * x.1, (m : ZMod p) * x.2) ∈ Q := by
    intro x hx l m
    obtain ⟨g, hg, hsg, hconj⟩ := exists_even_conj_altTr hp2 x.1 x.2 (altDg_mem_normalizer l m)
    have h1 := hinv g hsg hg _ hx
    rw [hconj, altDg_conj] at h1
    exact h1
  have hQS : ∀ x ∈ Q, (x.2, x.1) ∈ Q := by
    intro x hx
    obtain ⟨g, hg, hsg, hconj⟩ := exists_even_conj_altTr hp2 x.1 x.2 altSwp_mem_normalizer
    have h1 := hinv g hsg hg _ hx
    rw [hconj, altSwp_conj] at h1
    exact h1
  set Z : Set (ZMod p) := {0}ᶜ with hZ
  set I : Set (ZMod p × ZMod p) := ({0} ×ˢ Z) ∪ (Z ×ˢ {0}) with hI
  set II : Set (ZMod p × ZMod p) := Z ×ˢ Z with hII
  have hQsub : Q ⊆ I ∪ II := by
    rintro ⟨a, b⟩ hx
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · exact absurd (by rw [ha, hb] at hx; exact hx) hQ0
      · exact Or.inl (Or.inl ⟨ha, hb⟩)
    · by_cases hb : b = 0
      · exact Or.inl (Or.inr ⟨ha, hb⟩)
      · exact Or.inr ⟨ha, hb⟩
  have h10 : ∀ a c : ZMod p, a ≠ 0 → c ≠ 0 → (a, (0 : ZMod p)) ∈ Q → (c, (0 : ZMod p)) ∈ Q := by
    intro a c ha hc h
    have h1 := hQD _ h (Units.mk0 (c / a) (div_ne_zero hc ha)) 1
    simpa [div_mul_cancel₀ _ ha] using h1
  have hIQ : (Q ∩ I).Nonempty → I ⊆ Q := by
    rintro ⟨⟨x1, x2⟩, hxQ, hxI⟩
    obtain ⟨a, ha, ha0⟩ : ∃ a : ZMod p, a ≠ 0 ∧ (a, (0 : ZMod p)) ∈ Q := by
      rcases hxI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨x2, h2, ?_⟩
        have := hQS _ hxQ
        have hx1 : x1 = 0 := h1
        simpa [hx1] using this
      · refine ⟨x1, h1, ?_⟩
        have hx2 : x2 = 0 := h2
        simpa [hx2] using hxQ
    rintro ⟨c, d⟩ hy
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hc : c = 0 := h1
      have hd : d ≠ 0 := h2
      have := hQS _ (h10 a d ha hd ha0)
      simpa [hc] using this
    · have hc : c ≠ 0 := h1
      have hd : d = 0 := h2
      simpa [hd] using h10 a c ha hc ha0
  have hIIQ : (Q ∩ II).Nonempty → II ⊆ Q := by
    rintro ⟨x, hxQ, hxI⟩ ⟨c, d⟩ hy
    have h1 := hQD x hxQ (Units.mk0 (c / x.1) (div_ne_zero hy.1 hxI.1))
      (Units.mk0 (d / x.2) (div_ne_zero hy.2 hxI.2))
    simpa [div_mul_cancel₀ _ hxI.1, div_mul_cancel₀ _ hxI.2] using h1
  obtain ⟨hcI, hcII⟩ := ncard_zmod_pairs (p := p)
  have hdisj : Disjoint I II := by
    rw [Set.disjoint_left]
    rintro ⟨a, b⟩ (⟨ha, hb⟩ | ⟨ha, hb⟩) ⟨ha', hb'⟩
    · exact ha' ha
    · exact hb' hb
  have hcU : (I ∪ II).ncard = p ^ 2 - 1 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hcI, hcII]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    simp only [Nat.add_sub_cancel]
    have : (q + 1) ^ 2 - 1 = q ^ 2 + 2 * q := by
      have : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
      omega
    rw [this]
    ring
  rw [hPQcard]
  by_cases h1 : (Q ∩ I).Nonempty <;> by_cases h2 : (Q ∩ II).Nonempty
  · right; left
    have : Q = I ∪ II :=
      Set.Subset.antisymm hQsub (Set.union_subset (hIQ h1) (hIIQ h2))
    rw [this, hcU]
  · right; right; left
    have : Q = I := by
      refine Set.Subset.antisymm (fun x hx => ?_) (hIQ h1)
      rcases hQsub hx with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ h2
    rw [this, hcI]
  · right; right; right
    have : Q = II := by
      refine Set.Subset.antisymm (fun x hx => ?_) (hIIQ h2)
      rcases hQsub hx with h | h
      · exact absurd ⟨x, hx, h⟩ h1
      · exact h
    rw [this, hcII]
  · left
    have : Q = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      rcases hQsub hx with h | h
      · exact h1 ⟨x, hx, h⟩
      · exact h2 ⟨x, hx, h⟩
    rw [this, Set.ncard_empty]

end Count

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
