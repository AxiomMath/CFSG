module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsNormal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

section OrbitCount

variable {X : Type*} [Group X] [Finite X]

theorem card_orderOf_modEq (α : X ≃* X) {p : ℕ} [hp : Fact p.Prime]
    (hα : ∀ x : X, (⇑α)^[p] x = x) (o : ℕ) :
    Set.ncard {x : X | orderOf x = o} ≡ Set.ncard {x : X | orderOf x = o ∧ α x = x} [MOD p] := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let β : Type _ := {x : X // orderOf x = o}
  let _ : Fintype β := Fintype.ofFinite β
  let f : Function.End β := fun x => ⟨α x, by rw [MulEquiv.orderOf_eq]; exact x.2⟩
  have hiter : ∀ (n : ℕ) (x : β), ((f ^ n) x : X) = (⇑α)^[n] x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Function.iterate_succ_apply]
      exact ih (f x)
  have hf : f ^ p ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one]
    show ((f ^ p) x : X) = x
    rw [hiter, hα]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  have hc1 : Fintype.card β = Set.ncard {x : X | orderOf x = o} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq {x : X | orderOf x = o}
  have hc2 : Fintype.card f.fixedPoints = Set.ncard {x : X | orderOf x = o ∧ α x = x} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩,
      fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩, ?_, ?_⟩
    · intro x; rfl
    · intro x; rfl
  rw [hc1, hc2] at hmod
  exact hmod

theorem ncard_partition_orderOf (P : Set X) (h1 : (1 : X) ∈ P) (h8 : ∀ x ∈ P, x ^ 8 = 1) :
    P.ncard = 1 + {x ∈ P | orderOf x = 2}.ncard + {x ∈ P | orderOf x = 4}.ncard +
      {x ∈ P | orderOf x = 8}.ncard := by
  have hP : P = {1} ∪ {x ∈ P | orderOf x = 2} ∪ {x ∈ P | orderOf x = 4} ∪ {x ∈ P | orderOf x = 8} := by
    ext x
    constructor
    · intro hx
      have hdvd : orderOf x ∣ 8 := orderOf_dvd_of_pow_eq_one (h8 x hx)
      have hmem : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h | h
      · left; left; left
        exact orderOf_eq_one_iff.mp h
      · left; left; right; exact ⟨hx, h⟩
      · left; right; exact ⟨hx, h⟩
      · right; exact ⟨hx, h⟩
    · rintro (((h | h) | h) | h)
      · rw [Set.mem_singleton_iff.mp h]; exact h1
      · exact h.1
      · exact h.1
      · exact h.1
  have hfin : ∀ S : Set X, S.Finite := fun S => Set.toFinite S
  have d1 : Disjoint ({1} ∪ {x ∈ P | orderOf x = 2} ∪ {x ∈ P | orderOf x = 4} : Set X)
      {x ∈ P | orderOf x = 8} := by
    rw [Set.disjoint_left]
    rintro x ((hx | hx) | hx) h8'
    · have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
      subst hx1
      have := h8'.2
      rw [orderOf_one] at this
      omega
    · have := hx.2; have := h8'.2; omega
    · have := hx.2; have := h8'.2; omega
  have d2 : Disjoint ({1} ∪ {x ∈ P | orderOf x = 2} : Set X) {x ∈ P | orderOf x = 4} := by
    rw [Set.disjoint_left]
    rintro x (hx | hx) h4
    · have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
      subst hx1
      have := h4.2
      rw [orderOf_one] at this
      omega
    · have := hx.2; have := h4.2; omega
  have d3 : Disjoint ({1} : Set X) {x ∈ P | orderOf x = 2} := by
    rw [Set.disjoint_left]
    rintro x hx h2
    have hx1 : x = 1 := Set.mem_singleton_iff.mp hx
    subst hx1
    have := h2.2
    rw [orderOf_one] at this
    omega
  conv_lhs => rw [hP]
  rw [Set.ncard_union_eq d1 (hfin _) (hfin _), Set.ncard_union_eq d2 (hfin _) (hfin _),
    Set.ncard_union_eq d3 (hfin _) (hfin _), Set.ncard_singleton]

end OrbitCount

theorem prime_ge_five_le_32 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h32 : p ≤ 32) :
    p ∈ [5, 7, 11, 13, 17, 19, 23, 29, 31] := by
  interval_cases p <;> first | exact absurd hp (by decide) | simp

section Main

theorem no_odd_prime_aut_of_normal {X : Type} [Group X] [Finite X] (ι : X →* P10)
    (hinj : Function.Injective ι) (hP : ∀ x, ι x ∈ P0)
    (hnorm : ∀ g ∈ P0, ∀ x : X, ∃ y : X, ι y = g * ι x * g⁻¹) (α : X ≃* X) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hα : ∀ x : X, (⇑α)^[p] x = x) (hne : ∃ x, α x ≠ x) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup P10 := ι.range with hN
  have hNP : N ≤ P0 := by
    rintro _ ⟨x, rfl⟩
    exact hP x
  have hNnorm : ∀ g ∈ P0, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    rintro g hg _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hnorm g hg x
    exact ⟨y, hy⟩
  obtain ⟨t, ht, hcardN, hn2, hn4, hn8⟩ := normal_subgroup_type hNP hNnorm
  have hcardX : Nat.card X = t.1 := by
    rw [← hcardN]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hord : ∀ x, orderOf (ι x) = orderOf x := fun x => orderOf_injective ι hinj x
  have hcnt : ∀ o, Set.ncard {x : X | orderOf x = o} =
      Set.ncard {y : P10 | y ∈ N ∧ orderOf y = o} := by
    intro o
    have : {y : P10 | y ∈ N ∧ orderOf y = o} = ι '' {x : X | orderOf x = o} := by
      ext y
      constructor
      · rintro ⟨⟨x, rfl⟩, hy⟩
        exact ⟨x, by show orderOf x = o; rw [← hord x]; exact hy, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, rfl⟩, by show orderOf (ι x) = o; rw [hord x]; exact hx⟩
    rw [this, Set.ncard_image_of_injective _ hinj]
  have hnX2 : Set.ncard {x : X | orderOf x = 2} = t.2.1 := by rw [hcnt, hn2]
  have hnX4 : Set.ncard {x : X | orderOf x = 4} = t.2.2.1 := by rw [hcnt, hn4]
  have hnX8 : Set.ncard {x : X | orderOf x = 8} = t.2.2.2 := by rw [hcnt, hn8]
  have hexp : ∀ x : X, x ^ 8 = 1 := fun x => hinj (by rw [map_pow, map_one]; exact P0_pow_eight (hP x))
  have hpartX := ncard_partition_orderOf (Set.univ : Set X) (Set.mem_univ _) (fun x _ => hexp x)
  simp only [Set.sep_univ, Set.ncard_univ, hcardX, hnX2, hnX4, hnX8] at hpartX
  let F : Subgroup X := MonoidHom.eqLocus (α : X →* X) (MonoidHom.id X)
  have hFmem : ∀ x, x ∈ F ↔ α x = x := fun x => Iff.rfl
  have hFne : F ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hne
    exact hx ((hFmem x).1 (h ▸ Subgroup.mem_top x))
  have hFdvd : Nat.card F ∣ Nat.card X := Subgroup.card_subgroup_dvd_card F
  have hXdvd : Nat.card X ∣ 32 := by
    rw [hcardX, ← hcardN, ← card_P0]
    exact Subgroup.card_dvd_of_le hNP
  have hFlt : Nat.card F < Nat.card X := by
    have hle : Nat.card F ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos hFdvd
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd ((Subgroup.card_eq_iff_eq_top F).mp h) hFne
  obtain ⟨b, hb, hFb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card F ∣ 2 ^ 5 from (hFdvd.trans hXdvd))
  have hb6 : b < 6 := by omega
  have hpartF := ncard_partition_orderOf (F : Set X) F.one_mem
    (fun x _ => hexp x)
  have hFcard : (F : Set X).ncard = Nat.card F := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have hset : ∀ o, {x ∈ (F : Set X) | orderOf x = o} = {x : X | orderOf x = o ∧ α x = x} := by
    intro o
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, hFmem]
    exact and_comm
  rw [hFcard, hset 2, hset 4, hset 8] at hpartF
  have hoc2 := card_orderOf_modEq α hα 2
  have hoc4 := card_orderOf_modEq α hα 4
  have hoc8 := card_orderOf_modEq α hα 8
  rw [hnX2] at hoc2
  rw [hnX4] at hoc4
  rw [hnX8] at hoc8
  set f2 := Set.ncard {x : X | orderOf x = 2 ∧ α x = x} with hf2
  set f4 := Set.ncard {x : X | orderOf x = 4 ∧ α x = x} with hf4
  set f8 := Set.ncard {x : X | orderOf x = 8 ∧ α x = x} with hf8
  have hf2le : f2 ≤ t.2.1 := by
    rw [← hnX2]
    exact Set.ncard_le_ncard (fun x hx => hx.1) (Set.toFinite _)
  have hf4le : f4 ≤ t.2.2.1 := by
    rw [← hnX4]
    exact Set.ncard_le_ncard (fun x hx => hx.1) (Set.toFinite _)
  have hf8le : f8 ≤ t.2.2.2 := by
    rw [← hnX8]
    exact Set.ncard_le_ncard (fun x hx => hx.1) (Set.toFinite _)
  have hbounds := Core.p0Types_bound
  rw [List.all_eq_true] at hbounds
  have hbt := hbounds t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbt
  obtain ⟨⟨⟨ht32, ht2⟩, ht4⟩, ht8⟩ := hbt
  have hpow : Nat.card F = 2 ^ b := hFb
  have hFcard' : 2 ^ b = 1 + f2 + f4 + f8 := by rw [← hpow]; exact hpartF
  have hcongr2 : t.2.1 % p = f2 % p := hoc2
  have hcongr4 : t.2.2.1 % p = f4 % p := hoc4
  have hcongr8 : t.2.2.2 % p = f8 % p := hoc8
  have hf8eq : f8 = 2 ^ b - 1 - f2 - f4 := by omega
  have hinv : f2 = 0 → 2 ^ b = 1 := by
    intro h0
    by_contra hne1
    have h2dvd : 2 ∣ Nat.card F := by
      rw [hpow]
      have : 1 ≤ b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · exfalso; apply hne1; rw [h]; rfl
        · exact h
      exact dvd_pow_self 2 (by omega)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 h2dvd
    have hxo : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hmem : (x : X) ∈ {y : X | orderOf y = 2 ∧ α y = y} := ⟨hxo, (hFmem _).1 x.2⟩
    have : 0 < f2 := (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmem⟩
    omega
  have hord8 : f8 ≠ 0 → 8 ≤ 2 ^ b := by
    intro h0
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero h0
    have hxF : x ∈ F := (hFmem x).2 hx.2
    have hdvd : orderOf (⟨x, hxF⟩ : F) ∣ Nat.card F := orderOf_dvd_natCard _
    have : orderOf (⟨x, hxF⟩ : F) = 8 := by
      rw [← Subgroup.orderOf_coe]; exact hx.1
    rw [this, hpow] at hdvd
    exact Nat.le_of_dvd (by positivity) hdvd
  have hord4 : f4 ≠ 0 → 4 ≤ 2 ^ b := by
    intro h0
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero h0
    have hxF : x ∈ F := (hFmem x).2 hx.2
    have hdvd : orderOf (⟨x, hxF⟩ : F) ∣ Nat.card F := orderOf_dvd_natCard _
    have : orderOf (⟨x, hxF⟩ : F) = 4 := by
      rw [← Subgroup.orderOf_coe]; exact hx.1
    rw [this, hpow] at hdvd
    exact Nat.le_of_dvd (by positivity) hdvd
  have hpdvd : p ∣ t.1 - 2 ^ b := by
    have h1 : t.2.1 ≡ f2 [MOD p] := hoc2
    have h2 : t.2.2.1 ≡ f4 [MOD p] := hoc4
    have h3 : t.2.2.2 ≡ f8 [MOD p] := hoc8
    have hsum : t.1 = 1 + t.2.1 + t.2.2.1 + t.2.2.2 := hpartX
    have h4 : t.1 ≡ 2 ^ b [MOD p] := by
      rw [hsum, hFcard']
      exact ((Nat.ModEq.refl 1).add h1 |>.add h2).add h3
    have hlt : 2 ^ b < t.1 := by rw [← hpow, ← hcardX]; exact hFlt
    exact (Nat.modEq_iff_dvd' hlt.le).mp h4.symm
  have hp32 : p ≤ 32 := by
    have := Nat.le_of_dvd (by omega) hpdvd
    omega
  have hplist := prime_ge_five_le_32 hp hp5 hp32
  have hbad : Core.arithBad t p b f2 f4 = true := by
    unfold Core.arithBad
    rw [decide_eq_true_iff]
    refine ⟨?_, ?_, hf2le, hf4le, ?_, hcongr2, hcongr4, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hpow, ← hcardX]; exact hFlt
    · omega
    · exact Nat.mod_eq_zero_of_dvd hpdvd
    · rw [← hf8eq]; exact hcongr8
    · rw [← hf8eq]; exact hf8le
    · by_cases h : f2 = 0
      · left; exact hinv h
      · right; omega
    · by_cases h : f8 = 0
      · left; rw [← hf8eq]; exact h
      · right; exact hord8 h
    · by_cases h : f4 = 0
      · left; exact h
      · right; exact hord4 h
  have hexcl := Core.arith_excl
  rw [List.all_eq_true] at hexcl
  have h1 := hexcl t ht
  rw [List.all_eq_true] at h1
  have h2 := h1 p hplist
  rw [List.all_eq_true] at h2
  have h3 := h2 b (List.mem_range.mpr hb6)
  rw [List.all_eq_true] at h3
  have h4 := h3 f2 (List.mem_range.mpr (lt_of_le_of_lt hf2le ht2))
  rw [List.all_eq_true] at h4
  have h5 := h4 f4 (List.mem_range.mpr (lt_of_le_of_lt hf4le ht4))
  rw [hbad] at h5
  exact absurd h5 (by decide)

end Main

end CFSG.QuasithinUnique.A6Facts
