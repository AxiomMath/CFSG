module

public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.LieType.Steinberg.CentralExt.Pairing

open Function

variable {k C : Type*} [Field k] [AddCommGroup C]

@[expose] def multRing (c : k →+ k →+ C) : Subring (k × k) where
  carrier := {m | ∀ s t, c (m.1 * s) t = c s (m.2 * t)}
  mul_mem' := by
    intro a b ha hb s t
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [mul_assoc, ha, hb, mul_comm a.2 b.2, mul_assoc]
  one_mem' := by intro s t; simp
  add_mem' := by
    intro a b ha hb s t
    simp only [Prod.fst_add, Prod.snd_add, add_mul, map_add, AddMonoidHom.add_apply]
    rw [ha s t, hb s t]
  zero_mem' := by intro s t; simp
  neg_mem' := by
    intro a ha s t
    simp only [Prod.fst_neg, Prod.snd_neg, neg_mul, map_neg, AddMonoidHom.neg_apply]
    rw [ha s t]

theorem mem_multRing {c : k →+ k →+ C} {m : k × k} :
    m ∈ multRing c ↔ ∀ s t, c (m.1 * s) t = c s (m.2 * t) := Iff.rfl

theorem skew_of_alternating {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) (s t : k) :
    c s t = - c t s := by
  have h := halt (s + t)
  simp only [map_add, AddMonoidHom.add_apply, halt s, halt t, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

theorem swap_mem_multRing {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) {m : k × k}
    (hm : m ∈ multRing c) : m.swap ∈ multRing c := by
  intro s t
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [skew_of_alternating halt, ← hm t s, ← skew_of_alternating halt]

theorem inv_mem_multRing {c : k →+ k →+ C} {a : k} (ha : a ≠ 0)
    (hinv : ∀ s t, c (a * s) (a * t) = c s t) : (a, a⁻¹) ∈ multRing c := by
  intro s t
  have := hinv s (a⁻¹ * t)
  rwa [← mul_assoc, mul_inv_cancel₀ ha, one_mul] at this

theorem eq_of_mem_multRing {c : k →+ k →+ C} (hc : c ≠ 0) {m m' : k × k}
    (hm : m ∈ multRing c) (hm' : m' ∈ multRing c) (h : m.1 = m'.1) : m = m' := by
  have hd : m - m' ∈ multRing c := sub_mem hm hm'
  by_contra hne
  have h2 : (m - m').2 ≠ 0 := by
    intro h2
    apply hne
    refine Prod.ext h ?_
    simpa [sub_eq_zero] using h2
  apply hc
  ext s t
  have := hd s ((m - m').2⁻¹ * t)
  rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul, Prod.fst_sub, h, sub_self, zero_mul,
    map_zero, AddMonoidHom.zero_apply] at this
  simpa using this.symm

@[expose] def swapHom {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) : multRing c →+* multRing c where
  toFun m := ⟨m.1.swap, swap_mem_multRing halt m.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem swapHom_involutive {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) (m : multRing c) :
    swapHom halt (swapHom halt m) = m := rfl

section Finite

variable [Finite k]

theorem inv_eq_pow_of_ne_zero {x : k} (hx : x ≠ 0) : x⁻¹ = x ^ (Nat.card k - 2) := by
  have : Fintype k := Fintype.ofFinite k
  have hq : 2 ≤ Nat.card k := by
    have := Fintype.one_lt_card (α := k)
    rw [Fintype.card_eq_nat_card] at this
    omega
  have h1 : x ^ (Nat.card k - 1) = 1 := by
    rw [← Fintype.card_eq_nat_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_succ', show Nat.card k - 2 + 1 = Nat.card k - 1 by omega, h1]

@[expose] def multField (c : k →+ k →+ C) : Subfield k where
  toSubring := (multRing c).map (RingHom.fst k k)
  inv_mem' := by
    intro x hx
    by_cases h0 : x = 0
    · rw [h0, inv_zero]
      exact Subring.zero_mem _
    · rw [inv_eq_pow_of_ne_zero h0]
      exact Subring.pow_mem _ hx _

theorem mem_multField {c : k →+ k →+ C} {x : k} :
    x ∈ multField c ↔ ∃ m ∈ multRing c, m.1 = x := by
  change x ∈ (multRing c).map (RingHom.fst k k) ↔ _
  simp [Subring.mem_map]

@[expose] def fstHom (c : k →+ k →+ C) : multRing c →+* multField c where
  toFun m := ⟨m.1.1, mem_multField.2 ⟨m.1, m.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fstHom_bijective {c : k →+ k →+ C} (hc : c ≠ 0) : Function.Bijective (fstHom c) := by
  refine ⟨fun m m' h => Subtype.ext (eq_of_mem_multRing hc m.2 m'.2 ?_), fun x => ?_⟩
  · exact congrArg Subtype.val h
  · obtain ⟨m, hm, hmx⟩ := mem_multField.1 x.2
    exact ⟨⟨m, hm⟩, Subtype.ext hmx⟩

@[expose] noncomputable def multAut {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) (hc : c ≠ 0) :
    multField c ≃+* multField c :=
  let e := RingEquiv.ofBijective (fstHom c) (fstHom_bijective hc)
  let sw : multRing c ≃+* multRing c :=
    { swapHom halt with
      invFun := swapHom halt
      left_inv := swapHom_involutive halt
      right_inv := swapHom_involutive halt }
  e.symm.trans (sw.trans e)

theorem multAut_apply {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) (hc : c ≠ 0) {m : k × k}
    (hm : m ∈ multRing c) :
    (multAut halt hc ⟨m.1, mem_multField.2 ⟨m, hm, rfl⟩⟩ : k) = m.2 := by
  let e := RingEquiv.ofBijective (fstHom c) (fstHom_bijective hc)
  have he : e.symm ⟨m.1, mem_multField.2 ⟨m, hm, rfl⟩⟩ = ⟨m, hm⟩ :=
    e.symm_apply_eq.2 rfl
  simp only [multAut, RingEquiv.trans_apply]
  rw [he]
  rfl

theorem pairing_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {c : k →+ k →+ C}
    (halt : ∀ s, c s s = 0) (S : Set k) (hS0 : ∀ a ∈ S, a ≠ 0)
    (hinv : ∀ a ∈ S, ∀ s t, c (a * s) (a * t) = c s t)
    (hfrob : ∀ i : ℕ, ∃ a ∈ S, a ^ (p ^ i + 1) ≠ 1) : c = 0 := by
  by_contra hc
  let F := multField c
  have : CharP F p := ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff k p n]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)⟩
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  let φ := multAut halt hc
  let g : F ≃ₐ[ZMod p] F := AlgEquiv.ofRingEquiv (f := φ) fun x =>
    congrArg (fun f : ZMod p →+* F => f x)
      (Subsingleton.elim (φ.toRingHom.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F))
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F g
  obtain ⟨a, haS, ha⟩ := hfrob i
  have hm : (a, a⁻¹) ∈ multRing c := inv_mem_multRing (hS0 a haS) (hinv a haS)
  have haF : a ∈ F := mem_multField.2 ⟨(a, a⁻¹), hm, rfl⟩
  have h1 : (φ ⟨a, haF⟩ : k) = a⁻¹ := multAut_apply halt hc hm
  have h2 : (g ⟨a, haF⟩ : k) = ((⟨a, haF⟩ : F) ^ (Nat.card (ZMod p) ^ i) : F) :=
    congrArg Subtype.val (hi ⟨a, haF⟩)
  have h3 : a⁻¹ = a ^ (p ^ i) := by
    rw [← h1]
    rw [Nat.card_zmod] at h2
    exact h2.trans (by simp)
  apply ha
  rw [pow_succ, ← h3, inv_mul_cancel₀ (hS0 a haS)]

theorem pairing_eq_zero_of_card_eq_prime (p : ℕ) [Fact p.Prime] [CharP k p]
    (hk : Nat.card k = p) {c : k →+ k →+ C} (halt : ∀ s, c s s = 0) : c = 0 := by
  have : Fintype k := Fintype.ofFinite k
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl p) k) := by
    have hinj : Function.Injective (ZMod.castHom (dvd_refl p) k) := (ZMod.castHom _ k).injective
    have hcard : Fintype.card (ZMod p) = Fintype.card k := by
      rw [ZMod.card, Fintype.card_eq_nat_card, hk]
    exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩ |>.2
  ext s t
  obtain ⟨m, rfl⟩ := hsurj s
  obtain ⟨n, rfl⟩ := hsurj t
  simp only [ZMod.castHom_apply, AddMonoidHom.zero_apply]
  rw [← ZMod.natCast_zmod_val m, ← ZMod.natCast_zmod_val n, ZMod.cast_natCast (dvd_refl p),
    ZMod.cast_natCast (dvd_refl p), ← nsmul_one m.val, ← nsmul_one n.val, map_nsmul, map_nsmul,
    AddMonoidHom.nsmul_apply, halt, smul_zero, smul_zero]

theorem pow_prime_pow_mod (p : ℕ) [Fact p.Prime] [CharP k p] {f : ℕ}
    (hf : Nat.card k = p ^ f) (x : k) (i : ℕ) : x ^ (p ^ i) = x ^ (p ^ (i % f)) := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = p ^ f := by rw [Fintype.card_eq_nat_card, hf]
  conv_lhs => rw [← Nat.div_add_mod i f, pow_add, pow_mul, pow_mul, ← hq,
    FiniteField.pow_card_pow]

theorem exists_sq_pow_ne_one (p : ℕ) [hp : Fact p.Prime] [CharP k p] (hq4 : Nat.card k ≠ 4)
    (hq9 : Nat.card k ≠ 9) (hnp : Nat.card k ≠ p) (i : ℕ) :
    ∃ a ∈ {a : k | ∃ u : k, u ≠ 0 ∧ a = u ^ 2}, a ^ (p ^ i + 1) ≠ 1 := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨f, -, hcard⟩ := FiniteField.card k p
  have hcardN : Nat.card k = p ^ (f : ℕ) := by rw [← Fintype.card_eq_nat_card, hcard]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf g = p ^ (f : ℕ) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcardN]
  refine ⟨(g : k) ^ 2, ⟨g, g.ne_zero, rfl⟩, fun h => ?_⟩
  set j := i % (f : ℕ) with hj
  have hjf : j < (f : ℕ) := Nat.mod_lt _ f.pos
  have h' : g ^ (2 * (p ^ j + 1)) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul, pow_add, pow_one,
      ← pow_prime_pow_mod p hcardN, ← pow_succ, h]
  have hdvd : p ^ (f : ℕ) - 1 ∣ 2 * (p ^ j + 1) := hord ▸ orderOf_dvd_of_pow_eq_one h'
  have hp2 : 2 ≤ p := hp.out.two_le
  set P := p ^ ((f : ℕ) - 1) with hP
  have hqP : p ^ (f : ℕ) = p * P := by
    rw [hP, ← pow_succ', Nat.sub_add_cancel f.pos]
  have hjP : p ^ j ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hle : p ^ (f : ℕ) - 1 ≤ 2 * (p ^ j + 1) := Nat.le_of_dvd (by positivity) hdvd
  have hP1' : P ≠ 1 := by
    intro h1
    apply hnp
    rw [hcardN, hqP, h1, mul_one]
  rcases Nat.lt_or_ge p 3 with hp3 | hp3
  ·
    have hp2' : p = 2 := by omega
    subst hp2'
    have hodd : Nat.Coprime (2 ^ (f : ℕ) - 1) 2 := by
      rw [Nat.coprime_two_right]
      exact Nat.Even.sub_odd (Nat.one_le_two_pow) (by
        rw [Nat.even_pow]; exact ⟨even_two, f.ne_zero⟩) odd_one
    have hdvd' : 2 ^ (f : ℕ) - 1 ∣ 2 ^ j + 1 := hodd.dvd_of_dvd_mul_left hdvd
    have hle' : 2 ^ (f : ℕ) - 1 ≤ 2 ^ j + 1 := Nat.le_of_dvd (by positivity) hdvd'
    have hP2 : P = 2 := by omega
    apply hq4
    rw [hcardN, hqP, hP2]
  · rcases Nat.lt_or_ge p 5 with hp5 | hp5
    · have hp3' : p = 3 := by
        rcases (show p = 3 ∨ p = 4 by omega) with h3 | h4
        · exact h3
        · exact absurd (h4 ▸ hp.out) (by decide)
      subst hp3'
      have hP3 : P ≤ 3 := by omega
      have hP3' : P = 3 := by
        rcases (show P = 1 ∨ P = 2 ∨ P = 3 by omega) with h | h | h
        · exact absurd h hP1'
        ·
          exfalso
          have : (2 : ℕ) ∣ 3 ^ ((f : ℕ) - 1) := ⟨1, by rw [← hP, h]⟩
          exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two this) (by decide)
        · exact h
      apply hq9
      rw [hcardN, hqP, hP3']
    · exfalso
      have : p * P ≤ 2 * P + 3 := by omega
      have : 5 * P ≤ p * P := Nat.mul_le_mul_right _ hp5
      omega

theorem pairing_eq_zero_of_sq (p : ℕ) [Fact p.Prime] [CharP k p] (hq4 : Nat.card k ≠ 4)
    (hq9 : Nat.card k ≠ 9) {c : k →+ k →+ C} (halt : ∀ s, c s s = 0)
    (hinv : ∀ u : k, u ≠ 0 → ∀ s t, c (u ^ 2 * s) (u ^ 2 * t) = c s t) : c = 0 := by
  by_cases hnp : Nat.card k = p
  · exact pairing_eq_zero_of_card_eq_prime p hnp halt
  refine pairing_eq_zero p halt {a : k | ∃ u : k, u ≠ 0 ∧ a = u ^ 2} ?_ ?_
    (exists_sq_pow_ne_one p hq4 hq9 hnp)
  · rintro a ⟨u, hu, rfl⟩
    exact pow_ne_zero 2 hu
  · rintro a ⟨u, hu, rfl⟩
    exact hinv u hu

theorem exists_pow_ne_one (p : ℕ) [hp : Fact p.Prime] [CharP k p] (hq4 : Nat.card k ≠ 4)
    (hnp : Nat.card k ≠ p) (i : ℕ) : ∃ a ∈ {a : k | a ≠ 0}, a ^ (p ^ i + 1) ≠ 1 := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨f, -, hcard⟩ := FiniteField.card k p
  have hcardN : Nat.card k = p ^ (f : ℕ) := by rw [← Fintype.card_eq_nat_card, hcard]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf g = p ^ (f : ℕ) - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcardN]
  refine ⟨(g : k), g.ne_zero, fun h => ?_⟩
  set j := i % (f : ℕ) with hj
  have hjf : j < (f : ℕ) := Nat.mod_lt _ f.pos
  have h' : g ^ (p ^ j + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_add, pow_one,
      ← pow_prime_pow_mod p hcardN, ← pow_succ, h]
  have hdvd : p ^ (f : ℕ) - 1 ∣ p ^ j + 1 := hord ▸ orderOf_dvd_of_pow_eq_one h'
  have hp2 : 2 ≤ p := hp.out.two_le
  set P := p ^ ((f : ℕ) - 1) with hP
  have hqP : p ^ (f : ℕ) = p * P := by
    rw [hP, ← pow_succ', Nat.sub_add_cancel f.pos]
  have hjP : p ^ j ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hle : p ^ (f : ℕ) - 1 ≤ p ^ j + 1 := Nat.le_of_dvd (by positivity) hdvd
  have hP1 : P ≠ 1 := by
    intro h1
    apply hnp
    rw [hcardN, hqP, h1, mul_one]
  have hP2 : 2 ≤ P := by
    have : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
    omega
  have hpP : p * P ≤ P + 2 := by omega
  have hp2' : p = 2 := by
    by_contra hne
    have : 3 * P ≤ p * P := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hp2'
  have hP2' : P = 2 := by omega
  apply hq4
  rw [hcardN, hqP, hP2']

theorem pairing_eq_zero_of_units (p : ℕ) [Fact p.Prime] [CharP k p] (hq4 : Nat.card k ≠ 4)
    {c : k →+ k →+ C} (halt : ∀ s, c s s = 0)
    (hinv : ∀ u : k, u ≠ 0 → ∀ s t, c (u * s) (u * t) = c s t) : c = 0 := by
  by_cases hnp : Nat.card k = p
  · exact pairing_eq_zero_of_card_eq_prime p hnp halt
  exact pairing_eq_zero p halt {a : k | a ≠ 0} (fun _ ha => ha) (fun a ha => hinv a ha)
    (exists_pow_ne_one p hq4 hnp)

end Finite

end CFSG.LieType.Steinberg.CentralExt.Pairing
