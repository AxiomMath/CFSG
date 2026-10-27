module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.AGLEmbedding

section Field

variable {p n : ℕ} [Fact p.Prime]

theorem addSubgroup_eq_bot_or_eq_top_of_mul_mem' {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    {γ : GaloisField p n} (hγ : ∀ d : ℕ, 0 < d → d < n → γ ^ (p ^ d - 1) ≠ 1)
    (hγ0 : γ ≠ 0) (W : AddSubgroup (GaloisField p n)) (hW : ∀ w ∈ W, γ * w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hp : p.Prime := Fact.out
  let _ : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hpow : ∀ {c : GaloisField p n}, (∀ w ∈ W, c * w ∈ W) →
      ∀ j : ℕ, ∀ w ∈ W, c ^ j * w ∈ W := by
    intro c hc j
    induction j with
    | zero => intro w hw; rwa [pow_zero, one_mul]
    | succ j ih => intro w hw; rw [pow_succ, mul_assoc]; exact ih _ (hc w hw)
  let A : Subfield (GaloisField p n) :=
    { carrier := {c | ∀ w ∈ W, c * w ∈ W}
      mul_mem' := fun {a b} ha hb w hw => by rw [mul_assoc]; exact ha _ (hb w hw)
      one_mem' := fun w hw => by rwa [one_mul]
      add_mem' := fun {a b} ha hb w hw => by rw [add_mul]; exact W.add_mem (ha w hw) (hb w hw)
      zero_mem' := fun w _ => by rw [zero_mul]; exact W.zero_mem
      neg_mem' := fun {a} ha w hw => by rw [neg_mul]; exact W.neg_mem (ha w hw)
      inv_mem' := fun a ha => by
        intro w hw
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero, zero_mul]; exact W.zero_mem
        · have hq := FiniteField.pow_card_sub_one_eq_one a ha0
          have hq2 : 1 < Fintype.card (GaloisField p n) := Fintype.one_lt_card
          have hinv : a⁻¹ = a ^ (Fintype.card (GaloisField p n) - 2) := by
            refine inv_eq_of_mul_eq_one_right ?_
            rw [← pow_succ', show Fintype.card (GaloisField p n) - 2 + 1 =
              Fintype.card (GaloisField p n) - 1 by omega, hq]
          rw [hinv]; exact hpow ha _ w hw }
  have hA : ∀ c, c ∈ A ↔ ∀ w ∈ W, c * w ∈ W := fun c => Iff.rfl
  obtain ⟨d, hdn, hd⟩ := (Nat.dvd_prime_pow hp).mp
    ((GaloisField.card p n hn) ▸ A.toSubring.toAddSubgroup.card_addSubgroup_dvd_card)
  let _ : Fintype A := Fintype.ofFinite A
  have hγd : γ ^ (p ^ d - 1) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨γ, (hA γ).mpr hW⟩ : A)
      (fun h => hγ0 (congrArg Subtype.val h))
    rw [← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card A = p ^ d := hd
    rw [h2] at h1
    simpa using congrArg Subtype.val h1
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := A)
    have h2 : Nat.card A = p ^ 0 := hd
    rw [h2, pow_zero] at h1
    exact lt_irrefl _ h1
  have hdn' : d = n := by
    by_contra hne
    exact hγ d (Nat.pos_of_ne_zero hd0) (lt_of_le_of_ne hdn hne) hγd
  have htop : A.toSubring.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hd, hdn', GaloisField.card p n hn])
  have hAall : ∀ c, c ∈ A := fun c => by
    have h : c ∈ A.toSubring.toAddSubgroup := htop ▸ AddSubgroup.mem_top c
    exact h
  rcases W.bot_or_exists_ne_zero with h | ⟨w₀, hw₀, hw₀0⟩
  · exact Or.inl h
  · refine Or.inr (eq_top_iff.mpr fun c _ => ?_)
    have h := (hA _).mp (hAall (c * w₀⁻¹)) w₀ hw₀
    rwa [mul_assoc, inv_mul_cancel₀ hw₀0, mul_one] at h

end Field

section Torus

variable {G : Type} [Group G] {p n : ℕ} [Fact p.Prime] {X : Subgroup G}

theorem conj_pow_of_torus_conj (φ : Multiplicative (GaloisField p n) ≃* X) {t : G}
    {c : GaloisField p n}
    (ht : ∀ a, t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd (c * Multiplicative.toAdd a)))
    (j : ℕ) (a : Multiplicative (GaloisField p n)) :
    t ^ j * (φ a : G) * (t ^ j)⁻¹ = φ (Multiplicative.ofAdd (c ^ j * Multiplicative.toAdd a)) := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    have h : ∀ x : G, t ^ j * t * x * (t ^ j * t)⁻¹ = t ^ j * (t * x * t⁻¹) * (t ^ j)⁻¹ :=
      fun x => by group
    rw [pow_succ, h, ht, ih, toAdd_ofAdd, ← mul_assoc, ← pow_succ]

theorem mem_normalizer_of_torus_conj (φ : Multiplicative (GaloisField p n) ≃* X) {t : G}
    {γ : GaloisField p n} (hγ : γ ≠ 0)
    (ht : ∀ a, t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a))) :
    t ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨a, ha⟩ := φ.surjective ⟨h, hh⟩
    have hha : (φ a : G) = h := congrArg Subtype.val ha
    rw [← hha, ht]
    exact (φ _).2
  · intro hh
    obtain ⟨b, hb⟩ := φ.surjective ⟨t * h * t⁻¹, hh⟩
    have hbh : (φ b : G) = t * h * t⁻¹ := congrArg Subtype.val hb
    have key := ht (Multiplicative.ofAdd (γ⁻¹ * Multiplicative.toAdd b))
    rw [toAdd_ofAdd, ← mul_assoc, mul_inv_cancel₀ hγ, one_mul, ofAdd_toAdd, hbh] at key
    rw [← mul_left_cancel (mul_right_cancel key)]
    exact (φ _).2

theorem eq_bot_or_eq_of_torus_conj' {p n : ℕ} [Fact p.Prime] {X : Subgroup G} (hn : n ≠ 0)
    (φ : Multiplicative (GaloisField p n) ≃* X) {t : G} {γ : GaloisField p n}
    (hγ : ∀ d : ℕ, 0 < d → d < n → γ ^ (p ^ d - 1) ≠ 1) (hγ0 : γ ≠ 0)
    (ht : ∀ a, t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a)))
    {Y : Subgroup G} (hYX : Y ≤ X) (hY : t ∈ Subgroup.normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = X := by
  let W : AddSubgroup (GaloisField p n) :=
    { carrier := {c | (φ (Multiplicative.ofAdd c) : G) ∈ Y}
      zero_mem' := by
        change (φ (Multiplicative.ofAdd 0) : G) ∈ Y
        rw [ofAdd_zero, map_one, Subgroup.coe_one]
        exact Y.one_mem
      add_mem' := fun {a b} ha hb => by
        change (φ (Multiplicative.ofAdd (a + b)) : G) ∈ Y
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        exact Y.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        change (φ (Multiplicative.ofAdd (-a)) : G) ∈ Y
        rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
        exact Y.inv_mem ha }
  have hWmem : ∀ c, c ∈ W ↔ (φ (Multiplicative.ofAdd c) : G) ∈ Y := fun c => Iff.rfl
  have hW : ∀ w ∈ W, γ * w ∈ W := fun w hw => by
    have h := (Subgroup.mem_normalizer_iff.mp hY (φ (Multiplicative.ofAdd w))).mp
      ((hWmem w).mp hw)
    rw [ht, toAdd_ofAdd] at h
    exact (hWmem _).mpr h
  rcases addSubgroup_eq_bot_or_eq_top_of_mul_mem' hn hγ hγ0 W hW with h | h
  · refine Or.inl ((Subgroup.eq_bot_iff_forall Y).mpr fun y hy => ?_)
    obtain ⟨a, ha⟩ := φ.surjective ⟨y, hYX hy⟩
    have hya : (φ a : G) = y := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W := by rwa [hWmem, ofAdd_toAdd, hya]
    rw [h, AddSubgroup.mem_bot] at haW
    have ha1 : a = 1 := Multiplicative.toAdd.injective (haW.trans toAdd_one.symm)
    rw [← hya, ha1, map_one, Subgroup.coe_one]
  · refine Or.inr (le_antisymm hYX fun x hx => ?_)
    obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W := h ▸ AddSubgroup.mem_top _
    rwa [hWmem, ofAdd_toAdd, hxa] at haW

theorem eq_bot_or_eq_of_torus_conj (hn : n ≠ 0) {r : ℕ} (hr : r.Prime)
    (hprim : ∀ k : ℕ, 0 < k → k < n → ¬ r ∣ p ^ k - 1) (φ : Multiplicative (GaloisField p n) ≃* X)
    {t : G} {γ : GaloisField p n} (hγr : γ ^ r = 1) (hγ1 : γ ≠ 1)
    (ht : ∀ a, t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a)))
    {Y : Subgroup G} (hYX : Y ≤ X) (hY : t ∈ Subgroup.normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = X := by
  have := Fact.mk hr
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow hr.ne_zero] at hγr
    exact zero_ne_one hγr
  refine eq_bot_or_eq_of_torus_conj' hn φ (fun d hd hdn hγd => ?_) hγ0 ht hYX hY
  exact hprim d hd hdn (orderOf_eq_prime hγr hγ1 ▸ orderOf_dvd_of_pow_eq_one hγd)

end Torus

theorem exists_ppd_torus_element {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 3 ≤ n) {B X : Subgroup G}
    (htorus : ∃ φ : Multiplicative (GaloisField p n) ≃* X, ∀ μ : (GaloisField p n)ˣ,
      ∃ t ∈ B, ∀ a : Multiplicative (GaloisField p n),
        t * (φ a : G) * t⁻¹ =
          φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a))) :
    ∃ (r : ℕ) (t : G), r.Prime ∧ n < r ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧
      t ∈ B ∧ t ∈ Subgroup.normalizer (X : Set G) ∧ IsPGroup r (Subgroup.zpowers t) ∧
      (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) ∧ (∃ x ∈ X, t * x * t⁻¹ ≠ x) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X := by
  obtain ⟨φ, htor⟩ := htorus
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨r, hr, hrdvd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one hp3 hn
  have := Fact.mk hr
  have hpr : (p : ZMod r) ^ n = 1 :=
    (CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos n).mp hrdvd
  have hord : orderOf (p : ZMod r) = n := by
    rw [orderOf_eq_iff (by omega)]
    exact ⟨hpr, fun k hk hk0 h => hprim k hk0 hk
      ((CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff hp.pos k).mpr h)⟩
  have hp0 : (p : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hpr
    exact zero_ne_one hpr
  have hrn : n < r := by
    have h := Nat.le_of_dvd (by have := hr.two_le; omega)
      (hord ▸ ZMod.orderOf_dvd_card_sub_one hp0)
    omega
  have hrp : r ≠ p := by
    rintro rfl
    exact hp0 (ZMod.natCast_self r)
  have hrp1 : ¬ r ∣ p - 1 := by
    have h := hprim 1 one_pos (by omega)
    rwa [pow_one] at h
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p n)ˣ) r
    (by rw [Nat.card_units, GaloisField.card p n (by omega)]; exact hrdvd)
  have hζr : (ζ : GaloisField p n) ^ r = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hζ, pow_orderOf_eq_one, Units.val_one]
  have hμ2 : ((ζ ^ ((r + 1) / 2) : (GaloisField p n)ˣ) : GaloisField p n) ^ 2 = ζ := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.mp (hr.odd_of_ne_two (by omega)).add_one), pow_succ,
      hζr, one_mul]
  obtain ⟨t₀, ht₀B, ht₀⟩ := htor (ζ ^ ((r + 1) / 2))
  rw [hμ2] at ht₀
  obtain ⟨e, m, hm, hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t₀).ne' r hr.one_lt.ne'
  have ht := conj_pow_of_torus_conj φ ht₀ m
  have hβk : ∀ k : ℕ, ((ζ : GaloisField p n) ^ m) ^ k = 1 ↔ r ∣ k := by
    intro k
    rw [← pow_mul, ← Units.val_pow_eq_pow_val, Units.val_eq_one, ← orderOf_dvd_iff_pow_eq_one,
      hζ, hr.dvd_mul]
    exact or_iff_right hm
  have hβ0 : (ζ : GaloisField p n) ^ m ≠ 0 := by
    rw [← Units.val_pow_eq_pow_val]
    exact Units.ne_zero _
  have htr : (t₀ ^ m) ^ (r ^ e) = 1 := by rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
  refine ⟨r, t₀ ^ m, hr, hrn, by omega, by omega, hrp, hrp1, B.pow_mem ht₀B m,
    mem_normalizer_of_torus_conj φ hβ0 ht, ?_, fun x hx => ?_, ?_, fun k hk Y hYX hY => ?_⟩
  · obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one htr)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  · obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : G) = x := congrArg Subtype.val ha
    rw [← hxa, conj_pow_of_torus_conj φ ht r, (hβk r).mpr dvd_rfl, one_mul, ofAdd_toAdd]
  · refine ⟨φ (Multiplicative.ofAdd 1), (φ _).2, fun h => ?_⟩
    rw [ht, toAdd_ofAdd, mul_one] at h
    have h1 := Multiplicative.ofAdd.injective (φ.injective (Subtype.ext h))
    exact hr.not_dvd_one ((hβk 1).mp (by rw [pow_one]; exact h1))
  · refine eq_bot_or_eq_of_torus_conj (by omega) hr hprim φ ?_ (fun h => hk ((hβk k).mp h))
      (conj_pow_of_torus_conj φ ht k) hYX hY
    rw [← pow_mul]
    exact (hβk (k * r)).mpr (dvd_mul_left r k)

theorem stmtPPDElement : StmtPPDElement :=
  fun h => exists_ppd_torus_element h.ph3.ne_two h.three_le h.torus

end CFSG.AGLEmbedding
