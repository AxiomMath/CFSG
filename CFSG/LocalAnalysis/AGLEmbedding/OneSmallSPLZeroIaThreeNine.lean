module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeLift
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Field

variable {p : ℕ} [Fact p.Prime]

theorem addSubgroup_eq_bot_or_eq_top_of_mul_mem_two {γ : GaloisField p 2} (hγ : γ ^ p ≠ γ)
    (W : AddSubgroup (GaloisField p 2)) (hW : ∀ w ∈ W, γ * w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hp : p.Prime := Fact.out
  let _ : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hpow : ∀ {c : GaloisField p 2}, (∀ w ∈ W, c * w ∈ W) →
      ∀ j : ℕ, ∀ w ∈ W, c ^ j * w ∈ W := by
    intro c hc j
    induction j with
    | zero => intro w hw; rwa [pow_zero, one_mul]
    | succ j ih => intro w hw; rw [pow_succ, mul_assoc]; exact ih _ (hc w hw)
  let A : Subfield (GaloisField p 2) :=
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
          have hq2 : 1 < Fintype.card (GaloisField p 2) := Fintype.one_lt_card
          have hinv : a⁻¹ = a ^ (Fintype.card (GaloisField p 2) - 2) := by
            refine inv_eq_of_mul_eq_one_right ?_
            rw [← pow_succ', show Fintype.card (GaloisField p 2) - 2 + 1 =
              Fintype.card (GaloisField p 2) - 1 by omega, hq]
          rw [hinv]; exact hpow ha _ w hw }
  have hA : ∀ c, c ∈ A ↔ ∀ w ∈ W, c * w ∈ W := fun c => Iff.rfl
  obtain ⟨d, hdn, hd⟩ := (Nat.dvd_prime_pow hp).mp
    ((GaloisField.card p 2 (by norm_num)) ▸ A.toSubring.toAddSubgroup.card_addSubgroup_dvd_card)
  let _ : Fintype A := Fintype.ofFinite A
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := A)
    have h2 : Nat.card A = p ^ 0 := hd
    rw [h2, pow_zero] at h1
    exact lt_irrefl _ h1
  have hd2 : d = 2 := by
    by_contra hne
    have hd1 : d = 1 := by omega
    have h1 := FiniteField.pow_card (⟨γ, (hA γ).mpr hW⟩ : A)
    rw [← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card A = p := by rw [show Nat.card A = p ^ d from hd, hd1, pow_one]
    rw [h2] at h1
    exact hγ (by simpa using congrArg Subtype.val h1)
  have htop : A.toSubring.toAddSubgroup = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [hd, hd2, GaloisField.card p 2 (by norm_num)])
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

variable {Y : Type*} [Group Y] {F : Type*} [Field F] {X : Subgroup Y}

theorem eq_bot_or_eq_of_torus_conj_two {p : ℕ} [Fact p.Prime]
    (φ : Multiplicative (GaloisField p 2) ≃* X) {t : Y} {γ : GaloisField p 2} (hγ : γ ^ p ≠ γ)
    (ht : ∀ a, t * (φ a : Y) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a)))
    {Y₀ : Subgroup Y} (hYX : Y₀ ≤ X) (hY : t ∈ Subgroup.normalizer (Y₀ : Set Y)) :
    Y₀ = ⊥ ∨ Y₀ = X := by
  let W : AddSubgroup (GaloisField p 2) :=
    { carrier := {c | (φ (Multiplicative.ofAdd c) : Y) ∈ Y₀}
      zero_mem' := by
        change (φ (Multiplicative.ofAdd 0) : Y) ∈ Y₀
        rw [ofAdd_zero, map_one, Subgroup.coe_one]
        exact Y₀.one_mem
      add_mem' := fun {a b} ha hb => by
        change (φ (Multiplicative.ofAdd (a + b)) : Y) ∈ Y₀
        rw [ofAdd_add, map_mul, Subgroup.coe_mul]
        exact Y₀.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        change (φ (Multiplicative.ofAdd (-a)) : Y) ∈ Y₀
        rw [ofAdd_neg, map_inv, Subgroup.coe_inv]
        exact Y₀.inv_mem ha }
  have hWmem : ∀ c, c ∈ W ↔ (φ (Multiplicative.ofAdd c) : Y) ∈ Y₀ := fun c => Iff.rfl
  have hW : ∀ w ∈ W, γ * w ∈ W := fun w hw => by
    have h := (Subgroup.mem_normalizer_iff.mp hY (φ (Multiplicative.ofAdd w))).mp
      ((hWmem w).mp hw)
    rw [ht, toAdd_ofAdd] at h
    exact (hWmem _).mpr h
  rcases addSubgroup_eq_bot_or_eq_top_of_mul_mem_two hγ W hW with h | h
  · refine Or.inl ((Subgroup.eq_bot_iff_forall Y₀).mpr fun y hy => ?_)
    obtain ⟨a, ha⟩ := φ.surjective ⟨y, hYX hy⟩
    have hya : (φ a : Y) = y := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W := by rwa [hWmem, ofAdd_toAdd, hya]
    rw [h, AddSubgroup.mem_bot] at haW
    have ha1 : a = 1 := Multiplicative.toAdd.injective (haW.trans toAdd_one.symm)
    rw [← hya, ha1, map_one, Subgroup.coe_one]
  · refine Or.inr (le_antisymm hYX fun x hx => ?_)
    obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
    have hxa : (φ a : Y) = x := congrArg Subtype.val ha
    have haW : Multiplicative.toAdd a ∈ W := h ▸ AddSubgroup.mem_top _
    rwa [hWmem, ofAdd_toAdd, hxa] at haW

theorem conj_pow_torus (φ : Multiplicative F ≃* X) {t : Y} {γ : F}
    (ht : ∀ a, t * (φ a : Y) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a)))
    (k : ℕ) : ∀ a, t ^ k * (φ a : Y) * (t ^ k)⁻¹ =
      φ (Multiplicative.ofAdd (γ ^ k * Multiplicative.toAdd a)) := by
  induction k with
  | zero => intro a; simp
  | succ k ih =>
    intro a
    calc t ^ (k + 1) * (φ a : Y) * (t ^ (k + 1))⁻¹ =
          t * (t ^ k * (φ a : Y) * (t ^ k)⁻¹) * t⁻¹ := by group
      _ = φ (Multiplicative.ofAdd (γ ^ (k + 1) * Multiplicative.toAdd a)) := by
        rw [ih a, ht, toAdd_ofAdd, ← mul_assoc, ← pow_succ']

theorem mem_normalizer_of_torus (φ : Multiplicative F ≃* X) {t : Y} {γ : F} (hγ : γ ≠ 0)
    (ht : ∀ a, t * (φ a : Y) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a))) :
    t ∈ Subgroup.normalizer (X : Set Y) := by
  have hr : (X.subtype.comp φ.toMonoidHom).range = X := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      obtain ⟨a, ha⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨a, by simp [ha]⟩
  have := mem_normalizer_range_of_mult (X.subtype.comp φ.toMonoidHom) hγ ht
  rwa [hr] at this

end Torus

theorem exists_gen_gf9 : ∃ μ : (GaloisField 3 2)ˣ, ∀ k : ℕ, ¬ 4 ∣ k →
    ((μ : GaloisField 3 2) ^ k) ^ 3 ≠ (μ : GaloisField 3 2) ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField 3 2)ˣ)
  have hcard : Nat.card (GaloisField 3 2)ˣ = 8 := by
    rw [Nat.card_units, GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hord : orderOf g = 8 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g, fun k hk h => hk ?_⟩
  have h2 : (g ^ k) ^ 3 = g ^ k := Units.ext (by push_cast; exact h)
  have h3 : g ^ (2 * k) * g ^ k = g ^ k := by
    rw [← pow_add, show 2 * k + k = k * 3 by ring, pow_mul]
    exact h2
  have h1 : g ^ (2 * k) = 1 := mul_right_cancel (h3.trans (one_mul _).symm)
  have h4 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h4
  omega

variable {G : Type} [Group G]

theorem mside_torus_two {M X : Subgroup G} (hXM : X ≤ M)
    (φ : Multiplicative (GaloisField 3 2) ≃* X) {t : G} (htM : t ∈ M) {γ : GaloisField 3 2}
    (hγ : ∀ k : ℕ, ¬ 4 ∣ k → (γ ^ k) ^ 3 ≠ γ ^ k)
    (ht : ∀ a, t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd (γ * Multiplicative.toAdd a))) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∈
        Subgroup.normalizer (barM M X : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      ∀ k : ℕ, ¬ 4 ∣ k → ∀ Y₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Y₀ ≤ barM M X →
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩) ^ k ∈
          Subgroup.normalizer (Y₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        Y₀ = ⊥ ∨ Y₀ = barM M X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hγ0 : γ ≠ 0 := by
    intro h0
    apply hγ 1 (by norm_num)
    rw [h0]
    norm_num
  have htX : t ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_torus φ hγ0 ht
  refine ⟨mem_normalizer_barM htM htX, fun k hk Y₀ hY₀ hYk => ?_⟩
  have htkM : t ^ k ∈ M := M.pow_mem htM k
  have htkX : t ^ k ∈ Subgroup.normalizer (X : Set G) := Subgroup.pow_mem _ htX k
  have hpow : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t ^ k, htkM⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩) ^ k := by
    rw [← map_pow]
    rfl
  exact eq_bot_or_eq_barM_of_mem_normalizer hXM htkM htkX
    (fun Y hYX hYn => eq_bot_or_eq_of_torus_conj_two φ (hγ k hk) (conj_pow_torus φ ht k) hYX hYn)
    hY₀ (hpow ▸ hYk)

end CFSG.AGLEmbedding
