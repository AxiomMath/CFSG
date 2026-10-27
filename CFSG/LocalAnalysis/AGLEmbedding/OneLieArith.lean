module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

theorem exists_subfield_of_mul_mem {p n : ℕ} [Fact p.Prime] (hn : n ≠ 0)
    {γ : GaloisField p n} (hγ0 : γ ≠ 0) (W : AddSubgroup (GaloisField p n))
    (hW : ∀ w ∈ W, γ * w ∈ W) (hbot : W ≠ ⊥) (htop : W ≠ ⊤) :
    ∃ f : ℕ, f ∣ n ∧ 0 < f ∧ f < n ∧ γ ^ (p ^ f - 1) = 1 ∧ p ^ f * Nat.card W ≤ p ^ n := by
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
  obtain ⟨f, hfn, hf⟩ := (Nat.dvd_prime_pow hp).mp
    ((GaloisField.card p n hn) ▸ A.toSubring.toAddSubgroup.card_addSubgroup_dvd_card)
  have hfA : Nat.card A = p ^ f := hf
  have hfdvd : f ∣ n := by
    have h1 := Module.natCard_eq_pow_finrank (K := A) (V := GaloisField p n)
    rw [GaloisField.card p n hn, hfA, ← pow_mul] at h1
    exact ⟨_, Nat.pow_right_injective hp.two_le h1⟩
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := Finite.one_lt_card (α := A)
      rw [hfA, pow_zero] at h1
      exact absurd h1 (lt_irrefl _)
    · exact h
  have hfl : f < n := by
    refine lt_of_le_of_ne hfn fun hfe => ?_
    have htopA : A.toSubring.toAddSubgroup = ⊤ :=
      AddSubgroup.eq_top_of_card_eq _ (by rw [hf, hfe, GaloisField.card p n hn])
    have hAall : ∀ c, c ∈ A := fun c => by
      have h : c ∈ A.toSubring.toAddSubgroup := htopA ▸ AddSubgroup.mem_top c
      exact h
    rcases W.bot_or_exists_ne_zero with h | ⟨w₀, hw₀, hw₀0⟩
    · exact hbot h
    · refine htop (eq_top_iff.mpr fun c _ => ?_)
      have h := (hA _).mp (hAall (c * w₀⁻¹)) w₀ hw₀
      rwa [mul_assoc, inv_mul_cancel₀ hw₀0, mul_one] at h
  let _ : Fintype A := Fintype.ofFinite A
  have hγd : γ ^ (p ^ f - 1) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨γ, (hA γ).mpr hW⟩ : A)
      (fun h => hγ0 (congrArg Subtype.val h))
    rw [← Nat.card_eq_fintype_card, hfA] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨x, hxW⟩ : ∃ x, x ∉ W := by
    by_contra hall
    push Not at hall
    exact htop (eq_top_iff.mpr fun c _ => hall c)
  have hinj : Function.Injective fun cw : A × W => (cw.1 : GaloisField p n) * x + cw.2 := by
    rintro ⟨c, w⟩ ⟨c', w'⟩ he
    simp only at he
    have hcc : c = c' := by
      by_contra hne
      have hne' : (c : GaloisField p n) - c' ≠ 0 :=
        sub_ne_zero.mpr fun h => hne (Subtype.ext h)
      have hmem : ((c : GaloisField p n) - c') * x ∈ W := by
        have e : ((c : GaloisField p n) - c') * x = (w' : GaloisField p n) - w := by
          linear_combination he
        rw [e]
        exact W.sub_mem w'.2 w.2
      have h := (hA _).mp (A.inv_mem (A.sub_mem c.2 c'.2)) _ hmem
      rw [← mul_assoc, inv_mul_cancel₀ hne', one_mul] at h
      exact hxW h
    subst hcc
    exact Prod.ext rfl (Subtype.ext (add_left_cancel he))
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hfA, GaloisField.card p n hn] at hcard
  exact ⟨f, hfdvd, hf0, hfl, hγd, hcard⟩

theorem three_pow_gt (m : ℕ) (hm : 3 ≤ m) : 8 * m + 2 < 3 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem stmtOneLieArithBi :
    ∀ n e f j : ℕ, 3 ≤ n → (e = 1 ∨ e = 2) → f ∣ n → f < n → 1 ≤ f →
      3 ^ n - 1 ≤ e * j * (3 ^ f - 1) → j ≤ (if e = 2 then n else 2 * n) + 1 →
      e = 2 ∧ n = 4 ∧ f = 2 ∧ j = 5 := by
  intro n e f j hn he hfn hfl hf1 hineq hj
  obtain ⟨c, rfl⟩ := hfn
  have hc2 : 2 ≤ c := by
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  have hj' : j ≤ 2 * (f * c) + 1 := by split_ifs at hj <;> omega
  have he2 : e ≤ 2 := by omega
  have h3f : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
  have hmain : 3 ^ (f * c) ≤ 2 * (2 * (f * c) + 1) * 3 ^ f := by
    have h1 : e * j * (3 ^ f - 1) ≤ 2 * (2 * (f * c) + 1) * (3 ^ f - 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul he2 hj')
    have h2 : 2 * (2 * (f * c) + 1) * (3 ^ f - 1) + 1 ≤ 2 * (2 * (f * c) + 1) * 3 ^ f := by
      have : 3 ^ f - 1 + 1 = 3 ^ f := Nat.sub_add_cancel h3f
      nlinarith
    have h3 : 1 ≤ 3 ^ (f * c) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hsplit : 3 ^ (f * c) = 3 ^ f * 3 ^ (f * (c - 1)) := by
    rw [← pow_add]
    congr 1
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    simp [Nat.mul_add]
    ring
  rw [hsplit, mul_comm (2 * (2 * (f * c) + 1))] at hmain
  have hm : 3 ^ (f * (c - 1)) ≤ 2 * (2 * (f * c) + 1) :=
    Nat.le_of_mul_le_mul_left hmain (by positivity)
  have hm2 : f * c ≤ 2 * (f * (c - 1)) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hsmall : f * (c - 1) ≤ 2 := by
    by_contra hbig
    have := three_pow_gt (f * (c - 1)) (by omega)
    omega
  have hn4 : f * c ≤ 4 := by omega
  have hf2 : f ≤ 2 := by nlinarith
  have hc4 : c ≤ 4 := by nlinarith
  rcases he with rfl | rfl <;> interval_cases f <;> interval_cases c <;> simp_all <;> omega

end CFSG.AGLEmbedding
