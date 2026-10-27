module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGAltSixFact

open Equiv

theorem pow_eq_pow_mod_five {G : Type*} [Group G] (g : G) (h5 : g ^ 5 = 1) (n : ℕ) :
    g ^ n = g ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, h5, one_pow, one_mul]

theorem fix_of_pow {α : Type*} {σ : Perm α} (h5 : σ ^ 5 = 1) {y : α} {n : ℕ}
    (hy : (σ ^ n) y = y) (hn : n % 5 ≠ 0) : σ y = y := by
  rw [pow_eq_pow_mod_five σ h5 n] at hy
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (n % 5 * k) % 5 = 1 := by
    rcases (by omega : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4) with h | h | h | h
    · exact ⟨1, by omega⟩
    · exact ⟨3, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨4, by omega⟩
  have h2 : ((σ ^ (n % 5)) ^ k) y = y := Perm.pow_apply_eq_self_of_apply_eq_self hy k
  rw [← pow_mul, pow_eq_pow_mod_five σ h5 (n % 5 * k), hk, pow_one] at h2
  exact h2

theorem pow_ne_of_lt {α : Type*} {σ : Perm α} (h5 : σ ^ 5 = 1) {y : α} (hy : σ y ≠ y)
    {a b : ℕ} (hb : b < 5) (hab : a < b) (heq : (σ ^ a) y = (σ ^ b) y) : False := by
  have e1 : (σ ^ (5 - b)) ((σ ^ a) y) = (σ ^ (5 - b + a)) y := by
    rw [← Perm.mul_apply, ← pow_add]
  have e2 : (σ ^ (5 - b)) ((σ ^ b) y) = y := by
    rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hb.le, h5, Perm.one_apply]
  have e3 : (σ ^ (5 - b + a)) y = y := by
    rw [← e1, heq, e2]
  exact hy (fix_of_pow h5 e3 (by omega))

theorem pow_inj_of_ne {α : Type*} {σ : Perm α} (h5 : σ ^ 5 = 1) {y : α} (hy : σ y ≠ y)
    {a b : ℕ} (ha : a < 5) (hb : b < 5) (heq : (σ ^ a) y = (σ ^ b) y) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact (pow_ne_of_lt h5 hy hb h heq).elim
  · exact h
  · exact (pow_ne_of_lt h5 hy ha h heq.symm).elim

theorem moved_pow {α : Type*} {σ : Perm α} {y : α} (hy : σ y ≠ y) (a : ℕ) :
    σ ((σ ^ a) y) ≠ (σ ^ a) y := by
  intro h
  apply hy
  have hc : σ * σ ^ a = σ ^ a * σ := (Commute.self_pow σ a).eq
  have h2 : (σ ^ a) (σ y) = (σ ^ a) y := by
    rw [← Perm.mul_apply, ← hc, Perm.mul_apply, h]
  exact (σ ^ a).injective h2

theorem fixed_subsingleton {σ : Perm (Fin 6)} (h5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) {x y : Fin 6}
    (hx : σ x = x) (hy : σ y = y) : x = y := by
  by_contra hxy
  obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext fun k => by simpa using h k)
  let g : Fin 5 ⊕ Bool → Fin 6 :=
    Sum.elim (fun a => (σ ^ (a : ℕ)) j) (fun c => if c then y else x)
  have hg : Function.Injective g := by
    rintro (a | c) (b | d) h
    · have h' : (σ ^ (a : ℕ)) j = (σ ^ (b : ℕ)) j := h
      exact congrArg Sum.inl (Fin.ext (pow_inj_of_ne h5 hj a.isLt b.isLt h'))
    · exfalso
      have h' : (σ ^ (a : ℕ)) j = (if d then y else x) := h
      have hw : σ (if d then y else x) = if d then y else x := by
        cases d <;> simp [hx, hy]
      exact moved_pow hj a (by rw [h']; exact hw)
    · exfalso
      have h' : (if c then y else x) = (σ ^ (b : ℕ)) j := h
      have hw : σ (if c then y else x) = if c then y else x := by
        cases c <;> simp [hx, hy]
      exact moved_pow hj b (by rw [← h']; exact hw)
    · have h' : (if c then y else x) = (if d then y else x) := h
      cases c <;> cases d
      · rfl
      · exact absurd (by simpa using h') hxy
      · exact absurd (by simpa using h'.symm) hxy
      · rfl
  have hcard := Fintype.card_le_of_injective g hg
  simp at hcard

theorem core_perm (σ : Perm (Fin 6)) (T : Subgroup (Perm (Fin 6)))
    (h5 : σ ^ 5 = 1) (hσ1 : σ ≠ 1) (hT : IsPGroup 2 T)
    (hnorm : ∀ t : Perm (Fin 6), t ∈ T ↔ σ * t * σ⁻¹ ∈ T) : T = ⊥ := by
  by_contra hne
  obtain ⟨t, htT, ht1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    exact hne ((Subgroup.eq_bot_iff_forall T).2 h)
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ i := by
    by_contra h
    push Not at h
    exact ht1 (Equiv.ext fun k => by simpa using h k)
  obtain ⟨O, hO⟩ : ∃ O : Set (Fin 6), O = MulAction.orbit (↥T) i := ⟨_, rfl⟩
  have hOmem : ∀ y, y ∈ O ↔ ∃ s ∈ T, s i = y := by
    intro y
    rw [hO, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, g.2, hg⟩
    · rintro ⟨s, hs, hsy⟩
      exact ⟨⟨s, hs⟩, hsy⟩
  have hiO : i ∈ O := (hOmem i).2 ⟨1, T.one_mem, rfl⟩
  have htiO : t i ∈ O := (hOmem (t i)).2 ⟨t, htT, rfl⟩
  have hOinv : ∀ u ∈ T, ∀ w ∈ O, u w ∈ O := by
    intro u hu w hw
    obtain ⟨s, hs, rfl⟩ := (hOmem w).1 hw
    exact (hOmem _).2 ⟨u * s, T.mul_mem hu hs, by rw [Perm.mul_apply]⟩
  have hOtrans : ∀ x ∈ O, ∀ y ∈ O, ∃ s ∈ T, s x = y := by
    intro x hx y hy
    obtain ⟨s1, hs1, rfl⟩ := (hOmem x).1 hx
    obtain ⟨s2, hs2, rfl⟩ := (hOmem y).1 hy
    exact ⟨s2 * s1⁻¹, T.mul_mem hs2 (T.inv_mem hs1), by simp [Perm.mul_apply]⟩
  have hOcard : ∃ m : ℕ, Nat.card O = 2 ^ m := by
    rw [hO]
    exact hT.card_orbit i
  have hOle : Nat.card O ≤ 6 := by
    have := Nat.card_le_card_of_injective (Subtype.val : O → Fin 6) Subtype.val_injective
    simpa using this
  have hnormpow : ∀ m : ℕ, ∀ s ∈ T, σ ^ m * s * (σ ^ m)⁻¹ ∈ T := by
    intro m
    induction m with
    | zero => intro s hs; simpa using hs
    | succ m ih =>
      intro s hs
      have e : σ ^ (m + 1) * s * (σ ^ (m + 1))⁻¹ = σ * (σ ^ m * s * (σ ^ m)⁻¹) * σ⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact (hnorm _).1 (ih s hs)
  have htransfer : ∀ m : ℕ, ∀ x ∈ O, (σ ^ m) x ∈ O → ∀ y ∈ O, (σ ^ m) y ∈ O := by
    intro m x hx hmx y hy
    obtain ⟨s, hs, hsxy⟩ := hOtrans x hx y hy
    rw [← hsxy]
    have e : (σ ^ m) (s x) = (σ ^ m * s * (σ ^ m)⁻¹) ((σ ^ m) x) := by
      simp [Perm.mul_apply]
    rw [e]
    exact hOinv _ (hnormpow m s hs) _ hmx
  have hstep : ∀ m : ℕ, (∀ y ∈ O, (σ ^ m) y ∈ O) → m % 5 ≠ 0 → ∀ y ∈ O, σ y ∈ O := by
    intro m hm hm0 y hy
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (m * k) % 5 = 1 := by
      rcases (by omega : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4) with h | h | h | h
      · exact ⟨1, by omega⟩
      · exact ⟨3, by omega⟩
      · exact ⟨2, by omega⟩
      · exact ⟨4, by omega⟩
    have hk' : ∀ k : ℕ, ∀ w ∈ O, ((σ ^ m) ^ k) w ∈ O := by
      intro k
      induction k with
      | zero => intro w hw; simpa using hw
      | succ k ih =>
        intro w hw
        rw [pow_succ', Perm.mul_apply]
        exact hm _ (ih w hw)
    have h1 := hk' k y hy
    rw [← pow_mul, pow_eq_pow_mod_five σ h5 (m * k), hk, pow_one] at h1
    exact h1
  by_cases hC : ∀ y ∈ O, σ y ∈ O
  ·
    have hfixO : ∀ y ∈ O, σ y = y := by
      intro y hy
      by_contra hy'
      have hpts : ∀ a : ℕ, (σ ^ a) y ∈ O := by
        intro a
        induction a with
        | zero => simpa using hy
        | succ a ih =>
          rw [pow_succ', Perm.mul_apply]
          exact hC _ ih
      let f : Fin 5 → O := fun a => ⟨(σ ^ (a : ℕ)) y, hpts a⟩
      have hf : Function.Injective f := by
        intro a b hab
        have h' : (σ ^ (a : ℕ)) y = (σ ^ (b : ℕ)) y := congrArg Subtype.val hab
        exact Fin.ext (pow_inj_of_ne h5 hy' a.isLt b.isLt h')
      have h5le : Nat.card (Fin 5) ≤ Nat.card O := Nat.card_le_card_of_injective f hf
      obtain ⟨m, hm⟩ := hOcard
      have h5le' : 5 ≤ 2 ^ m := by
        rw [← hm]
        simpa using h5le
      have h6 : 2 ^ m ≤ 6 := by
        rw [← hm]
        exact hOle
      have hm3 : m < 3 := by
        by_contra hcon
        push Not at hcon
        have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hcon
        norm_num at h8
        omega
      interval_cases m <;> norm_num at h5le'
    exact hi (fixed_subsingleton h5 hσ1 (hfixO i hiO) (hfixO (t i) htiO)).symm
  ·
    have hP : ∀ x ∈ O, ∀ m : ℕ, (σ ^ m) x ∈ O → 5 ∣ m := by
      intro x hx m hmx
      by_contra h5m
      exact hC (hstep m (htransfer m x hx hmx) (fun h => h5m (Nat.dvd_of_mod_eq_zero h)))
    have hpO : ∀ c : Bool, (if c then t i else i) ∈ O := by
      intro c
      cases c
      · simpa using hiO
      · simpa using htiO
    let g : Fin 5 × Bool → Fin 6 := fun q => (σ ^ (q.1 : ℕ)) (if q.2 then t i else i)
    have hg : Function.Injective g := by
      rintro ⟨a, c⟩ ⟨b, d⟩ hab
      have hab' : (σ ^ (a : ℕ)) (if c then t i else i) =
          (σ ^ (b : ℕ)) (if d then t i else i) := hab
      have hb5 := b.isLt
      have ha5 := a.isLt
      have hmO : (σ ^ (5 - (b : ℕ) + a)) (if c then t i else i) = (if d then t i else i) := by
        rw [pow_add, Perm.mul_apply, hab', ← Perm.mul_apply, ← pow_add,
          Nat.sub_add_cancel hb5.le, h5, Perm.one_apply]
      have hdiv : 5 ∣ 5 - (b : ℕ) + a :=
        hP _ (hpO c) _ (by rw [hmO]; exact hpO d)
      have hab_eq : (a : ℕ) = b := by omega
      rw [hab_eq] at hab'
      have hcd' : (if c then t i else i) = (if d then t i else i) :=
        (σ ^ (b : ℕ)).injective hab'
      have hcd : c = d := by
        cases c <;> cases d
        · rfl
        · exact absurd (by simpa using hcd') hi.symm
        · exact absurd (by simpa using hcd') hi
        · rfl
      exact Prod.ext (Fin.ext hab_eq) hcd
    have hcard := Fintype.card_le_of_injective g hg
    simp at hcard

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGAltSixFact

end
