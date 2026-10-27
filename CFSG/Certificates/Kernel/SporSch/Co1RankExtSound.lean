module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KS.SporSch.Co1Rank

variable {G : Type*} [Group G]

@[expose] def Good (S : Subgroup G) (A : Set G) (E : Subgroup G) : Prop :=
  E ≤ S ∧ (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x ≠ 1 → x ∉ A

theorem mem_map_conj {s x : G} {E : Subgroup G} :
    x ∈ E.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * x * s ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using he
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem good_map {S : Subgroup G} {A : Set G} (hA : ∀ s ∈ S, ∀ x, s * x * s⁻¹ ∈ A ↔ x ∈ A)
    {E : Subgroup G} (hE : Good S A E) {s : G} (hs : s ∈ S) :
    Good S A (E.map (MulAut.conj s).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj s).toMonoidHom) = Nat.card E := by
  obtain ⟨hES, hsq, hcm, hnA⟩ := hE
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Subgroup.card_map_of_injective (MulAut.conj s).injective⟩
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact S.mul_mem (S.mul_mem hs (hES ha)) (S.inv_mem hs)
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc s * a * s⁻¹ * (s * a * s⁻¹) = s * (a * a) * s⁻¹ := by group
      _ = 1 := by rw [hsq a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc s * a * s⁻¹ * (s * b * s⁻¹) = s * (a * b) * s⁻¹ := by group
      _ = s * (b * a) * s⁻¹ := by rw [hcm a ha b hb]
      _ = s * b * s⁻¹ * (s * a * s⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩ h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
    rw [hA s hs a]
    exact hnA a ha fun h => h1 (by rw [h]; group)

theorem eq_of_two_pow {K H X : Subgroup G} {r : ℕ} (hKH : K ≤ H) (hHX : H ≤ X) (hne : ¬ H ≤ K)
    (hK : Nat.card K = 2 ^ r) (hX : Nat.card X = 2 ^ (r + 1)) : H = X := by
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; positivity)
  have : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHX)
  obtain ⟨m, hm, hHm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hX ▸ Subgroup.card_dvd_of_le hHX)
  have hrm : r ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
    (hK ▸ hHm ▸ Subgroup.card_dvd_of_le hKH)
  rcases Nat.eq_or_lt_of_le hrm with h | h
  · exfalso
    subst h
    exact hne (Subgroup.eq_of_le_of_card_ge hKH (by rw [hHm, hK])).ge
  · exact Subgroup.eq_of_le_of_card_ge hHX (by rw [hX, hHm]; exact (Nat.pow_le_pow_right
      (by norm_num) (by omega)))

theorem ext_step {S : Subgroup G} {A : Set G} (hA : ∀ s ∈ S, ∀ x, s * x * s⁻¹ ∈ A ↔ x ∈ A)
    {c : G} (R : ℕ → ℕ → Subgroup G) (n : ℕ → ℕ)
    (hcard : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, Nat.card (R r a) = 2 ^ r)
    (hcR : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, c ∈ R r a)
    (hext : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, ∀ y ∈ S, y * y = 1 → (∀ e ∈ R r a, e * y = y * e) →
      y ∉ R r a → (∀ e ∈ R r a, e * y ∉ A) →
      r < 4 ∧ ∃ a' < n (r + 1), ∃ s ∈ S, R r a ≤ (R (r + 1) a').map (MulAut.conj s).toMonoidHom ∧
        y ∈ (R (r + 1) a').map (MulAut.conj s).toMonoidHom)
    {r a : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (ha : a < n r) {E : Subgroup G} (hE : Good S A E)
    (hRE : R r a ≤ E) :
    E ≤ R r a ∨ (r < 4 ∧ ∃ a' < n (r + 1), ∃ E' : Subgroup G, Good S A E' ∧
      Nat.card E' = Nat.card E ∧ R (r + 1) a' ≤ E') := by
  by_cases hER : E ≤ R r a
  · exact Or.inl hER
  right
  obtain ⟨y, hyE, hyR⟩ := Set.not_subset.1 hER
  obtain ⟨hES, hsq, hcm, hnA⟩ := hE
  have hyA : ∀ e ∈ R r a, e * y ∉ A := by
    intro e he
    refine hnA _ (E.mul_mem (hRE he) hyE) fun h1 => hyR ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    exact (R r a).inv_mem he
  obtain ⟨hr, a', ha', s, hs, hRX, hyX⟩ := hext r hr1 hr4 a ha y (hES hyE) (hsq y hyE)
    (fun e he => hcm e (hRE he) y hyE) hyR hyA
  refine ⟨hr, a', ha', E.map (MulAut.conj s⁻¹).toMonoidHom,
    good_map hA ⟨hES, hsq, hcm, hnA⟩ (S.inv_mem hs) |>.1,
    good_map hA ⟨hES, hsq, hcm, hnA⟩ (S.inv_mem hs) |>.2, ?_⟩
  have hX : Nat.card ((R (r + 1) a').map (MulAut.conj s).toMonoidHom) = 2 ^ (r + 1) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]
    exact hcard (r + 1) (by omega) (by omega) a' ha'
  have hH := eq_of_two_pow (K := R r a) (H := R r a ⊔ Subgroup.zpowers y) le_sup_left
    (sup_le hRX ((Subgroup.zpowers_le).2 hyX))
    (fun h => hyR (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))))
    (hcard r hr1 hr4 a ha) hX
  have hXE : (R (r + 1) a').map (MulAut.conj s).toMonoidHom ≤ E :=
    hH ▸ sup_le hRE ((Subgroup.zpowers_le).2 hyE)
  intro x hx
  rw [mem_map_conj, inv_inv]
  exact hXE (mem_map_conj.2 (by simpa [mul_assoc] using hx))

theorem card_le_of_ext {S : Subgroup G} {A : Set G} (hA : ∀ s ∈ S, ∀ x, s * x * s⁻¹ ∈ A ↔ x ∈ A)
    {c : G} (R : ℕ → ℕ → Subgroup G) (n : ℕ → ℕ) (hn : 0 < n 1) (hR1 : R 1 0 = Subgroup.zpowers c)
    (hcard : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, Nat.card (R r a) = 2 ^ r)
    (hcR : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, c ∈ R r a)
    (hext : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, ∀ y ∈ S, y * y = 1 → (∀ e ∈ R r a, e * y = y * e) →
      y ∉ R r a → (∀ e ∈ R r a, e * y ∉ A) →
      r < 4 ∧ ∃ a' < n (r + 1), ∃ s ∈ S, R r a ≤ (R (r + 1) a').map (MulAut.conj s).toMonoidHom ∧
        y ∈ (R (r + 1) a').map (MulAut.conj s).toMonoidHom)
    {E : Subgroup G} (hE : Good S A E) (hcE : c ∈ E) : Nat.card E ≤ 16 := by
  have key : ∀ k, k ≤ 3 → ∀ a < n (4 - k), ∀ E' : Subgroup G, Good S A E' →
      R (4 - k) a ≤ E' → Nat.card E' ≤ 16 := by
    intro k
    induction k with
    | zero =>
      intro _ a ha E' hE' hRE'
      rcases ext_step hA R n hcard hcR hext (by omega) (by omega) ha hE' hRE' with h | ⟨h, -⟩
      · have hc := hcard 4 (by omega) le_rfl a ha
        have : Finite (R 4 a) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
        exact (Subgroup.card_le_of_le h).trans (by rw [hc]; norm_num)
      · omega
    | succ k ih =>
      intro hk a ha E' hE' hRE'
      rcases ext_step hA R n hcard hcR hext (by omega) (by omega) ha hE' hRE' with
        h | ⟨-, a', ha', E'', hE'', hc'', hR''⟩
      · have hc := hcard (4 - (k + 1)) (by omega) (by omega) a ha
        have : Finite (R (4 - (k + 1)) a) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
        refine (Subgroup.card_le_of_le h).trans (hc ▸ ?_)
        calc 2 ^ (4 - (k + 1)) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 16 := by norm_num
      · have e : 4 - (k + 1) + 1 = 4 - k := by omega
        rw [e] at ha' hR''
        exact hc'' ▸ ih (by omega) a' ha' E'' hE'' hR''
  exact key 3 le_rfl 0 hn E hE (by rw [hR1]; exact (Subgroup.zpowers_le).2 hcE)

end CFSG.KS.SporSch.Co1Rank

end
