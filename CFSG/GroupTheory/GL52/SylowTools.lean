module

public import CFSG.GroupTheory.GL52.Basic

public noncomputable section

namespace CFSG.GroupTheory.GL52

variable {G : Type*} [Group G]

theorem card_sylow_of_card_eq_prime_mul [Finite G] {p m : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p * m) (hm : ¬ p ∣ m) (P : Sylow p G) : Nat.card P = p := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.out.ne_zero hm0, Finsupp.add_apply,
    hp.out.factorization_self, Nat.factorization_eq_zero_of_not_dvd hm, add_zero, pow_one]

theorem card_sylow_of_card_eq_pow_mul [Finite G] {p k m : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) (P : Sylow p G) : Nat.card P = p ^ k := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  rw [P.card_eq_multiplicity, hG, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hp.out.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero, smul_eq_mul, mul_one]

theorem exists_sylow_eq_of_card_pow [Finite G] {p k : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ k) (hP : ∀ P : Sylow p G, Nat.card P = p ^ k) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H := by
  have hH' : IsPGroup p H := IsPGroup.of_card hH
  obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  rw [hP Q, hH]

theorem exists_sylow_eq_of_card [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p) (hP : ∀ P : Sylow p G, Nat.card P = p) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H := by
  have hH' : IsPGroup p H := IsPGroup.of_card (n := 1) (by rw [hH, pow_one])
  obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
  refine ⟨Q, (Subgroup.eq_of_le_of_card_ge hQ ?_).symm⟩
  rw [hP Q, hH]

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {x g : G}
    (h : g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ Subgroup.zpowers x :=
    (Subgroup.zpowers_le).2 h
  have heq : Subgroup.zpowers (g * x * g⁻¹) = Subgroup.zpowers x := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers]
    exact ((MulAut.conj g).orderOf_eq x).symm.le
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨k, rfl⟩
    rw [← heq]
    refine ⟨k, ?_⟩
    simp only [conj_zpow]
  · intro hy
    rw [← heq] at hy
    obtain ⟨k, hk⟩ := hy
    simp only [conj_zpow] at hk
    have : y = x ^ k := by
      have := congrArg (fun z => g⁻¹ * z * g) hk
      simpa [mul_assoc] using this.symm
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k

theorem isFrobeniusSubgroup_map_conj (c : G) {Y K R : Subgroup G} (hKY : K ≤ Y) (hRY : R ≤ Y)
    (hnorm : Y ≤ Subgroup.normalizer (K : Set G)) (hinf : K ⊓ R = ⊥) (hsup : K ⊔ R = Y)
    (hfpf : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k ≠ 1 → r * k * r⁻¹ ≠ k) (hK : K ≠ ⊥) (hR : R ≠ ⊥) :
    IsFrobeniusSubgroup (Y.map (MulAut.conj c).toMonoidHom) := by
  set f := (MulAut.conj c).toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.conj c).injective
  refine isFrobeniusSubgroup_of_fixedPointFree (K := K.map f) (R := R.map f)
    (Subgroup.map_mono hKY) (Subgroup.map_mono hRY) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hf, normalizer_map_conj]
    exact Subgroup.map_mono hnorm
  · rw [← Subgroup.map_inf_eq _ _ _ hinj, hinf, Subgroup.map_bot]
  · rw [← Subgroup.map_sup, hsup]
  · rintro _ ⟨r, hr, rfl⟩ hr1 _ ⟨k, hk, rfl⟩ hk1 h
    have hr1' : r ≠ 1 := by
      rintro rfl
      exact hr1 (map_one f)
    have hk1' : k ≠ 1 := by
      rintro rfl
      exact hk1 (map_one f)
    apply hfpf r hr hr1' k hk hk1'
    apply hinj
    simpa [hf, MulAut.conj_apply, mul_assoc] using h
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]

end CFSG.GroupTheory.GL52
