module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TB

open Subgroup

variable {G : Type} [Group G]

@[reducible] def conjAct (T K : Subgroup G) (hTK : T ≤ normalizer (K : Set G)) :
    MulDistribMulAction T K where
  smul t k := ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : G) * k * 1⁻¹ = k; group)
  mul_smul s t k := Subtype.ext (by
    change (s * t : G) * k * (s * t : G)⁻¹ = s * (t * k * (t : G)⁻¹) * (s : G)⁻¹
    group)
  smul_mul t k l := Subtype.ext (by
    change (t : G) * (k * l) * (t : G)⁻¹ = (t * k * (t : G)⁻¹) * (t * l * (t : G)⁻¹)
    group)
  smul_one t := Subtype.ext (by change (t : G) * 1 * (t : G)⁻¹ = 1; group)

theorem card_modEq_card_inf_centralizer {q : ℕ} [Fact q.Prime] [Finite G] {f : G} (hf : orderOf f = q)
    {A : Subgroup G} (hfA : f ∈ normalizer (A : Set G)) :
    Nat.card A ≡ Nat.card (A ⊓ centralizer ({f} : Set G) : Subgroup G) [MOD q] := by
  classical
  have hT : zpowers f ≤ normalizer (A : Set G) := by
    rw [zpowers_le]; exact hfA
  let _ : MulDistribMulAction (zpowers f) A := conjAct _ _ hT
  have hp : IsPGroup q (zpowers f) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hf, pow_one]
  have key := hp.card_modEq_card_fixedPoints A
  have hfix : ∀ a : MulAction.fixedPoints (zpowers f) A, f * (a.1 : G) * f⁻¹ = a.1 :=
    fun a => congrArg Subtype.val (a.2 ⟨f, mem_zpowers f⟩)
  have h1 : ∀ a : MulAction.fixedPoints (zpowers f) A, (a.1 : G) ∈ A ⊓ centralizer ({f} : Set G) := by
    intro a
    refine mem_inf.mpr ⟨a.1.2, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have h2 := hfix a
    calc (a.1 : G) * f = f * a.1 * f⁻¹ * f := by rw [h2]
      _ = f * a.1 := by group
  have h3 : ∀ a : ↥(A ⊓ centralizer ({f} : Set G)),
      (⟨(a : G), (mem_inf.mp a.2).1⟩ : A) ∈ MulAction.fixedPoints (zpowers f) A := by
    intro a g
    have hac : (a : G) ∈ centralizer ({f} : Set G) := (mem_inf.mp a.2).2
    have hfa : f ∈ centralizer ({(a : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hac ⊢
      exact hac.symm
    have hga : (g : G) ∈ centralizer ({(a : G)} : Set G) := (zpowers_le.mpr hfa) g.2
    rw [mem_centralizer_singleton_iff] at hga
    apply Subtype.ext
    change (g : G) * (a : G) * (g : G)⁻¹ = a
    calc (g : G) * (a : G) * (g : G)⁻¹ = (a : G) * g * (g : G)⁻¹ := by rw [← hga]
      _ = a := by group
  have heq : Nat.card (MulAction.fixedPoints (zpowers f) A) =
      Nat.card (A ⊓ centralizer ({f} : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), h1 a⟩
        invFun := fun a => ⟨⟨(a : G), (mem_inf.mp a.2).1⟩, h3 a⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [heq] at key
  exact key

theorem le_centralizer_of_card {p q r m : ℕ} [Fact p.Prime] [Fact q.Prime] [Finite G] {f : G}
    (hf : orderOf f = q) {A : Subgroup G} (hfA : f ∈ normalizer (A : Set G))
    (hAcard : Nat.card A = r * p ^ m) (hqr : ¬ q ∣ r) (hqp : ¬ q ∣ p)
    (hr : r ∣ Nat.card (A ⊓ centralizer ({f} : Set G) : Subgroup G))
    (hord : ∀ k : ℕ, 0 < k → k ≤ m → ¬ q ∣ p ^ k - 1) :
    A ≤ centralizer ({f} : Set G) := by
  set B : Subgroup G := A ⊓ centralizer ({f} : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hdvd : Nat.card B ∣ r * p ^ m := hAcard ▸ Subgroup.card_dvd_of_le hBA
  obtain ⟨d, hd⟩ := hr
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, zero_mul] at hAcard
      exact absurd hAcard Nat.card_pos.ne'
    · exact h0
  have hdp : d ∣ p ^ m := by
    rw [hd] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hr0 hdvd
  obtain ⟨j, hjm, hdj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdp
  have hmod := card_modEq_card_inf_centralizer hf hfA
  rw [hAcard, hd, hdj] at hmod
  have hjm' : j = m := by
    by_contra hne
    have hlt : j < m := lt_of_le_of_ne hjm hne
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hq : q.Prime := Fact.out
    have hcop : Nat.Coprime q (r * p ^ j) := by
      refine (Nat.Prime.coprime_iff_not_dvd hq).mpr fun hdiv => ?_
      rcases (Nat.Prime.dvd_mul hq).mp hdiv with h | h
      · exact hqr h
      · exact hqp (hq.dvd_of_dvd_pow h)
    have hmod2 : (r * p ^ j) * p ^ (k + 1) ≡ (r * p ^ j) * 1 [MOD q] := by
      have e1 : r * p ^ m = (r * p ^ j) * p ^ (k + 1) := by
        rw [hk, show j + k + 1 = j + (k + 1) by ring, pow_add]; ring
      rw [e1] at hmod
      simpa using hmod
    have hmod3 : p ^ (k + 1) ≡ 1 [MOD q] :=
      Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime, Nat.gcd_comm] using hcop) hmod2
    have h1le : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
    have hdvd2 : q ∣ p ^ (k + 1) - 1 := (Nat.modEq_iff_dvd' h1le).mp hmod3.symm
    exact hord (k + 1) (Nat.succ_pos k) (by omega) hdvd2
  have hcardB : Nat.card A ≤ Nat.card B := by
    rw [hAcard, hd, hdj, hjm']
  have hAB : B = A := Subgroup.eq_of_le_of_card_ge hBA hcardB
  intro a ha
  have : a ∈ B := hAB.symm ▸ ha
  exact (mem_inf.mp this).2

end CFSG.GH74.Uniqueness.SU.SU13.TB
