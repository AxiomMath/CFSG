module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma fourB_conjIn_symm {G : Type} [Group G] {K : Subgroup G} {x y : G}
    (h : ConjIn K x y) : ConjIn K y x := by
  obtain ⟨k, hk, hxy⟩ := h
  refine ⟨k⁻¹, K.inv_mem hk, ?_⟩
  rw [← hxy]
  group

private lemma fourB_conjIn_trans {G : Type} [Group G] {K : Subgroup G} {x y w : G}
    (h1 : ConjIn K x y) (h2 : ConjIn K y w) : ConjIn K x w := by
  obtain ⟨k1, hk1, h1⟩ := h1
  obtain ⟨k2, hk2, h2⟩ := h2
  refine ⟨k2 * k1, K.mul_mem hk2 hk1, ?_⟩
  rw [← h2, ← h1]
  group

theorem fourB_pigeon {G : Type} [Group G] (K : Subgroup G) (I : Set G) (S : Fin 7 → Set G)
    (r : Fin 7 → G) (hr : ∀ t ∈ I, ∃ j, ConjIn K t (r j)) (hsub : ∀ i, S i ⊆ I)
    (hcover : ∀ t ∈ I, ∃ i, t ∈ S i) (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hinv : ∀ i, ∀ k ∈ K, ∀ c ∈ S i, k * c * k⁻¹ ∈ S i) (hne : ∀ i, (S i).Nonempty) :
    IsOrbitPartition K I S := by
  classical
  have hne0 : ∀ i, (S i).Nonempty := hne
  choose s hs using hne
  choose f hf using fun i => hr (s i) (hsub i (hs i))
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hji : ConjIn K (s j) (s i) :=
      fourB_conjIn_trans (hf j) (fourB_conjIn_symm (by simpa [hij] using hf i))
    obtain ⟨k, hk, hkij⟩ := hji
    have hmem : s i ∈ S j := by
      have h2 : k * s j * k⁻¹ ∈ S j := hinv j k hk (s j) (hs j)
      rwa [hkij] at h2
    exact Set.disjoint_left.mp (hdisj i j hne) (hs i) hmem
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  have hclass : ∀ i, ∀ c ∈ S i, ConjIn K c (r (f i)) := by
    intro i c hc
    obtain ⟨j, hj⟩ := hr c (hsub i hc)
    obtain ⟨i1, hi1⟩ := hf_surj j
    have hcsi : ConjIn K c (s i1) :=
      fourB_conjIn_trans hj (fourB_conjIn_symm (by simpa [hi1] using hf i1))
    have hcS : c ∈ S i1 := by
      obtain ⟨k, hk, hkcs⟩ := hcsi
      have h2 : k⁻¹ * s i1 * (k⁻¹)⁻¹ ∈ S i1 :=
        hinv i1 k⁻¹ (K.inv_mem hk) (s i1) (hs i1)
      rw [inv_inv, ← hkcs] at h2
      have hce : k⁻¹ * (k * c * k⁻¹) * k = c := by group
      rwa [hce] at h2
    have hii1 : i = i1 := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj i i1 hne) hc hcS
    rw [← hii1] at hi1
    simpa [hi1] using hj
  refine ⟨hsub, hcover, hdisj, ?_⟩
  intro i
  refine ⟨hinv i, hne0 i, ?_⟩
  intro c hc c' hc'
  exact fourB_conjIn_trans (hclass i c hc) (fourB_conjIn_symm (hclass i c' hc'))

theorem fourB_mul_mem_of_orbit {G : Type} [Group G] (K : Subgroup G) (S S' : Set G) (b : G)
    (hS : IsConjOrbit K S) (hS' : ∀ k ∈ K, ∀ c ∈ S', k * c * k⁻¹ ∈ S')
    (hb : ∀ k ∈ K, k * b * k⁻¹ = b) (t₀ : G) (ht₀ : t₀ ∈ S) (ht₀b : t₀ * b ∈ S') :
    ∀ t ∈ S, t * b ∈ S' := by
  intro t ht
  obtain ⟨k, hk, hkt⟩ := hS.transitive t₀ ht₀ t ht
  have hkb : k * b * k⁻¹ = b := hb k hk
  have hcalc : t * b = k * (t₀ * b) * k⁻¹ := by
    calc t * b = (k * t₀ * k⁻¹) * b := by rw [← hkt]
      _ = (k * t₀ * k⁻¹) * (k * b * k⁻¹) := by rw [hkb]
      _ = k * (t₀ * b) * k⁻¹ := by group
  rw [hcalc]
  exact hS' k hk (t₀ * b) ht₀b

theorem fourB_exists_fixed_of_odd {G : Type} [Group G] (T : Set G) (q : G) (hq : q * q = 1)
    (hT : ∀ t ∈ T, q * t * q⁻¹ ∈ T) (hodd : Odd (Nat.card ↥T)) : ∃ t ∈ T, q * t = t * q := by
  classical
  haveI : Finite ↥T := Nat.finite_of_card_ne_zero hodd.pos.ne'
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  let c : ↥T → ↥T := fun t => ⟨q * (t : G) * q⁻¹, hT t t.2⟩
  have hc2 : ∀ t : ↥T, c (c t) = t := by
    intro t
    apply Subtype.ext
    simp only [c]
    calc q * (q * (t : G) * q⁻¹) * q⁻¹ = (q * q) * (t : G) * (q * q) := by
          rw [hqinv]; group
      _ = (t : G) := by rw [hq]; group
  let σ : Equiv.Perm ↥T := ⟨c, c, hc2, hc2⟩
  have hσ2 : σ ^ 2 = 1 := by
    rw [pow_two]
    apply Equiv.ext
    intro t
    exact hc2 t
  have hσ : σ ^ 2 ^ 1 = 1 := by simpa using hσ2
  have hα : ¬ 2 ∣ Fintype.card ↥T := by
    rw [← Nat.card_eq_fintype_card]
    exact hodd.not_two_dvd_nat
  obtain ⟨t, ht⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hα hσ
  refine ⟨t, t.2, ?_⟩
  have ht' : q * (t : G) * q⁻¹ = (t : G) := by
    have h := congrArg (fun s : ↥T => (s : G)) ht
    simpa [σ, c] using h
  calc q * (t : G) = (q * (t : G) * q⁻¹) * q := by group
    _ = (t : G) * q := by rw [ht']

end CFSG.EvenSporadicStandard.HNRecog.Section3
