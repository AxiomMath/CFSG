module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_perfectJoin_of_mem_normalizer {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) {x : G} (hx : x ∈ perfectJoin J) :
    y * x * y⁻¹ ∈ perfectJoin J := by
  have h : (perfectJoin J).map (MulAut.conj y).toMonoidHom ≤ perfectJoin J := by
    refine le_perfectJoin ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hy w).1 (perfectJoin_le J hw)
    · rw [← Subgroup.map_commutator, perfectJoin_perfect]
  exact h ⟨x, hx, rfl⟩

@[expose] def twoElems (J : Subgroup G) : Set G := {x | x ∈ J ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}

@[expose] def twoCore (J : Subgroup G) : Subgroup G :=
  Subgroup.closure ((perfectJoin J : Set G) ∪ twoElems J)

theorem perfectJoin_le_twoCore (J : Subgroup G) : perfectJoin J ≤ twoCore J :=
  fun _ hx => Subgroup.subset_closure (Or.inl hx)

theorem twoElems_subset_twoCore (J : Subgroup G) : twoElems J ⊆ twoCore J :=
  fun _ hx => Subgroup.subset_closure (Or.inr hx)

theorem twoCore_le (J : Subgroup G) : twoCore J ≤ J :=
  (Subgroup.closure_le J).2 (Set.union_subset (perfectJoin_le J) fun _ hx => hx.1)

theorem conj_mem_twoCore {J : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (J : Set G))
    {x : G} (hx : x ∈ twoCore J) : y * x * y⁻¹ ∈ twoCore J := by
  have h : twoCore J ≤ (twoCore J).comap (MulAut.conj y).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g (hg | ⟨hgJ, k, hk⟩)
    · show y * g * y⁻¹ ∈ twoCore J
      exact perfectJoin_le_twoCore J (conj_mem_perfectJoin_of_mem_normalizer hy hg)
    · show y * g * y⁻¹ ∈ twoCore J
      refine twoElems_subset_twoCore J ⟨(Subgroup.mem_normalizer_iff.1 hy g).1 hgJ, k, ?_⟩
      rw [conj_pow, hk]
      simp
  exact h hx

theorem mem_normalizer_twoCore {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) :
    y ∈ Subgroup.normalizer ((twoCore J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_twoCore hy hx, fun hx => ?_⟩
  have := conj_mem_twoCore (inv_mem hy) hx
  simpa [mul_assoc] using this

theorem mem_normalizer_perfectJoin {J : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (J : Set G)) :
    y ∈ Subgroup.normalizer ((perfectJoin J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_perfectJoin_of_mem_normalizer hy hx, fun hx => ?_⟩
  have := conj_mem_perfectJoin_of_mem_normalizer (inv_mem hy) hx
  simpa [mul_assoc] using this

theorem borelLike_facts {J S T : Subgroup G} (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) (hTJ : T ≤ J)
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTodd : ∀ t ∈ T, ∃ m : ℕ, Odd m ∧ t ^ m = 1)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) (hgen : J ≤ T ⊔ S ⊔ perfectJoin J) :
    twoCore J = perfectJoin J ⊔ S ∧ ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ twoCore J := by
  set P := perfectJoin J with hP
  have hJP : J ≤ Subgroup.normalizer (P : Set G) := le_normalizer_perfectJoin J
  have hT' : T ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup (hJP (hTJ ht)) (hTS ht)
  have hS' : S ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun s hs =>
    Subgroup.le_normalizer (Subgroup.mem_sup_right hs)
  have hP' : P ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun w hw =>
    Subgroup.le_normalizer (Subgroup.mem_sup_left hw)
  have hJN : J ≤ Subgroup.normalizer ((P ⊔ S : Subgroup G) : Set G) := fun g hg =>
    (sup_le (sup_le hT' hS') hP') (hgen hg)
  have hNJ : P ⊔ S ≤ J := sup_le (perfectJoin_le J) hSJ
  have hdec : ∀ a ∈ J, ∃ t ∈ T, ∃ n ∈ P ⊔ S, a = t * n := by
    intro a ha
    have hEq : T ⊔ S ⊔ P = T ⊔ (P ⊔ S) := by rw [sup_assoc, sup_comm S P]
    have h1 : a ∈ T ⊔ (P ⊔ S) := by
      rw [← hEq]
      exact hgen ha
    have h2 := Subgroup.coe_mul_of_left_le_normalizer_right T (P ⊔ S) hT'
    rw [← SetLike.mem_coe, h2, Set.mem_mul] at h1
    obtain ⟨t, ht, n, hn, rfl⟩ := h1
    exact ⟨t, ht, n, hn, rfl⟩
  have : ((P ⊔ S).subgroupOf J).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hJN
  set φ : ↥J →* ↥J ⧸ (P ⊔ S).subgroupOf J := QuotientGroup.mk' ((P ⊔ S).subgroupOf J) with hφ
  have hφt : ∀ a (ha : a ∈ J), ∃ t, ∃ ht : t ∈ T, φ ⟨a, ha⟩ = φ ⟨t, hTJ ht⟩ := by
    intro a ha
    obtain ⟨t, ht, n, hn, rfl⟩ := hdec a ha
    refine ⟨t, ht, ?_⟩
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_inv_rev, mul_assoc] using inv_mem hn
  have hker : ∀ x (hx : x ∈ J), φ ⟨x, hx⟩ = 1 → x ∈ P ⊔ S := by
    intro x hx h
    have := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 this
  have hle1 : twoCore J ≤ P ⊔ S := by
    refine (Subgroup.closure_le _).2 (Set.union_subset (fun w hw => Subgroup.mem_sup_left hw) ?_)
    rintro x ⟨hxJ, k, hk⟩
    obtain ⟨t, ht, h1⟩ := hφt x hxJ
    obtain ⟨m, hm, htm⟩ := hTodd t ht
    have h2 : φ ⟨x, hxJ⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxJ⟩ : ↥J) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h3 : φ ⟨x, hxJ⟩ ^ m = 1 := by
      rw [h1, ← map_pow]
      have : (⟨t, hTJ ht⟩ : ↥J) ^ m = 1 := Subtype.ext (by simpa using htm)
      rw [this, map_one]
    apply hker x hxJ
    have hd : orderOf (φ ⟨x, hxJ⟩) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hle2 : P ⊔ S ≤ twoCore J := by
    refine sup_le (perfectJoin_le_twoCore J) fun s hs => twoElems_subset_twoCore J ⟨hSJ hs, ?_⟩
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hEq : twoCore J = P ⊔ S := le_antisymm hle1 hle2
  refine ⟨hEq, fun a ha b hb => ?_⟩
  rw [hEq]
  · obtain ⟨t₁, ht₁, h1⟩ := hφt a ha
    obtain ⟨t₂, ht₂, h2⟩ := hφt b hb
    have hcomm : ⁅(⟨a, ha⟩ : ↥J), (⟨b, hb⟩ : ↥J)⁆ ∈ ((P ⊔ S).subgroupOf J) := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      have hc : ⁅(⟨t₁, hTJ ht₁⟩ : ↥J), (⟨t₂, hTJ ht₂⟩ : ↥J)⁆ = 1 := by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        rw [mul_inv_eq_one, hTc _ ht₁ _ ht₂]
        group
      change φ ⁅_, _⁆ = 1
      rw [map_commutatorElement, h1, h2, ← map_commutatorElement, hc, map_one]
    exact Subgroup.mem_subgroupOf.1 hcomm

theorem pSubgroup_le_perfectJoin {J S : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS2 : IsPGroup 2 S) (hSJ : S ≤ J) {A : Subgroup G} (hA : A ≤ perfectJoin J ⊔ S)
    (hAp : IsPGroup p A) : A ≤ perfectJoin J := by
  set P := perfectJoin J with hP
  have hJP : J ≤ Subgroup.normalizer (P : Set G) := le_normalizer_perfectJoin J
  have hNJ : P ⊔ S ≤ J := sup_le (perfectJoin_le J) hSJ
  have hNP : P ⊔ S ≤ Subgroup.normalizer (P : Set G) := hNJ.trans hJP
  have : (P.subgroupOf (P ⊔ S)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNP
  intro x hx
  have hxN : x ∈ P ⊔ S := hA hx
  have h2 := Subgroup.coe_mul_of_left_le_normalizer_right S P (hSJ.trans hJP)
  have hxN' : x ∈ ((S ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hxN
  rw [h2, Set.mem_mul] at hxN'
  obtain ⟨s, hs, w, hw, rfl⟩ := hxN'
  obtain ⟨k, hk⟩ := hAp ⟨s * w, hx⟩
  obtain ⟨l, hl⟩ := hS2 ⟨s, hs⟩
  set ψ : ↥(P ⊔ S) →* ↥(P ⊔ S) ⧸ P.subgroupOf (P ⊔ S) := QuotientGroup.mk' _ with hψ
  have hsN : s ∈ P ⊔ S := Subgroup.mem_sup_right hs
  have hψeq : ψ ⟨s * w, hxN⟩ = ψ ⟨s, hsN⟩ := by
    rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_inv_rev, mul_assoc] using inv_mem hw
  have h1 : ψ ⟨s * w, hxN⟩ ^ p ^ k = 1 := by
    rw [← map_pow]
    have : (⟨s * w, hxN⟩ : ↥(P ⊔ S)) ^ p ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [this, map_one]
  have h3 : ψ ⟨s * w, hxN⟩ ^ 2 ^ l = 1 := by
    rw [hψeq, ← map_pow]
    have : (⟨s, hsN⟩ : ↥(P ⊔ S)) ^ 2 ^ l = 1 := Subtype.ext (by
      have := congrArg Subtype.val hl
      simpa using this)
    rw [this, map_one]
  have hd : orderOf (ψ ⟨s * w, hxN⟩) ∣ Nat.gcd (p ^ k) (2 ^ l) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h3)
  have hcop : Nat.Coprime (p ^ k) (2 ^ l) :=
    Nat.Coprime.pow k l ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hd
  have := (QuotientGroup.eq_one_iff _).1 hd
  exact Subgroup.mem_subgroupOf.1 this

end CFSG.AGLEmbedding.ParabAutIrr
