module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def scalarKer {G : Type} [Group G] (S U E : Subgroup G) : Subgroup G where
  carrier := {s | s ∈ S ∧ s ∈ Subgroup.normalizer (U : Set G) ∧
    ∀ e ∈ E, s * e * s⁻¹ * e⁻¹ ∈ U}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    intro e _
    simp
  mul_mem' := by
    intro s t hs ht
    obtain ⟨hsS, hsN, hsE⟩ := hs
    obtain ⟨htS, htN, htE⟩ := ht
    refine ⟨Subgroup.mul_mem _ hsS htS, Subgroup.mul_mem _ hsN htN, ?_⟩
    intro e he
    have h1 : s * (t * e * t⁻¹ * e⁻¹) * s⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hsN (t * e * t⁻¹ * e⁻¹)).mp (htE e he)
    have h2 : s * e * s⁻¹ * e⁻¹ ∈ U := hsE e he
    have heq : (s * t) * e * (s * t)⁻¹ * e⁻¹
        = (s * (t * e * t⁻¹ * e⁻¹) * s⁻¹) * (s * e * s⁻¹ * e⁻¹) := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ h1 h2
  inv_mem' := by
    intro s hs
    obtain ⟨hsS, hsN, hsE⟩ := hs
    have hsN' : s⁻¹ ∈ Subgroup.normalizer (U : Set G) := Subgroup.inv_mem _ hsN
    refine ⟨Subgroup.inv_mem _ hsS, hsN', ?_⟩
    intro e he
    have h1 : (s * e * s⁻¹ * e⁻¹)⁻¹ ∈ U := Subgroup.inv_mem _ (hsE e he)
    have h2 : s⁻¹ * (s * e * s⁻¹ * e⁻¹)⁻¹ * s ∈ U := by
      have h := (Subgroup.mem_normalizer_iff.mp hsN' (s * e * s⁻¹ * e⁻¹)⁻¹).mp h1
      simpa using h
    rw [inv_inv]
    have heq : s⁻¹ * e * s * e⁻¹ = s⁻¹ * (s * e * s⁻¹ * e⁻¹)⁻¹ * s := by
      group
    rw [heq]
    exact h2

theorem scalarKer_le {G : Type} [Group G] (S U E : Subgroup G) : scalarKer S U E ≤ S := by
  intro s hs
  exact hs.1

theorem mem_scalarKer_iff {G : Type} [Group G] {S U E : Subgroup G}
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) {s : G} :
    s ∈ scalarKer S U E ↔ s ∈ S ∧ ∀ e ∈ E, s * e * s⁻¹ * e⁻¹ ∈ U := by
  constructor
  · rintro ⟨hsS, -, hsE⟩
    exact ⟨hsS, hsE⟩
  · rintro ⟨hsS, hsE⟩
    exact ⟨hsS, hSU hsS, hsE⟩

private lemma conj_mem_scalarKer {G : Type} [Group G] {S U E : Subgroup G}
    (hUS : U ≤ S) (hEU : E ≤ Subgroup.normalizer (U : Set G)) {e s : G}
    (he : e ∈ E) (hs : s ∈ scalarKer S U E) : e * s * e⁻¹ ∈ scalarKer S U E := by
  obtain ⟨hsS, hsN, hsE⟩ := hs
  have heN : e ∈ Subgroup.normalizer (U : Set G) := hEU he
  have huU : (s * e * s⁻¹ * e⁻¹)⁻¹ ∈ U := Subgroup.inv_mem _ (hsE e he)
  have huS : (s * e * s⁻¹ * e⁻¹)⁻¹ ∈ S := hUS huU
  have huN : (s * e * s⁻¹ * e⁻¹)⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer huU
  have hdecomp : e * s * e⁻¹ = (s * e * s⁻¹ * e⁻¹)⁻¹ * s := by
    group
  refine ⟨?_, ?_, ?_⟩
  · rw [hdecomp]
    exact Subgroup.mul_mem _ huS hsS
  · rw [hdecomp]
    exact Subgroup.mul_mem _ huN hsN
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer (U : Set G) := hEU hx
    have hxU : (s * e * s⁻¹ * e⁻¹) ∈ U := by simpa using Subgroup.inv_mem _ huU
    have h1 : s * x * s⁻¹ * x⁻¹ ∈ U := hsE x hx
    have h2 : x * (s * e * s⁻¹ * e⁻¹) * x⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hxN (s * e * s⁻¹ * e⁻¹)).mp hxU
    have heq : (e * s * e⁻¹) * x * (e * s * e⁻¹)⁻¹ * x⁻¹
        = (s * e * s⁻¹ * e⁻¹)⁻¹ * (s * x * s⁻¹ * x⁻¹)
            * (x * (s * e * s⁻¹ * e⁻¹) * x⁻¹) := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ huU h1) h2

theorem le_normalizer_scalarKer {G : Type} [Group G] {S U E : Subgroup G} (hUS : U ≤ S)
    (hEU : E ≤ Subgroup.normalizer (U : Set G)) :
    E ≤ Subgroup.normalizer (scalarKer S U E : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact conj_mem_scalarKer hUS hEU he
  · intro hs
    have h := conj_mem_scalarKer hUS hEU (E.inv_mem he) hs
    have h' : e⁻¹ * (e * s * e⁻¹) * e⁻¹⁻¹ = s := by group
    rwa [h'] at h

private lemma mem_of_mul_mem_of_two_pow {G : Type} [Group G] {K U : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hU : IsPGroup 2 U)
    {u z : G} (huN : u ∈ Subgroup.normalizer (K : Set G))
    (hzN : z ∈ Subgroup.normalizer (K : Set G)) (huU : u ∈ U)
    (hzq : z ^ q = 1) (huzK : u * z ∈ K) : z ∈ K := by
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let K' : Subgroup N := K.subgroupOf N
  haveI hK' : K'.Normal := Subgroup.normal_in_normalizer
  have huN' : u ∈ N := huN
  have hzN' : z ∈ N := hzN
  have huzN : u * z ∈ N := Subgroup.mul_mem _ huN' hzN'
  have hφuz : QuotientGroup.mk' K' ⟨u * z, huzN⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact huzK
  have hφz : QuotientGroup.mk' K' ⟨z, hzN'⟩ = (QuotientGroup.mk' K' ⟨u, huN'⟩)⁻¹ := by
    have h1 : QuotientGroup.mk' K' ⟨u, huN'⟩ * QuotientGroup.mk' K' ⟨z, hzN'⟩ = 1 := by
      rw [← map_mul]
      have h2 : (⟨u, huN'⟩ : N) * ⟨z, hzN'⟩ = ⟨u * z, huzN⟩ := Subtype.ext rfl
      rw [h2]
      exact hφuz
    exact (inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one hU ⟨u, huU⟩
  have huk : u ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hφu2 : (QuotientGroup.mk' K' ⟨u, huN'⟩) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have h1 : (⟨u, huN'⟩ : N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using huk)
    rw [h1, map_one]
  have hφz2 : (QuotientGroup.mk' K' ⟨z, hzN'⟩) ^ 2 ^ k = 1 := by
    rw [hφz, inv_pow, hφu2, inv_one]
  have hφzq : (QuotientGroup.mk' K' ⟨z, hzN'⟩) ^ q = 1 := by
    rw [← map_pow]
    have h1 : (⟨z, hzN'⟩ : N) ^ q = 1 := Subtype.ext (by simpa using hzq)
    rw [h1, map_one]
  have hcop : Nat.Coprime (2 ^ k) q :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  have h1 : orderOf (QuotientGroup.mk' K' ⟨z, hzN'⟩) ∣ Nat.gcd (2 ^ k) q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hφz2) (orderOf_dvd_of_pow_eq_one hφzq)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

private lemma not_dvd_sub_one_of_scalar {G : Type} [Group G] {U : Subgroup G} {q : ℕ}
    {s e₀ : G} {j : ℕ} (he₀q : e₀ ^ q = 1) (hsj : s * e₀ * s⁻¹ * (e₀ ^ j)⁻¹ ∈ U)
    (hne : s * e₀ * s⁻¹ * e₀⁻¹ ∉ U) : ¬ (q : ℤ) ∣ ((j : ℤ) - 1) := by
  have hzj : e₀ ^ ((j : ℤ) - 1) = e₀ ^ j * e₀⁻¹ := by
    rw [zpow_sub_one, zpow_natCast]
  rintro ⟨c, hc⟩
  have h1 : e₀ ^ ((j : ℤ) - 1) = 1 := by
    rw [hc]
    calc e₀ ^ ((q : ℤ) * c) = (e₀ ^ (q : ℤ)) ^ c := zpow_mul e₀ _ _
      _ = (e₀ ^ q) ^ c := by rw [zpow_natCast]
      _ = 1 := by rw [he₀q, one_zpow]
  apply hne
  have h2 : e₀ ^ j * e₀⁻¹ = 1 := by
    rw [← hzj, h1]
  have heq : s * e₀ * s⁻¹ * e₀⁻¹
      = (s * e₀ * s⁻¹ * (e₀ ^ j)⁻¹) * (e₀ ^ j * e₀⁻¹) := by
    group
  rw [heq, h2, mul_one]
  exact hsj

theorem le_of_scalar_commutator {G : Type} [Group G] {K U E : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hU : IsPGroup 2 U)
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEq : ∀ x ∈ E, x ^ q = 1) {s : G} (hsK : s ∈ K) {j : ℕ}
    (hsj : ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ U)
    {e₀ : G} (he₀ : e₀ ∈ E) (hne : s * e₀ * s⁻¹ * e₀⁻¹ ∉ U) : E ≤ K := by
  have hnotdvd : ¬ (q : ℤ) ∣ ((j : ℤ) - 1) :=
    not_dvd_sub_one_of_scalar (hEq e₀ he₀) (hsj e₀ he₀) hne
  intro x hxE
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hEK hxE
  have hsxK : s * x * s⁻¹ * x⁻¹ ∈ K := by
    have h1 : x * s⁻¹ * x⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hxN (s⁻¹)).mp (Subgroup.inv_mem _ hsK)
    have h2 : s * (x * s⁻¹ * x⁻¹) ∈ K := Subgroup.mul_mem _ hsK h1
    simpa [mul_assoc] using h2
  have huU : s * x * s⁻¹ * (x ^ j)⁻¹ ∈ U := hsj x hxE
  have huN : s * x * s⁻¹ * (x ^ j)⁻¹ ∈ Subgroup.normalizer (K : Set G) := hUK huU
  have hzx : x ^ ((j : ℤ) - 1) = x ^ j * x⁻¹ := by
    rw [zpow_sub_one, zpow_natCast]
  have hzN : x ^ ((j : ℤ) - 1) ∈ Subgroup.normalizer (K : Set G) := by
    rw [hzx]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hxN j) (Subgroup.inv_mem _ hxN)
  have huzK : (s * x * s⁻¹ * (x ^ j)⁻¹) * x ^ ((j : ℤ) - 1) ∈ K := by
    rw [hzx]
    rw [show (s * x * s⁻¹ * (x ^ j)⁻¹) * (x ^ j * x⁻¹) = s * x * s⁻¹ * x⁻¹ by group]
    exact hsxK
  have hzq : (x ^ ((j : ℤ) - 1)) ^ q = 1 := by
    calc (x ^ ((j : ℤ) - 1)) ^ q
        = (x ^ ((j : ℤ) - 1)) ^ (q : ℤ) := by rw [zpow_natCast]
      _ = x ^ (((j : ℤ) - 1) * (q : ℤ)) := (zpow_mul x _ _).symm
      _ = (x ^ (q : ℤ)) ^ ((j : ℤ) - 1) := zpow_mul' x _ _
      _ = (x ^ q) ^ ((j : ℤ) - 1) := by rw [zpow_natCast]
      _ = 1 := by rw [hEq x hxE, one_zpow]
  have hzK : x ^ ((j : ℤ) - 1) ∈ K :=
    mem_of_mul_mem_of_two_pow hq hq2 hU huN hzN huU hzq huzK
  have hndvd_n : ¬ q ∣ ((j : ℤ) - 1).natAbs := by
    intro hd
    apply hnotdvd
    have hd' : (q : ℤ) ∣ ((((j : ℤ) - 1).natAbs : ℕ) : ℤ) := by exact_mod_cast hd
    rwa [Int.dvd_natAbs] at hd'
  have hcop_n : Nat.Coprime ((j : ℤ) - 1).natAbs q :=
    ((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd_n).symm
  have hdvdq : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one (hEq x hxE)
  have hcop_d : Nat.Coprime ((j : ℤ) - 1).natAbs (orderOf x) :=
    Nat.Coprime.of_dvd_right hdvdq hcop_n
  have hmem : x ∈ Subgroup.zpowers (x ^ ((j : ℤ) - 1)) := by
    rw [mem_zpowers_zpow_iff, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hcop_d
  exact (Subgroup.zpowers_le_of_mem hzK) hmem

end CFSG.LocalAnalysis.RankThreeUC.S15

end
