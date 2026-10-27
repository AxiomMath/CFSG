module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveTMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

section TypeFree

variable {G : Type} [Group G]

theorem isPGroup_sup_zpowers_of_mem_normalizer {R : Subgroup G} (hR : IsPGroup 2 R) {s : G}
    (hsN : s ∈ normalizer (R : Set G)) (hs : IsPGroup 2 (zpowers s)) :
    IsPGroup 2 (R ⊔ zpowers s : Subgroup G) :=
  hR.to_sup_of_normal_left' hs ((zpowers_le).2 hsN)

theorem mem_of_mem_normalizer_of_not_two_dvd_index [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index) {s : G} (hsN : s ∈ normalizer (S : Set G))
    (hs : IsPGroup 2 (zpowers s)) : s ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := isPGroup_sup_zpowers_of_mem_normalizer hS hsN hs
  have heq : S ⊔ zpowers s = S :=
    (hS.toSylow hodd).is_maximal' hP le_sup_left
  rw [← heq]
  exact mem_sup_right (mem_zpowers s)

theorem isPGroup_zpowers_two_of_mul_self {t : G} (ht2 : t * t = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  refine ⟨1, Subtype.ext ?_⟩
  change (t ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht2, one_zpow]

theorem mem_normalizer_or_of_not_two_dvd_index [Finite G] {S₀ W : Subgroup G} {d t : G}
    (hS₀p : IsPGroup 2 S₀) (hS₀W : S₀ ≤ normalizer (W : Set G))
    (htW : t ∈ normalizer (W : Set G)) (htS₀ : t ∈ normalizer (S₀ : Set G))
    (hdS₀ : d ∈ normalizer (S₀ : Set G)) (hdt : d * t = t * d) (hdd : d * d ∈ S₀)
    (ht2 : t * t = 1) (hodd : ¬ 2 ∣ (S₀ ⊔ zpowers d ⊔ zpowers t).index) :
    ∀ s ∈ normalizer ((S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) : Set G),
      IsPGroup 2 (zpowers s) → s ∈ normalizer (W : Set G) ∨ d⁻¹ * s ∈ normalizer (W : Set G) := by
  intro s hsN hs
  set S₁ : Subgroup G := S₀ ⊔ zpowers t with hS₁def
  have hdS₁ : d ∈ normalizer (S₁ : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer hdS₀
      (mem_normalizer_zpowers_of_mul_eq_mul hdt.symm)
  have hddS₁ : d * d ∈ S₁ := mem_sup_left hdd
  have hS₁W : S₁ ≤ normalizer (W : Set G) := sup_le hS₀W ((zpowers_le).2 htW)
  have hSeq : S₀ ⊔ zpowers d ⊔ zpowers t = S₁ ⊔ zpowers d := by
    rw [hS₁def, sup_right_comm]
  have hS₀d : IsPGroup 2 (S₀ ⊔ zpowers d : Subgroup G) :=
    isPGroup_sup_zpowers_of_mul_self_mem hS₀p hdS₀ hdd
  have htN : t ∈ normalizer ((S₀ ⊔ zpowers d : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer htS₀ (mem_normalizer_zpowers_of_mul_eq_mul hdt)
  have hSp : IsPGroup 2 (S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) :=
    isPGroup_sup_zpowers_of_mem_normalizer hS₀d htN (isPGroup_zpowers_two_of_mul_self ht2)
  have hsS := mem_of_mem_normalizer_of_not_two_dvd_index hSp hodd hsN hs
  rw [hSeq] at hsS
  rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hdS₁ hddS₁ hsS with h | h
  · exact Or.inl (hS₁W h)
  · refine Or.inr (hS₁W ?_)
    have h1 : d⁻¹ * s = d⁻¹ * (s * d) * d * (d * d)⁻¹ := by group
    rw [h1]
    exact mul_mem (inv_mul_mul_mem_of_mem_normalizer hdS₁ h) (inv_mem hddS₁)

theorem not_two_dvd_index_of_forall_conj [Finite G] {S : Subgroup G} {t : G}
    (hS : IsPGroup 2 S)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ⊓ centralizer ({t} : Set G) ≤ P →
      P ≤ centralizer ({t} : Set G) → P = S ⊓ centralizer ({t} : Set G))
    (hfus : ∀ s ∈ normalizer (S : Set G), IsPGroup 2 (zpowers s) →
      ∃ x ∈ S, s * t * s⁻¹ = x * t * x⁻¹) :
    ¬ 2 ∣ S.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  have hne : S ≠ (T : Subgroup G) := fun h => T.not_dvd_index (h ▸ h2)
  obtain ⟨s, hsT, hsS, hsN⟩ :=
    exists_mem_normalizer_notMem_of_lt_isPGroup T.isPGroup' (lt_of_le_of_ne hST hne)
  have hsp : IsPGroup 2 (zpowers s) := T.isPGroup'.to_le (zpowers_le.2 hsT)
  obtain ⟨x, hxS, hx⟩ := hfus s hsN hsp
  set n := x⁻¹ * s with hn
  have hnC : n ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc n * t = x⁻¹ * (s * t * s⁻¹) * s := by rw [hn]; group
      _ = x⁻¹ * (x * t * x⁻¹) * s := by rw [hx]
      _ = t * n := by rw [hn]; group
  have hnT : n ∈ (T : Subgroup G) := mul_mem (inv_mem (hST hxS)) hsT
  have hnS : n ∉ S := fun h => hsS (by
    have h1 : s = x * n := by rw [hn]; group
    rw [h1]
    exact mul_mem hxS h)
  have hP : IsPGroup 2 (S ⊓ centralizer ({t} : Set G) ⊔ zpowers n : Subgroup G) :=
    T.isPGroup'.to_le (sup_le (inf_le_left.trans hST) (zpowers_le.2 hnT))
  have hPeq := hmax _ hP le_sup_left (sup_le inf_le_right (zpowers_le.2 hnC))
  have hn' : n ∈ S ⊓ centralizer ({t} : Set G) := by
    rw [← hPeq]
    exact mem_sup_right (mem_zpowers n)
  exact hnS (mem_inf.1 hn').1

theorem mem_or_of_mem_sup_zpowers_sup_zpowers {S₀ : Subgroup G} {d t : G}
    (htS₀ : t ∈ normalizer (S₀ : Set G)) (hdS₀ : d ∈ normalizer (S₀ : Set G))
    (hdt : d * t = t * d) (hdd : d * d ∈ S₀) (ht2 : t * t = 1) {h : G}
    (hh : h ∈ S₀ ⊔ zpowers d ⊔ zpowers t) :
    h ∈ S₀ ∨ h * t ∈ S₀ ∨ h * d ∈ S₀ ∨ h * (d * t) ∈ S₀ := by
  have htN : t ∈ normalizer ((S₀ ⊔ zpowers d : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer htS₀ (mem_normalizer_zpowers_of_mul_eq_mul hdt)
  have htt : t * t ∈ S₀ ⊔ zpowers d := by rw [ht2]; exact one_mem _
  rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem htN htt hh with h1 | h1
  · rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hdS₀ hdd h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rcases mem_or_mul_mem_of_mem_sup_zpowers_of_mul_self_mem hdS₀ hdd h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr (Or.inr ?_))
      have h3 : h * (d * t) = h * t * d := by rw [hdt, mul_assoc]
      rw [h3]
      exact h2

theorem exists_mem_normalizer_notMem_mul_self_mem [Finite G] {S T : Subgroup G}
    (hT : IsPGroup 2 T) (hST : S < T) :
    ∃ d ∈ T, d ∉ S ∧ d ∈ normalizer (S : Set G) ∧ d * d ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsT, hsS, hsN⟩ := exists_mem_normalizer_notMem_of_lt_isPGroup hT hST
  obtain ⟨m, hm⟩ := hT ⟨s, hsT⟩
  have hm' : s ^ 2 ^ m = 1 := by
    have h1 := congrArg Subtype.val hm
    simpa using h1
  have hex : ∃ k : ℕ, s ^ 2 ^ (k + 1) ∈ S :=
    ⟨m, by rw [pow_succ, pow_mul, hm', one_pow]; exact one_mem _⟩
  classical
  set k := Nat.find hex with hk
  have hkS : s ^ 2 ^ (k + 1) ∈ S := Nat.find_spec hex
  have hkS' : s ^ 2 ^ k ∉ S := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero, pow_one]
      exact hsS
    · have h1 := Nat.find_min hex (show k - 1 < k by omega)
      rwa [show k - 1 + 1 = k by omega] at h1
  refine ⟨s ^ 2 ^ k, pow_mem hsT _, hkS', pow_mem hsN _, ?_⟩
  rw [← sq, ← pow_mul, ← pow_succ]
  exact hkS

end TypeFree

end CFSG.SeitzReduction.LinearPilot
