module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB

open CFSG.Open Subgroup

variable {A : Type} [Group A]

theorem mem_normalizer_sup' {H K : Subgroup A} {g : A} (hH : g ∈ normalizer (H : Set A))
    (hK : g ∈ normalizer (K : Set A)) : g ∈ normalizer ((H ⊔ K : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_normalizer_inf' {H K : Subgroup A} {g : A} (hH : g ∈ normalizer (H : Set A))
    (hK : g ∈ normalizer (K : Set A)) : g ∈ normalizer ((H ⊓ K : Subgroup A) : Set A) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

theorem mem_normalizer_centralizer' {L : Subgroup A} {g : A} (hg : g ∈ normalizer (L : Set A)) :
    g ∈ normalizer (centralizer (L : Set A) : Set A) := by
  have key : ∀ {g : A}, g ∈ normalizer (L : Set A) → ∀ a ∈ centralizer (L : Set A),
      g * a * g⁻¹ ∈ centralizer (L : Set A) := by
    intro g hg a ha
    have hg' := mem_normalizer_iff.mp hg
    rw [mem_centralizer_iff] at ha ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have e : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
      exact (hg' _).mpr (by rw [e]; exact hl)
    have h1 := ha _ hl'
    calc l * (g * a * g⁻¹) = g * ((g⁻¹ * l * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * l := by group
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key hg h hh, fun hh => ?_⟩
  have := key (inv_mem hg) _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem mem_normalizer_of_commute {T : Subgroup A} {b : A} (h : ∀ t ∈ T, b * t = t * b) :
    b ∈ normalizer (T : Set A) := by
  rw [mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    have h1 : b * t * b⁻¹ = t := by rw [h t ht, mul_inv_cancel_right]
    rw [h1]
    exact ht
  · intro ht
    have hbu : b * (b * t * b⁻¹) = (b * t * b⁻¹) * b := h _ ht
    have h2 : b * (b * t * b⁻¹) = b * t := by rw [hbu]; group
    have h3 : b * t * b⁻¹ = t := mul_left_cancel h2
    rwa [h3] at ht

theorem exists_mul_of_le_normalizer {K S : Subgroup A} (hS : S ≤ normalizer (K : Set A)) {y : A}
    (hy : y ∈ K ⊔ S) : ∃ s ∈ S, ∃ k ∈ K, y = s * k := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right S K hS
  have hy' : y ∈ ((S ⊔ K : Subgroup A) : Set A) := by rw [sup_comm]; exact hy
  rw [h] at hy'
  obtain ⟨s, hs, k, hk, rfl⟩ := hy'
  exact ⟨s, hs, k, hk, rfl⟩

theorem pow_mul_mem {K : Subgroup A} {s : A} (hs : s ∈ normalizer (K : Set A)) {k : A} (hk : k ∈ K)
    (m : ℕ) : ∃ k' ∈ K, (s * k) ^ m = s ^ m * k' := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', hm⟩ := ih
    have hconj : s⁻¹ * k' * s ∈ K := by
      have e : s * (s⁻¹ * k' * s) * s⁻¹ = k' := by group
      exact (mem_normalizer_iff.mp hs _).mpr (by rw [e]; exact hk')
    refine ⟨s⁻¹ * k' * s * k, K.mul_mem hconj hk, ?_⟩
    rw [pow_succ, hm, pow_succ]
    group

theorem mem_of_pow_mem {K S : Subgroup A} (hS : S ≤ normalizer (K : Set A)) (hS2 : IsPGroup 2 S)
    {y : A} (hy : y ∈ K ⊔ S) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hyq : y ^ q = 1) : y ∈ K := by
  obtain ⟨s, hsS, k, hkK, rfl⟩ := exists_mul_of_le_normalizer hS hy
  obtain ⟨a, ha⟩ := hS2 ⟨s, hsS⟩
  have hsa : s ^ (2 ^ a) = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨k', hk', hm⟩ := pow_mul_mem (hS hsS) hkK (2 ^ a)
  rw [hsa, one_mul] at hm
  have hcop : Nat.Coprime (2 ^ a) q :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
  have hpow : (s * k) ^ (2 ^ a * r) = s * k := by
    have h1 : (s * k) ^ (2 ^ a * r) = (s * k) ^ ((2 ^ a * r) % q) := by
      conv_lhs => rw [← Nat.div_add_mod (2 ^ a * r) q, pow_add, pow_mul, hyq, one_pow, one_mul]
    rw [h1, hr, pow_one]
  rw [← hpow, pow_mul, hm]
  exact K.pow_mem hk' r

variable [Finite A]

theorem exists_isSylowOf_ge {f : ℕ} [Fact f.Prime] {L X : Subgroup A} (hXL : X ≤ L)
    (hX : IsPGroup f X) : ∃ E : Subgroup A, CFSG.ABGLocalTools.IsSylowOf f E L ∧ X ≤ E := by
  have hX' : IsPGroup f (X.subgroupOf L) := hX.comap_subtype
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hXL]
  exact Subgroup.map_mono hQ

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB
