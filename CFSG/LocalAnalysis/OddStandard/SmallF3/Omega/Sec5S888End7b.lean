module

public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Goldschmidt.StrongClosure
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem exists_p_element_psl2 {f p : ℕ} (hf : 2 ≤ f) (hp : p.Prime) (hpf : p ∣ 2 ^ f - 1)
    (U : Sylow 2 PSL(2, GaloisField 2 f)) :
    ∃ d ∈ Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 f)) :
        Set PSL(2, GaloisField 2 f)),
      d ^ p = 1 ∧ ∃ u ∈ (U : Subgroup PSL(2, GaloisField 2 f)), d * u * d⁻¹ ≠ u := by
  obtain ⟨D, hDcyc, hDcard, -, hsup, hreg⟩ :=
    CFSG.Walter.psl2_even_normalizer_sylow_two hf U
  obtain ⟨-, hUcard⟩ := CFSG.Walter.psl2_even_sylow_two hf U
  obtain ⟨g, hg⟩ := hDcyc.exists_generator
  have hord : orderOf g = 2 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hDcard]
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set k : ℕ := (2 ^ f - 1) / p with hk
  have hdiv : p * k = 2 ^ f - 1 := by
    rw [hk]
    exact Nat.mul_div_cancel' hpf
  have hkpos : 0 < k := by
    rw [hk]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hklt : k < 2 ^ f - 1 := by
    rw [hk]
    exact Nat.div_lt_self (by omega) hp.one_lt
  have hg_ne : g ^ k ≠ 1 := by
    intro h
    have hdvd : orderOf g ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd hkpos hdvd
    omega
  have hgpow : (g : PSL(2, GaloisField 2 f)) ^ (2 ^ f - 1) = 1 := by
    have hg1 : (g : D) ^ (2 ^ f - 1) = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one g
    simpa [Subgroup.coe_pow] using congrArg (Subtype.val) hg1
  have hdp : ((g : PSL(2, GaloisField 2 f)) ^ k) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm k p, hdiv]
    exact hgpow
  obtain ⟨⟨u, hu⟩, hu1⟩ : ∃ a : (U : Subgroup PSL(2, GaloisField 2 f)), a ≠ 1 := by
    rw [← Subgroup.ne_bot_iff_exists_ne_one]
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    omega
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine ⟨(g : PSL(2, GaloisField 2 f)) ^ k, ?_, hdp, u, hu, ?_⟩
  · rw [← hsup]
    exact Subgroup.mem_sup_right (pow_mem g.2 k)
  · intro h
    have h1 : ((g ^ k : D) : PSL(2, GaloisField 2 f)) * u *
        ((g ^ k : D) : PSL(2, GaloisField 2 f))⁻¹ = u := by
      simpa [Subgroup.coe_pow] using h
    have h2 : ((1 : D) : PSL(2, GaloisField 2 f)) * u *
        ((1 : D) : PSL(2, GaloisField 2 f))⁻¹ = u := by simp
    exact hg_ne ((hreg u hu hu1' u hu hu1').unique h1 h2)

theorem exists_p_element_of_component {Y : Type} [Group Y] [Finite Y] (D : Sylow 2 Y)
    {J : Subgroup Y} [J.Normal] {f p : ℕ} (hf : 2 ≤ f) (hp : p.Prime) (hpf : p ∣ 2 ^ f - 1)
    (e : ↥J ≃* PSL(2, GaloisField 2 f)) :
    ∃ d ∈ J, (∀ x ∈ (D : Subgroup Y) ⊓ J, d * x * d⁻¹ ∈ (D : Subgroup Y) ⊓ J) ∧ d ^ p = 1 ∧
      ∃ u ∈ (D : Subgroup Y) ⊓ J, d * u * d⁻¹ ≠ u := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (D : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, D.isPGroup', by rw [Subgroup.relIndex_top_right]; exact D.not_dvd_index⟩
  obtain ⟨S, hS⟩ := hT.inf_of_le_normalizer (N := J) le_top
    (by rw [Subgroup.normalizer_eq_top])
  let U : Sylow 2 PSL(2, GaloisField 2 f) :=
    S.mapSurjective (f := (e : ↥J →* PSL(2, GaloisField 2 f))) e.surjective
  have hU : ∀ y, y ∈ (U : Subgroup PSL(2, GaloisField 2 f)) ↔
      e.symm y ∈ (S : Subgroup ↥J) := by
    intro y
    change y ∈ (S : Subgroup ↥J).map (e : ↥J →* PSL(2, GaloisField 2 f)) ↔ _
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨e.symm y, h, by simp⟩
  obtain ⟨d₀, hd₀, hd₀p, u₀, hu₀, hne⟩ := exists_p_element_psl2 hf hp hpf U
  refine ⟨((e.symm d₀ : ↥J) : Y), (e.symm d₀).2, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hS] at hx ⊢
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨x', hx', rfl⟩ := hx
    refine ⟨(e.symm d₀) * x' * (e.symm d₀)⁻¹, ?_, rfl⟩
    have hmemU : d₀ * e x' * d₀⁻¹ ∈ (U : Subgroup PSL(2, GaloisField 2 f)) :=
      ((Subgroup.mem_normalizer_iff.mp hd₀) (e x')).mp ((hU (e x')).mpr (by simpa using hx'))
    have : e ((e.symm d₀) * x' * (e.symm d₀)⁻¹) ∈
        (U : Subgroup PSL(2, GaloisField 2 f)) := by
      simpa [map_mul] using hmemU
    simpa using (hU _).mp this
  · have h1 : (e.symm d₀ : ↥J) ^ p = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      simpa using hd₀p
    exact (map_pow J.subtype (e.symm d₀) p).symm.trans (by rw [h1, map_one])
  · refine ⟨J.subtype (e.symm u₀), ?_, ?_⟩
    · rw [← hS]
      exact Subgroup.mem_map_of_mem J.subtype ((hU u₀).mp hu₀)
    · intro h
      have h' : (e.symm d₀ : ↥J) * (e.symm u₀) * (e.symm d₀)⁻¹ = e.symm u₀ := by
        apply J.subtype_injective
        simpa [map_mul] using h
      exact hne (by simpa [map_mul] using congrArg e h')

end CFSG.OddStandard.SmallF3.Omega
