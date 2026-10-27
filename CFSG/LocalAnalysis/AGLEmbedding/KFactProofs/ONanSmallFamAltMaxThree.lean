module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltMax
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltTransport
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltModelMore

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv

variable {K : Type} [Group K] [Finite K]

theorem exists_order_four_normalizer_of_isAltTwoP_three (hK : IsAltTwoP 3 K) (T : Sylow 3 K) :
    ∃ k : K, k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧ orderOf k = 4 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨e⟩ := hK
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  obtain ⟨Φ, hsign, hmem⟩ := exists_altModel hp2 hEab hEcard
  obtain ⟨g, hg⟩ := exists_sign_altMulPerm_eq_neg_one (p := 3) hp2
  set ν₀ : Perm (ZMod 3 × Fin 2) := altDg g 1 * altSwp with hν₀
  have hν₀sign : Perm.sign ν₀ = 1 := by
    rw [hν₀, map_mul, sign_altDg, hg, altMulPerm_one, map_one, sign_altSwp hp2]
    norm_num
  have hν₀N : ν₀ ∈ Subgroup.normalizer ((altEtr : Subgroup (Perm (ZMod 3 × Fin 2))) :
      Set (Perm (ZMod 3 × Fin 2))) :=
    mul_mem (altDg_mem_normalizer g 1) altSwp_mem_normalizer
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [altMulPerm_one, map_one] at hg
    norm_num at hg
  have hgg : g * g = 1 := by
    apply Units.ext
    have := ZMod.pow_card_sub_one_eq_one g.ne_zero
    simpa [sq] using this
  have hν₀sq : ν₀ * ν₀ = altDg g g := by
    calc ν₀ * ν₀ = altDg g 1 * (altSwp * altDg g 1) * altSwp := by simp only [hν₀, mul_assoc]
      _ = altDg g 1 * (altDg 1 g * altSwp) * altSwp := by rw [altSwp_mul_altDg]
      _ = (altDg g 1 * altDg 1 g) * (altSwp * altSwp) := by simp only [mul_assoc]
      _ = altDg g g := by rw [altDg_mul_altDg, altSwp_mul_altSwp, mul_one, mul_one, one_mul]
  have hν₀ne : ν₀ ^ 2 ^ 1 ≠ 1 := by
    rw [pow_one, sq, hν₀sq]
    intro h
    have h1 := congrArg (fun f : Perm (ZMod 3 × Fin 2) => f (1, 0)) h
    simp only [altDg_apply, Perm.one_apply] at h1
    exact hg1 (Units.ext (by simpa using congrArg Prod.fst h1))
  have hν₀4 : ν₀ ^ 2 ^ (1 + 1) = 1 := by
    have : ν₀ ^ 2 ^ (1 + 1) = (ν₀ * ν₀) * (ν₀ * ν₀) := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq ν₀, sq (ν₀ * ν₀)]
    rw [this, hν₀sq, altDg_mul_altDg, hgg, altDg_one_one]
  have hord : orderOf ν₀ = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hν₀ne hν₀4
    simpa using this
  let k : K := e.symm ⟨Φ ν₀, Perm.mem_alternatingGroup.2 ((hsign ν₀).trans hν₀sign)⟩
  have hιk : altPermEmbed e k = Φ ν₀ := by simp [k, altPermEmbed]
  refine ⟨k, ?_, ?_⟩
  · apply Subgroup.mem_normalizer_fintype
    intro t ht
    obtain ⟨x, hx⟩ := Φ.surjective (altPermEmbed e t)
    have hxE : x ∈ (altEtr : Subgroup (Perm (ZMod 3 × Fin 2))) :=
      (hmem x).1 (hx ▸ ⟨t, ht, rfl⟩)
    have hconj : ν₀ * x * ν₀⁻¹ ∈ (altEtr : Subgroup (Perm (ZMod 3 × Fin 2))) :=
      (Subgroup.mem_normalizer_iff.1 hν₀N x).1 hxE
    obtain ⟨t', ht', hι'⟩ := Subgroup.mem_map.1 ((hmem _).2 hconj)
    have : t' = k * t * k⁻¹ := by
      apply altPermEmbed_injective e
      rw [hι']
      simp only [map_mul, map_inv, hιk]
      rw [hx]
    exact this ▸ ht'
  · rw [← orderOf_injective (altPermEmbed e) (altPermEmbed_injective e) k, hιk,
      MulEquiv.orderOf_eq, hord]

theorem eq_or_eq_top_of_glbCore_le_three (hK : IsAltTwoP 3 K) (T : Sylow 3 K) {Y : Subgroup K}
    (hY : GLBCore 3 1 (T : Subgroup K) ≤ Y) : Y = GLBCore 3 1 (T : Subgroup K) ∨ Y = ⊤ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨k, hkN, hk4⟩ := exists_order_four_normalizer_of_isAltTwoP_three hK T
  set Γ := GLBCore 3 1 (T : Subgroup K) with hΓ
  set N := Subgroup.normalizer ((T : Subgroup K) : Set K) with hN
  obtain ⟨e⟩ := hK
  have hTcard : Nat.card T = 3 ^ 2 := sylowSq_of_isAltTwoP hp hp2 ⟨e⟩ T
  have hT0 : (T : Subgroup K) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hTcard
    norm_num at hTcard
  have hNΓ : N ≤ Γ := normalizer_le_glbCore_one hp T hT0
  have h9 : 9 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer : (T : Subgroup K) ≤ N)
    rwa [hTcard] at this
  have h4 : 4 ∣ Nat.card N := by
    have : orderOf (⟨k, hkN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hk4] at this
  have h36 : 36 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9 h4
  have hNY : Nat.card N ∣ Nat.card Y := Subgroup.card_dvd_of_le (hNΓ.trans hY)
  have hKcard : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv]
    have h2 : 2 * Nat.card (alternatingGroup (Fin (2 * 3))) = (2 * 3).factorial := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have h3 : (2 * 3).factorial = 720 := by decide
    omega
  have hidx : Y.index * Nat.card Y = 360 := by rw [Subgroup.index_mul_card, hKcard]
  by_cases hYtop : Y = ⊤
  · exact Or.inr hYtop
  · left
    have hsimple : IsSimpleGroup K := by
      have : IsSimpleGroup (alternatingGroup (Fin (2 * 3))) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.symm.isSimpleGroup_congr.1 this
    have hidx6 : 6 ≤ Y.index := by
      have hcore : Y.normalCore = ⊥ := by
        rcases hsimple.eq_bot_or_eq_top_of_normal Y.normalCore with h | h
        · exact h
        · exact absurd (top_le_iff.1 (h ▸ Subgroup.normalCore_le Y)) hYtop
      have h1 := Subgroup.index_normalCore_dvd_factorial_index (H := Y)
      rw [hcore, Subgroup.index_bot, hKcard] at h1
      by_contra hlt
      push Not at hlt
      generalize Y.index = j at h1 hlt
      interval_cases j <;> simp [Nat.factorial] at h1
    obtain ⟨m, hm⟩ := h36.trans hNY
    have hm10 : Y.index * m = 10 := by
      rw [hm] at hidx
      linarith
    have hm1 : m = 1 := by
      rcases Nat.lt_or_ge m 2 with h | h
      · interval_cases m
        · omega
        · rfl
      · nlinarith
    have hYcard : Nat.card Y = 36 := by rw [hm, hm1]; rfl
    have hΓcard : 36 ≤ Nat.card Γ :=
      (Nat.le_of_dvd Nat.card_pos h36).trans (Subgroup.card_le_of_le hNΓ)
    exact (Subgroup.eq_of_le_of_card_ge hY (by rw [hYcard]; exact hΓcard)).symm

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
