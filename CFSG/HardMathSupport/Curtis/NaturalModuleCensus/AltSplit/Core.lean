module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagUnitary
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.EvenCentre
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsAux

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.LieOut CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

theorem not_sixteen_dvd_card_alt {p : ℕ} (hp : p = 5 ∨ p = 7) :
    ¬ 16 ∣ Nat.card (alternatingGroup (Fin p)) := by
  rcases hp with rfl | rfl
  · rw [nat_card_alt_five]; norm_num
  · rw [nat_card_alt_seven]; norm_num

theorem exists_quasisimple_of_sl2_hom {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hZ : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J)
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (h : BorelQuotient D n H π M) {π' : K →* ↥L ⧸ Subgroup.center ↥L}
    (hker : π'.ker = π.ker) {i : Fin D.rank}
    (hiJ : (rankOne D.rootGroup i).map π' ≤ quotImage L J)
    {k : Type} [Field k] [Finite k] [CharP k 2] {φ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hφ : Function.Injective φ) (hφR : φ.range ≤ rankOne D.rootGroup i)
    {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hk16 : 16 ∣ Nat.card k ∨ (p = 7 ∧ Nat.card k = 8))
    (hpk : p ∣ Nat.card k ^ 2 - 1) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ ψ : ↥X →* alternatingGroup (Fin p), ¬ ψ.ker ≤ Subgroup.center ↥X := by
  have hk8 : 8 ≤ Nat.card k := by
    rcases hk16 with h16 | ⟨-, h8⟩
    · exact (Nat.le_of_dvd Nat.card_pos h16).trans' (by norm_num)
    · exact h8.ge
  have hk4 : 4 ≤ Nat.card k := by omega
  set G := Matrix.SpecialLinearGroup (Fin 2) k with hG
  set ρ : G →* (↥L ⧸ Subgroup.center ↥L) := π'.comp φ with hρ
  have hker_ρ : ρ.ker ≤ Subgroup.center G := by
    intro g hg
    have hg1 : π' (φ g) = 1 := hg
    have hc : φ g ∈ Subgroup.center K := h.ker_central _ (hker ▸ hg1)
    rw [Subgroup.mem_center_iff]
    intro t
    apply hφ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hc (φ t)
  have hρJ : ρ.range ≤ quotImage L J := by
    refine le_trans ?_ hiJ
    rw [hρ, MonoidHom.range_comp]
    exact Subgroup.map_mono hφR
  have hcenter : Subgroup.center G = ⊥ := sl2_center_eq_bot
  have hker_bot : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have := hker_ρ hg
    rw [hcenter] at this
    exact this
  have hGcard : Nat.card G = Nat.card k * (Nat.card k ^ 2 - 1) := card_sl2
  have hpG : p ∣ Nat.card ρ.range := by
    have hc := Subgroup.card_ker_mul_card_range ρ
    rw [hker_bot, Subgroup.card_bot, one_mul, hGcard] at hc
    rw [hc]
    exact Dvd.dvd.mul_left hpk _
  have hcq : Nat.card (G ⧸ Subgroup.center G) = Nat.card G := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    have h1 : Nat.card (Subgroup.center G) = 1 := by rw [hcenter, Subgroup.card_bot]
    rw [h1, mul_one] at h
    exact h.symm
  have hno : NoAp p (G ⧸ Subgroup.center G) := by
    rcases hk16 with h16 | ⟨rfl, h8⟩
    · refine NoAp.of_dvd (r := 16) (not_sixteen_dvd_card_alt hp57) ?_
      rw [hcq, hGcard]
      exact Dvd.dvd.mul_right h16 _
    · refine noAp_seven_of_card_eq ?_
      rw [hcq, hGcard, h8]
      norm_num
  exact exists_quasisimple_of_cover hZ ρ hρJ hker_ρ (isQuasisimple_sl2 hk4) hpG hno

theorem false_of_quasisimple_of_altSq {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hAlt : PerfectSectionsAltSq p J)
    (hX : ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ ψ : ↥X →* alternatingGroup (Fin p), ¬ ψ.ker ≤ Subgroup.center ↥X) : False := by
  have hpp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  obtain ⟨X, hXJ, hXq, hpX, hno⟩ := hX
  obtain ⟨ψ, hψ⟩ := exists_hom_alternating_of_altSq hAlt hXJ hXq hpX hpp
  exact hno ψ hψ

theorem false_of_altSq_of_borel {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}
    (h : CompParabE L J) (hp57 : p = 5 ∨ p = 7) (hAlt : PerfectSectionsAltSq p J)
    {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* ↥L ⧸ Subgroup.center ↥L} {M : ℕ}
    (hB : BorelQuotient D n H π M)
    (hnode : (∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : Y) ∈ J) →
      ∀ π' : K →* ↥L ⧸ Subgroup.center ↥L, π'.ker = π.ker → ∀ i : Fin D.rank,
      (rankOne D.rootGroup i).map π' ≤ quotImage L J →
      ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
        ∀ ψ : ↥X →* alternatingGroup (Fin p), ¬ ψ.ker ≤ Subgroup.center ↥X) : False := by
  obtain ⟨hJL, T, hT, hNT⟩ := h.parab
  obtain ⟨π', -, hker, -, i, hi⟩ := exists_rankOne_le_of_borel hB (barSylow hT) (quotImage L J)
    (normalizer_barSylow_le_quotImage hT hNT) (quotImage_ne_normalizer hT hJL (h.ne_borel T hT) hNT)
  exact false_of_quasisimple_of_altSq hp57 hAlt
    (hnode (fun z hz => center_le_of_normalizer_le hT hNT hz) π' hker i hi)

theorem range_le_rankOne_of_hasSL2Node {K : Type} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {k : Type} [Field k] {φ : Matrix.SpecialLinearGroup (Fin 2) k →* K}
    (hU : ∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1))
    (hL : ∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1)) :
    φ.range ≤ rankOne D.rootGroup i := by
  rintro _ ⟨A, rfl⟩
  have hA := Sp.mem_closure_sl2 A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := k)) ∪ Set.range sl2Lower) ≤
      (rankOne D.rootGroup i).comap φ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact le_sup_left (a := D.rootGroup (Pi.single i 1)) (hU c)
    · exact le_sup_right (b := D.rootGroup (-Pi.single i 1)) (hL c)
  exact hle hA

theorem dvd_sq_sub_one_of_dvd {p c : ℕ} (h : p ∣ c - 1) : p ∣ c ^ 2 - 1 := by
  refine h.trans ?_
  simpa using Nat.sub_dvd_pow_sub_pow c 1 2

theorem split_exponent {p f : ℕ} (hp57 : p = 5 ∨ p = 7) (hf : 1 ≤ f) (h : p ∣ 2 ^ f - 1) :
    3 ≤ f ∧ (4 ≤ f ∨ (p = 7 ∧ f = 3)) := by
  rcases hp57 with rfl | rfl
  · have := four_le_of_five_dvd hf h
    exact ⟨by omega, Or.inl this⟩
  · have h3 := three_le_of_seven_dvd hf h
    rcases Nat.lt_or_ge f 4 with h4 | h4
    · exact ⟨h3, Or.inr ⟨rfl, by omega⟩⟩
    · exact ⟨h3, Or.inl h4⟩

theorem sixteen_dvd_two_pow {f : ℕ} (h : 4 ≤ f) : 16 ∣ 2 ^ f := by
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ f := pow_dvd_pow 2 h

theorem sixteen_or_eight {p f : ℕ} (hp57 : p = 5 ∨ p = 7) (hf : 1 ≤ f) (h : p ∣ 2 ^ f - 1) :
    16 ∣ 2 ^ f ∨ (p = 7 ∧ 2 ^ f = 8) := by
  obtain ⟨-, h4 | ⟨hp, rfl⟩⟩ := split_exponent hp57 hf h
  · exact Or.inl (sixteen_dvd_two_pow h4)
  · exact Or.inr ⟨hp, by norm_num⟩

theorem sixteen_dvd_two_pow_sq {f : ℕ} (h : 3 ≤ f) : 16 ∣ (2 ^ f) ^ 2 := by
  rw [← pow_mul]
  calc 16 = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ (f * 2) := pow_dvd_pow 2 (by omega)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
