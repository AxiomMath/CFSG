module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem i133_twoPart_pos (n : ℕ) : 0 < twoPart n := by
  unfold twoPart
  exact pow_pos (by norm_num) _

theorem i133_twoPart_mul_of_ne {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    twoPart (a * b) = twoPart a * twoPart b := by
  unfold twoPart
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]

theorem i133_twoPart_dvd_twoPart {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) : twoPart a ∣ twoPart b := by
  have ha : a ≠ 0 := fun h0 => hb (zero_dvd_iff.1 (h0 ▸ h))
  unfold twoPart
  exact pow_dvd_pow 2 ((Nat.factorization_le_iff_dvd ha hb).2 h 2)

theorem i133_twoPart_eq_one_of_odd {n : ℕ} (hn : Odd n) : twoPart n = 1 := by
  unfold twoPart
  have h2 : ¬ 2 ∣ n := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hn
  rw [Nat.factorization_eq_zero_of_not_dvd h2, pow_zero]

theorem i133_pow_two_le_twoPart {k n : ℕ} (hn : n ≠ 0) (h : 2 ^ k ∣ n) : 2 ^ k ≤ twoPart n := by
  unfold twoPart
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.prime_two.pow_dvd_iff_le_factorization hn).1 h)

theorem i133_exists_card_eq_twoPart (H : Type) [Group H] [Finite H] :
    ∃ K : Subgroup H, Nat.card K = twoPart (Nat.card H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2
    (n := (Nat.card H).factorization 2) (Nat.ordProj_dvd _ _)
  exact ⟨K, hK⟩

@[expose] noncomputable def i133ImageHom (p : ℕ) {G : Type} [Group G] {J I : Subgroup G} (hIJ : I ≤ J) :
    ↥I →* PQuot p J :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥J)).comp (Subgroup.inclusion hIJ)

theorem i133ImageHom_apply (p : ℕ) {G : Type} [Group G] {J I : Subgroup G} (hIJ : I ≤ J) (i : ↥I) :
    i133ImageHom p hIJ i = (QuotientGroup.mk (Subgroup.inclusion hIJ i) : PQuot p J) := rfl

theorem i133_card2_le_twoPart_image {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {J I : Subgroup G} (hIJ : I ≤ J) :
    card2 p I ≤ twoPart (Nat.card (i133ImageHom p hIJ).range) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set ι := i133ImageHom p hIJ with hι
  set K₀ : Subgroup ↥I := ι.ker with hK₀
  set O : Subgroup ↥I := GLAPPrimeCore p ↥I with hO
  have hinj : Function.Injective (Subgroup.inclusion hIJ) := Subgroup.inclusion_injective hIJ
  have hK₀map : K₀.map (Subgroup.inclusion hIJ) ≤ GLAPPrimeCore p ↥J := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : ι x = 1 := hx
    have h2 : (QuotientGroup.mk (Subgroup.inclusion hIJ x) : PQuot p J) = 1 := h1
    exact (QuotientGroup.eq_one_iff _).1 h2
  have hcopK : Nat.Coprime p (Nat.card K₀) := by
    have hdvd : Nat.card K₀ ∣ Nat.card (GLAPPrimeCore p ↥J) := by
      rw [← Subgroup.card_map_of_injective (f := Subgroup.inclusion hIJ) hinj]
      exact Subgroup.card_dvd_of_le hK₀map
    exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥J))
  have hK₀O : K₀ ≤ O := CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcopK
  have hk : 0 < Nat.card K₀ := Nat.card_pos
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hK₀O
  have h1 : K₀.index * Nat.card K₀ = Nat.card ↥I := Subgroup.index_mul_card K₀
  have h2 : O.index * Nat.card O = Nat.card ↥I := Subgroup.index_mul_card O
  have hidx : K₀.index = O.index * t := by
    apply Nat.eq_of_mul_eq_mul_right hk
    calc K₀.index * Nat.card K₀ = Nat.card ↥I := h1
      _ = O.index * Nat.card O := h2.symm
      _ = O.index * t * Nat.card K₀ := by rw [ht]; ring
  have hdivO : O.index ∣ K₀.index := ⟨t, hidx⟩
  have hdivR : O.index ∣ Nat.card ι.range := by
    rw [← Subgroup.index_ker ι]
    exact hdivO
  have hcard2 : card2 p I = twoPart O.index := rfl
  rw [hcard2]
  exact Nat.le_of_dvd (i133_twoPart_pos _) (i133_twoPart_dvd_twoPart Nat.card_pos.ne' hdivR)

end CFSG.LocalAnalysis.GLTheoremA
