module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem card_sl2 (F : Type) [Field F] [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  rw [Matrix.card_SL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card F with hq
  have hq1 : 2 ≤ q := Fintype.one_lt_card
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one]; ring_nf
  have h2 : (q ^ 2 - 1) * (q * (q - 1)) = (q * (q ^ 2 - 1)) * (q - 1) := by ring
  rw [h1, h2]
  exact Nat.mul_div_cancel _ (by omega)

variable {G : Type*} [Group G]

theorem lin2_card_U {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    Nat.card (blockU L) = 2 ^ (2 * n) * Nat.card (blockZ L) := by
  obtain ⟨F, _, _, hcard, α, hα, hker, β, hβ, hβker, hequiv⟩ := h
  have h1 := Subgroup.card_ker_mul_card_of_surjective hβ
  rw [hβker] at h1
  have h2 : Nat.card ((blockZ L).subgroupOf (blockU L)) = Nat.card (blockZ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card (Multiplicative (Fin 2 → F)) = (2 ^ n) ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card, hcard]
    simp
  rw [h2, h3] at h1
  rw [← h1, mul_comm]
  ring

theorem lin2_card_L {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    Nat.card L = Nat.card (pCoreOf 2 L) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
  obtain ⟨F, _, _, hcard, α, hα, hker, β, hβ, hβker, hequiv⟩ := h
  have h1 := Subgroup.card_ker_mul_card_of_surjective hα
  rw [hker, card_sl2, hcard] at h1
  rw [← h1]
  congr 1
  unfold pCoreOf
  rw [Subgroup.card_map_of_injective L.subtype_injective]

theorem lin2_card_sylow [Finite G] {L P : Subgroup G} {n : ℕ} (h : IsLin2Type L n)
    (hP : IsSylowTwoOf P L) : Nat.card P = Nat.card (pCoreOf 2 L) * 2 ^ n := by
  have hL := lin2_card_L h
  have hK : IsPGroup 2 (pCoreOf 2 L) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hK
  obtain ⟨F, _, _, hcard, -⟩ := h
  have hn : 0 < n := by
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    rw [hcard] at h1
    exact Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
  have h2n : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn.ne') (by norm_num)
  have h1n : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hodd : ¬ 2 ∣ (2 ^ n) ^ 2 - 1 := by omega
  have hpos : 0 < (2 ^ n) ^ 2 - 1 := by
    have : 2 ≤ (2 ^ n) ^ 2 := Nat.le_of_dvd (by positivity) h2n
    omega
  rw [hP.card_eq]
  unfold twoPart
  rw [hL, hk]
  have hf : (2 ^ k * (2 ^ n * ((2 ^ n) ^ 2 - 1))).factorization 2 = k + n := by
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) hpos.ne']
    simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hodd,
      Nat.Prime.factorization_self Nat.prime_two]
  rw [hf, pow_add]

end CFSG.QuasithinUnique.Lin2
