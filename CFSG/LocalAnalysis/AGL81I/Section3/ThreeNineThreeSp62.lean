module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies
public import CFSG.LocalAnalysis.StandardType.SpSixSylowOvergroup
import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner
import CFSG.Adapters.LieModelOrders

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem sp62_card_dvd_of_not_dvd_index
    {Y : Subgroup H6} (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) :
    Nat.card Y ∣ 51840 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.StandardType.SylowOvergroup.forall_of_sylow_le T0S (fun Y => Nat.card Y ∣ 51840)
    ?_ ?_ hY h3
  · intro g Y hY'
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hY'
  · intro Y hTY hYtop
    have hT : T0 ≤ Y := by
      rw [← coe_T0S]
      exact hTY
    rw [← card_W0]
    exact Subgroup.card_dvd_of_le (CFSG.StandardType.SpSixSylow.le_W0_of_ne_top hT hYtop)

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_Sp62
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSp 3 2 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hLie : LieModel ↥K .PSp 3 2 1 := Or.inl ⟨by decide, hK⟩
  have hcard : Nat.card ↥K = 1451520 := LieModel.card_psp_three_two hLie
  have hZ : Subgroup.center ↥K = ⊥ := CFSG.RankThree.PartTwo.Sec8.Hering611.center_eq_bot_of_sp62 hK
  have hOut : Nat.card (Outer ↥K) = 1 :=
    CFSG.ComponentClassification.Foote5.card_outer_eq_one_of_psp_three_two hK
  obtain ⟨hY, hm3, hmd, h3Y, hdY, hdK⟩ := h.index_facts hZ (by rw [hOut]; norm_num)
    (by rw [hOut]; exact Nat.Prime.not_dvd_one h.d_prime)
  rw [hcard] at h3Y hdY hdK
  obtain ⟨e⟩ := CFSG.LocalAnalysis.EvenBN.Tits.R2.nonempty_mulEquiv_H6_of_lieModel hLie
  have h3idx : ¬ 3 ∣ (X₁.subgroupOf K).index := by
    intro h3
    have := hm3
    unfold Nat.ModEq at this
    omega
  have hYW : Nat.card (X₁.subgroupOf K) ∣ 51840 :=
    CFSG.StandardType.SylowOvergroup.forall_of_mulEquiv (p := 3) e
      (fun A _ => Nat.card A ∣ 51840)
      (fun A B _ _ f hA => by rwa [← Nat.card_congr f.toEquiv])
      (fun Y hY h3 => sp62_card_dvd_of_not_dvd_index hY h3) _ hY h3idx
  have hd57 : d = 5 ∨ d = 7 := by
    have hfac : (1451520 : ℕ) = 2 ^ 9 * 3 ^ 4 * 5 * 7 := by norm_num
    rw [hfac] at hdK
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp h1)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1)
  have h81 : (3 : ℕ) ^ (1451520 : ℕ).factorization 3 = 81 := by
    have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 4)
      (k := 17920) (N := 1451520) (by norm_num) (by norm_num)).symm
    rw [this]
    norm_num
  rw [h81] at h3Y
  rcases hd57 with rfl | rfl
  ·
    have h5 : (5 : ℕ) ^ (1451520 : ℕ).factorization 5 = 5 := by
      have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 5) (a := 1)
        (k := 290304) (N := 1451520) (by norm_num) (by norm_num)).symm
      rw [this]
      norm_num
    rw [h5] at hdY
    have h405 : 405 ∣ Nat.card (X₁.subgroupOf K) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 81 5) h3Y hdY
    have hidx := index_dvd_div_of_dvd_card h405
    rw [hcard] at hidx
    have h28 : 28 ∣ (X₁.subgroupOf K).index := by
      obtain ⟨k, hk⟩ := hYW
      have hmul := (X₁.subgroupOf K).card_mul_index
      rw [hcard] at hmul
      have hpos : 0 < Nat.card (X₁.subgroupOf K) := Nat.card_pos
      refine ⟨k, Nat.eq_of_mul_eq_mul_left hpos ?_⟩
      rw [hmul]
      calc (1451520 : ℕ) = 28 * 51840 := by norm_num
        _ = 28 * (Nat.card (X₁.subgroupOf K) * k) := by rw [hk]
        _ = Nat.card (X₁.subgroupOf K) * (28 * k) := by ring
    have key : ∀ m ∈ Nat.divisors 3584, 28 ∣ m → m ≡ 1 [MOD 3] → m ≡ 1 [MOD 5] → False := by
      decide +kernel
    exact key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) h28 hm3 hmd
  ·
    have h7 : (7 : ℕ) ^ (1451520 : ℕ).factorization 7 = 7 := by
      have := (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 7) (a := 1)
        (k := 207360) (N := 1451520) (by norm_num) (by norm_num)).symm
      rw [this]
      norm_num
    rw [h7] at hdY
    have := hdY.trans hYW
    norm_num at this

theorem threeNineThreeSp62_holds :
    ThreeNineThreeSp62 :=
  fun _ _ _ _ _ _ _ _ h hK => false_of_threeNineHyp_Sp62 h hK

end CFSG.LocalAnalysis.AGL81I.Section3
