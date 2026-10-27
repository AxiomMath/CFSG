module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthFamily
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdConf

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def ordL2sq (Q : ℕ) : ℕ := Q ^ 2 * ((Q ^ 2) ^ 2 - 1) / 2

theorem ordL2sq_mono {Q Q' : ℕ} (h : Q ≤ Q') : ordL2sq Q ≤ ordL2sq Q' := by
  unfold ordL2sq
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul (Nat.pow_le_pow_left h 2)
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_left (Nat.pow_le_pow_left h 2) 2) 1

theorem lt_of_ordL2sq_dvd {Q N B : ℕ} (hN : 0 < N) (hB : N < ordL2sq B) (h : ordL2sq Q ∣ N) :
    Q < B := by
  by_contra hlt
  push Not at hlt
  have h1 := Nat.le_of_dvd hN h
  have h2 := ordL2sq_mono hlt
  omega

variable {H : Type} [Group H] [Finite H]

theorem card_PSL2_sq {F : Type} [Field F] [Finite F] {Q : ℕ} (hQ : Odd Q)
    (hF : Nat.card F = Q ^ 2) : Nat.card (StatedProj (StatedSL 2 F)) = ordL2sq Q := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  simp only [show 2 * (2 - 1) / 2 = 1 from rfl, pow_one, show Finset.Icc 2 2 = {2} from rfl,
    Finset.prod_singleton]
  have h2 : Nat.gcd 2 (Q ^ 2 - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hQ.pow odd_one))
  rw [h2]
  rfl

namespace StdConf

variable (c : StdConf H)

theorem odd_q : Odd (c.p ^ c.f) := (c.prime.odd_of_ne_two c.ne_two).pow

theorem card_K_bar : Nat.card (c.K ⧸ pPrimeCore 2 c.K) = ordL2sq (c.p ^ c.f) := by
  have h := OddClassSelector.statedClassicalModel_of_lieModel c.type_K
    (by simp [Blueprint.chevalleyExceptionalTags]) (by simp [Blueprint.reeTitsTags]) (by decide)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact card_PSL2_sq c.odd_q (by rw [hF, pow_mul, ← pow_mul, mul_comm, pow_mul])

theorem ordL2sq_dvd : ordL2sq (c.p ^ c.f) ∣ Nat.card ↥(generalizedFitting H) := by
  rw [← c.card_K_bar]
  calc Nat.card (c.K ⧸ pPrimeCore 2 c.K) ∣ Nat.card c.K := Subgroup.card_quotient_dvd_card _
    _ ∣ Nat.card ↥(generalizedFitting H) := Subgroup.card_dvd_of_le c.K_le_G

theorem ordL2sq_dvd_of_equiv {Y : Type*} [Group Y] (e : ↥(generalizedFitting H) ≃* Y) :
    ordL2sq (c.p ^ c.f) ∣ Nat.card Y := by
  rw [← Nat.card_congr e.toEquiv]
  exact c.ordL2sq_dvd

end StdConf

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
