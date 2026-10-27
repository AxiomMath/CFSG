module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelOrbit

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage2 (urRows)

variable {ε : Eps}

@[expose] noncomputable def PM (ε : Eps) : Subgroup (Equiv.Perm (Fin (deg ε))) :=
  Lm ε ⊓ normalizer (QMm ε : Set _)

@[expose] noncomputable def aM (ε : Eps) : Equiv.Perm (Fin (deg ε)) := psiM ε (Pi.single 0 1)

theorem pM_mem_normalizer (i : Fin 6) : pM ε i ∈ normalizer (QMm ε : Set _) :=
  mem_normalizer_of_conj_mem fun x hx => by
    obtain ⟨v, rfl⟩ := mem_QMm.1 hx
    rw [pM_act]
    exact psiM_mem_Q _

theorem uM_mem_normalizer (k : Fin 6) : uM ε k ∈ normalizer (QMm ε : Set _) :=
  mem_normalizer_of_conj_mem fun x hx => by
    obtain ⟨v, rfl⟩ := mem_QMm.1 hx
    rw [uM_act]
    exact psiM_mem_Q _

theorem QMm_le_PM : QMm ε ≤ PM ε := fun _ hx => ⟨QMm_le_L hx, le_normalizer hx⟩

theorem PQm_le_PM : PQm ε ≤ PM ε := by
  rw [PQm_eq, closure_le]
  rintro x (⟨j, rfl⟩ | ⟨i, rfl⟩)
  · exact QMm_le_PM (psiM_mem_Q _)
  · exact ⟨pM_mem_L i, pM_mem_normalizer i⟩

theorem UQm_le_PM : UQm ε ≤ PM ε := by
  rw [UQm_eq, closure_le]
  rintro x (⟨j, rfl⟩ | ⟨k, rfl⟩)
  · exact QMm_le_PM (psiM_mem_Q _)
  · exact ⟨uM_mem_L k, uM_mem_normalizer k⟩

theorem PQm_eq_PM : PQm ε = PM ε :=
  eq_of_le_of_card_ge PQm_le_PM (by rw [card_PQm]; exact card_normalizer_le)

theorem card_PM : Nat.card (PM ε) = 64 * (oBound ε / 2) := by rw [← PQm_eq_PM, card_PQm]

theorem zero_mem_pBase : (⟨0, by have := one_le_deg ε; omega⟩ : Fin (deg ε)) ∈ pBase ε := by
  cases ε <;> decide

theorem eq_one_of_fix_Oset {y : Equiv.Perm (Fin (deg ε))} (hy : y ∈ PQm ε)
    (hfix : ∀ z ∈ Oset ε, y z = z) : y = 1 := by
  have hV : ValidSchreier (pQ ε) := ofArrays_valid (by norm_num) (pChain_ok ε).1
  have h1 : y ∈ (pQ ε).levelSubgroup (pQ ε).baseCount := by
    rw [RawSchreierDatum.mem_levelSubgroup_iff _ hV _ le_rfl]
    refine ⟨hy, fun b hb => hfix b (pBase_mem_Oset ?_)⟩
    have : (pQ ε).base.toList = pBase ε := RawSchreierDatum.ofArrays_base_toList
    rw [List.take_of_length_le (by simp), this] at hb
    exact hb
  rw [RawSchreierDatum.levelSubgroup_terminal_eq_bot _ hV, mem_bot] at h1
  exact h1

theorem mem_QMm_of_commute {x : Equiv.Perm (Fin (deg ε))} (hxL : x ∈ Lm ε)
    (hx : ∀ q ∈ QMm ε, x * q = q * x) : x ∈ QMm ε := by
  have hxN : x ∈ normalizer (QMm ε : Set _) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun q hq => (hx q hq).symm)
  have hxP : x ∈ PQm ε := by rw [PQm_eq_PM]; exact ⟨hxL, hxN⟩
  set z0 : Fin (deg ε) := ⟨0, by have := one_le_deg ε; omega⟩
  have hz0 : z0 ∈ Oset ε := pBase_mem_Oset zero_mem_pBase
  obtain ⟨v, hv⟩ := exists_psiM_apply (apply_mem_Oset hxN hz0)
  obtain ⟨y, hy⟩ : ∃ y, y = (psiM ε v)⁻¹ * x := ⟨_, rfl⟩
  have hyP : y ∈ PQm ε := hy ▸ mul_mem (inv_mem (psiM_mem_P v)) hxP
  have hyQ : ∀ q ∈ QMm ε, y * q = q * y := by
    intro q hq
    have h1 := hx q hq
    obtain ⟨w, rfl⟩ := mem_QMm.1 hq
    have h2 : (psiM ε v)⁻¹ * psiM ε w = psiM ε w * (psiM ε v)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← psiM_add, add_comm, psiM_add, mul_assoc,
        mul_inv_cancel, mul_one]
    calc y * psiM ε w = (psiM ε v)⁻¹ * (x * psiM ε w) := by rw [hy]; group
      _ = (psiM ε v)⁻¹ * (psiM ε w * x) := by rw [h1]
      _ = ((psiM ε v)⁻¹ * psiM ε w) * x := by group
      _ = psiM ε w * (psiM ε v)⁻¹ * x := by rw [h2]
      _ = psiM ε w * y := by rw [hy]; group
  have hy0 : y z0 = z0 := by
    rw [hy, Equiv.Perm.mul_apply, ← hv]
    simp [z0]
  have hfix : ∀ z ∈ Oset ε, y z = z := by
    intro z hz
    obtain ⟨w, rfl⟩ := exists_psiM_apply hz
    have := congrArg (fun g : Equiv.Perm (Fin (deg ε)) => g z0) (hyQ _ (psiM_mem_Q w))
    simp only [Equiv.Perm.mul_apply, hy0] at this
    exact this
  have hy1 := eq_one_of_fix_Oset hyP hfix
  have : x = psiM ε v := by
    have := congrArg (fun g => psiM ε v * g) (hy.symm.trans hy1)
    simpa using this
  rw [this]
  exact psiM_mem_Q v

theorem center_UQm {x : Equiv.Perm (Fin (deg ε))} (hx : x ∈ UQm ε)
    (hc : ∀ y ∈ UQm ε, x * y = y * x) : x = 1 ∨ x = aM ε := by
  have hxQ := mem_QMm_of_commute (UQm_le_PM hx).1 fun q hq => hc q (QMm_le_U hq)
  obtain ⟨v, rfl⟩ := mem_QMm.1 hxQ
  have hfix : ∀ k : Fin 6, toMat 6 6 (urRows ε k) *ᵥ v = v := by
    intro k
    apply psiM_injective (ε := ε)
    rw [← uM_act, ← hc _ (uM_mem_U k), mul_inv_cancel_right]
  rcases eq_of_urRows_fixed hfix with rfl | rfl
  · exact Or.inl psiM_zero
  · exact Or.inr rfl

theorem UQm_max {V : Subgroup (Equiv.Perm (Fin (deg ε)))}
    (hVL : V ≤ Lm ε) (hV : IsPGroup 2 V) (hUV : UQm ε ≤ V) : V = UQm ε := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
  have hdvd : 2 ^ k ∣ 4096 * lOdd ε := by
    rw [← hk, ← card_Lm]
    exact card_dvd_of_le hVL
  have hcop : Nat.Coprime (2 ^ k) (lOdd ε) :=
    Nat.Coprime.pow_left _ ((Nat.coprime_two_left).2 (odd_lOdd ε))
  have h4096 : 2 ^ k ∣ 4096 := hcop.dvd_of_dvd_mul_right hdvd
  have hle : Nat.card V ≤ Nat.card (UQm ε) := by
    rw [hk, card_UQm]
    exact Nat.le_of_dvd (by norm_num) h4096
  exact (eq_of_le_of_card_ge hUV hle).symm

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
