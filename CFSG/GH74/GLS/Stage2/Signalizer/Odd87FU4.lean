module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL4
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section Embed

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem exists_injective_su2_su3 {q : ℕ} (hq : 1 ≤ q) :
    ∃ β : ↥(StatedSU 2 q K) →* ↥(StatedSU 3 q K), Function.Injective β := by
  let β : ↥(StatedSU 2 q K) →* ↥(StatedSU 3 q K) :=
    (blockGL3.comp (StatedSU 2 q K).subtype).codRestrict (StatedSU 3 q K) fun A =>
      map_blockGL3_statedSU_le hq ⟨A, A.2, rfl⟩
  refine ⟨β, ?_⟩
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : blockGL3 (A : GL (Fin 2) K) = 1 := congrArg Subtype.val hA
  exact Subtype.ext (blockGL3_eq_one_of_scalar (by rw [h1]; exact one_mem _))

theorem exists_injective_qdSL_hypPSU [Fact p.Prime] [CharP K p] (h : UnitaryFieldData p f K)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ ψ : CFSG.Glauberman.qdSL p →* hypPSU h 2 0, Function.Injective ψ := by
  obtain ⟨e₁⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := p) (f := f) hK
  obtain ⟨β, hβ⟩ := exists_injective_su2_su3 (K := K) (q := p ^ f)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  obtain ⟨ψ₃, hψ₃⟩ := exists_su3Hom_hypSU h (r := 2) (ε := 0) (by norm_num)
  let ι : ZMod p →+* ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) := ZMod.castHom (dvd_refl p) _
  let φ : SpecialLinearGroup (Fin 2) (ZMod p) →*
      SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) :=
    SpecialLinearGroup.map ι
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f) =>
      (g : Matrix (Fin 2) (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K p f))) h
    exact Matrix.map_injective ι.injective this
  have hψ : Function.Injective ((hypProj h 2 0).comp ψ₃) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact hψ₃ x hx
  exact ⟨((hypProj h 2 0).comp ψ₃).comp (β.comp (e₁.toMonoidHom.comp φ)),
    hψ.comp (hβ.comp (e₁.injective.comp hφ))⟩

end Embed

section Order

variable {p f : ℕ} {K : Type} [Field K]

theorem not_card_dvd_factorial_statedProj_four [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    ¬ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) ∣ Nat.factorial 11 := by
  intro hdvd
  have hp : p.Prime := Fact.out
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 4) hp hf hK
    (by norm_num)
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have h3 : 3 ≤ p ^ f := by
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have e1 : (∏ i ∈ Finset.Icc 2 4, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      ((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
    have a1 : ((((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    have a2 : ((((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    have a3 : ((((p ^ f : ℕ) : ℤ)) ^ 4 - (-1) ^ 4).toNat = (p ^ f) ^ 4 - 1 := by
      have : (((p ^ f : ℕ) : ℤ)) ^ 4 - (-1) ^ 4 = (((p ^ f) ^ 4 - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        ring
      rw [this, Int.toNat_natCast]
    rw [a1, a2, a3]
  rw [e1] at hcard
  have hg4 : Nat.gcd 4 (p ^ f + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hgd : Nat.gcd 4 (p ^ f + 1) ∣ (p ^ f) ^ 2 - 1 := by
    obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
    have h1 : (p ^ f) ^ 2 - 1 = m * (p ^ f + 1) := by
      rw [hm]
      have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
      omega
    rw [h1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
  have hmul : Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) * Nat.gcd 4 (p ^ f + 1) =
      (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1))) := by
    rw [hcard]
    exact Nat.div_mul_cancel (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgd _) _)
  have key : (p ^ f) ^ 6 ∣ 4 * Nat.factorial 11 := by
    have h1 : (p ^ f) ^ 6 ∣ Nat.card (StatedProj (StatedSU 4 (p ^ f) K)) *
        Nat.gcd 4 (p ^ f + 1) := by
      rw [hmul]
      exact dvd_mul_right _ _
    rw [mul_comm 4]
    exact dvd_trans h1 (Nat.mul_dvd_mul hdvd hg4)
  have h4f : 4 * Nat.factorial 11 = 159667200 := by decide
  rw [h4f] at key
  exact not_pow_six_dvd_four_factorial hodd h3 key

end Order

theorem not_kindFactorAll_fu4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {Y : Type}
    [Group Y] (hL : CFSG.Blueprint.LieModel Y .PSU 4 p f) (k : Kind) : ¬ KindFactorAll k Y := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (Y ≃* StatedProj (StatedSU 4 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have : Fact p.Prime := ⟨hp⟩
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have : CharP K p := h.charP
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  have e : Y ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm
  have : Finite Y := Finite.of_equiv _ e₀.symm.toEquiv
  obtain ⟨ψ, hψ⟩ := exists_injective_qdSL_hypPSU h hcard
  have hinv := involved_of_injective ((e.symm : hypPSU h 2 0 →* Y).comp ψ) (e.symm.injective.comp hψ)
  have hord : ¬ Nat.card Y ∣ Nat.factorial 11 := by
    rw [Nat.card_congr e₀.toEquiv]
    exact not_card_dvd_factorial_statedProj_four hp2 hf hcard
  exact not_kindFactorAll hp2 hinv hord

theorem cell87_FU4_of_surv (hInv : InvSec) (h : Cell87Surv FU4) :
    Cell87 FU4 :=
  cell87_of_surv hInv (fun k Y _ hF => by
    obtain ⟨p, f, hp, hf, hp2, -, hL⟩ := hF
    exact not_kindFactorAll_fu4 hp hp2 hf hL k) h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
