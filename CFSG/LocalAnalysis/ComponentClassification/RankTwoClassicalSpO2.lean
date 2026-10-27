module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpO2Matrix
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSpYDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviGen

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem noNormalTwo_of_quot {G : Type} {S : Type*} [Group G] [Group S] [Finite G] [Finite S]
    {A : Subgroup G} (ψ : ↥A →* S) (hψ : Function.Surjective ψ) (hker : ψ.ker = center ↥A)
    (hZ : Odd (Nat.card (center ↥A))) {z : G} (hzA : z ∈ A)
    (hS : ∀ Q₁ : Subgroup S, Q₁ ≤ centralizer {ψ ⟨z, hzA⟩} → IsPGroup 2 Q₁ →
      centralizer {ψ ⟨z, hzA⟩} ≤ normalizer (Q₁ : Set S) → Q₁ = ⊥) :
    NoNormalTwo (A ⊓ centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q hQ hQ2 hN
  set za : ↥A := ⟨z, hzA⟩
  set CA := centralizer ({za} : Set ↥A) with hCA
  set C := centralizer ({ψ za} : Set S) with hC
  set N := CA.map ψ with hNdef
  have hQA : Q ≤ A := hQ.trans inf_le_left
  set Qa := Q.subgroupOf A with hQa
  set Q₁ := Qa.map ψ with hQ₁
  have hQaC : Qa ≤ CA := by
    intro q hq
    rw [mem_subgroupOf] at hq
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQ hq).2)
  have hCAN : CA ≤ normalizer (Qa : Set ↥A) := by
    intro c hc
    have hcG : (c : G) ∈ A ⊓ centralizer ({z} : Set G) := by
      refine mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
    rw [mem_normalizer_iff]
    intro q
    rw [mem_subgroupOf, mem_subgroupOf]
    exact (mem_normalizer_iff.mp (hN hcG) q).trans (by simp)
  have hNC : N ≤ C := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hn]
  have hconj : ∀ a : ↥A, ψ a ∈ C → ∀ n ∈ CA, a * n * a⁻¹ ∈ CA := by
    intro a ha n hn
    have hz' : (za⁻¹ * (a * za * a⁻¹)) ∈ center ↥A := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv,
        mem_centralizer_singleton_iff.mp ha, mul_inv_cancel_right, inv_mul_cancel]
    set ζ := za⁻¹ * (a * za * a⁻¹)
    have haz : a * za * a⁻¹ = za * ζ := by rw [mul_inv_cancel_left]
    rw [mem_centralizer_singleton_iff]
    have hnz : n * za = za * n := mem_centralizer_singleton_iff.mp hn
    have h1 : (a * n * a⁻¹) * (a * za * a⁻¹) = (a * za * a⁻¹) * (a * n * a⁻¹) := by
      calc (a * n * a⁻¹) * (a * za * a⁻¹) = a * (n * za) * a⁻¹ := by group
        _ = a * (za * n) * a⁻¹ := by rw [hnz]
        _ = (a * za * a⁻¹) * (a * n * a⁻¹) := by group
    rw [haz] at h1
    have hζ := mem_center_iff.mp hz'
    have h2 : a * n * a⁻¹ * za * ζ = za * (a * n * a⁻¹) * ζ := by
      calc a * n * a⁻¹ * za * ζ = a * n * a⁻¹ * (za * ζ) := by group
        _ = za * ζ * (a * n * a⁻¹) := h1
        _ = za * (ζ * (a * n * a⁻¹)) := by group
        _ = za * ((a * n * a⁻¹) * ζ) := by rw [← hζ (a * n * a⁻¹)]
        _ = za * (a * n * a⁻¹) * ζ := by group
    exact mul_right_cancel h2
  have hCN : C ≤ normalizer (N : Set S) := by
    intro c hc
    obtain ⟨a, rfl⟩ := hψ c
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨a * n * a⁻¹, hconj a hc n hn, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨n, hn, hnh⟩
      have hainv : ψ a⁻¹ ∈ C := by rw [map_inv]; exact inv_mem hc
      refine ⟨a⁻¹ * n * a⁻¹⁻¹, hconj a⁻¹ hainv n hn, ?_⟩
      rw [map_mul, map_mul, hnh, map_inv, inv_inv]
      group
  have hQ₁N : Q₁ ≤ N := map_mono hQaC
  have hNQ₁ : N ≤ normalizer (Q₁ : Set S) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨n * q * n⁻¹, (mem_normalizer_iff.mp (hCAN hn) q).mp hq, by
        rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨q, hq, hqh⟩
      refine ⟨n⁻¹ * q * n⁻¹⁻¹, (mem_normalizer_iff.mp (hCAN (inv_mem hn)) q).mp hq, ?_⟩
      rw [map_mul, map_mul, hqh, map_inv, inv_inv]
      group
  have hQ₁2 : IsPGroup 2 Q₁ :=
    (hQ2.of_equiv (subgroupOfEquivOfLe hQA).symm).map ψ
  have hle := le_pCoreOf_of_le_normalizer 2 hQ₁N hNQ₁ hQ₁2
  have hO : CFSG.Open.pCoreOf 2 N = ⊥ := hS _ ((pCoreOf_le 2 N).trans hNC) (pCoreOf_isPGroup 2 N)
    (hCN.trans (normalizer_le_normalizer_pCoreOf 2 N))
  rw [hO, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro q hq
  rw [mem_bot]
  have hqa : (⟨q, hQA hq⟩ : ↥A) ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker]
    have : ψ ⟨q, hQA hq⟩ ∈ Q₁ := ⟨⟨q, hQA hq⟩, (mem_subgroupOf.mpr hq), rfl⟩
    rw [hle, mem_bot] at this
    exact this
  obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
  have hqk : (⟨⟨q, hQA hq⟩, hqa⟩ : center ↥A) ^ 2 ^ k = 1 :=
    Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))
  have hodd : Odd (orderOf (⟨⟨q, hQA hq⟩, hqa⟩ : center ↥A)) :=
    Odd.of_dvd_nat hZ (orderOf_dvd_natCard _)
  have h1 := orderOf_dvd_of_pow_eq_one hqk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (by
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      exact ⟨2 ^ i, by rw [pow_succ]; ring⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact congrArg (fun y : center ↥A => ((y : ↥A) : G)) hj

theorem symplecticOddCentralizerO2 : SymplecticOddCentralizerO2 := by
  intro G _ _ A D hD _ hZ _ z hzA hzo
  cases D with
  | symplectic n f hn hf hnf K hK e =>
    have : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
    have : NeZero n := ⟨by omega⟩
    have : Finite (StatedSp n K) := Subtype.finite
    set pe : StatedSp n K ≃* StatedProj (StatedSp n K) := MulEquiv.ofBijective (proj n K)
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    set ψ : ↥A →* StatedSp n K := pe.symm.toMonoidHom.comp (quotModelHom e) with hψdef
    have hψ : Function.Surjective ψ := pe.symm.surjective.comp quotModelHom_surjective
    have hker : ψ.ker = center ↥A := by
      rw [← ker_quotModelHom (e := e)]
      ext a
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    refine noNormalTwo_of_quot ψ hψ hker hZ hzA fun Q₁ hQ₁ hQ₁2 hN₁ =>
      eq_bot_of_le_centralizer_statedSp ?_ hQ₁ hQ₁2 hN₁
    refine Odd.of_dvd_nat hzo ((orderOf_map_dvd ψ _).trans ?_)
    rw [Subgroup.orderOf_mk]
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
