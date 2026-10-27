module

public import CFSG.HardMathSupport.Lang.AnisoE8.Closing

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE8

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.Timmesfeld
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem dvd_card_SL8_of_dvd {p q : ℕ} (hq : 1 ≤ q) (hp : p ∣ q ^ 4 + 1) :
    p ∣ q ^ (8 * (8 - 1) / 2) * ∏ j ∈ Finset.Icc 2 8, (q ^ j - 1) := by
  have h8 : q ^ 8 - 1 = (q ^ 4 - 1) * (q ^ 4 + 1) := by
    have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
    zify [h1, Nat.one_le_pow 8 q hq]
    ring
  have hmem : (8 : ℕ) ∈ Finset.Icc 2 8 := by decide
  refine Dvd.dvd.mul_left ?_ _
  exact (h8 ▸ Dvd.dvd.mul_left hp _).trans (Finset.dvd_prod_of_mem _ hmem)

theorem e8Delta_chain_facts :
    (e8D8Root ≠ e8Delta ∧ e8D8Root ≠ -e8Delta ∧ iform e8D8Root e8Delta = 0 ∧
      ¬ IsRoot .E8 (e8D8Root + e8Delta) ∧ ¬ IsRoot .E8 (e8D8Root + -e8Delta)) ∧
    ∀ k : Fin 7, k ≠ 0 →
      (Pi.single (e8D8Node k.castSucc) 1 : Fin (Tag.rank .E8) → ℤ) ≠ e8Delta ∧
      (Pi.single (e8D8Node k.castSucc) 1 : Fin (Tag.rank .E8) → ℤ) ≠ -e8Delta ∧
      iform (Pi.single (e8D8Node k.castSucc) 1) e8Delta = 0 ∧
      ¬ IsRoot .E8 (Pi.single (e8D8Node k.castSucc) 1 + e8Delta) ∧
      ¬ IsRoot .E8 (Pi.single (e8D8Node k.castSucc) 1 + -e8Delta) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  decide +kernel

variable {K : Type} [Field K]

theorem commutes_e8D8Chain_rootPairE8_delta (k : Fin 7) :
    Commutes (e8D8Chain K k.castSucc) (rootPairE8 K e8Delta) := by
  obtain ⟨⟨n0, n0', i0, s0, s0'⟩, hk⟩ := e8Delta_chain_facts
  by_cases h0 : k = 0
  · subst h0
    have hU0 : e8D8Chain K (Fin.castSucc 0) =
        (e8Datum K).rootGroup e8D8Root ⊔ (e8Datum K).rootGroup (-e8D8Root) := by
      simp [e8D8Chain]
    rw [hU0]
    exact commutes_rootPair_of_noG2 noG2_E8 isRoot_e8D8Root isRoot_e8Delta n0 n0' i0 s0 s0'
  · obtain ⟨n1, n1', i1, s1, s1'⟩ := hk k h0
    have hne : k.castSucc ≠ 0 := fun h => h0 (Fin.castSucc_eq_zero_iff.1 h)
    have hUk : e8D8Chain K k.castSucc = rankOne (e8Datum K).rootGroup (e8D8Node k.castSucc) := by
      unfold e8D8Chain
      rw [ite_eq_right_iff.2 (fun h => absurd h hne)]
    rw [hUk]
    exact commutes_rootPair_of_noG2 noG2_E8 (isRoot_single _ _) isRoot_e8Delta n1 n1' i1 s1 s1'

theorem exists_e1_E8_eight_of_family [Finite K] {p : ℕ} [hpF : Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p ∣ Nat.card K ^ 4 + 1) (ρ : Fin 8 → SL(2, K) →* adjointGroup .E8 K)
    (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e8D8Chain K k)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeD 8 i j → ¬ edgeD 8 j i →
      ∀ u ∈ e8D8Chain K i, ∀ v ∈ e8D8Chain K j, u * v = v * u)
    (hψ : ∀ i j : Fin 8, edgeD 8 i j → ∃ ψ : SL(3, K) →* adjointGroup .E8 K,
      ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
        ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j) :
    ∃ e ∈ ⨆ k : Fin 7, e8D8Chain K k.castSucc, orderOf e = p ∧
      ∀ y ∈ rootPairE8 K e8Delta, Commute e y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n', hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n' : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL (7 + 1) (ringChar K) n' :=
    ⟨hℓ, n'.pos, by norm_num, by simp, by simp⟩
  obtain ⟨Ψ, hker, hrange, -, -⟩ := specialLinear_frame_subgroup (m := 7) hadm (by norm_num) hK
    (U := fun k : Fin 7 => e8D8Chain K k.castSucc)
    (fun i j hij h1 h2 => hcomm i.castSucc j.castSucc (fun h => hij (Fin.castSucc_injective _ h))
      (by simp only [edgeD, Fin.val_castSucc]; omega) (by simp only [edgeD, Fin.val_castSucc]; omega))
    (ρ := fun k => ρ k.castSucc) (fun k => hρ k.castSucc)
    (fun i j hij => hψ i.castSucc j.castSucc (Or.inl ⟨by simp only [Fin.val_castSucc]; omega,
      by simp only [Fin.val_castSucc]; omega⟩))
  have hcard : p ∣ Nat.card (SL(7 + 1, K)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)]
    exact dvd_card_SL8_of_dvd Nat.card_pos hp
  obtain ⟨A₀, hA₀⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hmem : Ψ A₀ ∈ ⨆ k : Fin 7, e8D8Chain K k.castSucc := hrange ▸ ⟨A₀, rfl⟩
  refine ⟨Ψ A₀, hmem, ?_, ?_⟩
  ·
    have hdvd : orderOf (Ψ A₀) ∣ p := hA₀ ▸ orderOf_map_dvd Ψ A₀
    rcases (Nat.dvd_prime hpF.out).1 hdvd with h1 | h1
    · exfalso
      rw [orderOf_eq_one_iff] at h1
      have hc : A₀ ∈ Subgroup.center SL(7 + 1, K) := hker h1
      obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
      have h8 : A₀ ^ 8 = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, Matrix.SpecialLinearGroup.coe_one]
        rw [show (Matrix.scalar (Fin (7 + 1)) r) ^ 8 = Matrix.scalar (Fin (7 + 1)) (r ^ 8) by
          rw [map_pow]]
        simp [Fintype.card_fin] at hr
        rw [hr, map_one]
      have hp8 : p ∣ 2 ^ 3 := by
        have := hA₀ ▸ orderOf_dvd_of_pow_eq_one h8
        norm_num
        exact this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpF.out Nat.prime_two).1
        (hpF.out.dvd_of_dvd_pow hp8))
    · exact h1
  ·
    intro y hy
    have hcent : (⨆ k : Fin 7, e8D8Chain K k.castSucc) ≤
        Subgroup.centralizer (rootPairE8 K e8Delta : Set (adjointGroup .E8 K)) := by
      refine iSup_le fun k x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((commutes_e8D8Chain_rootPairE8_delta k) x hx z hz).symm
    exact (Subgroup.mem_centralizer_iff.1 (hcent hmem) y hy).symm

end CFSG.HardMathSupport.Lang.AnisoE8
