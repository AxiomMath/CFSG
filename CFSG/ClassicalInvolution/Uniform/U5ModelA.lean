module

public import CFSG.ClassicalInvolution.Asc77.AscR10D3a
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.Uniform.U5Three
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3CII (injOn_of_natCard_map neg_one_eq_commutator_sl2)
open scoped MatrixGroups commutatorElement

section Model



variable {M X : Type} [Group M] [Group X]

theorem uniqueInvolution_comm {K : Subgroup X} {z : X} (hz : IsUniqueInvolution K z) :
    ∀ y ∈ K, z * y = y * z := by
  intro y hy
  have h1 : y * z * y⁻¹ ∈ K := K.mul_mem (K.mul_mem hy hz.mem) (K.inv_mem hy)
  have h2 : (y * z * y⁻¹) * (y * z * y⁻¹) = 1 := by
    calc (y * z * y⁻¹) * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    have : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [h] at this
    simpa using this
  · calc z * y = (y * z * y⁻¹) * y := by rw [h]
      _ = y * z := by group

theorem conj_eq_of_mem_normalizer {K : Subgroup X} {z n : X} (hz : IsUniqueInvolution K z)
    (hn : n ∈ Subgroup.normalizer (K : Set X)) : n * z * n⁻¹ = z := by
  have h1 : n * z * n⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hn z).mp hz.mem
  have h2 : (n * z * n⁻¹) * (n * z * n⁻¹) = 1 := by
    calc (n * z * n⁻¹) * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ h1 h2 with h | h
  · exfalso
    apply hz.ne_one
    have : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    rw [h] at this
    simpa using this
  · exact h

theorem uniqueInvolution_map [Finite M] (ψ : M →* X) {R : Subgroup M}
    (e : R ≃* SL(2, GaloisField 3 1)) (hcard : Nat.card (R.map ψ) = 24) :
    IsUniqueInvolution (R.map ψ) (ψ (sl2Inv e)) ∧ ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := by
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have hRcard : Nat.card R = Nat.card (R.map ψ) := by
    rw [hcard, Nat.card_congr e.toEquiv]
    exact natCard_sl2_galoisField_three
  have hinj := injOn_of_natCard_map ψ hRcard
  refine ⟨⟨Subgroup.mem_map_of_mem ψ (sl2Inv_mem e), ?_, ?_, ?_⟩, hinj⟩
  · intro h
    apply sl2Inv_ne_one hodd e
    exact hinj _ (sl2Inv_mem e) 1 R.one_mem (h.trans (map_one ψ).symm)
  · rw [← map_mul, sl2Inv_mul_self hodd e, map_one]
  · rintro _ ⟨r, hr, rfl⟩ hy
    have hrr : r * r = 1 :=
      hinj _ (R.mul_mem hr hr) 1 R.one_mem (by rw [map_mul, hy, map_one])
    by_cases hr1 : r = 1
    · left
      rw [hr1, map_one]
    · right
      have h2 : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
      rw [eq_sl2Inv_of_orderOf_eq_two hodd e hr h2]

theorem center_map_eq [Finite M] (ψ : M →* X) {R : Subgroup M} (e : R ≃* SL(2, GaloisField 3 1))
    (hcard : Nat.card (R.map ψ) = 24) {z : X} (hz : IsUniqueInvolution (R.map ψ) z) :
    ∀ w ∈ R.map ψ, (∀ x ∈ R.map ψ, w * x = x * w) → w = 1 ∨ w = z := by
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  obtain ⟨-, hinj⟩ := uniqueInvolution_map ψ e hcard
  have hbij : Function.Bijective (ψ.subgroupMap R) := by
    refine ⟨fun a b hab => Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab)),
      ψ.subgroupMap_surjective R⟩
  let eK : ↥(R.map ψ) ≃* SL(2, GaloisField 3 1) :=
    (MulEquiv.ofBijective (ψ.subgroupMap R) hbij).symm.trans e
  exact thm5IH_center_of_exact hodd hz eK


theorem inf_eq_bot_of_commutes [Finite M] (ψ : M →* X) {R₁ R₂ : Subgroup M}
    (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1))
    (h₁ : Nat.card (R₁.map ψ) = 24) (h₂ : Nat.card (R₂.map ψ) = 24)
    (hKJ : Commutes (R₁.map ψ) (R₂.map ψ)) {z : X} (hz : IsUniqueInvolution (R₁.map ψ) z)
    (hzJ : ¬ IsUniqueInvolution (R₂.map ψ) z) : R₁.map ψ ⊓ R₂.map ψ = ⊥ := by
  obtain ⟨uJ, -⟩ := uniqueInvolution_map ψ e₂ h₂
  refine (Subgroup.eq_bot_iff_forall _).2 fun w hw => ?_
  have hwK : ∀ x ∈ R₁.map ψ, w * x = x * w := fun x hx => (hKJ x hx w hw.2).symm
  have hwJ : ∀ x ∈ R₂.map ψ, w * x = x * w := fun x hx => hKJ w hw.1 x hx
  rcases center_map_eq ψ e₁ h₁ hz w hw.1 hwK with h | h
  · exact h
  · rcases center_map_eq ψ e₂ h₂ uJ w hw.2 hwJ with h' | h'
    · exact h'
    · exact absurd (by rw [h] at h'; rw [h']; exact uJ) hzJ

theorem mem_of_four_group [Finite M] (ψ : M →* X) {R₁ R₂ : Subgroup M}
    (e₁ : R₁ ≃* SL(2, GaloisField 3 1)) (e₂ : R₂ ≃* SL(2, GaloisField 3 1))
    (h₁ : Nat.card (R₁.map ψ) = 24) (h₂ : Nat.card (R₂.map ψ) = 24)
    (hKJ : Commutes (R₁.map ψ) (R₂.map ψ)) {z : X} (hz : IsUniqueInvolution (R₁.map ψ) z)
    (hzJ : ¬ IsUniqueInvolution (R₂.map ψ) z) {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1)
    (hA4 : Nat.card A = 4) (hAKJ : A ≤ R₁.map ψ ⊔ R₂.map ψ) (hzA : z ∈ A) :
    ψ (sl2Inv e₂) ∈ A := by
  obtain ⟨uJ, -⟩ := uniqueInvolution_map ψ e₂ h₂
  have hbot := inf_eq_bot_of_commutes ψ e₁ e₂ h₁ h₂ hKJ hz hzJ
  obtain ⟨u, huA, hu1, huz⟩ := thm5IH_exists_ne hA4 1 z
  obtain ⟨k', hk', j', hj', hkj⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hKJ (hAKJ huA)
  have huu : u * u = 1 := hA2 u huA
  have hkjc : k' * j' = j' * k' := hKJ k' hk' j' hj'
  have hkk : k' * k' = (j' * j')⁻¹ := by
    have h : (k' * k') * (j' * j') = 1 := by
      calc (k' * k') * (j' * j') = k' * (k' * j') * j' := by group
        _ = k' * (j' * k') * j' := by rw [hkjc]
        _ = (k' * j') * (k' * j') := by group
        _ = u * u := by rw [hkj]
        _ = 1 := huu
    exact eq_inv_of_mul_eq_one_left h
  have hkkJ : k' * k' ∈ R₂.map ψ := by
    rw [hkk]
    exact (R₂.map ψ).inv_mem ((R₂.map ψ).mul_mem hj' hj')
  have hkk1 : k' * k' = 1 := by
    have : k' * k' ∈ R₁.map ψ ⊓ R₂.map ψ := ⟨(R₁.map ψ).mul_mem hk' hk', hkkJ⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hjj1 : j' * j' = 1 := by
    rw [hkk1] at hkk
    exact inv_eq_one.mp hkk.symm
  have hkc : k' = 1 ∨ k' = z := hz.unique k' hk' hkk1
  have hjc : j' = 1 ∨ j' = ψ (sl2Inv e₂) := uJ.unique j' hj' hjj1
  have hzz : z * z = 1 := hz.sq
  rcases hkc with hk1 | hkz <;> rcases hjc with hj1 | hjz
  · exact absurd (by rw [← hkj, hk1, hj1, mul_one]) hu1
  · have : ψ (sl2Inv e₂) = u := by rw [← hkj, hk1, hjz, one_mul]
    rw [this]
    exact huA
  · exact absurd (by rw [← hkj, hkz, hj1, mul_one]) huz
  · have hz2 : ψ (sl2Inv e₂) = z * u := by
      rw [← hkj, hkz, hjz, ← mul_assoc, hzz, one_mul]
    rw [hz2]
    exact A.mul_mem hzA huA


theorem card_su_three_three : Nat.card (Phan.Su (GaloisField 3 2) 3 1 3) = 6048 := by
  have hF : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨P₃, hP₃⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF 3
  have e : Nat.card (CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 2) 3 1) 3) =
      Nat.card (Phan.Su (GaloisField 3 2) 3 1 3) :=
    Nat.card_congr (CFSG.LieType.Universal.Unitary.conjEquiv P₃ hP₃).toEquiv
  rw [← e, CFSG.LieType.Steinberg.card_SU_three hF]
  norm_num

end Model

end CFSG.ClassicalInvolution.Uniform
