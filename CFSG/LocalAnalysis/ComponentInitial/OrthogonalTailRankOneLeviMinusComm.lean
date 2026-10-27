module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
import CFSG.RankThree.GF2n.Smith81.OrthTensorModel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Module QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.RankThree.GF2n.Smith81 CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
open scoped commutatorElement

theorem commutator_mem_tailUnipotent_of_torus_comm {K : Type} [Field K] {A : Type}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) (hT : ∀ x y : ↥(tailTorus r qA), x * y = y * x)
    {b₁ b₂ : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (h₁ : b₁ ∈ tailBorel r qA) (h₂ : b₂ ∈ tailBorel r qA) : ⁅b₁, b₂⁆ ∈ tailUnipotent r qA := by
  classical
  haveI := tailUnipotent_normal hani (r := r) (qA := qA)
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := r) (qA := qA)
  have hcomm : ∀ x y : ↥(tailBorel r qA) ⧸
      (tailUnipotent r qA).subgroupOf (tailBorel r qA), x * y = y * x := fun x y =>
    e.injective (by rw [map_mul, map_mul]; exact hT _ _)
  have h1 : (QuotientGroup.mk' ((tailUnipotent r qA).subgroupOf (tailBorel r qA)))
      ⁅(⟨b₁, h₁⟩ : ↥(tailBorel r qA)), ⟨b₂, h₂⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem tailTorus_comm_of_odd {r : ℕ} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hodd : Odd (Nat.card ↥(tailTorus r (minusTailForm K b c))))
    (x y : ↥(tailTorus r (minusTailForm K b c))) : x * y = y * x := by
  classical
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have key : ∀ z : ↥(tailTorus r (minusTailForm K b c)), ∃ (t : Fin r → Kˣ)
      (h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)), IsOmegaTwisted b c h 0 ∧
        h ∈ TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) ∧
        tailDiag r t h = (z : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] _) := by
    intro z
    obtain ⟨-, t, h, hh, hz⟩ := mem_tailTorus.1 z.2
    refine ⟨t, h, ?_, hh, hz⟩
    have hpow : tailDiag r (t ^ Nat.card (tailTorus r (minusTailForm K b c)))
        (h ^ Nat.card (tailTorus r (minusTailForm K b c))) = 1 := by
      rw [← tailDiag_pow, hz, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
    refine plane_isOmegaTwisted_zero hirr hodd h 1 (fun a => by
        have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hh a
        rw [one_mul]
        exact this) (s := 1) (fun a => ?_)
    have h1 := LinearEquiv.congr_fun hpow ((0 : Fin r ⊕ Fin r → K), a)
    rw [tailDiag_apply] at h1
    have h2 := congrArg Prod.snd h1
    rw [one_smul]
    simpa using h2
  obtain ⟨t₁, h₁, p₁, -, hx⟩ := key x
  obtain ⟨t₂, h₂, p₂, -, hy⟩ := key y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, tailDiag_mul, tailDiag_mul, mul_comm t₁ t₂,
    commute_of_isOmegaTwisted_zero p₁ p₂]

private theorem card_orthElementaryGroup_two_H18 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) =
      (Nat.card K) ^ 6 * ((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) *
        ((Nat.card K) ^ 4 - 1) := by
  set q := Nat.card K
  have hcard : Nat.card ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) =
      Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) :=
    Nat.card_congr (tailOmegaEquiv (minusTailIsometry 3 K b c)
      (coe_quadMinus (n := 3) (K := K) b c)
      (commutator_orthogonalGroup_quadMinus_of_two_le (n := 3) (by norm_num) hirr)).toEquiv.symm
  rw [hcard]
  have hInt := card_statedOmega_minus_eq (K := K) (m := 3) (by norm_num) hirr
  have hInt' : ((Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) : ℕ) : ℤ) =
      ((q ^ 6 * (q ^ 3 + 1) * (q ^ 2 - 1) * (q ^ 4 - 1) : ℕ) : ℤ) := by
    rw [hInt]
    have hIcc : Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
    rw [hIcc]
    norm_num [q, Finset.prod_insert]
    push_cast
    ring
  exact_mod_cast hInt'

private theorem card_tailUnipotent_two_H18 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(tailUnipotent 2 (minusTailForm K b c)) = (Nat.card K) ^ 6 := by
  rw [card_tailUnipotent (K := K) (A := Fin 2 → K) (qA := minusTailForm K b c) (r := 2)
    (hani := anisotropic_minusTailForm hirr)]
  norm_num [finrank_fin_two_fun]

private theorem odd_oddFactor_two_H18 (h2 : 2 ∣ Nat.card K) :
    Odd (((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1)) := by
  have hq_even : Even (Nat.card K) := even_iff_two_dvd.mpr h2
  have h1 : Odd ((Nat.card K) ^ 3 + 1) := (hq_even.pow_of_ne_zero (by norm_num)).add_one
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hq2ge : 1 ≤ (Nat.card K) ^ 2 := Nat.one_le_pow 2 _ hqpos
  have h2' : Odd ((Nat.card K) ^ 2 - 1) :=
    Nat.Even.sub_odd hq2ge (hq_even.pow_of_ne_zero (by norm_num)) odd_one
  have hq4ge : 1 ≤ (Nat.card K) ^ 4 := Nat.one_le_pow 4 _ hqpos
  have h3 : Odd ((Nat.card K) ^ 4 - 1) :=
    Nat.Even.sub_odd hq4ge (hq_even.pow_of_ne_zero (by norm_num)) odd_one
  exact (h1.mul h2').mul h3

private theorem card_tailBorel_two_H18 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(tailBorel 2 (minusTailForm K b c)) =
      Nat.card ↥(tailTorus 2 (minusTailForm K b c)) * (Nat.card K) ^ 6 := by
  have hani := anisotropic_minusTailForm hirr
  haveI := tailUnipotent_normal hani (r := 2) (qA := minusTailForm K b c)
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv_tailTorus hani (r := 2) (qA := minusTailForm K b c)
  have hq : Nat.card (tailBorel 2 (minusTailForm K b c) ⧸
      (tailUnipotent 2 (minusTailForm K b c)).subgroupOf
        (tailBorel 2 (minusTailForm K b c))) =
      Nat.card ↥(tailTorus 2 (minusTailForm K b c)) := Nat.card_congr e.toEquiv
  have hsub : Nat.card ↥((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (tailBorel 2 (minusTailForm K b c))) =
      Nat.card ↥(tailUnipotent 2 (minusTailForm K b c)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (tailUnipotent_le_tailBorel hani)).toEquiv
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((tailUnipotent 2 (minusTailForm K b c)).subgroupOf (tailBorel 2 (minusTailForm K b c)))
  rw [hsub, hq, card_tailUnipotent_two_H18 hirr] at hcard
  exact hcard

theorem odd_card_tailTorus_two (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Odd (Nat.card ↥(tailTorus 2 (minusTailForm K b c))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  have hdvd : Nat.card ↥(tailBorel 2 (minusTailForm K b c)) ∣
      Nat.card ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
    Subgroup.card_dvd_of_le (tailBorel_le (r := 2) (qA := minusTailForm K b c))
  rw [card_tailBorel_two_H18 hirr, card_orthElementaryGroup_two_H18 hirr] at hdvd
  have hTdvd : Nat.card ↥(tailTorus 2 (minusTailForm K b c)) ∣
      ((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) := by
    apply Nat.dvd_of_mul_dvd_mul_left (pow_pos (show 0 < Nat.card K from Nat.card_pos) 6)
    rw [mul_comm ((Nat.card K) ^ 6) (Nat.card ↥(tailTorus 2 (minusTailForm K b c)))]
    simpa only [mul_assoc] using hdvd
  exact (odd_oddFactor_two_H18 (K := K) (dvd_natCard_of_charP (K := K) (p := 2))).of_dvd_nat hTdvd

theorem commutator_mem_tailUnipotent_two (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {b₁ b₂ : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))}
    (h₁ : b₁ ∈ tailBorel 2 (minusTailForm K b c)) (h₂ : b₂ ∈ tailBorel 2 (minusTailForm K b c)) :
    ⁅b₁, b₂⁆ ∈ tailUnipotent 2 (minusTailForm K b c) :=
  commutator_mem_tailUnipotent_of_torus_comm (anisotropic_minusTailForm hirr)
    (tailTorus_comm_of_odd hirr (odd_card_tailTorus_two hirr)) h₁ h₂

theorem commutator_mem_tailUnipotent_minus {r : ℕ} (hr : 2 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {b₁ b₂ : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}
    (h₁ : b₁ ∈ tailBorel r (minusTailForm K b c)) (h₂ : b₂ ∈ tailBorel r (minusTailForm K b c)) :
    ⁅b₁, b₂⁆ ∈ tailUnipotent r (minusTailForm K b c) := by
  rcases (show r = 2 ∨ 3 ≤ r by omega) with h2 | h3
  · subst h2
    exact commutator_mem_tailUnipotent_two hirr h₁ h₂
  · exact commutator_mem_tailUnipotent h3 hirr h₁ h₂

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
