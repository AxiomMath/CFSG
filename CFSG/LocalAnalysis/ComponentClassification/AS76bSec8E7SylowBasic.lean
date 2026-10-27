module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Regular
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7LineTransport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction

variable {K : Type} [Field K]

theorem mem_posUnipotent_of_mem_borelGroup_of_pow
    [Finite K] [CharP K 2] {g : ModGL .E7 K}
    (hg : g ∈ borelGroup .E7 K) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g ∈ posUnipotent .E7 K := by
  have hN : torusGroup .E7 K ≤ normalizer (posUnipotent .E7 K : Set (ModGL .E7 K)) :=
    torusGroup_le_normalizer_posUnipotent
  have hg' : g ∈ ((torusGroup .E7 K ⊔ posUnipotent .E7 K : Subgroup (ModGL .E7 K)) :
      Set (ModGL .E7 K)) := hg
  rw [coe_mul_of_left_le_normalizer_right _ _ hN] at hg'
  obtain ⟨t, ht, u, hu, rfl⟩ := hg'
  have hpow : ∀ n : ℕ, (t ^ n)⁻¹ * (t * u) ^ n ∈ posUnipotent .E7 K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : (t ^ (n + 1))⁻¹ * (t * u) ^ (n + 1) =
          t⁻¹ * ((t ^ n)⁻¹ * (t * u) ^ n) * t * u := by
        rw [pow_succ, pow_succ, ← (Commute.self_pow t n).eq]
        group
      rw [h1]
      refine mul_mem ?_ hu
      have ht' : t⁻¹ ∈ normalizer (posUnipotent .E7 K : Set (ModGL .E7 K)) :=
        hN (inv_mem ht)
      have h2 := (mem_normalizer_iff.1 ht' _).1 ih
      simpa [mul_assoc] using h2
  have h1 := hpow (2 ^ k)
  rw [hk, mul_one] at h1
  have h2 : t ^ 2 ^ k ∈ torusGroup .E7 K ⊓ posUnipotent .E7 K :=
    ⟨pow_mem ht _, by simpa using inv_mem h1⟩
  rw [torusGroup_inf_posUnipotent, mem_bot] at h2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units K, Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero n.ne_zero) odd_one
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Kˣ) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have ht1 : orderOf t = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one (pow_card_units_eq_one_of_mem_torusGroup_e7 ht))
  rw [orderOf_eq_one_iff.1 ht1]
  simpa using hu

theorem exists_conj_highRoot_eq_e7FrameElt
    [Finite K] [CharP K 2] {β : Fin Tag.E7.rank → ℤ}
    (hβ : IsRoot .E7 β) {c : K} (hc : c ≠ 0) :
    ∃ b : adjointGroup .E7 K, b * e7FramePt K [highRoot .E7] * b⁻¹ = e7FrameElt K [β] c := by
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  have hr : ∀ σ ∈ [highRoot .E7], IsRoot .E7 σ := by simpa using isRoot_highRoot .E7
  have ho : [highRoot .E7].Pairwise fun σ σ' => iform σ σ' = 0 := List.pairwise_singleton _ _
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq hτ hβ
  obtain ⟨s, hs⟩ := exists_e7FrameScale_conj hr ho hc
  refine ⟨e7WeylRep K w * e7FrameScale K [highRoot .E7] s, ?_⟩
  have h1 := hs 1
  rw [mul_one, e7FrameElt_one] at h1
  calc e7WeylRep K w * e7FrameScale K [highRoot .E7] s * e7FramePt K [highRoot .E7] *
        (e7WeylRep K w * e7FrameScale K [highRoot .E7] s)⁻¹ =
        e7WeylRep K w * (e7FrameScale K [highRoot .E7] s * e7FramePt K [highRoot .E7] *
          (e7FrameScale K [highRoot .E7] s)⁻¹) * (e7WeylRep K w)⁻¹ := by group
    _ = e7FrameElt K [β] c := by
      rw [h1, e7FrameElt_conj_weyl w hr]
      simp [hw]

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
