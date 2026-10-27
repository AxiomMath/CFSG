module

public import CFSG.GH74.Uniqueness.Section7Theta
public import CFSG.GH74.Uniqueness.Section6Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open Section7Theta

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.lemma75 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W)
    {β : Subgroup X} (hβ : β ∈ omegaFix M (W : Set X))
    (hCF : centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊓ β ⊓ conjugate β z ≤ M) :
    oPrimePrime p (β ⊓ conjugate β z) ≤ oPrimePrime p (M ⊓ β ⊓ conjugate β z) := by
  have hz := hW.mem_Z
  have hzM := hW.mem_M
  have hz2 : orderOf z = 2 := hZ.1 z hz
  have hzz : z * z = 1 := hZ.mul_self_eq_one hz
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨hz1, by rw [pow_two]; exact hzz⟩
  have hβz : conjugate β z ∈ omegaFix M (W : Set X) := hW.conjugate_z_mem_omegaFix hβ
  have hWβ : W ≤ β := (h.mem_omegaFix_iff.mp hβ).2
  have hWβz : W ≤ conjugate β z := (h.mem_omegaFix_iff.mp hβz).2
  have hWF : W ≤ β ⊓ conjugate β z := le_inf hWβ hWβz
  have hWE : W ≤ M ⊓ β ⊓ conjugate β z := le_inf (le_inf hW.le_M hWβ) hWβz
  have hEF : M ⊓ β ⊓ conjugate β z ≤ β ⊓ conjugate β z :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hFnorm : z ∈ normalizer ((β ⊓ conjugate β z : Subgroup X) : Set X) :=
    mem_normalizer_inf_conjugate hzz
  have hzT : z ∈ normalizer (oPrimePrime p (β ⊓ conjugate β z) : Set X) :=
    mem_normalizer_oPrimePrime p hFnorm
  have hWT : W ≤ normalizer (oPrimePrime p (β ⊓ conjugate β z) : Set X) :=
    hWF.trans (le_normalizer_oPrimePrime p _)
  have hcomm : ⁅W, zpowers z⁆ = W := by
    rw [Subgroup.commutator_comm]
    exact hW.comm_eq
  have hTodd : Odd (Nat.card (oPrimePrime p (β ⊓ conjugate β z))) := oPrimePrime_odd_card p _
  have hcop : Nat.Coprime (Nat.card ↥(W ⊔ zpowers z))
      (Nat.card (oPrimePrime p (β ⊓ conjugate β z))) :=
    CFSG.BenderSuzuki.lemma75_theta_actor_card_coprime hW.prime hW.pgroup hinv hW.normalizes _
  have hgen := CFSG.BenderSuzuki.lemma75_II146_specialized hinv hW.normalizes hWT hzT hcomm hTodd
    hcop
  have hTF : oPrimePrime p (β ⊓ conjugate β z) ≤ β ⊓ conjugate β z := oPrimePrime_le p _
  have hKC : centralizer (CFSG.OddInversion.invertedSet W z : Set X) = centralizer (W : Set X) := by
    have := Subgroup.centralizer_closure (CFSG.OddInversion.invertedSet W z)
    rw [hW.closure_invertedSet hZ] at this
    exact this.symm
  have hCTW : CFSG.subgroupCentralizerIn (oPrimePrime p (β ⊓ conjugate β z)) W ≤
      M ⊓ β ⊓ conjugate β z := by
    intro x hx
    have hxF := hTF hx.1
    have hxM : x ∈ M := hCF ⟨⟨by rw [hKC]; exact hx.2, hxF.1⟩, hxF.2⟩
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hCTz : CFSG.elementCentralizerIn (oPrimePrime p (β ⊓ conjugate β z)) z ≤
      M ⊓ β ⊓ conjugate β z := by
    intro x hx
    have hxF := hTF hx.1
    have hxM : x ∈ M := h.centralizer_le_of_mem hz hzM hx.2
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hTE := CFSG.BenderSuzuki.lemma75_le_of_II146Conclusion hgen hCTW hCTz hWE
  exact le_oPrimePrime_of_le_normalizer hTE (hEF.trans (le_normalizer_oPrimePrime p _)) hTodd
    (oPrimePrime_coprime_card hW.prime _)

end CFSG.GH74.Uniqueness
