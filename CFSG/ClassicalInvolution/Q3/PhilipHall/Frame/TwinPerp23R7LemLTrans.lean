module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAbs
public import CFSG.ClassicalInvolution.Q3.TL3T1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin

section Trans

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem exists_third_member (hΦ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J) {K K' : Subgroup G}
    (hK : K ∈ Φ) (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K) {a : G} (ha : HasS3Quot ↥(Ea Φ a)) :
    ∃ J ∈ Φ, J ≠ K ∧ J ≠ K' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hK'Φ, z, hzK, hzK'⟩ := hK'tw
  have hcomm := OddQuot.commutes_of_twin_pgroup hΦ h2 hK hK'Φ hne.symm hzK hzK'
  have hKK' : IsPGroup 2 ↥(K ⊔ K') := by
    have hnorm : K ≤ Subgroup.normalizer (K' : Set G) := fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hx hcomm)
    exact (h2 K hK).to_sup_of_normal_right' (h2 K' hK'Φ) hnorm
  have hEa : IsPGroup 2 ↥(Ea Φ a) := by
    refine hKK'.to_le (Ea_le (fun L hL _ => ?_))
    by_cases hLK : L = K
    · exact hLK ▸ le_sup_left
    · exact (hcon L hL hLK) ▸ le_sup_right
  obtain ⟨π, hπ⟩ := ha
  have hS3 : IsPGroup 2 (Equiv.Perm (Fin 3)) := hEa.of_surjective π hπ
  obtain ⟨m, hm⟩ := hS3.exists_card_eq
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [h6] at hm
  have h3 : 3 ∣ 2 ^ m := by rw [← hm]; norm_num
  have := (Nat.prime_three).dvd_of_dvd_pow h3
  omega

theorem trans_of_twin {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card G < n)
    (hΦ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    (hq : ∀ J ∈ Φ, Nonempty (↥J ≃* QuaternionGroup 2)) (hA : ∀ J ∈ Φ, AEmpty Φ J)
    (hO : classicalInvolutionOddCore G = ⊥) {K K' : Subgroup G} (hK : K ∈ Φ)
    (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K')
    (hperp' : ∀ J ∈ Φ, J ≠ K' → J ≤ Subgroup.normalizer (K' : Set G) → J = K) {a : G}
    (ha : HasS3Quot ↥(Ea Φ a)) : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : G, conjSub g L = L' := by
  have hK'Φ : K' ∈ Φ := hK'tw.1
  have hq' : ∀ J ∈ Φ, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    intro J hJ P hP
    have hJP : J = P := hP.2.2 J le_rfl (h2 J hJ) hP.1
    subst hJP
    exact hq J hJ
  have h4' := h4 G hlt Φ hΦ (fun J hJ => IsPGroup.of_surjective (h2 J hJ) (QuotientGroup.mk' (classicalInvolutionOddCore ↥J))
      (QuotientGroup.mk'_surjective _)) hq' hA hO
  have hnorm : ∀ J K₀ : Subgroup G, Commutes K₀ J → J ≤ Subgroup.normalizer (K₀ : Set G) :=
    fun J K₀ hc y hy => mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hy hc.symm)
  have hA_ : ∀ L ∈ Φ, L ≠ K → (¬ ∃ g : G, conjSub g K = L) → L = K' := fun L hL hLK hno =>
    hperp L hL hLK (hnorm L K (h4' K hK L hL hno))
  have hA' : ∀ L ∈ Φ, L ≠ K' → (¬ ∃ g : G, conjSub g K' = L) → L = K := fun L hL hLK hno =>
    hperp' L hL hLK (hnorm L K' (h4' K' hK'Φ L hL hno))
  obtain ⟨J₁, hJ₁, hJ₁K, hJ₁K'⟩ := exists_third_member hΦ h2 hK hK'tw hne ha
  have hJ₁orb : ∃ g : G, conjSub g K = J₁ := by
    by_contra hno
    exact hJ₁K' (hA_ J₁ hJ₁ hJ₁K hno)
  have hJ₁orb' : ∃ g : G, conjSub g K' = J₁ := by
    by_contra hno
    exact hJ₁K (hA' J₁ hJ₁ hJ₁K' hno)
  obtain ⟨g₁, hg₁⟩ := hJ₁orb
  obtain ⟨g₂, hg₂⟩ := hJ₁orb'
  have hK'orb : ∃ g : G, conjSub g K = K' :=
    ⟨g₂⁻¹ * g₁, by rw [conjSub_mul, hg₁, ← hg₂, conjSub_inv_conjSub]⟩
  have horb : ∀ L ∈ Φ, ∃ g : G, conjSub g K = L := by
    intro L hL
    by_cases hLK : L = K
    · exact ⟨1, by rw [conjSub_one, hLK]⟩
    · by_contra hno
      have := hA_ L hL hLK hno
      subst this
      exact hno hK'orb
  intro L hL L' hL'
  obtain ⟨g, rfl⟩ := horb L hL
  obtain ⟨g', rfl⟩ := horb L' hL'
  exact ⟨g' * g⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩

end Trans

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
