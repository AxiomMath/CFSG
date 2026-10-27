module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section B

@[expose] def E189ConclF {Y : Type} [Group Y] [Finite Y] (Λ : Set (Subgroup Y)) (K : Subgroup Y)
    (z t : Y) : Prop :=
  (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧
      IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧
        x * u * x⁻¹ = z * t ∧ ((∃ e : Y, e * u * e⁻¹ = z) ∨ ∀ a ∈ R₁, ∀ b ∈ R₂, orderOf a = 4 →
          orderOf b = 4 → ∃ e : Y, e * u * e⁻¹ = a * b)) ∨
  (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
      ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧
        Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

@[expose] def E189LeafQ8 : Prop :=
  ∀ n : ℕ, EIH n →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ Λ : Set (Subgroup Y), TwinDisc.Q8Section Y Λ → Q3CL.ClassicalClause Λ →
        ∀ K ∈ Λ, (∀ L ∈ Λ, ∃ y : Y, conjSub y K = L) → (∀ L ∈ Λ, L ∈ dstarComp Λ K) →
          (∃ K' ∈ twinSet Λ K, K' ≠ K) →
          ∀ z : Y, IsUniqueInvolution K z →
            oddCoreImg (Subgroup.centralizer ({z} : Set Y)) = ⊥ →
            ∀ J ∈ Λ, ∀ t : Y, IsUniqueInvolution J t → z * t = t * z → conjSub t K ≠ K →
              E189ConclF Λ K z t

@[expose] def E189OddCoreQ8 : Prop :=
  ∀ n : ℕ, EIH n →
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
      ∀ Λ : Set (Subgroup Y), TwinDisc.Q8Section Y Λ → Q3CL.ClassicalClause Λ →
        ∀ K ∈ Λ, (∀ L ∈ Λ, ∃ y : Y, conjSub y K = L) → (∀ L ∈ Λ, L ∈ dstarComp Λ K) →
          (∃ K' ∈ twinSet Λ K, K' ≠ K) →
          ∀ z : Y, IsUniqueInvolution K z →
            oddCoreImg (Subgroup.centralizer ({z} : Set Y)) ≠ ⊥ →
            ∀ J ∈ Λ, ∀ t : Y, IsUniqueInvolution J t → z * t = t * z → conjSub t K ≠ K →
              E189ConclF Λ K z t

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem classicalClause_restrict (hcls : Q3CL.ClassicalClause Ω) (Y : Subgroup G) :
    Q3CL.ClassicalClause (restrictFamily Ω Y) where
  subnormal :=
    (TwinThmE.classicalClause_restrict hcls Y).subnormal
  commOdd :=
    (TwinThmE.classicalClause_restrict hcls Y).commOdd

theorem two_restrict (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (Y : Subgroup G) :
    ∀ L ∈ restrictFamily Ω Y, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.two_restrict h2 Y

theorem q8_restrict
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (Y : Subgroup G) :
    ∀ L ∈ restrictFamily Ω Y,
      ∃ P : Subgroup Y, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.q8_restrict hq8 Y

theorem hypOmegaGen_of_sub {Φ Ψ : Set (Subgroup G)} (h : HypOmegaGen Φ) (hsub : Ψ ⊆ Φ)
    (hc : ConjInvariant Ψ) : HypOmegaGen Ψ where
  conjInvariant := hc
  omega1 := fun K hK => h.omega1 K (hsub hK)
  omega2 := fun K hK => h.omega2 K (hsub hK)
  omega3 := fun K hK J hJ => h.omega3 K (hsub hK) J (hsub hJ)
  omega4 := fun K hK J hJ => h.omega4 K (hsub hK) J (hsub hJ)
  omega5 := fun K hK J hJ => h.omega5 K (hsub hK) J (hsub hJ)

theorem aEmpty_of_sub {Φ Ψ : Set (Subgroup G)} (h : HypOmegaGen Φ) (hsub : Ψ ⊆ Φ)
    (hA : ∀ L ∈ Φ, AEmpty Φ L) : ∀ L ∈ Ψ, AEmpty Ψ L := by
  intro L hL J hJ hJn zK zJ hzK hzJ
  have hJΨ : J ∈ Ψ := hJ.1
  obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := hJ
  have hUΦ : U ∈ USet Φ := by
    obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
    obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
    exact ⟨R, mem_RSet_of_isSylow2In (hsub hM) hRM, hUR, hcyc, hidx⟩
  have hJ' : J ∈ omegaStarNbr Φ L := ⟨hsub hJΨ, hne, U, hUΦ, hUJ, hUN⟩
  have hJn' : J ∉ omegaNbr Φ L := by
    rintro ⟨-, -, R, hR, hRJ, hRN⟩
    apply hJn
    obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
    have h8 := h.eight_le_of_mem_RSet hR
    have hMJ : M = J := h.eq_of_le_of_le hM (hsub hJΨ) hRM.2.1 (by omega) hRM.1 hRJ
    rw [hMJ] at hRM
    exact ⟨hJΨ, hne, R, mem_RSet_of_isSylow2In hJΨ hRM, hRJ, hRN⟩
  exact hA L (hsub hL) J hJ' hJn' zK zJ hzK hzJ

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

end B

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
