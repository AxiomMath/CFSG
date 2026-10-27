module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscSix69
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedSplit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_commutes_isSylow2InE {K R R' : Subgroup G} (hR : IsSylow2In R K)
    (hR' : IsSylow2In R' K) (hc : Commutes R R') : R' = R := by
  have hn : R' ≤ Subgroup.normalizer (R : Set G) := by
    intro y hy
    refine Subgroup.centralizer_le_normalizer (R : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hc x hx y hy
  have h2 : IsPGroup 2 ↥(R' ⊔ R) := hR'.2.1.to_sup_of_normal_right' hR.2.1 hn
  have heq : R' ⊔ R = R := hR.2.2 (R' ⊔ R) (sup_le hR'.1 hR.1) h2 le_sup_right
  exact Subgroup.eq_of_le_of_card_ge (heq ▸ le_sup_left) (le_of_eq (hR'.natCard_eq hR).symm)

theorem conjSub_mem_omegaNbrE (hcl : ConjInvariant Ω)
    (hsyl : ∀ {M R : Subgroup G}, M ∈ Ω → R ∈ RSet Ω → R ≤ M → IsSylow2In R M)
    (h8 : ∀ {R : Subgroup G}, R ∈ RSet Ω → 8 ≤ Nat.card R)
    {K R : Subgroup G} {S : Sylow 2 G}
    (hl67 : ∀ R₁ ∈ RSet Ω, ∀ R₂ ∈ RSet Ω, R₁ ≤ (S : Subgroup G) → R₂ ≤ (S : Subgroup G) →
      R₁ ≠ R₂ → Commutes R₁ R₂)
    (hnorm : ∀ {K₀ J₀ : Subgroup G} {z₀ : G} {A : Subgroup G}, K₀ ∈ Ω → J₀ ∈ Ω → K₀ ≠ J₀ →
      IsUniqueInvolution K₀ z₀ → A ≤ J₀ → IsPGroup 2 A → 3 ≤ Nat.card A →
        A ≤ Subgroup.centralizer ({z₀} : Set G) → A ≤ Subgroup.normalizer (K₀ : Set G))
    (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K)
    (hRS : R ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hfix : conjSub s R ≠ R) : conjSub s K ∈ omegaNbr Ω K := by
  have hRsyl : IsSylow2In R K := hsyl hK hR hRK
  have h8 : 8 ≤ Nat.card R := h8 hR
  have hK' : conjSub s K ∈ Ω := hcl s K hK
  have hP : conjSub s R ∈ RSet Ω := RSet.conj hcl hR s
  have hPS : conjSub s R ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := s) hRS
    rwa [conjSub_eq_self_of_mem hs] at this
  have hcomm : Commutes R (conjSub s R) :=
    hl67 R hR _ hP hRS hPS (Ne.symm hfix)
  have hPK' : conjSub s R ≤ conjSub s K := conjSub_mono hRK
  have hPsyl : IsSylow2In (conjSub s R) (conjSub s K) := hRsyl.conj s
  have hKK' : conjSub s K ≠ K := by
    intro h
    rw [h] at hPsyl
    exact hfix (eq_of_commutes_isSylow2InE hRsyl hPsyl hcomm)
  have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hRsyl.2.1 (by omega)
  have hPN : conjSub s R ≤ Subgroup.normalizer (K : Set G) := by
    refine hnorm hK hK' hKK'.symm hz hPK' hPsyl.2.1
      (by rw [natCard_conjSub]; omega) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm z hzR x hx).symm
  exact ⟨hK', hKK', conjSub s R, hP, hPK', hPN⟩

end T8

end CFSG.ClassicalInvolution.Asc77
