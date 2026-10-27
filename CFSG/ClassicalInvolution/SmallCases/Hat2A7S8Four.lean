module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Min
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Two
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S6Main
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7Coset
import CFSG.StronglyEmbedded.UniqueCosetFixedEng
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8E274A
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8E274B
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.StronglyEmbedded.UniqueCoset

section Four


theorem a7C27_4a_proved :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8A7 Ω K J S R T W z t →
        ¬ DConnected Ω → FixesUniqueCoset (z * t) (T8.H274 Ω K z) := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hs' : Hat2A7S8.Asc77.Std8 Ω K J S R T W z t := Hat2A7S8.Asc77.Std8.of_std8A7 hs
  have hcomp : dComp Ω K = dstarComp Ω K := a7C27_2_proved G Ω K J S R T W z t hs hdisc
  have hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ T8.H274 Ω K z :=
    fun S₂ hRS₂ hcount x _ hx2 hx1 hcent =>
      Hat2A7S8.centralizer_le_H274_of_eight hs' hRS₂ hcount hx2 hx1 hcent
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact Hat2A7S8.Asc77.T8.mem_H274_of_min hs' hcomp hmin hg

theorem a7C27_4_proved : A7C27_4 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hs' : Hat2A7S8.Asc77.Std8 Ω K J S R T W z t := Hat2A7S8.Asc77.Std8.of_std8A7 hs
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hcls := hs.stand.classical
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hcomp : dComp Ω K = dstarComp Ω K := a7C27_2_proved G Ω K J S R T W z t hs hdisc
  by_contra hne
  have hH : T8.H274 Ω K z ≠ ⊤ := hne
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c :=
    Hat2A7S8.Asc77.T8.fixesUniqueCoset_z hs' hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
      have := hz.conj g⁻¹
      rwa [inv_inv] at this
    have hKg : conjSub g⁻¹ K ∈ Ω := hΩ.conjInvariant g⁻¹ K hK
    have hKne : conjSub g⁻¹ K ≠ K := by
      intro h
      apply hne'
      have := hz.conj_eq (n := g⁻¹) h
      simpa using this
    have hzN : z ∈ Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) :=
      T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hKg (hnt _ hKg) hb
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    have hnbr : conjSub g⁻¹ K ∈ omegaNbr Ω K :=
      mem_omegaNbr_of_normalizes_a7 hΩ hcls hK hKg hKne hz hb hzN
    obtain ⟨S', R', T', W', hstd⟩ := a7C27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
      (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
    exact a7C27_4a_proved G Ω K (conjSub g⁻¹ K) S' R' T' W' z (g⁻¹ * z * g) hstd hdisc
  have hKcl : Hat2A7.IsClassical2A7 ⊤ K z :=
    Hat2A7S8.Asc77.T8.isClassical2A7_of_isUniqueInvolution hcls hK hz
  exact false_of_uniqueCoset_a7 hs.stand.nonabelian hH hz2 h1 h2' hKcl

end Four

end CFSG.ClassicalInvolution.Hat2A7S
