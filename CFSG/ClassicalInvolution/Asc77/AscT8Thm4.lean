module

public import CFSG.ClassicalInvolution.Asc77.AscIHD4
public import CFSG.ClassicalInvolution.Asc77.AscIHExact
public import CFSG.ClassicalInvolution.Asc77.AscIHTwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section G2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem eqOfMapEqOfInjOn {M X : Type*} [Group M] [Group X] (ψ : M →* X) {T : Subgroup M}
    (hinj : ∀ x ∈ T, ψ x = 1 → x = 1) {x y : M} (hx : x ∈ T) (hy : y ∈ T) (h : ψ x = ψ y) :
    x = y := by
  have : x⁻¹ * y = 1 := hinj _ (T.mul_mem (T.inv_mem hx) hy) (by simp [map_mul, map_inv, h])
  exact inv_mul_eq_one.mp this

theorem false_of_g2_pair_noTwins (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmega p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) (D : OmegaLie p f Ω) (i : Fin D.card)
    (hG2 : D.tag i = .G2) {R S : Subgroup (D.model i).K}
    (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hS : S ∈ fundamentalSubgroups (D.tag i) (D.model i).D)
    (hK : R.map (D.hom i) ∈ Ω) (hJ : S.map (D.hom i) ∈ Ω)
    (hnc : ¬ ∃ g : G, conjSub g (R.map (D.hom i)) = S.map (D.hom i)) : False := by
  have hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := fun h => by
    rw [hG2] at h
    exact absurd h.1 (by decide)
  have hker := D.ker_le_center i
  have hinjR := D.injOn_fund i hne hR
  have hinjS := D.injOn_fund i hne hS
  set K := R.map (D.hom i) with hKdef
  set J := S.map (D.hom i) with hJdef
  obtain ⟨zK, hzK0⟩ := hΩ.classical K hK
  obtain ⟨zJ, hzJ0⟩ := hΩ.classical J hJ
  have hzK := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzK0
  have hzJ := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hzJ0
  obtain ⟨rR, hrR, hψrR⟩ := hzK.mem
  obtain ⟨rS, hrS, hψrS⟩ := hzJ.mem
  have hrR2 : rR * rR = 1 := by
    refine eqOfMapEqOfInjOn (D.hom i) hinjR (R.mul_mem hrR hrR) R.one_mem ?_
    rw [map_mul, hψrR, map_one, hzK.sq]
  have hrS2 : rS * rS = 1 := by
    refine eqOfMapEqOfInjOn (D.hom i) hinjS (S.mul_mem hrS hrS) S.one_mem ?_
    rw [map_mul, hψrS, map_one, hzJ.sq]
  have hrR1 : rR ≠ 1 := fun h => hzK.ne_one (by rw [← hψrR, h, map_one])
  have hrS1 : rS ≠ 1 := fun h => hzJ.ne_one (by rw [← hψrS, h, map_one])
  obtain ⟨g, hg⟩ := g2_model_involutions_conj hG2 hp2 (D.admissible i) hrR2 hrS2 hrR1 hrS1
  set K₀ := conjSub (D.hom i g) K with hK₀def
  have hK₀Ω : K₀ ∈ Ω := hΩ.conjInvariant _ K hK
  have hzK₀ : IsUniqueInvolution K₀ zJ := by
    have h1 := hzK.conj (D.hom i g)
    have e : D.hom i g * zK * (D.hom i g)⁻¹ = zJ := by
      rw [← hψrR, ← hψrS, ← hg]
      simp [map_mul, map_inv]
    rwa [e] at h1
  have hK₀J : K₀ ≠ J := fun h => hnc ⟨D.hom i g, h⟩
  exact hK₀J (hnt J hJ K₀ ⟨hK₀Ω, zJ, hzJ, hzK₀⟩)

end G2

@[expose] def Thm4NTBelow (p f n : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ (Ω : Set (Subgroup G)),
      HypOmegaMod p f Ω → CFSG.Open.classicalInvolutionOddCore G = ⊥ →
        (∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) →
          ∀ K ∈ Ω, ∀ J ∈ Ω, (¬ ∃ g : G, conjSub g K = J) → Commutes K J

theorem thm4NTBelow_of_citBelow {n : ℕ} (hn : CITBelowU p f n) : Thm4NTBelow p f n := by
  intro hp2 hq G _ _ hG Ω hΩ hO hnt K hK J hJ hnc
  obtain ⟨D⟩ := exists_omegaLie hn hΩ ⟨K, hK⟩ hO hG
  have hΩ := hΩ.toExact (D.exactMembers hp2 hq hΩ)
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, S, hS, hJS⟩ := D.fundamental J hJ
  by_cases hij : i = j
  swap
  · intro a ha b hb
    rw [hKR] at ha
    rw [hJS] at hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    exact D.commute i j hij x y
  subst hij
  exfalso
  have key : ∀ g, S = R.map (MulAut.conj g).toMonoidHom → ∃ g' : G, conjSub g' K = J := by
    intro g hg
    refine ⟨D.hom i g, ?_⟩
    rw [hKR, hJS, hg, map_conj_eq_conjSub_map]
  by_cases hconj : ∃ g, S = R.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    exact hnc (key g hg)
  by_cases hG2' : D.tag i = .G2
  · refine false_of_g2_pair_noTwins hp2 hq hΩ hnt D i hG2' hR hS (by rw [← hKR]; exact hK)
      (by rw [← hJS]; exact hJ) (by rw [← hKR, ← hJS]; exact hnc)
  by_cases hD4' : D.tag i = .trialityD4
  · have hne : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := fun h => by
      rw [hD4'] at h
      exact absurd h.1 (by decide)
    have hcardR : Nat.card R = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn (D.hom i) (D.injOn_fund i hne hR), ← hKR]
      exact natCard_member hΩ hK
    have hcardS : Nat.card S = Nat.card SL(2, GaloisField p f) := by
      rw [← natCard_map_of_injOn (D.hom i) (D.injOn_fund i hne hS), ← hJS]
      exact natCard_member hΩ hJ
    exact d4OrdersDiffer p (D.tag i) (D.rank i) (D.exp i) hD4' (D.admissible i) R hR S hS hconj
      (hcardR.trans hcardS.symm)
  exact hconj (ModelFacts.fundamentalSingleClass (D.tag i) (D.rank i) p (D.exp i) Fact.out
    (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i) hG2' hD4' R hR S hS)

end CFSG.ClassicalInvolution.Asc77
