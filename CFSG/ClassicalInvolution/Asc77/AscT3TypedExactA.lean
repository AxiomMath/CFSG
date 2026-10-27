module

public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactComp
public import CFSG.ClassicalInvolution.Asc77.AscT3Final

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.G2D4Models
open scoped commutatorElement

section Conj

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K J : Subgroup G} {zK zJ : G}

theorem _root_.CFSG.ClassicalInvolution.Asc77.T3.AViol.conj (hΩ : ConjInvariant Ω)
    (h : AViol Ω K J zK zJ) (g : G) :
    AViol Ω (conjSub g K) (conjSub g J) (g * zK * g⁻¹) (g * zJ * g⁻¹) where
  star := omegaStarNbr_conj hΩ h.star g
  not_nbr := fun hn => h.not_nbr (by
    have := omegaNbr_conj hΩ hn g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this)
  hzK := h.hzK.conj g
  hzJ := h.hzJ.conj g
  no_conj := by
    intro g' hg' hcon
    rw [← conjSub_pairNormalizers', mem_conjSub_iff] at hg'
    apply h.no_conj (g⁻¹ * g' * g) hg'
    rw [conjSub_mul, conjSub_mul, hcon, conjSub_inv_conjSub]

theorem aSet_conj (hΩ : ConjInvariant Ω) (h : J ∈ aSet Ω K) (g : G) :
    conjSub g J ∈ aSet Ω (conjSub g K) := by
  obtain ⟨zK, zJ, hv⟩ := h
  exact ⟨_, _, hv.conj hΩ g⟩

theorem aGraphAdj_conj (hΩ : ConjInvariant Ω) (h : aGraphAdj Ω K J) (g : G) :
    aGraphAdj Ω (conjSub g K) (conjSub g J) := by
  obtain ⟨hJ, h | h | ⟨ht, hne⟩⟩ := h
  · exact ⟨hΩ g J hJ, Or.inl (aSet_conj hΩ h g)⟩
  · exact ⟨hΩ g J hJ, Or.inr (Or.inl (aSet_conj hΩ h g))⟩
  · exact ⟨hΩ g J hJ, Or.inr (Or.inr ⟨twinSet_conj hΩ ht g, fun e => hne ((conjSub_inj g).mp e)⟩)⟩

theorem aStar_conj (hΩ : ConjInvariant Ω) (h : J ∈ aStar Ω K) (g : G) :
    conjSub g J ∈ aStar Ω (conjSub g K) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (aGraphAdj_conj hΩ hbc g)

theorem aGraphAdj_symm (hK : K ∈ Ω) (h : aGraphAdj Ω K J) : aGraphAdj Ω J K := by
  obtain ⟨hJ, h | h | ⟨ht, hne⟩⟩ := h
  · exact ⟨hK, Or.inr (Or.inl h)⟩
  · exact ⟨hK, Or.inl h⟩
  · obtain ⟨-, z, hz, hzJ⟩ := ht
    exact ⟨hK, Or.inr (Or.inr ⟨⟨hK, z, hzJ, hz⟩, fun e => hne e.symm⟩)⟩

theorem mem_aStar_symm (hK : K ∈ Ω) (h : J ∈ aStar Ω K) : J ∈ Ω ∧ K ∈ aStar Ω J := by
  induction h with
  | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    exact ⟨hbc.1, Relation.ReflTransGen.head (aGraphAdj_symm ih.1 hbc) ih.2⟩

theorem mem_conjStab_aStar (hΩ : ConjInvariant Ω) (hK : K ∈ Ω) (hJ : J ∈ aStar Ω K) {x : G}
    (hx : conjSub x J = J) : x ∈ conjStab (aStar Ω K) := by
  obtain ⟨-, hKJ⟩ := mem_aStar_symm hK hJ
  have fwd : ∀ y : G, conjSub y J = J → ∀ M, M ∈ aStar Ω K → conjSub y M ∈ aStar Ω K := by
    intro y hy M hM
    have h2 := aStar_conj hΩ (hKJ.trans hM) y
    rw [hy] at h2
    exact hJ.trans h2
  have hx' : conjSub x⁻¹ J = J := by
    calc conjSub x⁻¹ J = conjSub x⁻¹ (conjSub x J) := by rw [hx]
      _ = J := conjSub_inv_conjSub x J
  intro M
  constructor
  · intro hM
    have := fwd x⁻¹ hx' _ hM
    rwa [conjSub_inv_conjSub] at this
  · exact fwd x hx M

end Conj

section Component

variable {X : Type} [Group X] [Finite X] {p f : ℕ} [Fact p.Prime] {Φ : Set (Subgroup X)}

theorem quotViol_of_aViol_self (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ)
    {K J : Subgroup X} {zK zJ : X} (hK : K ∈ Φ) (hv : AViol Φ K J zK zJ) :
    ∃ a : X, QuotViol Φ K J zK zJ a := by
  obtain ⟨a, ha, haj, -, -, hne⟩ := hv.exists_twin (l6_2 p f) hp hq hΦ hK
  exact ⟨a, hK, hv.mem, hv.hzK, hv.hzJ, (hv.ne_involution hΦ hK).symm, hv.comm hp hΦ, hv.star, ha,
    haj, hne⟩

variable (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΦ : HypOmegaMod p f Φ) (D : OmegaLie p f Φ)
  {i : Fin D.card}

include hp hq hΦ

theorem aStar_subset_compMembers (hi : D.tag i = .G2 ∨ D.tag i = .trialityD4) {K : Subgroup X}
    (hK : K ∈ compMembers D i) {J : Subgroup X} (hJ : J ∈ aStar Φ K) : J ∈ compMembers D i := by
  induction hJ with
  | refl => exact hK
  | @tail B C _ hbc ih =>
    obtain ⟨hCΦ, h | h | ⟨ht, -⟩⟩ := hbc
    · obtain ⟨zB, zC, hv⟩ := h
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_self hp hq hΦ (compMembers_subset D i ih) hv
      obtain ⟨i', R, S, hR, hS, hBR, hCS⟩ := hQ.exists_components D
      have := compMembers_unique hΦ D ih (⟨R, hR, hBR⟩ : B ∈ compMembers D i')
      subst this
      exact ⟨S, hS, hCS⟩
    · obtain ⟨zC, zB, hv⟩ := h
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_self hp hq hΦ hCΦ hv
      obtain ⟨i', R, S, hR, hS, hCR, hBS⟩ := hQ.exists_components D
      have := compMembers_unique hΦ D ih (⟨S, hS, hBS⟩ : B ∈ compMembers D i')
      subst this
      exact ⟨R, hR, hCR⟩
    · exact twin_mem_compMembers hp D hi ih ht

end Component

end CFSG.ClassicalInvolution.Asc77.T3Typed
