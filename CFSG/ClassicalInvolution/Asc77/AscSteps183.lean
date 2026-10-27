module

public import CFSG.ClassicalInvolution.Asc77.AscSix610
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem E187C.e18_3_of {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K R H : Subgroup G} {S : Sylow 2 G} (hc : ConjInvariant Ω) (hK : K ∈ Ω)
    (hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G))
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J)
    (hzK0 : ∀ {K : Subgroup G}, K ∈ Ω → ∃ z : G, IsUniqueInvolution K z)
    (h8R : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → 8 ≤ Nat.card Q)
    (heq : ∀ {K J A : Subgroup G}, K ∈ Ω → J ∈ Ω → IsPGroup 2 A → 4 ≤ Nat.card A → A ≤ K →
      A ≤ J → K = J)
    (hl67 : ∀ (S : Sylow 2 G) (T : Subgroup G), T ∈ RSet Ω → ∀ R : Subgroup G, R ∈ RSet Ω →
      T ≤ (S : Subgroup G) → R ≤ (S : Subgroup G) → T ≠ R → Commutes T R)
    (hnorm : ∀ {K J : Subgroup G} {z : G} {A : Subgroup G}, K ∈ Ω → J ∈ Ω → K ≠ J →
      IsUniqueInvolution K z → A ≤ J → IsPGroup 2 A → 3 ≤ Nat.card A →
        A ≤ Subgroup.centralizer ({z} : Set G) → A ≤ Subgroup.normalizer (K : Set G))
    (hquat : ∀ {Q : Subgroup G}, Q ∈ RSet Ω → IsQuatSub Q) :
    ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := by
  intro J hJ
  obtain ⟨hRR, hRK, hRS⟩ := hR
  obtain ⟨RJ, hRJmem, hRJ, -⟩ :=
    exists_mem_RSet_ge hJ (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hRJ.2.1
  obtain ⟨y, hy⟩ := exists_conjSub_eq_of_sylow S Q
  set J' : Subgroup G := conjSub y⁻¹ J with hJ'def
  set R' : Subgroup G := conjSub y⁻¹ RJ with hR'def
  have hJ'Ω : J' ∈ Ω := hc y⁻¹ J hJ
  have hR'mem : R' ∈ RSet Ω := RSet.conj hc hRJmem y⁻¹
  have hR'J : IsSylow2In R' J' := hRJ.conj y⁻¹
  have hR'S : R' ≤ (S : Subgroup G) := by
    have h1 : RJ ≤ conjSub y (S : Subgroup G) := hy ▸ hQ
    have := conjSub_mono (n := y⁻¹) h1
    rwa [conjSub_inv_conjSub] at this
  have key : J' ∈ dstarComp Ω K := by
    by_cases hJK : J' = K
    · rw [hJK]
      exact Relation.ReflTransGen.refl
    obtain ⟨z, hz⟩ := hzK0 hK
    have hR2 : IsPGroup 2 R := by
      obtain ⟨J₀, -, -, h2, -⟩ := mem_RSet_iff.mp hRR
      exact h2
    have h8 := h8R hRR
    have h8' := h8R hR'mem
    have hRne : R ≠ R' := by
      intro hRR'
      exact hJK (heq hJ'Ω hK hR2 (by omega) (hRR' ▸ hR'J.1) hRK)
    have hcomm : Commutes R R' := hl67 S R hRR R' hR'mem hRS hR'S hRne
    have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
    have hR'c : R' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR x hx).symm
    have hR'N : R' ≤ Subgroup.normalizer (K : Set G) :=
      hnorm hK hJ'Ω (Ne.symm hJK) hz hR'J.1 hR'J.2.1
        (by omega) hR'c
    obtain ⟨U, hUR, hUcyc, hUcard⟩ :=
      (hquat hR'mem).exists_cyclic_index_two
    have hU : U ∈ USet Ω := mem_USet_of_natCard hJ'Ω hR'J hUR hUcyc hUcard
    exact Relation.ReflTransGen.single ⟨hJ'Ω, Or.inl ⟨hJ'Ω, hJK, U, hU, hUR.trans hR'J.1,
      hUR.trans hR'N⟩⟩
  obtain ⟨h, -, hh⟩ := htrans J' key
  refine ⟨y * h, ?_⟩
  rw [conjSub_mul, hh]
  exact conjSub_conjSub_inv y J

set_option linter.unusedSectionVars false in
theorem e18_3 (h67 : L6_7 p f) : E18_3 p f := by
  intro G _ _ Ω K S R W H c
  exact E187C.e18_3_of c.stand.hyp.conjInvariant c.stand.mem c.stand.hR c.hyp.trans
    (fun hK => c.stand.hyp.exists_uniqueInvolution c.stand.odd c.stand.five hK)
    (fun hQ => c.stand.hyp.eight_le_of_mem_RSet c.stand.odd hQ)
    (fun hK hJ hA h4 hAK hAJ => c.stand.hyp.eq_of_le_of_le hK hJ hA h4 hAK hAJ)
    (h67 c.stand.odd c.stand.five G Ω c.stand.hyp)
    (fun hK hJ hKJ hz hAJ hA2 hA3 hAc =>
      c.stand.hyp.le_normalizer_of_le_centralizer c.stand.odd c.stand.five hK hJ hKJ hz hAJ hA2
        hA3 hAc)
    (fun hQ => c.stand.hyp.isQuatSub_of_mem_RSet c.stand.odd hQ)

end CFSG.ClassicalInvolution.Asc77
