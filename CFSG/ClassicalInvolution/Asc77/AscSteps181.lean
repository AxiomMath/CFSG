module

public import CFSG.ClassicalInvolution.Asc77.AscSix610
public import CFSG.ClassicalInvolution.Asc77.WP1Section18

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem E187C.centralizer_le_of {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K R H : Subgroup G} {z : G} (hK : K ∈ Ω) (hRΩ : R ∈ RSet Ω) (hRK : R ≤ K)
    (h8 : 8 ≤ Nat.card R) (hcent : CentralizersSylowPairs Ω K H) (hz : IsUniqueInvolution K z) :
    Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨-, -, -, hR2, -⟩ := mem_RSet_iff.mp hRΩ
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hRK hR2 (by omega)
  exact hcent K ⟨hK, z, hz, hz⟩ K (Set.mem_insert _ _) R R hRΩ hRK hRΩ hRK
    (Or.inr rfl) z (Subgroup.mem_sup_left hzR) hz.ne_one hz.sq

set_option linter.unusedSectionVars false in
theorem MinCex.centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex p f Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H :=
  E187C.centralizer_le_of c.stand.mem c.stand.hR.1 c.stand.hR.2.1
    (c.stand.hyp.eight_le_of_mem_RSet c.stand.odd c.stand.hR.1) c.hyp.cent hz

theorem MinCex.exists_centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex p f Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨z, hz⟩ := c.stand.hyp.exists_uniqueInvolution c.stand.odd c.stand.five c.stand.mem
  exact ⟨z, hz, c.centralizer_le p f hz⟩

theorem E187C.e18_1_of {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K H : Subgroup G}
    {z : G} (hc : ConjInvariant Ω) (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) (hproper : H ≠ ⊤) :
    (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K := by
  have key : ∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H := by
    intro g hg
    obtain ⟨h, hhH, hh⟩ := htrans _ hg
    have hn : conjSub (h⁻¹ * g) K = K := by
      rw [conjSub_mul, ← hh, conjSub_inv_conjSub]
    have hcent : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_inv_eq_iff_eq_mul.mp (hz.conj_eq hn)
    have hg' : g = h * (h⁻¹ * g) := by group
    rw [hg']
    exact H.mul_mem hhH (hcz hcent)
  refine ⟨key, ?_⟩
  by_contra hno
  push Not at hno
  apply hproper
  rw [eq_top_iff]
  intro g _
  exact key g (hno _ (hc g K hK))

theorem e18_1 : E18_1 p f := by
  intro G _ _ Ω K S R W H c
  obtain ⟨z, hz, hcz⟩ := c.exists_centralizer_le p f
  exact E187C.e18_1_of c.stand.hyp.conjInvariant c.stand.mem hz hcz c.hyp.trans c.proper

end CFSG.ClassicalInvolution.Asc77
