module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM05
public import CFSG.ClassicalInvolution.Asc77.AscE187Main
public import CFSG.ClassicalInvolution.Q3.Q3T7FUE6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7E

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.part1 (h : E187Hyps) (h4 : E187E4C)
    (c : MinCex Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgt : g * a * g⁻¹ ∈ H) :
    ∃ h' ∈ H, h' * a * h'⁻¹ = g * a * g⁻¹ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.part1 (h := h.toU) (h6 := (h.e6.atG c))
    (h4 := (h4.atG c)) (c := c.toU) (hz := hz) (hzW := hzW) (hP := hP) (ha2 := ha2) (ha1 := ha1)
    (haH := haH) (hgt := hgt)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_config_sylow (c : MinCex Ω K S R W H)
    {K' R' X : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) (hRX : R ⊔ R' ≤ X) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex Ω K S' R W' H ∧ R ⊔ R' ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
  have hΩ : HM Ω := c.stand.hyp
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hRR' : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  obtain ⟨P, hP, hRRP⟩ := IsSylow2In.exists_ge hRR' hRX
  obtain ⟨S', hPS'⟩ := IsPGroup.exists_le_sylow hP.2.1
  have hSyl : IsSylow2In ((S' : Subgroup G) ⊓ X) X := by
    have hle : P ≤ (S' : Subgroup G) ⊓ X := le_inf hPS' hP.1
    have hp2 : IsPGroup 2 ↥((S' : Subgroup G) ⊓ X) := S'.isPGroup'.to_le inf_le_left
    have heq := hP.eq_of_le hp2 inf_le_right hle
    rw [heq]
    exact hP
  obtain ⟨W', hW', hW'S', hW'n⟩ := WSet.exists_normalized_sylow hΩ S'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans (hRRP.trans hPS')
  have hR'S' : R' ≤ (S' : Subgroup G) := le_sup_right.trans (hRRP.trans hPS')
  exact ⟨S', W', c.of_sylow hRS' hK' hne hR' hR'K' hR'S' hW' hW'S' hW'n,
    sup_le hRS' hR'S', hSyl⟩

theorem MinCex.exists_config_sylow_centralizer (c : MinCex Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) :
    ∃ (S' : Sylow 2 G) (W' : Subgroup G), MinCex Ω K S' R W' H ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
        (Subgroup.centralizer ({z} : Set G)) := by
  have hΩ : HM Ω := c.stand.hyp
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨-, hRK, -⟩ := c.stand.hR
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'K'⟩ := hK'tw
    have := hz.eq hz'K
    rwa [← this] at hz'K'
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz.commute_of_mem hx).symm
  have hK'C : K' ≤ Subgroup.centralizer ({z} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hz'.commute_of_mem hx).symm
  obtain ⟨S', W', c', -, hSyl⟩ := c.exists_config_sylow hK'tw hne hR' hR'K' hR'S
    (X := Subgroup.centralizer ({z} : Set G)) (sup_le (hRK.trans hKC) (hR'K'.trans hK'C))
  exact ⟨S', W', c', hSyl⟩

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.goodFour_of_noncommute (h : E187Hyps) (h4 : E187E4C)
    (c : MinCex Ω K S R W H) {z g t : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hSylz : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G))
      (Subgroup.centralizer ({z} : Set G)))
    (hg : g ∉ H) (ht : t = g * z * g⁻¹) (htS : t ∈ (S : Subgroup G)) (hnc : ¬ t * z = z * t) :
    GoodFour H t :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.goodFour_of_noncommute (h := h.toU)
    (h6 := (h.e6.atG c)) (h4 := (h4.atG c)) (c := c.toU) (hz := hz) (hzW := hzW) (hzH := hzH)
    (hSylz := hSylz) (hg := hg) (ht := ht) (htS := htS) (hnc := hnc)

end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.part2 (h : E187Hyps) (h4 : E187E4C)
    (c : MinCex Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z)
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) :
    ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H := by
  have hΩ : HM Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hΩ
  have hM : EtaMeet Ω := h.etaMeet hΩ
  obtain ⟨S', W', c', hSylz⟩ := c.exists_config_sylow_centralizer hz
  have hzW' : z ∈ W' := by
    obtain ⟨z', hz'K, hz'W, -⟩ := c'.exists_z
    rwa [hz'K.eq hz] at hz'W
  exact E187C.part2_of hΩ.conjInvariant c.stand.mem hz (c'.sylow_le hA)
    (fun {g₁ t} hg₁H ht htS => by
      by_cases hcomm : t * z = z * t
      · exact c'.goodFour_of_commute h hz hzH hg₁H ht htS hcomm
      · exact c'.goodFour_of_noncommute h h4 hz hzW' hzH hSylz hg₁H ht htS hcomm)
    (fun hg' => c'.hbad_of_conj hA hM hz hg')
    (fun hbad hK₁ ht g₁ g₂ g₃ hcm => endgame_four hΩ hbad hK₁ ht g₁ g₂ g₃ hcm)

theorem e18_7 (h : E187Hyps) (h4 : E187E4C) : E18_7 := by
  intro G _ _ Ω K S R W H c a ha1 ha2 haH g hgt
  obtain ⟨z, hz, hzW, hzH⟩ := c.exists_z
  exact c.part1 h h4 hz hzW (c.part2 h h4 hz hzH) ha2 ha1 haH hgt

end Main
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7E
