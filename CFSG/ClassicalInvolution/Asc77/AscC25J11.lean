module

public import CFSG.ClassicalInvolution.Asc77.AscC25J7
public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem crossIn_swap_ne (d : TwinCtx p f Ω K K' z) {a : G}
    (hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K a)))
    {c : ↥(Subgroup.centralizer ({a} : Set G))} (hcK : conjSub (c : G) K = K') :
    conjSub c (crossIn K a) ≠ crossIn K a := by
  have hΩg : HypOmegaGen (conjFamily (crossIn K a)) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΛ
  have hM₁ : crossIn K a ∈ conjFamily (crossIn K a) := ⟨1, conjSub_one _⟩
  have hKaK : K ⊓ Subgroup.centralizer ({a} : Set G) ≤ K := inf_le_left
  have hmap1 : (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype =
      K ⊓ Subgroup.centralizer ({a} : Set G) := by
    simp
  have hmap2 : (conjSub c (crossIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := map_conjSub_crossIn c
  intro h
  obtain ⟨P, hP, hP1, -⟩ := exists_mem_RSet_ge hM₁
    (isPGroup_two_bot' (G := ↥(Subgroup.centralizer ({a} : Set G)))) bot_le
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg hP
  have hP2 : IsPGroup 2 P := hP1.2.1
  have hA2 : IsPGroup 2 (P.map (Subgroup.centralizer ({a} : Set G)).subtype) := hP2.map _
  have hcard : Nat.card ↥(P.map (Subgroup.centralizer ({a} : Set G)).subtype) = Nat.card P :=
    (Nat.card_congr (Subgroup.equivMapOfInjective P _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv).symm
  have hPle : P ≤ crossIn K a := hP1.1
  have hAK : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K := by
    rw [← hmap1] at hKaK
    exact (Subgroup.map_mono hPle).trans hKaK
  have hAK' : P.map (Subgroup.centralizer ({a} : Set G)).subtype ≤ K' := by
    have h1 : (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype ≤
        conjSub (c : G) K := by
      calc (crossIn K a).map (Subgroup.centralizer ({a} : Set G)).subtype
          = (conjSub c (crossIn K a)).map
              (Subgroup.centralizer ({a} : Set G)).subtype := by rw [h]
        _ = conjSub (c : G) (K ⊓ Subgroup.centralizer ({a} : Set G)) := hmap2
        _ ≤ conjSub (c : G) K := Subgroup.map_mono hKaK
    rw [hcK] at h1
    exact (Subgroup.map_mono hPle).trans h1
  exact d.ne (d.hΩ.eq_of_le_of_le d.hK d.hK' hA2 (by omega) hAK hAK').symm

theorem crossIn_isUniqueInvolution_secImg (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (secImg (conjGen (crossIn K a)) (conjSub c (crossIn K a)))
      (QuotientGroup.mk' _ ⟨c * ⟨z, hzA⟩ * c⁻¹, le_conjGen ⟨c, rfl⟩
        (crossIn_isUniqueInvolution_conjSub hI hzA hzKa c).mem⟩) :=
  isUniqueInvolution_map_mk (CFSG.ComponentClassification.OddCore.odd_card _)
    (S1911.isUniqueInvolution_subgroupOf (crossIn_isUniqueInvolution_conjSub hI hzA hzKa c)
      (le_conjGen ⟨c, rfl⟩))

end Datum

end CFSG.ClassicalInvolution.Asc77.C25J
