module

public import CFSG.ClassicalInvolution.Q3.Q3VLiftCover
public import CFSG.ClassicalInvolution.Q3.Q3VLiftDict

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.Lift

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane longBlock)
open CFSG.ClassicalInvolution.Q3.Q3W (LocalOddThreeFree3 Pow3 card_gf3 pow3_range_sl2
  eq_of_map_eq_of_pow3 pow_three_mem_commutator_of_equiv)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (exists_lift_of_noCover)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

theorem pow3_planeGroupR {m : ℕ} (hm : 1 ≤ m)
    {P : Submodule (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1)}
    (hP : IsHyperbolicPlane P) : Pow3 (planeGroup P) := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP
    (⟨0, hm⟩ : Fin m)
  rw [hg]
  exact (pow3_range_sl2 card_gf3 (longBlock (GaloisField 3 1) m ⟨0, hm⟩)).map _

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem exists_layer_liftR {m : ℕ} (hm : 2 ≤ m) (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {z}) (hO3 : LocalOddThreeFree3 Ω z) (d : ShapeCDictR m Ω z) :
    ∃ (Θ : StatedSp m (GaloisField 3 1) →* G) (hΘ : ∀ g, Θ g ∈ locLayer Ω z),
      Θ.ker ≤ Subgroup.center (StatedSp m (GaloisField 3 1)) ∧
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z))).comp
        (Θ.codRestrict (locLayer Ω z) hΘ) = d.ψ ∧
      ∀ P, IsHyperbolicPlane P → (planeGroup P).map Θ ∈ centralizingMembers Ω {z} ∧
        locImg Ω z ((planeGroup P).map Θ) = (planeGroup P).map d.ψ := by
  set O := classicalInvolutionOddCore ↥(locLayer Ω z) with hOdef
  have hker0 : (QuotientGroup.mk' O).ker ≤ Subgroup.center ↥(locLayer Ω z) := by
    rw [QuotientGroup.ker_mk']
    exact hP1
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card _
  have hcop : ∀ w ∈ (QuotientGroup.mk' O).ker, ¬ 3 ∣ orderOf w := by
    intro w hw h
    rw [QuotientGroup.ker_mk'] at hw
    exact hO3 (h.trans (Subgroup.orderOf_dvd_natCard O hw))
  have : Group.IsPerfect (StatedSp m (GaloisField 3 1)) := isPerfect_sp_three hm
  have hdiv : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ 3 ∣ n) → (Odd m ∧ ¬ 3 ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  obtain ⟨β, hβ⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ 3 ∣ n) hdiv
    (spR_three_noCover m) (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O) hker0
    (by rw [QuotientGroup.ker_mk']; exact ⟨hOodd, hO3⟩) d.ψ
  have hβ' : ∀ g, QuotientGroup.mk' O (β g) = d.ψ g := fun g => DFunLike.congr_fun hβ g
  have hΘ : ∀ g, ((locLayer Ω z).subtype.comp β) g ∈ locLayer Ω z := fun g => (β g).2
  have hcodRestrict : ((locLayer Ω z).subtype.comp β).codRestrict (locLayer Ω z) hΘ = β :=
    MonoidHom.ext fun g => Subtype.ext rfl
  refine ⟨(locLayer Ω z).subtype.comp β, hΘ, ?_, by rw [hcodRestrict]; exact hβ, ?_⟩
  · intro g hg
    apply d.ker_le
    have h1 : β g = 1 := Subtype.ext (MonoidHom.mem_ker.mp hg)
    rw [MonoidHom.mem_ker, ← hβ', h1, map_one]
  · intro P hP
    obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam P hP)
    have hLY : L ≤ locLayer Ω z := le_centralizingLayer hL
    have hA : Pow3 ((planeGroup P).map β) := (pow3_planeGroupR (by omega) hP).map β
    have hB : Pow3 (L.subgroupOf (locLayer Ω z)) := by
      obtain ⟨zL, hzL⟩ := hΩ.classical L hL.1
      obtain ⟨e⟩ := hzL.nonempty_equiv_sl2 (hex L hL.1)
      exact pow_three_mem_commutator_of_equiv (Nat.card_zmod 3)
        ((Subgroup.subgroupOfEquivOfLe hLY).trans e)
    have hAB : ((planeGroup P).map β).map (QuotientGroup.mk' O) =
        (L.subgroupOf (locLayer Ω z)).map (QuotientGroup.mk' O) := by
      rw [Subgroup.map_map, hβ]
      exact hLR.symm
    have hEq := eq_of_map_eq_of_pow3 (QuotientGroup.mk' O) hker0 hcop hA hB hAB
    have hmap : (planeGroup P).map ((locLayer Ω z).subtype.comp β) = L := by
      rw [← Subgroup.map_map, hEq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLY]
    rw [hmap]
    exact ⟨hL, hLR⟩

end CFSG.ClassicalInvolution.Q3.Q3V.Lift
