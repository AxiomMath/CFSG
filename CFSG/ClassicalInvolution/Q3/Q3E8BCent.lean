module

public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3WAPow
public import CFSG.ClassicalInvolution.RouteD.GapsR2

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


theorem le_centralizer_iff_map3 {K X : Type*} [Group K] [Group X] (φ : K →* X)
    (hker : φ.ker ≤ Subgroup.center K) (hcop : ∀ w ∈ φ.ker, ¬ 3 ∣ orderOf w) {R : Subgroup K}
    (hR : Pow3 R) (k : K) :
    R ≤ Subgroup.centralizer ({k} : Set K) ↔
      R.map φ ≤ Subgroup.centralizer ({φ k} : Set X) := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (h hb)]
  · intro h r hr
    have hc : ∀ a ∈ Subgroup.zpowers k, ∀ l ∈ R, φ a * φ l = φ l * φ a := by
      intro a ha l hl
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have h1 : φ k * φ l = φ l * φ k :=
        (Subgroup.mem_centralizer_singleton_iff.mp (h ⟨l, hl, rfl⟩)).symm
      rw [map_zpow]
      exact (Commute.zpow_left (show Commute (φ k) (φ l) from h1) m).eq
    have := commutes_of_map_commute_exponent3 φ hker hcop (A := Subgroup.zpowers k) (L := R) hR hc
      k (Subgroup.mem_zpowers k) r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

theorem le_centralizer_iff_locImg3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (y : ↥(locLayer Ω x)) :
    L ≤ Subgroup.centralizer ({(y : G)} : Set G) ↔
      locImg Ω x L ≤ Subgroup.centralizer ({locMk Ω x y} : Set (locQuot Ω x)) := by
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h hb))
  · intro h l hl
    obtain ⟨z, hz⟩ := hΩ.classical L hL.1
    have hLY := le_centralizingLayer hL
    obtain ⟨e⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
    have hK : Nonempty (↥(L.subgroupOf (locLayer Ω x)) ≃* SL(2, ZMod 3)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e⟩
    have hbot := commutes_of_equiv_sl2Three hP1 hO3 hK (L := Subgroup.zpowers y)
      (fun a ha b hb => by
        rw [← QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore ↥(locLayer Ω x))]
        change locMk Ω x ⁅a, b⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        have h1 : locMk Ω x a * locMk Ω x y = locMk Ω x y * locMk Ω x a :=
          Subgroup.mem_centralizer_singleton_iff.mp (h ⟨a, ha, rfl⟩)
        rw [map_zpow]
        exact (Commute.zpow_right (show Commute (locMk Ω x a) (locMk Ω x y) from h1) m))
    have h2 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      (Subgroup.mem_subgroupOf.mpr hl : (⟨l, hLY hl⟩ : ↥(locLayer Ω x)) ∈
        L.subgroupOf (locLayer Ω x))
    have h3 := Subgroup.mem_centralizer_iff.mp h2 y (Subgroup.mem_zpowers y)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val h3).symm

end CFSG.ClassicalInvolution.Q3.Q3W
