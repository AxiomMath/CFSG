module

public import CFSG.ClassicalInvolution.Q3.Q3TY7
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3TCCtx

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def involutionMembers3 (Ω : Set (Subgroup G)) (x : G) : Set (Subgroup G) :=
  {N | N ∈ Ω ∧ IsClassicalMember3 N x}

theorem ncard_involutionMembers3_le (hMFZ : Gaps.FundNoncentral 3) {ι : Type} [Finite ι]
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) :
    (involutionMembers3 Ω x).Finite ∧ (involutionMembers3 Ω x).ncard ≤ Nat.card ι := by
  have hmem : ∀ N ∈ involutionMembers3 Ω x, N ∈ centralizingMembers Ω {x} := fun N hN =>
    ⟨hN.1, isSubnormal_le hN.2.subnormal⟩
  let g : ↥(involutionMembers3 Ω x) → ι := fun N =>
    Classical.choose (locImg_eq_range_of_involution3 (D := D) hMFZ (hmem N.1 N.2) N.2.2)
  have hg : ∀ N : ↥(involutionMembers3 Ω x), locImg Ω x N.1 = (D.hom (g N)).range := fun N =>
    (Classical.choose_spec
      (locImg_eq_range_of_involution3 (D := D) hMFZ (hmem N.1 N.2) N.2.2)).2
  have hinj : Function.Injective g := by
    intro N N' h
    apply Subtype.ext
    exact locImg_injOn3 hΩ hex hP1 hO3 (hmem N.1 N.2) (hmem N'.1 N'.2)
      ((hg N).trans (h ▸ (hg N').symm))
  have : Finite ↥(involutionMembers3 Ω x) := Finite.of_injective g hinj
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective g hinj

theorem perfect_le_normalizer_of_involution3 (hMFZ : Gaps.FundNoncentral 3) {ι : Type} [Finite ι]
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x))
    (hD : Nat.card ι ≤ 4) {S : Subgroup G} (hS : S ≤ Subgroup.centralizer ({x} : Set G))
    (hSp : ⁅S, S⁆ = S) {β : Subgroup G} (hβ : β ∈ Ω) (hxβ : IsClassicalMember3 β x) :
    S ≤ Subgroup.normalizer (β : Set G) := by
  have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hSp
  obtain ⟨hfin, hcard⟩ := ncard_involutionMembers3_le hMFZ hΩ hex hP1 hO3 D
  refine RouteD.Gaps.perfect_le_normalizer_of_card_le_four S (involutionMembers3 Ω x) hfin
    (hcard.trans hD) ?_ (⟨hβ, hxβ⟩ : β ∈ involutionMembers3 Ω x)
  intro g hg N hN
  have hgx : g * x * g⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hS hg)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine ⟨hΩ.conjInvariant g N hN.1, ?_⟩
  have := hN.2.conj g
  rwa [hgx] at this

end CFSG.ClassicalInvolution.Q3.Q3TY

namespace CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag}
  {nY : ℕ} {K : Subgroup G}

theorem commutes_partner_of_centralizes3 (c : TCtx3 tY nY Ω K z)
    (hMFZ : Gaps.FundNoncentral 3) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNt : N ≤ Subgroup.centralizer ({t} : Set G))
    (hNK : Commutes K N) : Commutes β N := by
  obtain ⟨W, hW⟩ := hKβ
  have hnK : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  exact ((commutes_iff_le_centralizer3 hMFZ c.hΩ c.hex hP1t hO3t Dt hβ ht hN.1 hNK.symm
    hnK).mpr hNt).symm

theorem commutes_partner_of_perfect3 (c : TCtx3 tY nY Ω K z) (hMFZ : Gaps.FundNoncentral 3)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type} [Finite ι]
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) (hD : Nat.card ι ≤ 4)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t) {S : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) : Commutes β S := by
  obtain ⟨h, hh⟩ := hsingle β hβ
  have ht_eq : t = h * z * h⁻¹ := involution_unique3 ht (hh ▸ c.hz.conj h)
  have hP1t : LocalOddCentral Ω {t} := by
    rw [ht_eq]
    exact Gaps.localOddCentral_conj c.hΩ.conjInvariant h z c.hP1
  have hO3t : LocalOddThreeFree3 Ω t := by
    rw [ht_eq]
    exact localOddThreeFree3_conj c.hΩ.conjInvariant h z c.hO3
  obtain ⟨Dt⟩ := exists_lieSystemData_conj3 c.hΩ.conjInvariant h z D
  rw [← ht_eq] at Dt
  have hnorm := Q3TY.perfect_le_normalizer_of_involution3 hMFZ c.hΩ c.hex hP1t hO3t Dt hD hSt hS
    hβ ht
  obtain ⟨e⟩ := ht.nonempty_equiv_sl2 (c.hex β hβ)
  have hcent := Q3TY.perfect_le_centralizer_of_normalizes_sl2 e hS hnorm
  intro b hb s hs
  exact Subgroup.mem_centralizer_iff.mp (hcent hs) b hb

end CFSG.ClassicalInvolution.Q3.Q3TC.TCtx3
