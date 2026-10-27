module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N0
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW3

public section

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

section W3

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {π : OddQuot K →* A7}
  {zE : OddQuot K} {b : G} (hb : b ∈ Subgroup.normalizer (K : Set G))
  (cov : IsDoubleCoverA7 π zE)

omit cov in
theorem fixImage_eq_fixedIn (hb2 : b * b = 1) :
    fixImage K b = fixedIn (oddQuotAut K (conjOn K b hb)) ⊤ := by
  ext y
  rw [mem_fixImage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (a7FixHom K hb ⟨(x : G), x.2, hx⟩).2
  · intro hy
    obtain ⟨c, hc⟩ := a7FixHom_surjective hb hb2 ⟨y, hy⟩
    refine ⟨Subgroup.inclusion inf_le_left c, c.2.2, ?_⟩
    have := congrArg Subtype.val hc
    rw [a7FixHom_coe] at this
    exact this


include hb

theorem fixDiv5_iff_cycleType (hb2 : b * b = 1) (hε : epsG cov b = -1) :
    FixDiv5 K b ↔ (nuG cov b).cycleType = {2} := by
  have hα := a7_alpha_sq hb hb2
  have hne := a7_alpha_ne_one hb cov hε
  have e : nuG cov b = cov.autPerm (oddQuotAut K (conjOn K b hb)) := nuG_eq_autPerm hb cov
  unfold FixDiv5
  rw [fixImage_eq_fixedIn hb hb2]
  rcases a7_cycleType hb cov hb2 hε with hc | hc
  · have h120 := card_fixedIn_top_five cov (oddQuotAut K (conjOn K b hb)) hα hne
      (by rw [← e]; exact hc)
    rw [h120]
    exact ⟨fun _ => hc, fun _ => by norm_num⟩
  · have h24 := card_fixedIn_top_four cov (oddQuotAut K (conjOn K b hb)) hα hne
      (by rw [← e]; exact hc)
    rw [h24]
    refine ⟨fun h => absurd h (by norm_num), fun h => ?_⟩
    rw [hc] at h
    exact absurd h (by decide)

theorem W3_five [Fact (Nat.Prime 5)] (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (h5 : FixDiv5 K b) :
    Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
        SL(2, GaloisField 5 1)) :=
  nonempty_perfectResidual_quotEquiv_sl2_five hb cov hb2 hε
    ((fixDiv5_iff_cycleType hb cov hb2 hε).mp h5)

theorem W3_five_mem [Fact (Nat.Prime 5)] (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (h5 : FixDiv5 K b) {x : G} (hxK : x ∈ K) (hxb : x ∈ Subgroup.centralizer ({b} : Set G))
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) :=
  mem_perfectResidualOf_of_isPGroup_five hb cov hb2 hε
    ((fixDiv5_iff_cycleType hb cov hb2 hε).mp h5) hxK hxb hx2

theorem W3_three (hb2 : b * b = 1) (hε : epsG cov b = -1) (h5 : ¬ FixDiv5 K b) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        SL(2, GaloisField 3 1)) := by
  have hc : (nuG cov b).cycleType = {2, 2, 2} := by
    rcases a7_cycleType hb cov hb2 hε with hc | hc
    · exact absurd ((fixDiv5_iff_cycleType hb cov hb2 hε).mpr hc) h5
    · exact hc
  exact nonempty_centralizer_quotEquiv_sl2_three hb cov hb2 hε hc

end W3

end CFSG.ClassicalInvolution.Hat2A7S
