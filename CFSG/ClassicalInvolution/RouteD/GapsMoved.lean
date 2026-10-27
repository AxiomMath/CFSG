module

public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import CFSG.ClassicalInvolution.RouteD.GapsPatternD

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember LocalOddCentral ExactMembers centralizingMembers ConjInvariant LieSystemData
  centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

section Moved

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem exists_moved_layer_member_gen
    (hF : OrthFacts (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D)
      (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (hfix : HasFixedMember Ω K β z) :
    ∃ N ∈ centralizingMembers Ω {z}, ¬ locImg Ω z N ≤ c.d.Q₁ ∧ Commutes K N ∧
      ¬ Commutes β N := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨M, hMΩ, hKM, hβM, -⟩ := hfix
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨xM, hxM⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hxM
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hKx : K ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes c.hK hxM.mem hKM
  have hβx : β ∈ centralizingMembers Ω {xM} :=
    mem_centralizingMembers_of_commutes hβ hxM.mem hβM
  have hKL := IsLayerMember.of_not_commutes cx hKx hβx hKne hnKβ
  have hβL := IsLayerMember.of_not_commutes cx hβx hKx hKne.symm
    (fun h => hnKβ (commutes_symm h))
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadj : ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) RK Rβ :=
    modelAdj_of_adj cx hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 hKx hβx hW
  rw [hKR, hβR] at hW'
  have hlinR := hF.lift cx.d.ψ cx.d.ker_le RK hRK Rβ hRβ ⟨W', hW'⟩
  obtain ⟨S₁, hS₁, S₂, hS₂, hS12, hc₁, hc₂, hn₁, hn₂⟩ := hF.perp2 RK hRK Rβ hRβ hadj hlinR
  obtain ⟨N₁, hN₁, -, -, hN₁R⟩ := cx.exists_member_of_fund hS₁
  obtain ⟨N₂, hN₂, -, -, hN₂R⟩ := cx.exists_member_of_fund hS₂
  have hN12 : N₁ ≠ N₂ := fun h => hS12 (eq_of_map_eq_of_perfect cx.d.ψ cx.d.ker_le
    (cx.hY.perfR S₁ hS₁) (cx.hY.perfR S₂ hS₂) (by rw [← hN₁R, ← hN₂R, h]))
  have hKN₁ : Commutes K N₁ := (cx.commutes_iff_fund hKx hN₁ hRK hKR hN₁R).mpr hc₁
  have hKN₂ : Commutes K N₂ := (cx.commutes_iff_fund hKx hN₂ hRK hKR hN₂R).mpr hc₂
  have hβN₁ : ¬ Commutes β N₁ := fun h =>
    hn₁ ((cx.commutes_iff_fund hβx hN₁ hRβ hβR hN₁R).mp h)
  have hβN₂ : ¬ Commutes β N₂ := fun h =>
    hn₂ ((cx.commutes_iff_fund hβx hN₂ hRβ hβR hN₂R).mp h)
  have hz₁ : N₁ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (commutes_symm hKN₁)
  have hz₂ : N₂ ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 c.hz.mem (commutes_symm hKN₂)
  by_cases h₁ : locImg Ω z N₁ ≤ c.d.Q₁
  · by_cases h₂ : locImg Ω z N₂ ≤ c.d.Q₁
    · exact absurd (c.eq_of_locImg_le_Q₁ hz₁ hz₂ h₁ h₂) hN12
    · exact ⟨N₂, hz₂, h₂, hKN₂, hβN₂⟩
  · exact ⟨N₁, hz₁, h₁, hKN₁, hβN₁⟩

theorem commutes_partner_of_centralizes_gen (hMFZ : FundNoncentral p)
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {z}) (hNt : N ≤ Subgroup.centralizer ({t} : Set G))
    (hNK : Commutes K N) : Commutes β N := by
  have : NeZero f := ⟨c.hf⟩
  have hS3 : StandardPairAutAbelian (GaloisField p f) :=
    standardPairAutAbelian_galoisField c.hp2 c.hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  obtain ⟨z', hz'⟩ := c.hΩ.classical N hN.1
  exact commutes_partner_of_perfect_conj c.hp2 c.hq hMFZ hS3 c.hΩ hsingle c.hz hD4 c.hP1 hβ ht hKβ
    (commutator_eq_of_isClassicalMember hz') hNt (fun y hy x hx => hNK x hx y hy)

end Moved

end CFSG.ClassicalInvolution.RouteD.Gaps
