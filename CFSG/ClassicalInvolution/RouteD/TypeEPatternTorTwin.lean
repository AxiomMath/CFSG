module

public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclChain

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem exists_distinguisher (c : ETCtx p f .POmegaPlus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeT p f 1 .POmegaPlus 6 Ω z)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {a d : Subgroup G} (ha : a ∈ Ω)
    (hd : d ∈ Ω) (hKa : Commutes K a) (hβa : Commutes β a) (hKd : Commutes K d)
    (hβd : Commutes β d) (had : Commutes a d) :
    ∃ N ∈ centralizingMembers Ω {z}, Commutes d N ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W a N := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨xd, hxd⟩ := c.hΩ.classical d hd
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hshape hd hxd
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two
      ht.orderOf_eq_two
  have hnormK : conjSub t K = K := Gaps.conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hKx : K ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes c.hK hxd.mem hKd
  have hβx : β ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes hβ hxd.mem hβd
  have hax : a ∈ centralizingMembers Ω {xd} := mem_centralizingMembers_of_commutes ha hxd.mem had
  have hKL := IsLayerMember.of_commutes_self cx hKx hKd
  have hβL := IsLayerMember.of_commutes_self cx hβx hβd
  have haL := IsLayerMember.of_commutes_self cx hax had
  obtain ⟨RK, hRK, hKR⟩ := hKL.exists_fund
  obtain ⟨Rβ, hRβ, hβR⟩ := hβL.exists_fund
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  have hadj : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) RK Rβ :=
    cx.modelAdj_of_adj hKx hβx hRK hRβ hKR hβR c.hz ht hKne hnKβ hzt hnormK
  obtain ⟨RN, hRN, ⟨W₂, hW₂⟩, hcN⟩ := Gaps.adjPerp_plus (p := p) (f := f) (m := 6) c.hp2
    (by norm_num) c.hq RK hRK Rβ hRβ hadj Ra hRa
    ((cx.commutes_iff_fund hax hKx hRa haR hKR).mp (commutes_symm hKa))
    ((cx.commutes_iff_fund hax hβx hRa haR hβR).mp (commutes_symm hβa))
  obtain ⟨N, hNx, hNd, hNR⟩ := cx.exists_member_of_fund hRN
  have hNK : Commutes N K := (cx.commutes_iff_fund hNx hKx hRN hNR hKR).mpr hcN
  exact ⟨N, mem_centralizingMembers_of_commutes hNx.1 c.hz.mem hNK,
    cx.commutes_K_of_ne hNx hNd, cx.stdPair_of_fund hax hNx hW₂ haR hNR⟩

end CFSG.ClassicalInvolution.RouteD.ETCtx
