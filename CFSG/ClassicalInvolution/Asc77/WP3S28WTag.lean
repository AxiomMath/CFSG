module

public import CFSG.ClassicalInvolution.Asc77.WP3SCVTag
public import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthC
import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
public import CFSG.ClassicalInvolution.Asc77.WP3SCVPart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28W

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.SCV
open scoped MatrixGroups commutatorElement

section Third

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

@[expose] def ThirdZTModAt (Ω : Set (Subgroup G)) (K J : Subgroup G) (z t : G) : Prop :=
  ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
    ∀ w : G, IsUniqueInvolution N w →
      z * t * w ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G))

theorem thirdZT_of_modAt (hs : ChainFrameSetting p f Ω K J K' z t z') (h : ThirdZTModAt Ω K J z t) :
    ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t) := by
  intro N hN hNK hNJ hzN htN
  obtain ⟨w, hw⟩ := hs.hyp.classical N hN
  have hwU : IsUniqueInvolution N w :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hs.odd hs.five hw
  have hmod := h N hN hNK hNJ hzN htN w hwU
  have hzw : z * w = w * z := by
    have := conj_eq_of_isUniqueInvolution hwU hzN.1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have htw : t * w = w * t := by
    have := conj_eq_of_isUniqueInvolution hwU htN.1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hzt : z * t = t * z := hs.frame.comm_zt hs.odd hs.hyp
  have hw2 : w * w = 1 := hwU.sq
  have hztw : (z * t) * w = w * (z * t) := by
    calc (z * t) * w = z * (t * w) := by rw [mul_assoc]
      _ = z * (w * t) := by rw [htw]
      _ = (z * w) * t := by rw [mul_assoc]
      _ = (w * z) * t := by rw [hzw]
      _ = w * (z * t) := by rw [mul_assoc]
  have hg2 : (z * t * w) * (z * t * w) = 1 := by
    calc (z * t * w) * (z * t * w) = (z * t) * (w * (z * t)) * w := by group
      _ = (z * t) * ((z * t) * w) * w := by rw [hztw]
      _ = ((z * t) * (z * t)) * (w * w) := by group
      _ = 1 := by rw [zt_sq hs, hw2, one_mul]
  have hg := eq_one_of_sq_eq_one_of_mem_oddCoreIn hmod hg2
  have hw' : w = z * t := by
    have h1 : w = (z * t)⁻¹ := eq_inv_of_mul_eq_one_right hg
    rw [h1]
    exact inv_eq_of_mul_eq_one_right (zt_sq hs)
  rw [← hw']
  exact hwU

end Third

section Tag

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem false_of_other_tag_at
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t))
    (hSmall : SmallSigmaFacts p)
    (hs : ChainFrameSetting p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (hPSL : D.tag j ≠ .PSL) (hPSU : D.tag j ≠ .PSU) : False := by
  have hp := hs.odd
  have hq := hs.five
  by_cases hex : D.tag j = .G2 ∨ D.tag j = .trialityD4
  · exact false_of_exotic hs D j hmov hex
  push Not at hex
  obtain ⟨hG2, hD4⟩ := hex
  obtain ⟨R_K, R_J, r_K, r_J, hRK, hRJ, hmodK, hmodJ, hrK, hrKc, hrK1, hrJ, hrJc, hrJ1, hrKb,
    hrJb, hcen, hKJ⟩ := moved_data hs D j hmov hD4
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hb := partner_bound hs hThird D j hG2 hD4 hRK hRJ hmodK hmodJ
  have hq5 : 5 ≤ p ^ D.exp j := by rw [V.exp_eq j hD4]; exact hq
  have hClosed : ClosedFamily (fundamentalSubgroups (D.tag j) (compModel D j).D) := by
    refine ⟨fun g R hR => ?_, fun R hR => ?_⟩
    · obtain ⟨g', γ, hγ, rfl⟩ := hR
      exact ⟨g * g', γ, hγ, (conjSub_mul g g' _).symm⟩
    · exact fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hD4) R hR
  have hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D :=
    ModelFacts.fundamentalSingleClass (D.tag j) (D.rank j) p (D.exp j) Fact.out (D.isFundTag j)
      (D.admissible j) hG2 hD4
  have hb' : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      ∃ a b : Subgroup (compModel D j).K, ∀ S ∈ Partners
        (fundamentalSubgroups (D.tag j) (compModel D j).D) R, S = a ∨ S = b := by
    intro R hR
    obtain ⟨a, b, hab⟩ := hb
    obtain ⟨g, hg⟩ := hsingle R_K hRK R hR
    exact ⟨conjSub g a, conjSub g b, hg ▸ partners_cover_conj hClosed hab g⟩
  have hcomm := moved_commutes hs D j hG2 hD4 hRK hRJ hmodJ hrK hrKc hrK1 hrJ hrJc hrJ1 hrKb hcen
    hKJ
  rcases ih8_tag_cases hp hq5 (D.isFundTag j) (D.admissible j) hG2 hD4 with hconn | hsm
  · have hKq : CFSG.Open.IsQuasisimple (compModel D j).K :=
      (ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag j) (D.admissible j)).1
    have htop : R_K ≠ ⊤ := by
      intro htop
      obtain ⟨S, hS, -, hcS⟩ := ih8_exists_edge_of_connected hp hq5 (D.isFundTag j)
        (D.admissible j) (fun h => hPSL h.1) hconn hRK
      exact hClosed.nonab hS fun x hx y hy => hcS x (by rw [htop]; exact Subgroup.mem_top x) y hy
    exact false_of_connected hClosed hb' hconn hRK hKq htop
  · have hdata := z'_data hs D j hmov hD4 hRK hmodK
    have key : SmallSigma p (D.tag j) (D.rank j) (D.exp j) → False := fun hsig => by
      have hvN := hdata.1
      have hperfJ : ⁅R_J, R_J⁆ = R_J := V.fund_perfect j hD4 hRJ
      set v : OddQuot (z * t) := oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ with hvdef
      have hv'2 : toInducedAutOn
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range
            ⟨v, hvN⟩ *
          toInducedAutOn
            (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range
            ⟨v, hvN⟩ = 1 := by
        rw [← map_mul]
        have : (⟨v, hvN⟩ : ↥(Subgroup.normalizer
            ((secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range :
              Set (OddQuot (z * t))))) * ⟨v, hvN⟩ = 1 := Subtype.ext hdata.2.1
        rw [this, map_one]
      have hX := hsig hp hq5 (D.admissible j)
        (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j)
        (V.psi_ker j) hRK hRJ hKJ hcomm hrK (fund_central_sq D j hp hG2 hD4 hRK hrK hrKc) hrK1 hrJ
        (fund_central_sq D j hp hG2 hD4 hRJ hrJ hrJc) hrJ1 hcen _ hv'2
        (fun r hr => toInduced_commute_innerHom _ hvN (hdata.2.2 r hr))
      exact false_of_z'_centralizes_J hs D j hmodJ
        (commute_of_toInduced_commute _ hperfJ hvN hX)
    rcases hsm with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, hn⟩ | ⟨h, hn⟩ | ⟨h, hn⟩ | ⟨h, hn⟩
    · exact hPSL h
    · exact hPSU h
    · exact key (by rw [h, hn]; exact (hSmall (D.exp j)).1)
    · exact key (by rw [h, hn]; exact (hSmall (D.exp j)).2.1)
    · exact false_of_d4 h hn hp hq5 (D.admissible j) hRK (hb' R_K hRK)
    · exact key (by rw [h, hn]; exact (hSmall (D.exp j)).2.2)

theorem tagZT_at (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t)) :
    ∃ D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t), ∀ j : Fin D.card,
      MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
          (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range →
        D.tag j = .PSL ∨ D.tag j = .PSU := by
  have hΩ := hs.hyp
  have hne : (tqMembers Ω (z * t)).Nonempty := ⟨K, zt_memK hs⟩
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian (zt_ne_one hs)
  obtain ⟨D⟩ := lieSystemAt_exactFamily hΩ.conjInvariant hΩ.classical (zt_hc2 hs) hs.below hnc hne
  refine ⟨D, fun j hmov => ?_⟩
  by_contra hno
  push Not at hno
  exact false_of_other_tag_at hThird smallSigmaFacts_proved hs D j hmov hno.1 hno.2

end Tag

end CFSG.ClassicalInvolution.Asc77.S28W
