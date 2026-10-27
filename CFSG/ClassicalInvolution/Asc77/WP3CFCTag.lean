module

public import CFSG.ClassicalInvolution.Asc77.WP3CFCPart
public import CFSG.ClassicalInvolution.Asc77.WP3SCVTag
public import CFSG.ClassicalInvolution.Asc77.WP3SCVOrthC
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
import CFSG.ClassicalInvolution.Asc77.AscIH8Std

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CFC

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.SCV
open scoped MatrixGroups commutatorElement

section Tag

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem moved_commutes (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4)
    {R_K R_J : Subgroup (compModel D j).K} {r_K r_J : (compModel D j).K}
    (hR_K : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hR_J : R_J ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J))
    (hrK : r_K ∈ R_K) (hrKc : ∀ s ∈ R_K, r_K * s = s * r_K) (hrK1 : r_K ≠ 1)
    (hrJ : r_J ∈ R_J) (hrJc : ∀ s ∈ R_J, r_J * s = s * r_J) (hrJ1 : r_J ≠ 1)
    (hrKb : secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j r_K =
      oddQuotMk (z * t) ⟨z, zt_z_mem hs⟩)
    (hcen : r_K * r_J ∈ Subgroup.center (compModel D j).K) (hKJ : R_K ≠ R_J) :
    Commutes R_K R_J := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hzC := zt_z_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hker : (V.psi j).ker ≤ Subgroup.center (compModel D j).K := V.psi_ker j
  have hq5 : 5 ≤ p ^ D.exp j := by rw [V.exp_eq j hD4]; exact hq
  have hperf : ∀ S ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, S ≤ ⁅S, S⁆ :=
    fun S hS => (V.fund_perfect j hD4 hS).ge
  have hord : ∀ {R : Subgroup (compModel D j).K} {r : (compModel D j).K},
      R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D → r ∈ R → (∀ s ∈ R, r * s = s * r) →
      r ≠ 1 → orderOf r = 2 := by
    intro R r hR hr hrc hr1
    exact orderOf_eq_prime (by rw [pow_two]; exact fund_central_sq D j hp hG2 hD4 hR hr hrc) hr1
  have hlong : ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      R ∈ ModelFacts.longestFundamental (compModel D j).D := fun R hR =>
    ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR
  have hcommr : r_K * r_J = r_J * r_K := by
    have h1 : (r_K * r_J) * r_K = r_K * (r_K * r_J) := (Subgroup.mem_center_iff.mp hcen r_K).symm
    have h2 : r_K * (r_J * r_K) = r_K * (r_K * r_J) := by rw [← mul_assoc]; exact h1
    exact (mul_left_cancel h2).symm
  have hdich := ih8_stdDichotomy (D.isFundTag j) hG2 hD4 (D.admissible j)
  have hmapc := hdich.map_of_commute hp hq5 (V.psi j) hker (hlong R_K hR_K) (hlong R_J hR_J)
    hrK hrJ (hord hR_K hrK hrKc hrK1) (hord hR_J hrJ hrJc hrJ1) hcommr
  have hz2 : z * z = 1 := hfd.hz.sq
  have hz1 : oddQuotMk (z * t) ⟨z, hzC⟩ ≠ 1 := by
    intro h
    have h1 : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) = 1 :=
      eq_one_of_oddQuotMk_eq_one (Subtype.ext hz2) h
    exact hfd.hz.ne_one (congrArg Subtype.val h1)
  have hzR : oddQuotMk (z * t) ⟨z, hzC⟩ ∈ R_K.map (V.psi j) := ⟨r_K, hrK, hrKb⟩
  have hquasiJ : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) J)) := by
    have h1 : R_J.map (V.psi j) = modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [← h1]
    exact isQuasisimple_map_of_ker_le_center _ hker
      (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hD4) R_J hR_J)
  have hzJ := oddQuotMk_centralizes_modOdd_exactCore hJcl (zt_hc2 hs) (zt_tq_J hs)
    (hfd.tq_z_J hp hq hΩ) hzC hquasiJ
  have hcentJ : ∀ y ∈ R_J.map (V.psi j),
      oddQuotMk (z * t) ⟨z, hzC⟩ * y = y * oddQuotMk (z * t) ⟨z, hzC⟩ := by
    intro y hy
    have h1 : R_J.map (V.psi j) = modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [h1] at hy
    exact hzJ y hy
  have hF : 4 ≤ Nat.card (GaloisField p (D.exp j)) := by
    rw [GaloisField.card p (D.exp j) (by have := (D.admissible j).2.1; omega)]
    omega
  rcases hmapc with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exact absurd (ih8_eq_of_map_eq (V.psi j) hker (hperf R_K hR_K) (hperf R_J hR_J) h) hKJ
  · exact ih8_commutes_of_commutes_map (V.psi j) hker (hperf R_K hR_K) h
  · exact absurd (CFSG.ClassicalInvolution.Asc77.LinearBlockStandardPair.eq_one_of_centralizes hF hW
      hzR hcentJ) hz1
  · exact absurd (CFSG.ClassicalInvolution.Asc77.UnitaryBlockStandardPair.eq_one_of_centralizes
      (CFSG.LieType.Universal.card_galoisField_two_mul p (D.exp j) (D.admissible j).2.1) hq5 hW hzR
      hcentJ) hz1

theorem z'_data (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    (hmov : MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) (z * t)
      (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range)
    (hj : D.tag j ≠ .trialityD4) {R_K : Subgroup (compModel D j).K}
    (hR_K : R_K ∈ fundamentalSubgroups (D.tag j) (compModel D j).D)
    (hmodK : R_K.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) K)) :
    oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ ∈ Subgroup.normalizer
        ((secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j).range :
          Set (OddQuot (z * t))) ∧
      oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ * oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ = 1 ∧
      ∀ s ∈ R_K, oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ *
          secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s =
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s *
          oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  set B : Subgroup G := Subgroup.closure ({z, t, z'} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have htB : t ∈ B := Subgroup.subset_closure (by simp)
  have hz'B : z' ∈ B := Subgroup.subset_closure (by simp)
  have hztB : z * t ∈ B := Subgroup.mul_mem _ hzB htB
  have hBel : IsElemAbelian 2 B := hfd.isElemAbelian hp hΩ
  have hne1 : z * t ≠ 1 := zt_ne_one hs
  have hz'C := zt_z'_mem hs
  have hKcl : IsClassicalMember p f K z := isClassicalMember_of_twin hΩ hfd.mem hfd.hz
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hne1
  let V : VertexCtx p f Ω (z * t) := ztVertex hs D
  have hQ : CFSG.IsComponent (V.psi j).range := V.isComponent_range j
  have hmov' : MovedByAll B (z * t) (V.psi j).range := hmov
  have hBN := FrameVertex.modOdd_le_normalizer hp hq hΩ.conjInvariant hΩ.classical hs.below
    (zt_hc2 hs) hnc hBel hztB hne1 hzB hfd.hz.ne_one (zt_z_ne hs) (zt_memK hs) hKcl hQ hmov'
  refine ⟨hBN (oddQuotMk_mem_modOdd hz'B hz'C), ?_, ?_⟩
  · rw [← map_mul]
    have : (⟨z', hz'C⟩ : ↥(Subgroup.centralizer ({z * t} : Set G))) * ⟨z', hz'C⟩ = 1 :=
      Subtype.ext hfd.hz'.sq
    rw [this, map_one]
  · intro s hs'
    have hquasiK : CFSG.Open.IsQuasisimple ↥(modOdd (z * t) (exactCore (z * t) K)) := by
      have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
      rw [← h1]
      exact isQuasisimple_map_of_ker_le_center _ (V.psi_ker j)
        (fundQuasisimple_core hp (D.isFundTag j) (D.admissible j) (V.four_le j hj) R_K hR_K)
    have hz'K := oddQuotMk_centralizes_modOdd_exactCore hKcl (zt_hc2 hs) (zt_tq_K hs)
      (hfd.tq_z' hp hq hΩ) hz'C hquasiK
    apply hz'K
    have h1 : R_K.map (V.psi j) = modOdd (z * t) (exactCore (z * t) K) := hmodK
    rw [← h1]
    exact ⟨s, hs', rfl⟩

theorem false_of_z'_centralizes_J (hs : ChainFrameCore p f Ω K J K' z t z')
    (D : LocalLieSystemAt p f (exactFamily Ω (z * t)) (z * t)) (j : Fin D.card)
    {R_J : Subgroup (compModel D j).K}
    (hmodJ : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
      modOdd (z * t) (exactCore (z * t) J))
    (hv : ∀ s ∈ R_J, oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩ *
          secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s =
        secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j s *
          oddQuotMk (z * t) ⟨z', zt_z'_mem hs⟩) : False := by
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hfd := hs.frame
  have hJcl : IsClassicalMember p f J t := isClassicalMember_of_twin hΩ hfd.memJ hfd.ht
  have hz'N : z' ∈ Subgroup.normalizer (J : Set G) :=
    mem_normalizer_of_commutes_involution hΩ.conjInvariant hs.noTwins hfd.memJ hfd.ht
      hfd.htz'.symm
  have hz'J : z' ∈ trivialOnQuot J := by
    refine mem_trivialOnQuot_of_centralizes_modOdd hJcl (zt_hc2 hs) (zt_tq_J hs) (zt_z'_mem hs)
      hz'N ?_
    intro y hy
    have h1 : R_J.map (secComponentHom (normalizesLayer_exactFamily hs.hyp.conjInvariant) D j) =
        modOdd (z * t) (exactCore (z * t) J) := hmodJ
    rw [← h1] at hy
    obtain ⟨s, hs', rfl⟩ := hy
    exact hv s hs'
  have hKJne : J ≠ K' := by
    intro h1
    apply hfd.z'_ne_t hΩ
    have h2 : IsUniqueInvolution J z' := by rw [h1]; exact hfd.hz'
    exact h2.eq hfd.ht
  have hJK' : J ∈ omegaNbr Ω K' :=
    mem_omegaNbr_of_trivialOnQuot hp hq hΩ hfd.memK' hfd.hz' hfd.memJ hKJne hz'J
  exact hfd.hperp (Set.mem_insert_of_mem _
    (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hfd.memK' hfd.memJ hJK'))

theorem false_of_other_tag_at
    (hThird : ∀ N ∈ Ω, N ≠ K → N ≠ J → z ∈ trivialOnQuot N → t ∈ trivialOnQuot N →
      IsUniqueInvolution N (z * t))
    (hSmall : SmallSigmaFacts p)
    (hs : ChainFrameCore p f Ω K J K' z t z')
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

theorem tagZT_at (hs : ChainFrameCore p f Ω K J K' z t z')
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

end CFSG.ClassicalInvolution.Asc77.CFC
