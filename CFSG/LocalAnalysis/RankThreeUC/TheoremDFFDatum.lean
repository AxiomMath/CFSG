module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.Quasithin.Background.B2FactorizationBridge
import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
import CFSG.LocalAnalysis.RankThreeUC.TIModule
import CFSG.LocalAnalysis.RankThreeUC.TheoremDSolvableQuotient
import CFSG.Quasithin.Background.B2FactorizationR2
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem isElemAbelian_of_le' {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E)
    (hFE : F ≤ E) : IsElemAbelian p F := CFSG.Open.IsElemAbelian.mono hE hFE

private theorem exists_card_eq_pow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {A : Subgroup X} (hA : IsElemAbelian p A) : ∃ k, Nat.card A = p ^ k :=
  (show IsPGroup p A from
    fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 x x.2)⟩).exists_card_eq

theorem pRank_le_add_pRank_autI {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : M ≤ normalizer (V : Set G)) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (M ⊓ centralizer (V : Set G)) +
      CFSG.Open.pRank p (CFSG.Quasithin.autI hV M) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  have hE' := hE.1
  let f : E →* MulAut (CFSG.Quasithin.IntMod V hV) :=
    (CFSG.Quasithin.convI hV).comp (Subgroup.inclusion (hEM.trans hMV))
  have hf := card_ker_mul_card_range f
  have hker : f.ker.map E.subtype = E ⊓ centralizer (V : Set G) := by
    ext x
    simp only [mem_map, MonoidHom.mem_ker, coe_subtype, mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (CFSG.Quasithin.convI_eq_one_iff hV ⟨y, hEM.trans hMV y.2⟩).1 hy⟩
    · rintro ⟨hxE, hxC⟩
      exact ⟨⟨x, hxE⟩, (CFSG.Quasithin.convI_eq_one_iff hV
        ⟨x, hEM.trans hMV hxE⟩).2 hxC, rfl⟩
  have hkerc : Nat.card f.ker = Nat.card (E ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← hker]
    exact (Subgroup.card_map_of_injective E.subtype_injective).symm
  have hrange : f.range ≤ CFSG.Quasithin.autI hV M := by
    rintro _ ⟨x, rfl⟩
    exact CFSG.Quasithin.convI_mem_autI hV (hEM x.2) (hMV (hEM x.2))
  have hrangeE : IsElemAbelian p f.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      change (a : MulAut (CFSG.Quasithin.IntMod V hV)) * (b : MulAut _) =
        (b : MulAut _) * (a : MulAut _)
      rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm' x y]
    · obtain ⟨x, rfl⟩ := ha
      have hxp : x ^ p = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ x.2)
      rw [← map_pow, hxp, map_one]
  have hEC : IsElemAbelian p (E ⊓ centralizer (V : Set G) : Subgroup G) :=
    isElemAbelian_of_le' hE inf_le_left
  obtain ⟨a', ha'⟩ := exists_card_eq_pow hEC
  obtain ⟨b', hb'⟩ := exists_card_eq_pow hrangeE
  have h1 : a' ≤ CFSG.Open.pRank p (M ⊓ centralizer (V : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (inf_le_inf_right _ hEM) hEC ha'
  have h2 : b' ≤ CFSG.Open.pRank p (CFSG.Quasithin.autI hV M) :=
    CFSG.SectionRank.le_pRank hp.one_lt hrange hrangeE hb'
  have h3 : p ^ (a' + b') = p ^ CFSG.Open.pRank p M := by
    rw [pow_add, ← ha', ← hb', ← hkerc, hf, hcard]
  have h4 := Nat.pow_right_injective hp.two_le h3
  omega

structure FFDatum {G : Type} [Group G] [Finite G] (p : ℕ) (M T : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  charTwo : CFSG.QuasithinUnique.CharTwo M
  elemAbelian : IsElemAbelian 2 (uCore M T)
  notCentral : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G)
  ffModule : CFSG.Quasithin.IsFFModule (CFSG.Quasithin.autI elemAbelian M)
  twoReduced : CFSG.Quasithin.IsTwoReducedIn M (uCore M T)
  notTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T)
  rank_M : CFSG.Open.pRank p M = 3
  rank_ker : CFSG.Open.pRank p (M ⊓ centralizer (uCore M T : Set G)) ≤ 1
  rank_aut : 2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.autOn M (uCore M T))
  good_cT : 2 ≤ CFSG.Open.pRank p
    (M ⊓ normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G))
  strong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M

omit [Finite G] in
theorem omegaOneCenterIn_characteristic (T : Subgroup G) :
    ((CFSG.RankThree.PartOne.omegaOneCenterIn T).subgroupOf T).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  obtain ⟨-, hc, hsq⟩ := CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mp
    (Subgroup.mem_subgroupOf.mp hx)
  refine Subgroup.mem_subgroupOf.mpr (CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.mpr
    ⟨(φ x).2, fun k hk => ?_, ?_⟩)
  · have h := hc (φ.symm ⟨k, hk⟩ : T) (φ.symm ⟨k, hk⟩).2
    have h' : (⟨k, hk⟩ : T) * φ x = φ x * ⟨k, hk⟩ := by
      have := congrArg φ (Subtype.ext h : (φ.symm ⟨k, hk⟩ : T) * x = x * φ.symm ⟨k, hk⟩)
      simpa using this
    exact congrArg Subtype.val h'
  · have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hsq)
    have h2 : (φ x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
    simpa using congrArg Subtype.val h2

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem ffDatum (hS : Standing G) (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hTI : ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T))
    (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M) : FFDatum p M T := by
  have hprime := sigmaA_prime p hp
  have hcharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hw.maxLocal.1
  have hU := uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT
  have hFF : ∀ (V : Subgroup G) (hV : IsElemAbelian 2 V), uCore M T = V → ∀ Q : Prop,
      ((¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (V : Set G) ∧
        CFSG.Quasithin.IsFFModule (CFSG.Quasithin.autI hV M) ∧
        CFSG.Quasithin.IsTwoReducedIn M V) ∨
      (CFSG.Quasithin.thompsonJ T ≤ centralizer (V : Set G) ∧ Q)) →
      ∃ hU' : IsElemAbelian 2 (uCore M T),
        CFSG.Quasithin.IsFFModule (CFSG.Quasithin.autI hU' M) ∧
        CFSG.Quasithin.IsTwoReducedIn M (uCore M T) := by
    intro V hV e Q h
    subst e
    rcases h with ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · exact ⟨hV, h2, h3⟩
    · exact absurd h1 hJe
  obtain ⟨hU0, hcase⟩ := CFSG.Quasithin.B2_15 hcharM (CFSG.ABGLocalTools.isSylowOf_iff.mp hT)
  obtain ⟨hU', hFFM, hred⟩ := hFF _ hU0 (uCore_eq_conjClosure M T) _ hcase
  have hMU := le_normalizer_uCore M T
  obtain ⟨hk, hc, -⟩ := hw.pRank_normalizer_of_not_isTI hS hp
    (elementary_isPGroup 2 _ hU.2) hMU hT hTI
  have h3 := (hw.pRank_eq_three hS hp).2
  have hadd := pRank_le_add_pRank_autI hU.2 hMU hprime
  exact
    { prime := hprime
      odd := sigmaA_odd p hp
      sylow := hT
      charTwo := hcharM
      elemAbelian := hU.2
      notCentral := hJe
      ffModule := hFFM
      twoReduced := hred
      notTI := hTI
      rank_M := h3
      rank_ker := hk
      rank_aut := by
        change 2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.autI hU.2 M)
        omega
      good_cT := hc
      strong := (hw.gamma_one_le_iff hS hp).mp hΓ }

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
