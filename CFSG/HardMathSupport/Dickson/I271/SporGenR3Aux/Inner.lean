module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerLieQ
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterBasic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Inner

theorem mem_innerAut_of_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : Nat.card (Outer G) ≤ 2) {ψ : MulAut G} (hψ : ψ ^ p = 1) :
    ψ ∈ innerAut G := by
  have hfin : Finite (MulAut G) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  have h1 : (QuotientGroup.mk ψ : Outer G) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hψ, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk ψ : Outer G) ∣ p := orderOf_dvd_of_pow_eq_one h1
  have hle : orderOf (QuotientGroup.mk ψ : Outer G) ≤ 2 :=
    (Nat.le_of_dvd hpos (orderOf_dvd_natCard _)).trans hO
  have h1' : orderOf (QuotientGroup.mk ψ : Outer G) = 1 := by
    rcases (Nat.dvd_prime hp).1 h3 with h | h
    · exact h
    · exfalso
      have h2 := hp.two_le
      omega
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1'
  exact h1'

variable {X : Type} [Group X] [Finite X]

theorem exists_inner_of_spor {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K B : Subgroup X}
    {name : TauCeti.SporadicName} (hOut : SporadicOuterLeTwo) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hS : I271SporType K name) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hBel : IsElemAbelian p B) {b : X} (hb : b ∈ B) :
    ∃ k ∈ K, k⁻¹ * b ∈ Subgroup.centralizer (K : Set X) := by
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hout := hOut _ hq.2 (exists_noncomm_of_isQuasisimple hq) name ⟨e⟩
  have hbN := hBN hb
  have h := mem_innerAut_of_pow_eq_one hp hp2 hout (actHom_pow_eq_one hbN (hBel.2 b hb))
  exact exists_inner_of_actHom_mem_innerAut hq.1 hbN h

theorem coreFree_of_inner_loc {p : ℕ} (hp : p.Prime) {K : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    {H : Subgroup (MulAut (barOf p K))} (hH : innerAut (barOf p K) ≤ H)
    {d : MulAut (barOf p K)} (hd : d ∈ innerAut (barOf p K))
    (hdN : d ∈ Subgroup.normalizer (H : Set (MulAut (barOf p K)))) (hdp : orderOf d = p) :
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (barOf p K)))) = ⊥ := by
  set Φ := autBarToQuot p hO with hΦ
  have hΦinj : Function.Injective Φ := autBarToQuot_injective p hO hq.1
  have hinnS : innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H.map Φ := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨MulAut.conj (barOfEquiv p hO x), hH ⟨_, rfl⟩, ?_⟩
    rw [hΦ, autBarToQuot_conj]
    simp
  have hxord : orderOf (Φ d) = p := by
    rw [orderOf_injective Φ hΦinj]
    exact hdp
  have hnorm : Φ d ∈ Subgroup.normalizer ((H.map Φ : Subgroup _) : Set _) :=
    Subgroup.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ hdN)
  have hS := hloc (Φ d) hxord (H.map Φ) hinnS hnorm
  rw [← map_inf_centralizer_of_injective Φ hΦinj,
    ← map_glaPPrimeCoreOf_of_injective p Φ hΦinj] at hS
  exact (Subgroup.map_eq_bot_iff_of_injective _ hΦinj).1 hS

theorem isCompLocallyBalanced_of_inner_loc {p : ℕ} (hp : p.Prime) {K A : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hO : GLAPPrimeCore p ↥K = ⊥)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hAN : A ≤ Subgroup.normalizer (K : Set X))
    (hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    IsCompLocallyBalanced p 1 A K := by
  intro D hD H hH hDH
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card D = p := by simpa using hD.2.2
  have hnt : 1 < Nat.card D := by rw [hcard]; exact hp.one_lt
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hnt
    obtain ⟨⟨d, hd⟩, hne⟩ := exists_ne (1 : D)
    exact ⟨d, hd, fun h => hne (Subtype.ext h)⟩
  have hdp : orderOf d = p := orderOf_eq_prime (hD.2.1.2 d hdD) hd1
  obtain ⟨γ, hγ, rfl⟩ := hD.1 hdD
  obtain ⟨k, hk, hkc⟩ := hin (γ : X) ((Subgroup.mem_subgroupOf.1 hγ).1)
  have hdinner : barAut p K γ ∈ innerAut (barOf p K) := by
    have := barAut_eq_conj_of_inner (p := p) hk hkc γ.2
    rw [show γ = ⟨(γ : X), γ.2⟩ from rfl, this]
    exact ⟨_, rfl⟩
  have key := coreFree_of_inner_loc hp hq hO hloc hH hdinner (hDH hdD) hdp
  unfold localDeltaIn
  refine eq_bot_iff.2 ?_
  exact (iInf_le_of_le (barAut p K γ) (iInf_le_of_le hdD (iInf_le _ hd1))).trans key.le

end Inner

section Constrained

theorem constraint_of_pConstrainedShape {Y : Type} [Group Y] [Finite Y] {p : ℕ} {N : Subgroup Y}
    (h : PConstrainedShape p N) :
    ∀ x ∈ N, (∀ r ∈ CFSG.Open.pCoreOf p N, x * r = r * x) → x ∈ CFSG.Open.pCoreOf p N := by
  obtain ⟨Q, hQN, hQn, hQp, hQc⟩ := h
  have hQcore : Q ≤ CFSG.Open.pCoreOf p N := by
    have hnorm : (Q.subgroupOf N).Normal :=
      ⟨fun x hx g => by
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        exact hQn g.1 g.2 x hx⟩
    have hpg : IsPGroup p (Q.subgroupOf N) :=
      hQp.of_injective (Subgroup.subgroupOfEquivOfLe hQN).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hQN).injective
    have hle : Q.subgroupOf N ≤ CFSG.pCore p ↥N := le_sSup ⟨hnorm, hpg⟩
    calc Q = (Q.subgroupOf N).map N.subtype := (Subgroup.map_subgroupOf_eq_of_le hQN).symm
      _ ≤ CFSG.Open.pCoreOf p N := Subgroup.map_mono hle
  intro x hx hxr
  exact hQcore (hQc ⟨hx, Subgroup.mem_centralizer_iff.2 fun q hq => (hxr q (hQcore hq)).symm⟩)

variable {X : Type} [Group X] [Finite X]

theorem not_glaPComponent_of_constrained {p : ℕ} (hp : p.Prime) {K : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) {a k : X} (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X))
    (hcon : PConstrainedShape p (Subgroup.centralizer ({(⟨k, hk⟩ : ↥K)} : Set ↥K)))
    {J : Subgroup X} (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) : False := by
  set k' : ↥K := ⟨k, hk⟩ with hk'
  set α : MulAut ↥K := MulAut.conj k' with hα
  have hfix : (K ⊓ Subgroup.centralizer ({a} : Set X)).subgroupOf K = fixSubgroup α := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_fixSubgroup, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    have hcy : (k⁻¹ * a) * (y : X) = (y : X) * (k⁻¹ * a) :=
      (Subgroup.mem_centralizer_iff.1 hc y y.2).symm
    constructor
    · rintro ⟨-, hy⟩
      apply Subtype.ext
      show k * (y : X) * k⁻¹ = (y : X)
      calc k * (y : X) * k⁻¹ = k * ((k⁻¹ * a) * y) * (k⁻¹ * a)⁻¹ * k⁻¹ := by
            rw [hcy]; group
        _ = a * (y : X) * a⁻¹ := by group
        _ = (y : X) := by rw [← hy]; group
    · intro hy
      refine ⟨y.2, ?_⟩
      have h1 : k * (y : X) * k⁻¹ = (y : X) := congrArg Subtype.val hy
      have hky : k * (y : X) = (y : X) * k := mul_inv_eq_iff_eq_mul.1 h1
      calc (y : X) * a = y * (k * (k⁻¹ * a)) := by group
        _ = (y * k) * (k⁻¹ * a) := by group
        _ = (k * y) * (k⁻¹ * a) := by rw [← hky]
        _ = k * (y * (k⁻¹ * a)) := by group
        _ = k * ((k⁻¹ * a) * y) := by rw [← hcy]
        _ = a * (y : X) := by group
  have hJ' := glaPComponent_subgroupOf hp
    (inf_le_left : K ⊓ Subgroup.centralizer ({a} : Set X) ≤ K) hJ
  rw [hfix] at hJ'
  have hfixC : fixSubgroup α = Subgroup.centralizer ({k'} : Set ↥K) := by
    ext y
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : k' * y * k'⁻¹ = y := h
      calc y * k' = (k' * y * k'⁻¹) * k' := by rw [h1]
        _ = k' * y := by group
    · intro h
      show k' * y * k'⁻¹ = y
      calc k' * y * k'⁻¹ = (y * k') * k'⁻¹ := by rw [h]
        _ = y := by group
  rw [hfixC] at hJ'
  have hlay : GLAPLayer p (Subgroup.centralizer ({k'} : Set ↥K)) = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.glaPLayer_eq_bot_of_constrained
      hp le_rfl (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (constraint_of_pConstrainedShape hcon)
  have hle : J.subgroupOf K ≤ GLAPLayer p (Subgroup.centralizer ({k'} : Set ↥K)) := le_sSup hJ'
  rw [hlay, le_bot_iff] at hle
  exact glaPComponent_ne_bot' hJ' hle

end Constrained

end CFSG.HardMathSupport.Dickson.I271
