module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LieType.SeitzGeneration.LowNarrow
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.SeitzGeneration
  CFSG.AGLEmbeddingD2

variable {X : Type} [Group X]

section Basic

theorem mem_of_pow_eq_one_of_not_dvd_outer {p : ℕ} (hp : p.Prime) (K : Subgroup X) [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) (hout : ¬ p ∣ Nat.card (Outer ↥K)) {x : X}
    (hx : x ^ p = 1) : x ∈ K := by
  refine mem_of_conjNormal_mem_inner K hKC ?_
  let ψ : Outer ↥K := QuotientGroup.mk (MulAut.conjNormal (H := K) x)
  have h1 : ψ ^ p = 1 := by
    show (QuotientGroup.mk ((MulAut.conjNormal (H := K) x) ^ p) : Outer ↥K) = 1
    rw [← map_pow, hx, map_one]
    rfl
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
  · rw [orderOf_eq_one_iff] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  · exact absurd (h ▸ orderOf_dvd_natCard ψ) hout

variable [Finite X]

theorem one_le_pRank_of_isPGroup {p : ℕ} (hp : p.Prime) {Q : Subgroup X} (hQ : IsPGroup p Q)
    (hQ1 : Q ≠ ⊥) : 1 ≤ CFSG.Open.pRank p Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hQ1 (Subgroup.eq_bot_of_card_eq Q (by simpa using hn))
  have hdvd : p ∣ Nat.card Q := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Q) p hdvd
  have hyp : (y : X) ^ p = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hord : orderOf (y : X) = p := by rw [Subgroup.orderOf_coe, hy]
  have hEQ : Subgroup.zpowers (y : X) ≤ Q := Subgroup.zpowers_le.2 y.2
  refine CFSG.SectionRank.le_pRank hp.one_lt hEQ
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hyp) ?_
  rw [Nat.card_zpowers, hord, pow_one]

theorem normalizer_le_gamma {p : ℕ} (hp : p.Prime) {P Q : Subgroup X} (hQP : Q ≤ P)
    (hQ : IsPGroup p Q) (hQ1 : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set X) ≤ rankThreeGamma 1 p P := by
  unfold rankThreeGamma GLBCore
  exact le_sSup ⟨Q, hQP, one_le_pRank_of_isPGroup hp hQ hQ1, rfl⟩

theorem mem_gamma_of_commute {p : ℕ} (hp : p.Prime) {P : Subgroup X} {a : X} (haP : a ∈ P)
    (hap : a ^ p = 1) (ha1 : a ≠ 1) {k : X} (hk : a * k * a⁻¹ = k) :
    k ∈ rankThreeGamma 1 p P := by
  have : Fact p.Prime := ⟨hp⟩
  have hQP : Subgroup.zpowers a ≤ P := Subgroup.zpowers_le.2 haP
  have hQ : IsPGroup p (Subgroup.zpowers a) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    show (a ^ m) ^ (p ^ 1) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap, one_zpow]
  have hQ1 : Subgroup.zpowers a ≠ ⊥ := by
    rwa [Ne, Subgroup.zpowers_eq_bot]
  refine normalizer_le_gamma hp hQP hQ hQ1 ?_
  have hc : Commute k a := by
    have h1 : k * a = a * k := by
      calc k * a = (a * k * a⁻¹) * a := by rw [hk]
        _ = a * k := by group
    exact h1
  have hcent : k ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hc.zpow_right m).eq).symm
  exact Subgroup.centralizer_le_normalizer _ hcent

end Basic

section Gamma

variable [Finite X]

theorem gamma_eq_top_of_le {p : ℕ} (hp : p.Prime) (P : Sylow p X) (K : Subgroup X) [K.Normal]
    (hT : (P : Subgroup X) ⊓ K ≠ ⊥) (hKΓ : K ≤ rankThreeGamma 1 p (P : Subgroup X)) :
    rankThreeGamma 1 p (P : Subgroup X) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT'⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  have hTmap : Subgroup.map K.subtype (T : Subgroup K) = (P : Subgroup X) ⊓ K := by
    rw [hT', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
  have hfr := Sylow.normalizer_sup_eq_top T
  have hfr' : Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ⊔ K = ⊤ := by
    rw [← hTmap]
    exact hfr
  have hN : Subgroup.normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤
      rankThreeGamma 1 p (P : Subgroup X) :=
    normalizer_le_gamma hp inf_le_left (P.isPGroup'.to_inf_left) hT
  rw [eq_top_iff, ← hfr']
  exact sup_le hN hKΓ

theorem gamma_eq_top_of_generation {p : ℕ} (hp : p.Prime) (P : Sylow p X) (K : Subgroup X)
    [K.Normal] {E : Subgroup X} (hEP : E ≤ (P : Subgroup X)) (hE : IsElemAbelian p E)
    (hT : (P : Subgroup X) ⊓ K ≠ ⊥)
    (hgen : Subgroup.closure {k : ↥K | ∃ a ∈ E, a ≠ 1 ∧ a * (k : X) * a⁻¹ = (k : X)} = ⊤) :
    rankThreeGamma 1 p (P : Subgroup X) = ⊤ := by
  refine gamma_eq_top_of_le hp P K hT fun k hk => ?_
  have hmem : (⟨k, hk⟩ : ↥K) ∈
      Subgroup.closure {k : ↥K | ∃ a ∈ E, a ≠ 1 ∧ a * (k : X) * a⁻¹ = (k : X)} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hle : Subgroup.closure {k : ↥K | ∃ a ∈ E, a ≠ 1 ∧ a * (k : X) * a⁻¹ = (k : X)} ≤
      (rankThreeGamma 1 p (P : Subgroup X)).comap K.subtype := by
    rw [Subgroup.closure_le]
    rintro k ⟨a, haE, ha1, hak⟩
    exact mem_gamma_of_commute hp (hEP haE) (hE.2 a haE) ha1 hak
  exact hle hmem

end Gamma

section Seitz

@[expose] def SeitzOuterRankOne : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ RankLE1 p (Cat d)

theorem seitzOuterRankOne_of_lowN (h : SeitzOuterLowN) : SeitzOuterRankOne :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.rankLE2, Or.inl hE.2⟩) h

theorem conjNormal_injective (K : Subgroup X) [K.Normal]
    (hKC : Subgroup.centralizer (K : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hKC] at hxc
  exact Subgroup.mem_bot.mp hxc

theorem closure_fixed_eq_top_of_seitz (hS : SeitzOuterRankOne) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (K : Subgroup X) [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ≃* Cat d) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) {E : Subgroup X} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hEK : ¬ E ≤ K) (hrk : RankLE1 p ↥K) :
    Subgroup.closure {k : ↥K | ∃ a ∈ E, a ≠ 1 ∧ a * (k : X) * a⁻¹ = (k : X)} = ⊤ := by
  have hφ := conjNormal_injective K hKC
  let φ : X →* MulAut ↥K := MulAut.conjNormal
  have hφE : IsElemAbelian p (E.map φ) := CFSG.Open.IsElemAbelian.map hE φ
  have hφc : Nat.card (E.map φ) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hφ, hEc]
  have hninner : ¬ InnerPlane d p ((E.map φ).map (MulAut.congr e).toMonoidHom) := by
    intro hin
    have h1 := InnerPlane.of_map_congr e hin
    obtain ⟨x, hxE, hxK⟩ := SetLike.not_le_iff_exists.1 hEK
    exact hxK (mem_of_conjNormal_mem_inner K hKC (h1 (Subgroup.mem_map_of_mem φ hxE)))
  have hpg := hS d p hp hp2 hpd hex ((E.map φ).map (MulAut.congr e).toMonoidHom)
    (CFSG.Open.IsElemAbelian.map hφE _)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hφc])
    ⟨hninner, RankLE1.of_mulEquiv e hrk⟩
  have hpg' : PlaneGen (E.map φ) := (planeGen_map_congr e _).1 hpg
  have hset : {k : ↥K | ∃ ε ∈ E.map φ, ε ≠ 1 ∧ ε k = k} =
      {k : ↥K | ∃ a ∈ E, a ≠ 1 ∧ a * (k : X) * a⁻¹ = (k : X)} := by
    ext k
    constructor
    · rintro ⟨_, ⟨a, haE, rfl⟩, hε1, hεk⟩
      refine ⟨a, haE, ?_, ?_⟩
      · rintro rfl
        exact hε1 (map_one φ)
      · have := congrArg Subtype.val hεk
        rwa [MulAut.conjNormal_apply] at this
    · rintro ⟨a, haE, ha1, hak⟩
      refine ⟨φ a, Subgroup.mem_map_of_mem φ haE,
        fun h => ha1 (hφ (h.trans (map_one φ).symm)), ?_⟩
      exact Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hak)
  unfold PlaneGen planeClosure at hpg'
  rwa [hset] at hpg'

end Seitz

section Config

variable [Finite X]

theorem card_le_of_isCyclic_of_pow_eq_one {p : ℕ} (hp : 0 < p) {A : Subgroup X} (hA : IsCyclic A)
    (hAp : ∀ a ∈ A, a ^ p = 1) : Nat.card A ≤ p := by
  have hC : ∀ c : A, c ^ p = 1 := fun c => Subtype.ext (by simpa using hAp c c.2)
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp (Monoid.exponent_dvd_of_forall_pow_eq_one hC)

theorem exists_sylow_cyclic {p : ℕ} (hp : p.Prime) (P : Sylow p X) (K : Subgroup X) [K.Normal]
    (hPK : IsCyclic ↥((P : Subgroup X) ⊓ K)) :
    ∃ T : Sylow p ↥K, IsCyclic ↥(T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  refine ⟨T, ?_⟩
  have e : ↥(T : Subgroup K) ≃* ↥((P : Subgroup X) ⊓ K) :=
    (MulEquiv.subgroupCongr hT).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  exact (MulEquiv.isCyclic e).mpr hPK

theorem rankLE1_of_isCyclic_inf {p : ℕ} (hp : p.Prime) (P : Sylow p X) (K : Subgroup X)
    [K.Normal] (hPK : IsCyclic ↥((P : Subgroup X) ⊓ K)) : RankLE1 p ↥K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := exists_sylow_cyclic hp P K hPK
  intro A hA
  exact CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA

theorem exists_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK3 : KFactOutCyclic)
    (K : Subgroup X) [K.Normal] (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K) (hKC : Subgroup.centralizer (K : Set X) = ⊥) (P : Sylow p X)
    (hPK : IsCyclic ↥((P : Subgroup X) ⊓ K)) (hrank : 2 ≤ CFSG.Open.pRank p (P : Subgroup X)) :
    ∃ E : Subgroup X, E ≤ (P : Subgroup X) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ¬ E ≤ K ∧ (P : Subgroup X) ⊓ K ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEP, hE, hEc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp hrank
  have hEnc : ¬ IsCyclic ↥E := by
    intro hc
    have := card_le_of_isCyclic_of_pow_eq_one hp.pos hc hE.2
    rw [hEc] at this
    nlinarith [hp.two_le]
  have hEK : ¬ E ≤ K := fun h => hEnc (by
    haveI := hPK
    exact Subgroup.isCyclic_of_le (le_inf hEP h))
  refine ⟨E, hEP, hE, hEc, hEK, fun hbot => ?_⟩
  obtain ⟨T, hT⟩ := exists_sylow_cyclic hp P K hPK
  have hout := hK3 K hs hnab hcat p hp hp2 T hT
  have hq := isCyclic_quotient_of_outer hp hp2 K hKC (P : Subgroup X) P.isPGroup' hout
  have hbot' : K.subgroupOf (P : Subgroup X) = ⊥ := by
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    exact hbot
  have hPc : IsCyclic ↥(P : Subgroup X) :=
    (MulEquiv.isCyclic ((QuotientGroup.quotientMulEquivOfEq hbot').trans
      QuotientGroup.quotientBot)).mp hq
  exact hEnc (Subgroup.isCyclic_of_le hEP)

end Config

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.CyclicOuter
