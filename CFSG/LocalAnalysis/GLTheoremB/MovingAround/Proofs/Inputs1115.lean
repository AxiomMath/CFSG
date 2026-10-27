module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1115
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1115

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped commutatorElement

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem barX_le_barX {p : ℕ} {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem exists_glaPComponent_cover {p : ℕ} (hp : p.Prime) {X Y K : Subgroup G} (hYX : Y ≤ X)
    (hK : GLAPComponent p X K) (hcov : barX p X K ≤ barX p X Y) :
    ∃ K' : Subgroup G, GLAPComponent p Y K' ∧ barX p X K' = barX p X K := by
  classical
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  set φ : ↥Y →* (↥X ⧸ GLAPPrimeCore p ↥X) := π.comp (Subgroup.inclusion hYX) with hφ
  set Q : Subgroup G := ((barX p X K).comap φ).map Y.subtype with hQ
  have hQY : Q ≤ Y := Subgroup.map_subtype_le _
  have hQX : Q ≤ X := hQY.trans hYX
  have hmemQ : ∀ x : ↥X, (x : G) ∈ Q ↔ (x : G) ∈ Y ∧ π x ∈ barX p X K := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyY : (y : G) ∈ Y := y.2
      refine ⟨hyx ▸ hyY, ?_⟩
      have e : Subgroup.inclusion hYX y = x := Subtype.ext hyx
      have hy' : φ y ∈ barX p X K := hy
      rw [hφ, MonoidHom.comp_apply, e] at hy'
      exact hy'
    · rintro ⟨hxY, hx⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      show φ ⟨x, hxY⟩ ∈ barX p X K
      have e : Subgroup.inclusion hYX ⟨(x : G), hxY⟩ = x := Subtype.ext rfl
      rw [hφ, MonoidHom.comp_apply, e]
      exact hx
  have hQsn : IsSubnormal Q Y := by
    have h1 := isSubnormal_comap' φ hK.2.2.1.2.1
    rw [Subgroup.comap_top] at h1
    have h2 := isSubnormal_map' Y.subtype h1
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h2
  have hbarQ : barX p X Q = barX p X K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ((hmemQ x).1 (Subgroup.mem_subgroupOf.1 hx)).2
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := hcov hz
      exact ⟨x, Subgroup.mem_subgroupOf.2 ((hmemQ x).2 ⟨Subgroup.mem_subgroupOf.1 hx, hz⟩), rfl⟩
  set T : Subgroup G := preimBarX p X K with hT
  have hTX : T ≤ X := preimBarX_le p X K
  have hTsn : IsSubnormal T X := isSubnormal_preimBarX p hK.2.2.1.2.1
  have hQT : Q ≤ T := by
    intro q hq
    have hqX : q ∈ X := hQX hq
    exact ⟨⟨q, hqX⟩, ((hmemQ ⟨q, hqX⟩).1 hq).2, rfl⟩
  have hOT : GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p T := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hTsn]
    refine le_inf ?_ le_rfl
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (GLAPPrimeCore p ↥X) n ∈ barX p X K
    rw [show QuotientGroup.mk' (GLAPPrimeCore p ↥X) n = 1 from (QuotientGroup.eq_one_iff n).2 hn]
    exact Subgroup.one_mem _
  have hcovT : T ≤ Q ⊔ GLAPPrimeCoreOf p T := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : π x ∈ barX p X Q := by rw [hbarQ]; exact hx
    obtain ⟨q, hq, hqx⟩ := hx'
    have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.1 hq
    have hn : (q : G)⁻¹ * x ∈ GLAPPrimeCoreOf p X :=
      ⟨q⁻¹ * x, QuotientGroup.eq.1 hqx, by simp⟩
    have e : X.subtype x = q * ((q : G)⁻¹ * x) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqQ) (Subgroup.mem_sup_right (hOT hn))
  obtain ⟨-, ⟨eQT⟩⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.barOf_equiv_of_cover hp hQT hcovT
  have hbarT : barX p X T = barX p X K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.1 hx
      have e : y = x := Subtype.ext hyx
      rw [← e]
      exact hy
    · exact barX_le_barX (le_preimBarX p hK.1)
  have eT : barOf p T ≃* ↥(barX p X K) :=
    (quotEquivBarX hp hTX hTsn).trans (MulEquiv.subgroupCongr hbarT)
  have hqQ : CFSG.Open.IsQuasisimple (barOf p Q) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (eQT.trans eT).symm
      hK.2.2.1.2.2
  have hqYQ : CFSG.Open.IsQuasisimple ↥(barX p Y Q) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (quotEquivBarX hp hQY hQsn) hqQ
  have hcompQ : IsComponentOf (barX p Y Q) ⊤ := by
    refine ⟨le_top, ?_, hqYQ⟩
    have := isSubnormal_barX (C := Y) p hQsn
    rwa [barX_self] at this
  obtain ⟨K', ⟨hK'Q, hK'sn, hK'bar⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {J : Subgroup G | J ≤ Q ∧ IsSubnormal J Y ∧ barX p Y J = barX p Y Q}
    ⟨Q, le_rfl, hQsn, rfl⟩
  have hK'Y : K' ≤ Y := hK'Q.trans hQY
  have hK'X : K' ≤ X := hK'Y.trans hYX
  have hK'comp : GLAPComponent p Y K' := by
    refine ⟨hK'Y, hK'sn, ?_, ?_⟩
    · change IsComponentOf (barX p Y K') ⊤
      rw [hK'bar]
      exact hcompQ
    · intro J hJ hJsn heq
      exact hmin J ⟨hJ.le.trans hK'Q, hJsn, heq.trans hK'bar⟩ hJ
  refine ⟨K', hK'comp, ?_⟩
  have hle : barX p X K' ≤ barX p X K := hbarQ ▸ barX_le_barX hK'Q
  have hsn : IsSubnormal (barX p X K') (barX p X K) := by
    have := isSubnormal_barX (C := X) p (isSubnormal_of_le_of_le hK'sn hK'Q hQY)
    rwa [hbarQ] at this
  have hperf : ⁅barX p X K', barX p X K'⁆ = barX p X K' := by
    rw [← barX_commutator p hK'X hK'X, glaPComponent_perfect hK'comp]
  have hne : barX p X K' ≠ ⊥ := by
    intro hbot
    have h1 : K' ≤ GLAPPrimeCoreOf p X := by
      intro k hk
      have hm : π ⟨k, hK'X hk⟩ ∈ barX p X K' := ⟨⟨k, hK'X hk⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hm
      exact ⟨⟨k, hK'X hk⟩, (QuotientGroup.eq_one_iff _).1 hm, rfl⟩
    have h2 : K' ≤ GLAPPrimeCoreOf p Y := by
      have h3 := CFSG.HardMathSupport.Solomon.LocalBalance.gLAPPrimeCoreOf_inf_le hp X Y
      rw [inf_eq_right.2 hYX] at h3
      exact fun k hk => h3 ⟨h1 hk, hK'Y hk⟩
    apply CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.A2_barX_ne_bot hK'comp
    refine eq_bot_iff.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hkk⟩ := h2 (Subgroup.mem_subgroupOf.1 hk)
    have e : k' = k := Subtype.ext hkk
    rw [Subgroup.mem_bot, ← e]
    exact (QuotientGroup.eq_one_iff _).2 hk'
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.eq_of_perfect_subnormal_of_quasisimple
    hK.2.2.1.2.2 hle hsn hperf hne

theorem le_glaPPrimeCoreOf_of_le_normalizer {p : ℕ} {X N : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p X := by
  have hn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hcop : Nat.Coprime p (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ GLAPPrimeCore p ↥X := le_sSup ⟨hn, hcop⟩
  calc N = (N.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hNX).symm
    _ ≤ GLAPPrimeCoreOf p X := Subgroup.map_mono hle

theorem le_of_isPGroup_le_sup {p : ℕ} {N O P : Subgroup G}
    (hO : p.Coprime (Nat.card O)) (hON : O ≤ Subgroup.normalizer (N : Set G))
    (hP : IsPGroup p ↥P) (hPNO : P ≤ N ⊔ O) : P ≤ N := by
  have hNA : N ≤ N ⊔ O := le_sup_left
  have hOA : O ≤ N ⊔ O := le_sup_right
  have hAN : N ⊔ O ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hON
  haveI : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 hAN
  have hidx : p.Coprime (N.subgroupOf (N ⊔ O)).index := by
    have htop : O.subgroupOf (N ⊔ O) ⊔ N.subgroupOf (N ⊔ O) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hOA hNA, sup_comm, Subgroup.subgroupOf_self]
    have h1 := Subgroup.relIndex_sup_right (O.subgroupOf (N ⊔ O)) (N.subgroupOf (N ⊔ O))
    rw [htop, Subgroup.relIndex_top_right] at h1
    rw [h1]
    refine Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_card _ _) ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOA).toEquiv]
  intro x hx
  set y : ↥(N ⊔ O) := ⟨x, hPNO hx⟩ with hy
  have hyN : y ^ (N.subgroupOf (N ⊔ O)).index ∈ N.subgroupOf (N ⊔ O) :=
    Subgroup.pow_index_mem _ y
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hyk : y ^ p ^ k = 1 := Subtype.ext (by
    have := congrArg Subtype.val hk
    simpa [hy] using this)
  have hcop : (N.subgroupOf (N ⊔ O)).index.gcd (orderOf y) = 1 :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hyk)
      (Nat.Coprime.pow_right k hidx.symm)
  have hmem : y ∈ Subgroup.zpowers (y ^ (N.subgroupOf (N ⊔ O)).index) :=
    mem_zpowers_pow_iff.2 hcop
  exact (Subgroup.zpowers_le.2 hyN) hmem

omit [Finite G] in
theorem ne_bot_of_isQuasisimple {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hbot
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
  apply hxy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : x = 1 := Subtype.ext (by simpa [hbot] using x.2)
  have hy : y = 1 := Subtype.ext (by simpa [hbot] using y.2)
  rw [hx, hy]

theorem commutator_eq_bot_of_normalizes_coprime {Γ : Type} [Group Γ] [Finite Γ]
    {K U : Subgroup Γ} (hK : IsComponentOf K ⊤) (hcore : GLAPPrimeCore 3 Γ = ⊥)
    (hU : Nat.Coprime 3 (Nat.card U)) (hKU : K ≤ Subgroup.normalizer (U : Set Γ)) :
    ⁅K, U⁆ = ⊥ := by
  have hUH : U ≤ U ⊔ K := le_sup_left
  have hKH : K ≤ U ⊔ K := le_sup_right
  haveI hnorm : (U.subgroupOf (U ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).2 (sup_le Subgroup.le_normalizer hKU)
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
      (K.subgroupOf (U ⊔ K)) (U.subgroupOf (U ⊔ K))
      (CFSG.ComponentClassification.LocalComponents.of_overgroup hK hKH) with hle | hcomm
  · exfalso
    have hKU' : K ≤ U := fun x hx =>
      hle (show (⟨x, hKH hx⟩ : ↥(U ⊔ K)) ∈ K.subgroupOf (U ⊔ K) from hx)
    have hKc : Nat.Coprime 3 (Nat.card K) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKU') hU
    have h1 : GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 (⊤ : Subgroup Γ) :=
      glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hK.2.1
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.A4_core_top hcore] at h1
    have h2 : GLAPPrimeCore 3 ↥K = ⊤ :=
      eq_top_iff.2 (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
    have h3 : GLAPPrimeCoreOf 3 K = K := by
      show (GLAPPrimeCore 3 ↥K).map K.subtype = K
      rw [h2, Subgroup.map_top, Subgroup.range_subtype]
    rw [h3] at h1
    exact ne_bot_of_isQuasisimple hK.2.2 (le_bot_iff.1 h1)
  · have hmap := congrArg (Subgroup.map (U ⊔ K).subtype) hcomm
    simpa only [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
      Subgroup.map_subgroupOf_eq_of_le hUH, Subgroup.map_bot] using hmap

omit [Finite G] in
theorem le_of_perfect_le_sup {Γ : Type*} [Group Γ] {Jb Pb Qb : Subgroup Γ}
    (hperf : ⁅Jb, Jb⁆ = Jb) (hJ : Jb ≤ Pb ⊔ Qb) (hQJ : Qb ≤ Subgroup.centralizer (Jb : Set Γ))
    (hQP : Qb ≤ Subgroup.normalizer (Pb : Set Γ)) (hJP : Jb ≤ Subgroup.normalizer (Pb : Set Γ)) :
    Jb ≤ Pb := by
  rw [← hperf, Subgroup.commutator_le]
  intro x hx c hc
  have hx' : x ∈ ((Qb ⊔ Pb : Subgroup Γ) : Set Γ) := by
    rw [sup_comm]
    exact hJ hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Qb Pb hQP] at hx'
  obtain ⟨b, hb, a, ha, rfl⟩ := hx'
  have hbc : b * c = c * b := (Subgroup.mem_centralizer_iff.1 (hQJ hb) c hc).symm
  have hac : a * c * a⁻¹ * c⁻¹ ∈ Pb := by
    have h1 : c * a⁻¹ * c⁻¹ ∈ Pb := (Subgroup.mem_normalizer_iff.1 (hJP hc) a⁻¹).1 (Pb.inv_mem ha)
    have := Pb.mul_mem ha h1
    simpa [mul_assoc] using this
  have hbc' : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ :=
    calc b⁻¹ * c⁻¹ = (c * b)⁻¹ := (mul_inv_rev c b).symm
      _ = (b * c)⁻¹ := by rw [hbc]
      _ = c⁻¹ * b⁻¹ := mul_inv_rev b c
  have e : ⁅b * a, c⁆ = b * (a * c * a⁻¹ * c⁻¹) * b⁻¹ := by
    rw [commutatorElement_def]
    calc b * a * c * (b * a)⁻¹ * c⁻¹ = b * a * c * a⁻¹ * (b⁻¹ * c⁻¹) := by group
      _ = b * a * c * a⁻¹ * (c⁻¹ * b⁻¹) := by rw [hbc']
      _ = b * (a * c * a⁻¹ * c⁻¹) * b⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (hQP hb) _).1 hac

theorem twoLocal_ne_top {m p : ℕ} (hS : GLStanding G m p) {H : Subgroup G} (hH : IsTwoLocal H) :
    H ≠ ⊤ := by
  intro htop
  obtain ⟨P, hP1, hP2, hHP⟩ := hH
  have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.1 (hHP ▸ htop)
  haveI := hS.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · exact hP1 hb
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG2 : IsPGroup 2 G := by
      rw [ht] at hP2
      exact hP2.of_equiv Subgroup.topEquiv
    haveI : Nontrivial G := by
      obtain ⟨a, b, hab⟩ := hS.nonabelian
      exact ⟨⟨a * b, b * a, hab⟩⟩
    haveI := hG2.center_nontrivial
    have hZ : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hz | hz
      · exfalso
        obtain ⟨⟨z, hz'⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
        apply hz1
        exact Subtype.ext (by rw [hz] at hz'; simpa using hz')
      · exact hz
    obtain ⟨a, b, hab⟩ := hS.nonabelian
    have ha : a ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem exists_glaPComponent_le_sup {p : ℕ} (hp : p.Prime) {X Y K : Subgroup G} (hYX : Y ≤ X)
    (hK : GLAPComponent p X K) (hcov : barX p X K ≤ barX p X Y) :
    ∃ K' : Subgroup G, GLAPComponent p Y K' ∧ barX p X K' = barX p X K ∧
      ∀ k ∈ K, ∃ k' ∈ K', k'⁻¹ * k ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨K', hK', hbar⟩ := exists_glaPComponent_cover hp hYX hK hcov
  exact ⟨K', hK', hbar, fun k hk => exists_of_barX_le hbar.symm.le hk (hK.1 hk)⟩

end General

section Context

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}

theorem elemAbelian_A (h : Cex117 G m 3 B M E A a K) : IsElemAbelian 3 A ∧ A ≤ M :=
  ⟨h.toCex117Base.toSec11.pair.1.2.1.1.1.2.1, h.toCex117Base.toSec11.pair.1.2.1.1.1.1⟩

theorem le_core_of_lemma1114 (h1114 : Lemma1114Statement) (h : Cex117 G m 3 B M E A a K)
    {S : Subgroup G} (hS : Nat.Coprime 3 (Nat.card S))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) : S ≤ GLAPPrimeCoreOf 3 M :=
  (le_iSup₂ (f := fun (T' : Subgroup G) (_ : IsInvThreePrimeSub ⊤ A T') => T') S
    ⟨le_top, hS, hAS⟩).trans (h1114 h)

theorem glaPPrimeCoreOf_le_M (h1114 : Lemma1114Statement) (h : Cex117 G m 3 B M E A a K)
    {X : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G)) : GLAPPrimeCoreOf 3 X ≤ M :=
  (le_core_of_lemma1114 h1114 h
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 X)
    (fun _ hx => CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf
      3 (hAX hx))).trans (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 M)

theorem normalizer_A0_le (h : Cex117 G m 3 B M E A a K) :
    Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M := by
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hsub : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ GLBCore 3 2 E :=
    le_sSup ⟨E ⊓ A, inf_le_left, hsec.pair.1.2.2, rfl⟩
  exact hsub.trans hsec.pair.1.1.2.clause_d

omit [Finite G] in
theorem jLayer_le (H : Subgroup G) : Lemma1115.jLayer a H ≤ H := by
  refine iSup₂_le fun g hg => ?_
  have hgH : g ∈ H := (sSup_le fun _ hL => hL.1 : GLAPLayer 3 H ≤ H) hg
  intro x hx
  rw [mem_gLBConj] at hx
  have h1 : g * x * g⁻¹ ∈ H :=
    ((sSup_le fun _ hL => hL.1 : GLAPLayer 3 (H ⊓ Cg a) ≤ H ⊓ Cg a).trans inf_le_left) hx
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e]
  exact H.mul_mem (H.mul_mem (H.inv_mem hgH) h1) hgH

omit [Finite G] in
theorem layer_le_jLayer (H : Subgroup G) : GLAPLayer 3 (H ⊓ Cg a) ≤ Lemma1115.jLayer a H := by
  have := le_iSup₂ (f := fun (g : G) (_ : g ∈ GLAPLayer 3 H) =>
    GLBConj g (GLAPLayer 3 (H ⊓ Cg a))) 1 (Subgroup.one_mem _)
  rwa [gLBConj_one] at this

theorem exists_cover_K (h : Cex117 G m 3 B M E A a K) {H : Subgroup G}
    (hH : InHFamily A K a H) :
    ∃ K' : Subgroup G, GLAPComponent 3 (H ⊓ Cg a) K' ∧ barX 3 (Cg a) K' = barX 3 (Cg a) K ∧
      ∀ k ∈ K, ∃ k' ∈ K', k'⁻¹ * k ∈ GLAPPrimeCoreOf 3 (Cg a) := by
  have hcov : barX 3 (Cg a) K ≤ barX 3 (Cg a) (H ⊓ Cg a) := by
    rw [barX_inf_self]
    exact hH.2.2
  exact exists_glaPComponent_le_sup Nat.prime_three inf_le_right h.hK hcov

end Context

section TNorm

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem glaPComponent_conj_of_mem {p : ℕ} {X L : Subgroup G} (hL : GLAPComponent p X L) {g : G}
    (hg : g ∈ X) : GLAPComponent p X (GLBConj g L) := by
  have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
  rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this

omit [Finite G] in
theorem gLBConj_sSup_le {g : G} {𝒮 : Set (Subgroup G)} {N : Subgroup G}
    (h : ∀ S ∈ 𝒮, GLBConj g S ≤ N) : GLBConj g (sSup 𝒮) ≤ N :=
  Subgroup.map_le_iff_le_comap.2 (sSup_le fun S hS => Subgroup.map_le_iff_le_comap.1 (h S hS))

theorem layer_cg_le_layer (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {H : Subgroup G} (hK : CFSG.Open.IsKGroup ↥H) {a : G} (haH : a ∈ H)
    (ha : IsPGroup 3 ↥(Subgroup.zpowers a)) :
    GLAPLayer 3 (H ⊓ Subgroup.centralizer ({a} : Set G)) ≤ GLAPLayer 3 H := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_inf_centralizer_le hS hK
    Nat.prime_three (Subgroup.zpowers_le.2 haH) ha
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h

theorem jLayer_perfect {a : G} (H : Subgroup G) :
    ⁅Lemma1115.jLayer a H, Lemma1115.jLayer a H⁆ = Lemma1115.jLayer a H := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine iSup₂_le fun g hg => gLBConj_sSup_le fun K'' hK'' => ?_
  have hle : GLBConj g K'' ≤ Lemma1115.jLayer a H :=
    (gLBConj_mono g (le_sSup hK'' : K'' ≤ GLAPLayer 3 (H ⊓ Cg a))).trans
      (le_iSup₂ (f := fun (g : G) (_ : g ∈ GLAPLayer 3 H) =>
        GLBConj g (GLAPLayer 3 (H ⊓ Cg a))) g hg)
  have hperf : ⁅GLBConj g K'', GLBConj g K''⁆ = GLBConj g K'' := by
    unfold GLBConj
    rw [← Subgroup.map_commutator, glaPComponent_perfect hK'']
  calc GLBConj g K'' = ⁅GLBConj g K'', GLBConj g K''⁆ := hperf.symm
    _ ≤ ⁅Lemma1115.jLayer a H, Lemma1115.jLayer a H⁆ := Subgroup.commutator_mono hle hle

theorem input1115TNorm_of_inputs
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1112 : Lemma1112Statement) (h1114 : Lemma1114Statement) : Lemma1115.Input1115TNorm := by
  intro G _ _ m B M E A a K h H hH T hT hTM
  have hsec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have hAH : A ≤ H := hH.2.1
  have ha : a ∈ A := h.ha.1
  have haH : a ∈ H := hAH ha
  have hAel : IsElemAbelian 3 A := (elemAbelian_A h).1
  have hAp : IsPGroup 3 ↥A := CFSG.Open.IsElemAbelian.isPGroup hAel
  have hTH : T ≤ H := hT.1
  set L : Subgroup G := GLAPLayer 3 H with hL
  set K0 : Subgroup G := GLAPLayer 3 (H ⊓ Cg a) with hK0
  set J : Subgroup G := Lemma1115.jLayer a H with hJ
  have hLH : L ≤ H := sSup_le fun _ hL' => hL'.1
  have hHtop : H ≠ ⊤ := twoLocal_ne_top hsec.standing hH.1
  have hKH : CFSG.Open.IsKGroup ↥H := isKGroup_of_isKProper hsec.standing.kProper hHtop
  have hK0L : K0 ≤ L :=
    layer_cg_le_layer hS hKH haH (hAp.to_le (Subgroup.zpowers_le.2 ha))
  have hJL : J ≤ L := iSup₂_le fun g hg =>
    (gLBConj_mono g hK0L).trans (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)).le
  have hLJ' : ∀ l ∈ L, GLBConj l J ≤ J := by
    intro l hl
    refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun g hg => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    show GLBConj l (GLBConj g K0) ≤ J
    rw [gLBConj_gLBConj]
    exact le_iSup₂ (f := fun (g : G) (_ : g ∈ L) => GLBConj g K0) (g * l) (L.mul_mem hg hl)
  have hLNJ : L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hLJ' l hl) ?_
    have := gLBConj_mono l (hLJ' l⁻¹ (L.inv_mem hl))
    rwa [gLBConj_gLBConj_inv] at this
  haveI hJn : (J.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).2 hLNJ
  have hA0K : E ⊓ A ≤ K := by
    rw [(h1112 h).2.1]
    exact inf_le_right
  have hA0p : IsPGroup 3 ↥(E ⊓ A : Subgroup G) := hAp.to_le inf_le_right
  obtain ⟨K', hK', -, hKK'⟩ := exists_cover_K h hH
  have hK'K0 : K' ≤ K0 := le_sSup hK'
  have hA0K0 : E ⊓ A ≤ K0 := by
    refine le_of_isPGroup_le_sup (O := GLAPPrimeCoreOf 3 (Cg a) ⊓ H) ?_ ?_ hA0p ?_
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 (Cg a))
    · refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3 ?_
      intro x hx
      exact Subgroup.le_normalizer ⟨hx.2,
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 (Cg a) hx.1⟩
    · intro x hx
      obtain ⟨k', hk', hkk⟩ := hKK' x (hA0K hx)
      have hk'H : k' ∈ H := (hK'.1.trans inf_le_left) hk'
      have hxH : x ∈ H := hAH hx.2
      have e : x = k' * (k'⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hK'K0 hk'))
        (Subgroup.mem_sup_right ⟨hkk, H.mul_mem (H.inv_mem hk'H) hxH⟩)
  have hA0J : E ⊓ A ≤ J := hA0K0.trans (layer_le_jLayer H)
  have hA0L : E ⊓ A ≤ L := hA0K0.trans hK0L
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    hAH.trans (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
      Subgroup.le_normalizer)
  have hOL : GLAPPrimeCoreOf 3 L ≤ M := glaPPrimeCoreOf_le_M h1114 h hAL
  have hNM := normalizer_A0_le h
  have hS6 : ∀ Lj : Subgroup G, GLAPComponent 3 H Lj → ¬ Lj ≤ J →
      ⁅barX 3 L Lj, barX 3 L J⁆ = ⊥ ∧ Lj ≤ M := by
    intro Lj hLj hnot
    have hLjL : Lj ≤ L := le_sSup hLj
    have hLjc : GLAPComponent 3 L Lj := glaPComponent_of_le Nat.prime_three hLj hLjL hLH
    rcases CFSG.HardMathSupport.Solomon.Coordinator.i183_le_or_commutator_eq_bot Nat.prime_three
      hLjc hJL with hle | hcomm
    · exact absurd hle hnot
    · refine ⟨hcomm, ?_⟩
      have h1 : barX 3 L Lj ≤ Subgroup.centralizer (barX 3 L (E ⊓ A) : Set _) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans
          (Subgroup.centralizer_le (barX_le_barX hA0J))
      have h2 := h1.trans
        (CFSG.HardMathSupport.Solomon.Coordinator.i183_centralizer_barX_le Nat.prime_three hA0L hA0p)
      intro x hx
      obtain ⟨y, hy, hyx⟩ := exists_of_barX_le h2 hx (hLjL hx)
      have hyM : y ∈ M := Lemma1114.centralizer_le_of_normalizer_le hNM (Subgroup.mem_inf.1 hy).2
      have := M.mul_mem hyM (hOL hyx)
      simpa using this
  have hS7 : ∀ Lj : Subgroup G, GLAPComponent 3 H Lj → Lj ≤ M → ∀ t ∈ T, GLBConj t Lj = Lj := by
    intro Lj hLj hLjM t ht
    set Y : Subgroup G := GLAPPrimeCoreOf 3 M ⊓ H with hY
    have hLjH : Lj ≤ H := hLj.1
    have hLjY : Lj ≤ Subgroup.normalizer (Y : Set G) := by
      intro x hx
      have hxO := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf
        3 M (hLjM hx)
      have hxH := Subgroup.le_normalizer (hLjH hx)
      rw [Subgroup.mem_normalizer_iff] at hxO hxH ⊢
      intro z
      constructor
      · rintro ⟨hz1, hz2⟩
        exact ⟨(hxO z).1 hz1, (hxH z).1 hz2⟩
      · rintro ⟨hz1, hz2⟩
        exact ⟨(hxO z).2 hz1, (hxH z).2 hz2⟩
    set X' : Subgroup G := Lj ⊔ Y with hX'
    have hX'H : X' ≤ H := sup_le hLjH inf_le_right
    have hYO : Y ≤ GLAPPrimeCoreOf 3 X' :=
      le_glaPPrimeCoreOf_of_le_normalizer le_sup_right (sup_le hLjY Subgroup.le_normalizer)
        (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 M))
    have htY : t ∈ Y := ⟨hTM ht, hTH ht⟩
    have hLjX : GLAPComponent 3 X' Lj := glaPComponent_of_le Nat.prime_three hLj le_sup_left hX'H
    have hconj : GLAPComponent 3 X' (GLBConj t Lj) :=
      glaPComponent_conj_of_mem hLjX ((le_sup_right : Y ≤ Lj ⊔ Y) htY)
    exact glaPComponent_unique hconj hLjX (barX_gLBConj_of_mem 3 (hYO htY) Lj)
  have hS8 : ∀ Li : Subgroup G, GLAPComponent 3 H Li → Li ≤ J → ∀ t ∈ T, GLBConj t Li ≤ J := by
    intro Li hLi hLiJ t ht
    by_contra hnot
    have hc : GLAPComponent 3 H (GLBConj t Li) := glaPComponent_conj_of_mem hLi (hTH ht)
    have hfix := hS7 _ hc (hS6 _ hc hnot).2 t⁻¹ (T.inv_mem ht)
    rw [gLBConj_inv_gLBConj] at hfix
    exact hnot (hfix ▸ hLiJ)
  set P : Subgroup G := sSup {Li | GLAPComponent 3 H Li ∧ Li ≤ J} with hP
  set Q : Subgroup G := sSup {Lj | GLAPComponent 3 H Lj ∧ ¬ Lj ≤ J} with hQ
  have hPJ : P ≤ J := sSup_le fun _ hLi => hLi.2
  have hPL : P ≤ L := sSup_le fun _ hLi => le_sSup hLi.1
  have hQL : Q ≤ L := sSup_le fun _ hLj => le_sSup hLj.1
  have hLPQ : L ≤ P ⊔ Q := sSup_le fun Li hLi => by
    by_cases hLiJ : Li ≤ J
    · exact le_sup_of_le_left (le_sSup ⟨hLi, hLiJ⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hLi, hLiJ⟩)
  have hLNP : L ≤ Subgroup.normalizer (P : Set G) := by
    have hle : ∀ l ∈ L, GLBConj l P ≤ P := fun l hl => gLBConj_sSup_le fun Li hLi =>
      le_sSup ⟨glaPComponent_conj_of_mem hLi.1 (hLH hl),
        (gLBConj_mono l hLi.2).trans (gLBConj_eq_of_mem_normalizer (hLNJ hl)).le⟩
    intro l hl
    rw [mem_normalizer_iff_gLBConj_eq]
    refine le_antisymm (hle l hl) ?_
    have := gLBConj_mono l (hle l⁻¹ (L.inv_mem hl))
    rwa [gLBConj_gLBConj_inv] at this
  have hJbar : barX 3 L J ≤ barX 3 L P := by
    refine le_of_perfect_le_sup (Qb := barX 3 L Q) ?_ ?_ ?_ ?_ ?_
    · rw [← barX_commutator 3 hJL hJL, jLayer_perfect H]
    · rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hPL hQL]
      exact barX_le_barX (hJL.trans hLPQ)
    · rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hQL]
      refine sSup_le fun Lj hLj => ?_
      have hLjL : Lj ≤ L := le_sSup hLj.1
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_le_iff hLjL]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hS6 Lj hLj.1 hLj.2).1
    · exact barX_le_normalizer (hQL.trans hLNP)
    · exact barX_le_normalizer (hJL.trans hLNP)
  have hJP : J ≤ P := by
    refine iSup₂_le fun g hg => gLBConj_sSup_le fun K'' hK'' => ?_
    have hgL : g ∈ L := hg
    have hc : GLAPComponent 3 (GLBConj g (H ⊓ Cg a)) (GLBConj g K'') :=
      CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK'' g
    have hle : GLBConj g K'' ≤ J :=
      (gLBConj_mono g (le_sSup hK'' : K'' ≤ K0)).trans
        (le_iSup₂ (f := fun (g : G) (_ : g ∈ L) => GLBConj g K0) g hgL)
    refine CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_le_sup Nat.prime_three hc
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 L)
      ((CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 L).trans hLNP) ?_
    intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_of_barX_le hJbar (hle hx) (hJL (hle hx))
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hyx)
  have hS10 : ∀ t ∈ T, GLBConj t J ≤ J := fun t ht =>
    (gLBConj_mono t hJP).trans (gLBConj_sSup_le fun Li hLi => hS8 Li hLi.1 hLi.2 t ht)
  intro t ht
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (hS10 t ht) ?_
  have := gLBConj_mono t (hS10 t⁻¹ (T.inv_mem ht))
  rwa [gLBConj_gLBConj_inv] at this

end TNorm

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_inf {x : G} {S₁ S₂ : Subgroup G} (h₁ : x ∈ Subgroup.normalizer (S₁ : Set G))
    (h₂ : x ∈ Subgroup.normalizer (S₂ : Set G)) : x ∈ Subgroup.normalizer ((S₁ ⊓ S₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h₁ h₂ ⊢
  intro z
  constructor
  · rintro ⟨hz1, hz2⟩
    exact ⟨(h₁ z).1 hz1, (h₂ z).1 hz2⟩
  · rintro ⟨hz1, hz2⟩
    exact ⟨(h₁ z).2 hz1, (h₂ z).2 hz2⟩

omit [Finite G] in
theorem mk_mem_barX {p : ℕ} {X S : Subgroup G} {x : G} (hxX : x ∈ X) (hxS : x ∈ S) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ ∈ barX p X S :=
  ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hxS, rfl⟩

omit [Finite G] in
theorem mk_eq_mk {p : ℕ} {X : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (h : x⁻¹ * y ∈ GLAPPrimeCoreOf p X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hx⟩ = QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hy⟩ := by
  obtain ⟨z, hz, hzxy⟩ := h
  refine QuotientGroup.eq.2 ?_
  have e : (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ = z := Subtype.ext (by simpa using hzxy.symm)
  rw [e]
  exact hz

theorem le_of_pElements {p : ℕ} (hp : p.Prime) {Y J N : Subgroup G} (hJ : GLAPComponent p Y J)
    (h : ∀ x ∈ J, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ N) : J ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hJY : J ≤ Y := hJ.1
  have h1 : CFSG.IsPComponent p (J.subgroupOf Y) :=
    ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ).2
  have h2 := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent p _ h1
  set ψ : ↥(J.subgroupOf Y) →* G := Y.subtype.comp (J.subgroupOf Y).subtype with hψ
  have hle : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p ↥(J.subgroupOf Y) ≤
      N.comap ψ := by
    refine sSup_le fun P hP z hz => ?_
    obtain ⟨k, hk⟩ := hP ⟨z, hz⟩
    refine h (ψ z) (Subgroup.mem_subgroupOf.1 z.2) ⟨k, ?_⟩
    have := congrArg (fun w : ↥P => ψ (w : ↥(J.subgroupOf Y))) hk
    simpa using this
  intro x hx
  have hz : (⟨⟨x, hJY hx⟩, hx⟩ : ↥(J.subgroupOf Y)) ∈
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p ↥(J.subgroupOf Y) := by
    rw [h2]
    exact Subgroup.mem_top _
  exact hle hz

theorem cover_transfer {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) {H : Subgroup G} (hH : InHFamily A K a H) {N : Subgroup G}
    (haT : a ∈ N) (hcov : Covers 3 H (N ⊓ H) (Lemma1115.jLayer a H)) : Covers 3 (Cg a) N K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAH : A ≤ H := hH.2.1
  have ha : a ∈ A := h.ha.1
  have haH : a ∈ H := hAH ha
  have ha3 : a ^ 3 = 1 := (elemAbelian_A h).1.2 a ha
  set O : Subgroup G := GLAPPrimeCoreOf 3 H with hO
  set Oa : Subgroup G := GLAPPrimeCoreOf 3 (Cg a) with hOa
  set X0 : Subgroup G := N ⊓ H with hX0
  set U : Subgroup G := O ⊓ Cg a with hU
  have haX0 : a ∈ X0 := ⟨haT, haH⟩
  have haCa : a ∈ Cg a := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hOH : O ≤ H := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPPrimeCoreOf 3 H
  have hOc : Nat.Coprime 3 (Nat.card O) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 H
  obtain ⟨K', hK', hbar, hKK'⟩ := exists_cover_K h hH
  have hK'J : K' ≤ Lemma1115.jLayer a H :=
    (le_sSup hK' : K' ≤ GLAPLayer 3 (H ⊓ Cg a)).trans (layer_le_jLayer H)
  have hK'Ca : K' ≤ Cg a := hK'.1.trans inf_le_right
  have hdec : ∀ k ∈ K', ∃ c ∈ X0 ⊓ Cg a, c⁻¹ * k ∈ U := by
    intro k hk
    have hkJ := hK'J hk
    obtain ⟨y, hy, hyk⟩ := exists_of_barX_le hcov hkJ (jLayer_le H hkJ)
    have hyX0 : y ∈ X0 := hy
    have hkCa : k ∈ Cg a := hK'Ca hk
    have hka : a * k * a⁻¹ = k := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hkCa
      rw [← this]; group
    have haN : a ∈ Subgroup.normalizer ((X0 ⊓ O : Subgroup G) : Set G) :=
      mem_normalizer_inf (Subgroup.le_normalizer haX0) (hHO haH)
    have hcop : Nat.Coprime 3 (Nat.card (X0 ⊓ O : Subgroup G)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right) hOc
    have hg : y⁻¹ * (a * y * a⁻¹) ∈ X0 ⊓ O := by
      refine ⟨X0.mul_mem (X0.inv_mem hyX0) (X0.mul_mem (X0.mul_mem haX0 hyX0) (X0.inv_mem haX0)), ?_⟩
      set o := y⁻¹ * k with ho
      have hoO : o ∈ O := hyk
      have hao : a * o⁻¹ * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hHO haH) o⁻¹).1 (O.inv_mem hoO)
      have e : y⁻¹ * (a * y * a⁻¹) = o * (a * o⁻¹ * a⁻¹) := by
        have hk' : k = y * o := by rw [ho]; group
        have : a * k * a⁻¹ = k := hka
        rw [hk'] at this
        calc y⁻¹ * (a * y * a⁻¹) = y⁻¹ * (a * (y * o) * a⁻¹) * (a * o⁻¹ * a⁻¹) := by group
          _ = y⁻¹ * (y * o) * (a * o⁻¹ * a⁻¹) := by rw [this]
          _ = o * (a * o⁻¹ * a⁻¹) := by group
      rw [e]
      exact O.mul_mem hoO hao
    obtain ⟨n, hn, hfix⟩ := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.exists_fixed_in_coset
      Nat.prime_three ha3 haN hcop hg
    have hcomm' : a * (y * n) = y * n * a :=
      calc a * (y * n) = a * (y * n) * a⁻¹ * a := by group
        _ = y * n * a := by rw [hfix]
    have hcy : y * n ∈ Cg a := Subgroup.mem_centralizer_singleton_iff.2 hcomm'.symm
    refine ⟨y * n, ⟨X0.mul_mem hyX0 hn.1, hcy⟩, ?_, ?_⟩
    · have e : (y * n)⁻¹ * k = n⁻¹ * (y⁻¹ * k) := by group
      rw [e]
      exact O.mul_mem (O.inv_mem hn.2) hyk
    · exact (Cg a).mul_mem ((Cg a).inv_mem hcy) hkCa
  set W' : Subgroup G := X0 ⊓ Cg a with hW'
  have hW'U : W' ≤ Subgroup.normalizer (U : Set G) := fun w hw =>
    mem_normalizer_inf (hHO hw.1.2) (Subgroup.le_normalizer hw.2)
  have hK'NU : K' ≤ Subgroup.normalizer (U : Set G) := by
    intro k hk
    obtain ⟨c, hc, hcu⟩ := hdec k hk
    have e : k = c * (c⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hW'U hc) (Subgroup.le_normalizer hcu)
  have hUCa : U ≤ Cg a := inf_le_right
  have hW'Ca : W' ≤ Cg a := inf_le_right
  have hOaCa : Oa ≤ Cg a :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le 3 (Cg a)
  have hKbarN : barX 3 (Cg a) K ≤ Subgroup.normalizer (barX 3 (Cg a) U : Set _) := by
    rw [← hbar]
    exact barX_le_normalizer hK'NU
  have hUc : Nat.Coprime 3 (Nat.card (barX 3 (Cg a) U)) := by
    have h1 : Nat.card (barX 3 (Cg a) U) ∣ Nat.card (U.subgroupOf (Cg a)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (U.subgroupOf (Cg a)) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUCa).toEquiv
    have h3 : Nat.card U ∣ Nat.card O := Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right (h1.trans (h2 ▸ h3)) hOc
  have hcomm : ⁅barX 3 (Cg a) K, barX 3 (Cg a) U⁆ = ⊥ :=
    commutator_eq_bot_of_normalizes_coprime h.hK.2.2.1
      (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hUc hKbarN
  have hkey : ∀ s ∈ K, (∃ j : ℕ, s ^ 3 ^ j = 1) → s ∈ W' ⊔ Oa := by
    rintro s hsK ⟨j, hj⟩
    have hsCa : s ∈ Cg a := h.hK.1 hsK
    obtain ⟨k', hk', hkk⟩ := hKK' s hsK
    obtain ⟨w, hw, hwu⟩ := hdec k' hk'
    have hwCa : w ∈ Cg a := hw.2
    have hk'Ca : k' ∈ Cg a := hK'Ca hk'
    have huCa : w⁻¹ * k' ∈ Cg a := (Cg a).mul_mem ((Cg a).inv_mem hwCa) hk'Ca
    set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg a)) with hπ
    have hs : π ⟨s, hsCa⟩ = π ⟨w, hwCa⟩ * π ⟨w⁻¹ * k', huCa⟩ := by
      rw [← map_mul]
      refine (mk_eq_mk _ hsCa ?_).symm
      show (w * (w⁻¹ * k'))⁻¹ * s ∈ _
      rw [show (w * (w⁻¹ * k'))⁻¹ * s = k'⁻¹ * s by group]
      exact hkk
    have hsu : Commute (π ⟨s, hsCa⟩) (π ⟨w⁻¹ * k', huCa⟩) := by
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm (mk_mem_barX hsCa hsK)
      exact (Subgroup.mem_centralizer_iff.1 hc _ (mk_mem_barX huCa hwu)).symm
    set ub := π ⟨w⁻¹ * k', huCa⟩ with hub
    set sb := π ⟨s, hsCa⟩ with hsb
    set wb := π ⟨w, hwCa⟩ with hwb
    have hwe : wb ^ orderOf ub = sb ^ orderOf ub := by
      have hw' : wb = sb * ub⁻¹ := by rw [hs]; group
      rw [hw', (hsu.inv_right).mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one]
    have hs3 : sb ^ 3 ^ j = 1 := by
      rw [hsb, ← map_pow]
      have e : (⟨s, hsCa⟩ : ↥(Cg a)) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hj)
      rw [e, map_one]
    have hcop : (orderOf ub).gcd (orderOf sb) = 1 := by
      have h1 : orderOf sb ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hs3
      have h2 : orderOf ub ∣ Nat.card (barX 3 (Cg a) U) :=
        Subgroup.orderOf_dvd_natCard _ (mk_mem_barX huCa hwu)
      have h3 : Nat.Coprime (orderOf ub) (3 ^ j) :=
        Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left h2 hUc.symm)
      exact Nat.Coprime.coprime_dvd_right h1 h3
    have hmem : sb ∈ Subgroup.zpowers (sb ^ orderOf ub) := mem_zpowers_pow_iff.2 hcop
    have hsW : sb ∈ barX 3 (Cg a) W' := by
      have hwbar : wb ^ orderOf ub ∈ barX 3 (Cg a) W' :=
        Subgroup.pow_mem _ (mk_mem_barX hwCa hw) _
      rw [hwe] at hwbar
      exact (Subgroup.zpowers_le.2 hwbar) hmem
    exact CFSG.HardMathSupport.Solomon.Coordinator.i183_mem_sup_of_mk_mem hsW
  have hKW : K ≤ W' ⊔ Oa := le_of_pElements Nat.prime_three h.hK hkey
  have hW'N : W' ≤ N := inf_le_left.trans inf_le_left
  calc barX 3 (Cg a) K ≤ barX 3 (Cg a) (W' ⊔ Oa) := barX_le_barX hKW
    _ = barX 3 (Cg a) W' := by
      rw [CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_sup hW'Ca hOaCa,
        (CFSG.HardMathSupport.Solomon.Coordinator.i183_barX_eq_bot_iff hOaCa).2 le_rfl, sup_bot_eq]
    _ ≤ barX 3 (Cg a) N := barX_le_barX hW'N

theorem input1115TransferInv_holds :
    ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
      (_h : Cex117 G m 3 B M E A a K) (H : Subgroup G), InHFamily A K a H →
      ∀ T0 : Subgroup G, A ≤ Subgroup.normalizer (T0 : Set G) →
        Covers 3 H (Subgroup.normalizer (T0 : Set G) ⊓ H) (Lemma1115.jLayer a H) →
        Covers 3 (Cg a) (Subgroup.normalizer (T0 : Set G)) K :=
  fun h _ hH _ hAT0 hcov => cover_transfer h hH (hAT0 h.ha.1) hcov

end Transfer

theorem input1115Chain_of_inputs (h111 : Prop111Statement) : Lemma1115.Input1115Chain := by
  intro G _ _ m B M E A a K h H hH hcov
  have hcov' : Covers 3 H (M ⊓ H) (Lemma1115.jLayer a H) := by
    show barX 3 H (Lemma1115.jLayer a H) ≤ barX 3 H (M ⊓ H)
    rw [barX_inf_self]
    exact hcov
  have hKM := cover_transfer h hH ((elemAbelian_A h).2 h.ha.1) hcov'
  have hOa : GLAPPrimeCoreOf 3 (Cg a) ≤ M := h111 h.toCex117Base.toSec11 h.ha.1 h.ha.2
  intro k hk
  obtain ⟨y, hy, hyk⟩ := exists_of_barX_le hKM hk (h.hK.1 hk)
  have := M.mul_mem hy (hOa hyk)
  simpa using this

section Gamma

variable {G : Type} [Group G] [Finite G]

theorem glbCore_barX_le {p : ℕ} (hp : p.Prime) {C B : Subgroup G} (k : ℕ) (hB : IsPGroup p ↥B)
    (hBC : B ≤ C) : GLBCore p k (barX p C B) ≤ barX p C (GLBCore p k B) := by
  refine sSup_le ?_
  rintro _ ⟨Q, hQB, hQk, rfl⟩
  obtain ⟨E, hEB, hEQ, hEr⟩ := exists_le_barX_eq hp hB hBC hQB
  have hEp : IsPGroup p ↥E := hB.to_le hEB
  rw [← hEQ]
  refine (normalizer_barX_le hp hEp (hEB.trans hBC)).trans (barX_le_barX ?_)
  exact le_sSup ⟨E, hEB, by rw [hEr]; exact hQk, rfl⟩

end Gamma

theorem lemma1115_iii_of_gamma (h1111 : Lemma1111Statement) (h113 : Lemma113_iStatement)
    (h104v : Lemma104_vStatement) (h111 : Prop111Statement)
    (hG : Lemma1115.Input1115Gamma) : Lemma1115_iiiStatement :=
  lemma1115_iii_of_inputs h1111 h113 h104v hG (input1115Chain_of_inputs h111)

theorem lemma1115_ii_of_pushUp
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement) (h1114 : Lemma1114Statement)
    (hPU : Lemma1115.Input1115PushUp) : Lemma1115_iiStatement := by
  intro G _ _ m p B M E A a K h H T hH hT
  obtain ⟨rfl, -, -⟩ := h1111 h
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hcopT : Nat.Coprime 3 (Nat.card T) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hTM : T ≤ GLAPPrimeCoreOf 3 M :=
    le_core_of_lemma1114 h1114 h hcopT hT.2.2.1
  have hTN : T ≤ Subgroup.normalizer (Lemma1115.jLayer a H : Set G) :=
    input1115TNorm_of_inputs hS h1112 h1114 h H hH T hT hTM
  obtain ⟨T0, hT0ne, hchar, hcov⟩ := hPU h H hH T hT hTN
  have hT0p : IsPGroup 2 ↥T0 := Lemma1114.isPGroup_of_le' hT2 hchar.1
  have hAT0 : A ≤ Subgroup.normalizer (T0 : Set G) := fun x hx =>
    Lemma1115.mem_normalizer_of_isCharIn hchar (hT.2.2.1 hx)
  exact ⟨T0, hT0ne, hchar, ⟨⟨T0, hT0ne, hT0p, rfl⟩, hAT0,
    input1115TransferInv_holds h H hH T0 hAT0 hcov⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1115

end
