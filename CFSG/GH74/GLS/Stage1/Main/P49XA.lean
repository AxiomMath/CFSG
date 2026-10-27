module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement Pointwise

section XB

theorem not_isCyclic_sylow_quasisimple49 {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (S : Sylow 2 Q) : ¬ IsCyclic ↥(S : Subgroup Q) := by
  intro hScyc
  obtain ⟨-, hmul, -, ⟨-, hodd, -, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement S hScyc
  set N := CFSG.pPrimeCore 2 Q with hN
  have hcycq : IsCyclic (Q ⧸ N) := by
    have := hScyc
    refine isCyclic_of_surjective ((QuotientGroup.mk' N).comp (S : Subgroup Q).subtype) ?_
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    have hq : q ∈ (N : Set Q) * (S : Set Q) := by
      rw [hmul]
      trivial
    obtain ⟨n, hn, s, hs, rfl⟩ := hq
    refine ⟨⟨s, hs⟩, ?_⟩
    have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    change QuotientGroup.mk' N s = QuotientGroup.mk' N (n * s)
    rw [map_mul, h1, one_mul]
  have hNtop : N = ⊤ := by
    have hperf : commutator Q = ⊤ := hQ.1.commutator_eq_top
    rw [eq_top_iff, ← hperf, _root_.commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (IsCyclic.commGroup.mul_comm _ _)
  have hQodd : Odd (Nat.card Q) := by
    have : Nat.card N = Nat.card Q := by rw [hNtop]; exact Subgroup.card_top
    rw [← this]
    exact hodd
  have hsolv : Group.IsSolvable Q := CFSG.Milestones.odd_order_solvable hQodd
  have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q hsolv


theorem isSylowOf_inf_subnormal49 {A : Type*} [Group A] [Finite A] {P H : Subgroup A}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) (hH : H.IsSubnormal) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ H) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction hH with
  | top =>
    simpa using hP
  | step A' K hAK _ hAn ih =>
    have hKN : K ≤ normalizer (A' : Set A) := (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).1 hAn
    have h1 := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer ih hAK hKN
    rwa [inf_assoc, inf_eq_right.2 hAK] at h1

theorem isSylowOf_inf_isPCompIn49 {G : Type} [Group G] [Finite G] {z : G} {S L : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cz z)) (hL : IsPCompIn 2 (Cz z) L) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hSA : CFSG.ABGLocalTools.IsSylowOf 2 (S.subgroupOf (Cz z)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · rw [← hQ]; exact Q.isPGroup'
    · rw [Subgroup.relIndex_top_right, ← hQ]; exact Q.not_dvd_index
  obtain ⟨Kc, -, hsub, -, -⟩ := hL.2
  have h1 := isSylowOf_inf_subnormal49 hSA hsub
  have h2 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (Cz z)).2 h1
  have e1 : (S.subgroupOf (Cz z) ⊓ L.subgroupOf (Cz z)).map (Cz z).subtype = S ⊓ L := by
    ext g
    constructor
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨ha1, ha2⟩
    · rintro ⟨hgS, hgL⟩
      exact ⟨⟨g, hS.le hgS⟩, ⟨hgS, hgL⟩, rfl⟩
  have e2 : (L.subgroupOf (Cz z)).map (Cz z).subtype = L := Subgroup.map_subgroupOf_eq_of_le hL.1
  rw [e1, e2] at h2
  exact h2


theorem exists_conj_mem_sylow49 {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) : ∃ g : G, ∀ q ∈ Q, g⁻¹ * q * g ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hQT⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S T
  refine ⟨g, fun q hq => ?_⟩
  have h := hQT hq
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa [MulAut.smul_def, mul_assoc] using h

theorem pRank_le_one_of_inv49 {H : Type*} [Group H] [Finite H] (c : H)
    (hH : ∀ t : H, t * t = 1 → t = 1 ∨ t = c) : CFSG.pRank 2 H ≤ 1 := by
  apply csSup_le'
  rintro k ⟨E, hE, hk⟩
  have hsub : (E : Set H) ⊆ {1, c} := by
    intro e he
    have h2 : e ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) e he
    rcases hH e (by rwa [sq] at h2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcard : Nat.card E ≤ 2 := by
    have h1 : Nat.card E = (E : Set H).ncard := Nat.card_coe_set_eq _
    rw [h1]
    calc (E : Set H).ncard ≤ ({1, c} : Set H).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le 1 {c}).trans ?_
        simp [Set.ncard_singleton]
  by_contra hk1
  push Not at hk1
  have : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  omega

theorem one_le_pRank49 {H : Type*} [Group H] [Finite H] {t : H} (ht : t * t = 1) (ht1 : t ≠ 1) :
    1 ≤ CFSG.pRank 2 H := by
  have ht2 : t ^ 2 = 1 := by rw [sq]; exact ht
  have hE : IsElementaryAbelian 2 ↥(Subgroup.zpowers t) := CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have hcard : Nat.card ↥(Subgroup.zpowers t) = 2 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one]
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨Subgroup.zpowers t, hE, hcard⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

end XB

section XD

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_of_le49 {H H' K : Subgroup G} (h : IsPCompIn 2 H K) (hKH' : K ≤ H')
    (hH'H : H' ≤ H) : IsPCompIn 2 H' K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hKH', ?_⟩
  have h2 : K.subgroupOf H ≤ H'.subgroupOf H := fun x hx => hKH' hx
  have h3 := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 h.2 h2
  exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hH'H 2
    Nat.prime_two).mp h3

theorem pLayerOf_self49 {X K : Subgroup G} (hK : IsPCompIn 2 X K) : pLayerOf 2 K = K :=
  le_antisymm (sSup_le fun _ hL => hL.1) (le_sSup (isPCompIn_of_le49 hK le_rfl hK.1))

theorem pumpUp_self49 {x : G} {K : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K) :
    pumpUp 2 K x = K := by
  unfold pumpUp
  rw [inf_eq_left.2 hK.1, pLayerOf_self49 hK]
  have hn := pLayerOf_le_normalizer hK
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    have := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hn hg)
    exact this.le
  · refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
    intro k hk
    exact ⟨k, hk, by simp⟩

theorem eq_of_isPCompIn_self49 {K K' : Subgroup G} (hK : IsPCompIn 2 K K) (hK' : IsPCompIn 2 K K') :
    K' = K := by
  have h := (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation
    2 Nat.prime_two (K'.subgroupOf K) (K.subgroupOf K) hK'.2 hK.2).1
    (fun a _ => Subgroup.mem_subgroupOf.2 a.2)
  have h4 := Subgroup.subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr hK'.1, inf_eq_left.mpr hK.1] at h4

theorem pumpUpLT_self49 {x t : G} {K K' : Subgroup G} (hK : IsPCompIn 2 (centralizer ({x} : Set G)) K)
    (hinv : ∀ s ∈ centralizer ({x} : Set G) ⊓ centralizerSection K (pPrimeCoreOf 2 K),
      orderOf s = 2 → s = x) (h : PumpUpLT 2 x K t K') : t = x ∧ K' = K := by
  obtain ⟨-, hILo', htC, htS, hK'⟩ := h
  have ht : t = x := hinv t ⟨htC, htS⟩ hILo'.1
  rw [ht, pumpUp_self49 hK] at hK'
  exact ⟨ht, eq_of_isPCompIn_self49 (isPCompIn_of_le49 hK le_rfl hK.1) hK'⟩

end XD

section XQ

theorem zmod_two_mul_eq_zero49 {n : ℕ} [NeZero n] (i : ZMod (2 * n)) (h : 2 * i = 0) :
    i = 0 ∨ i = (n : ZMod (2 * n)) := by
  have hn : n ≠ 0 := NeZero.ne n
  have h2n : 2 * n ≠ 0 := by omega
  have : NeZero (2 * n) := ⟨h2n⟩
  have hk : (i.val : ZMod (2 * n)) = i := ZMod.natCast_zmod_val i
  have hlt : i.val < 2 * n := ZMod.val_lt i
  have h1 : ((2 * i.val : ℕ) : ZMod (2 * n)) = 0 := by
    push_cast
    rw [hk]
    exact h
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨t, ht⟩ := h1
  have hk' : i.val = n * t := by
    have : 2 * i.val = 2 * (n * t) := by rw [ht]; ring
    omega
  have ht2 : t < 2 := by
    by_contra hge
    push Not at hge
    have : n * 2 ≤ n * t := Nat.mul_le_mul_left n hge
    omega
  interval_cases t
  · left
    rw [← hk]
    simp [hk']
  · right
    rw [← hk, hk']
    simp


theorem quatModel_central49 {n : ℕ} [NeZero n] (Q₀ : Subgroup (QuaternionGroup n))
    (hnc : ¬ IsCyclic ↥Q₀) {c : QuaternionGroup n} (hc : ∀ x ∈ Q₀, c * x = x * c) :
    c * c = 1 := by
  have hn : n ≠ 0 := NeZero.ne n
  have h2n : 2 * n ≠ 0 := by omega
  have : NeZero (2 * n) := ⟨h2n⟩
  have hA : ∃ j, QuaternionGroup.xa j ∈ Q₀ := by
    by_contra hcon
    push Not at hcon
    apply hnc
    have hle : Q₀ ≤ Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup n) := by
      intro x hx
      cases x with
      | a i =>
        refine ⟨(i.val : ℤ), ?_⟩
        show (QuaternionGroup.a 1 : QuaternionGroup n) ^ (i.val : ℤ) = QuaternionGroup.a i
        rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      | xa i => exact absurd hx (hcon i)
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨j₀, hj₀⟩ := hA
  have hB : ∃ i, QuaternionGroup.a i ∈ Q₀ ∧ 2 * i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnc
    have hinv : (QuaternionGroup.xa j₀)⁻¹ = QuaternionGroup.xa ((n : ZMod (2 * n)) + j₀) := rfl
    have hle : Q₀ ≤ Subgroup.zpowers (QuaternionGroup.xa j₀ : QuaternionGroup n) := by
      intro x hx
      cases x with
      | a i =>
        have h2 := hcon i hx
        rcases zmod_two_mul_eq_zero49 i h2 with h | h
        · rw [h, ← QuaternionGroup.one_def]; exact one_mem _
        · rw [h, ← QuaternionGroup.xa_sq j₀]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
      | xa k =>
        have hprod : (QuaternionGroup.xa j₀)⁻¹ * QuaternionGroup.xa k ∈ Q₀ :=
          mul_mem (inv_mem hj₀) hx
        rw [hinv, QuaternionGroup.xa_mul_xa] at hprod
        have h2 := hcon _ hprod
        have e : (2 : ZMod (2 * n)) * ((n : ZMod (2 * n)) + k - ((n : ZMod (2 * n)) + j₀)) =
            2 * (k - j₀) := by ring
        rw [e] at h2
        rcases zmod_two_mul_eq_zero49 (k - j₀) h2 with h | h
        · have : k = j₀ := sub_eq_zero.1 h
          rw [this]; exact Subgroup.mem_zpowers _
        · have : k = (n : ZMod (2 * n)) + j₀ := by rw [← h]; ring
          rw [this, ← hinv]; exact inv_mem (Subgroup.mem_zpowers _)
    exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  obtain ⟨i₀, hi₀, hi₀ne⟩ := hB
  cases c with
  | a m =>
    have h1 := hc _ hj₀
    rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
    have h2 : QuaternionGroup.xa (j₀ - m) = (QuaternionGroup.xa (j₀ + m) : QuaternionGroup n) := h1
    have h3 : j₀ - m = j₀ + m := by simpa using h2
    have h4 : 2 * m = 0 := by
      have : (2 : ZMod (2 * n)) * m = (j₀ + m) - (j₀ - m) := by ring
      rw [this, ← h3]; ring
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
    rw [← two_mul]; exact h4
  | xa m =>
    exfalso
    have h1 := hc _ hi₀
    rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at h1
    have h2 : QuaternionGroup.xa (m + i₀) = (QuaternionGroup.xa (m - i₀) : QuaternionGroup n) := h1
    have h3 : m + i₀ = m - i₀ := by simpa using h2
    apply hi₀ne
    have : (2 : ZMod (2 * n)) * i₀ = (m + i₀) - (m - i₀) := by ring
    rw [this, h3]; ring

end XQ

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
