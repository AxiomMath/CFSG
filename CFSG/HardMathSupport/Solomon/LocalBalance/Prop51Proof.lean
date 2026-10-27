module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.Open.StatedCenterThree
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance
namespace Prop51Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

section CenterThreeSec

open CFSG.Assembly.LowTwoRank Matrix

namespace CenterThree

variable {K : Type} [Field K]

export CFSG.Open.StatedCenterThree (card_rootsOfUnity_three card_center_statedSL_three
  eq_diagonal_of_commute cyc3 cyc3_mul_transpose transpose_mul_cyc3 cyc3GL
  eq_of_diagonal_commute_cyc3 cyc3GL_mem diagGL diagGL_mem scalar_mem two_le_of_card_eq_sq
  sq_sub_one_eq exists_orderOf_eq card_center_statedSU_three)

end CenterThree

end CenterThreeSec

theorem card_center_of_isSLThreeEps {Y : Type*} [Group Y] (h : IsSLThreeEps Y) :
    Nat.card (Subgroup.center Y) = 3 := by
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hK, hq, -, ⟨e⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CenterThree.card_center_statedSL_three (by omega)
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CenterThree.card_center_statedSU_three hK (by omega)

section Generic

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_aux {A N : Subgroup G} (hAN : A ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (A ⊔ N : Subgroup G) * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem isPGroup_three_of_isElemAbelian {E : Subgroup G} (h : IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup h

theorem card_eq_pow_of_isElemAbelian [Finite G] {E : Subgroup G} (h : IsElemAbelian 3 E) :
    ∃ k, Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (isPGroup_three_of_isElemAbelian h).exists_card_eq

theorem three_le_pRank_of_le_card [Finite G] {E : Subgroup G} (h : IsElemAbelian 3 E)
    (hc : 27 ≤ Nat.card E) : 3 ≤ CFSG.Open.pRank 3 E := by
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian h
  rw [pRank_eq_of_card Nat.prime_three h hk]
  by_contra hlt
  have h2 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem orderOf_eq_three_of_pow {b : G} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) : orderOf b = 3 :=
  orderOf_eq_prime hb3 hb1

theorem nine_le_card_of_not_le_zpowers [Finite G] {E : Subgroup G} {b : G}
    (h : IsElemAbelian 3 E) (hb : b ∈ E) (hb1 : b ≠ 1) (hn : ¬ E ≤ Subgroup.zpowers b) :
    9 ≤ Nat.card E := by
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian h
  have hb3 : b ^ 3 = 1 := h.2 b hb
  have hcz : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow hb3 hb1]
  have hle : Subgroup.zpowers b ≤ E := (Subgroup.zpowers_le).2 hb
  have hge : 3 ≤ Nat.card E := hcz ▸ Subgroup.card_le_of_le hle
  by_contra hlt
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 3 ^ k ≤ 3 := by
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have heq : Subgroup.zpowers b = E :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hk]; exact h3)
  exact hn heq.ge

theorem mem_zpowers_of_mem_zpowers_ne_one [Finite G] {b x : G} (hb3 : b ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers b) (hx1 : x ≠ 1) : b ∈ Subgroup.zpowers x := by
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hx
    exact hx1 hx
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).2 hx
  have hc1 : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow hb3 hb1]
  have hc2 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_three_of_pow hx3 hx1]
  have := Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
  rw [this]
  exact Subgroup.mem_zpowers b

theorem exists_mul_of_mem_sup_of_le_normalizer {A N : Subgroup G}
    (h : A ≤ Subgroup.normalizer (N : Set G)) {g : G} (hg : g ∈ A ⊔ N) :
    ∃ a ∈ A, ∃ n ∈ N, g = a * n := by
  have hg' : g ∈ ((A ⊔ N : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A N h] at hg'
  obtain ⟨a, ha, n, hn, rfl⟩ := hg'
  exact ⟨a, ha, n, hn, rfl⟩

theorem card_le_three_mul_card_inf [Finite G] {B2 B1 A1 L1 : Subgroup G}
    (hB2 : B2 ≤ B1 ⊔ L1) (hA1B1 : A1 ≤ B1) (hB1 : B1 ≤ Subgroup.normalizer (L1 : Set G))
    (hidx : Nat.card B1 = 3 * Nat.card A1) :
    Nat.card B2 ≤ 3 * Nat.card (B2 ⊓ (A1 ⊔ L1) : Subgroup G) := by
  set M : Subgroup G := B1 ⊔ L1 with hM
  set N : Subgroup G := A1 ⊔ L1 with hN
  have hNM : N ≤ M := sup_le_sup_right hA1B1 _
  have hr : N.relIndex M * Nat.card N = Nat.card M := by
    have := Subgroup.relIndex_mul_card N M
    rwa [inf_of_le_left hNM] at this
  have h1 := card_sup_mul_card_inf_aux hB1
  have h2 := card_sup_mul_card_inf_aux (hA1B1.trans hB1)
  have h3 : Nat.card (A1 ⊓ L1 : Subgroup G) ≤ Nat.card (B1 ⊓ L1 : Subgroup G) :=
    Subgroup.card_le_of_le (inf_le_inf_right _ hA1B1)
  have hposN : 0 < Nat.card N := Nat.card_pos
  have hposB : 0 < Nat.card (B1 ⊓ L1 : Subgroup G) := Nat.card_pos
  have hr3 : N.relIndex M ≤ 3 := by
    have key : N.relIndex M * Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G) =
        3 * Nat.card N * Nat.card (A1 ⊓ L1 : Subgroup G) := by
      rw [hr]
      calc Nat.card M * Nat.card (B1 ⊓ L1 : Subgroup G) = Nat.card B1 * Nat.card L1 := h1
        _ = 3 * (Nat.card A1 * Nat.card L1) := by rw [hidx]; ring
        _ = 3 * (Nat.card N * Nat.card (A1 ⊓ L1 : Subgroup G)) := by rw [h2]
        _ = _ := by ring
    have hle : N.relIndex M * (Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G)) ≤
        3 * (Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G)) := by
      calc N.relIndex M * (Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G))
          = N.relIndex M * Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G) := by ring
        _ = 3 * Nat.card N * Nat.card (A1 ⊓ L1 : Subgroup G) := key
        _ ≤ 3 * Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G) := Nat.mul_le_mul_left _ h3
        _ = 3 * (Nat.card N * Nat.card (B1 ⊓ L1 : Subgroup G)) := by ring
    exact Nat.le_of_mul_le_mul_right hle (Nat.mul_pos hposN hposB)
  have hne : N.relIndex M ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h4 : N.relIndex B2 ≤ N.relIndex M := Subgroup.relIndex_le_of_le_right hB2 hne
  have h5 := Subgroup.relIndex_mul_card N B2
  rw [inf_comm] at h5
  calc Nat.card B2 = N.relIndex B2 * Nat.card (B2 ⊓ N : Subgroup G) := h5.symm
    _ ≤ 3 * Nat.card (B2 ⊓ N : Subgroup G) :=
        Nat.mul_le_mul_right _ (h4.trans hr3)

end Generic

section Comp

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimePOf_le_self (p : ℕ) (L : Subgroup G) : oPrimePOf p L ≤ L :=
  Subgroup.map_subtype_le _

theorem isQuasisimple_barOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (h : GLAPComponent p X L) :
    CFSG.Open.IsQuasisimple (barOf p L) := by
  have h1 := quotEquivBarX hp h.1 h.2.1
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv h1 h.2.2.1.2.2

theorem not_le_gLAPPrimeCoreOf_of_component {p : ℕ} (_hp : p.Prime) {X L : Subgroup G}
    (h : GLAPComponent p X L) : ¬ L ≤ GLAPPrimeCoreOf p X := by
  intro hle
  have hbot : barX p X L = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hkk⟩ := hle ((Subgroup.mem_subgroupOf).1 hk)
    have : k' = k := Subtype.ext hkk
    subst this
    exact (QuotientGroup.eq_one_iff k').2 hk'
  have h3 : IsComponentOf (barX p X L) ⊤ := h.2.2.1
  rw [hbot] at h3
  obtain ⟨-, -, -, hsimple⟩ := h3
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem le_gLAPPrimeCoreOf_of_coprime_of_isSubnormal {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (hsn : IsSubnormal L X) (hc : ¬ p ∣ Nat.card L) : L ≤ GLAPPrimeCoreOf p X := by
  have h1 : L ≤ GLAPPrimeCoreOf p L := by
    intro y hy
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    have hcop : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥L)) := by
      rw [Subgroup.card_top]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hc
    have hmem : (⊤ : Subgroup ↥L) ∈ {N : Subgroup ↥L | N.Normal ∧ Nat.Coprime p (Nat.card N)} :=
      ⟨inferInstance, hcop⟩
    exact (le_sSup hmem : (⊤ : Subgroup ↥L) ≤ _) (Subgroup.mem_top _)
  exact h1.trans (CFSG.HardMathSupport.Solomon.LocalBalance.glaPPrimeCoreOf_le_of_isSubnormal p hsn)

omit [Finite G] in
theorem normalizer_le_normalizer_gLAPPrimeCoreOf (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

omit [Finite G] in
theorem normalizer_le_normalizer_oPrimePOf (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (oPrimePOf p L : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ y ∈ oPrimePOf p L,
      g * y * g⁻¹ ∈ oPrimePOf p L := by
    intro g hg y hy
    obtain ⟨y', hy', rfl⟩ := hy
    have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥L) y' ∈ CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) := hy'
    let ψ : (↥L ⧸ GLAPPrimeCore p ↥L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) :=
      (barAut p L ⟨g, hg⟩ : MulAut _)
    have hψ := CFSG.pCore_map_iso p ψ
    have hψmem : ψ (QuotientGroup.mk' (GLAPPrimeCore p ↥L) y') ∈
        CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) := by
      rw [← hψ]
      exact ⟨_, hmem, rfl⟩
    have hbar : ψ (QuotientGroup.mk' (GLAPPrimeCore p ↥L) y') =
        QuotientGroup.mk' (GLAPPrimeCore p ↥L) (L.normalizerMonoidHom ⟨g, hg⟩ y') :=
      barAut_mk p L ⟨g, hg⟩ y'
    rw [hbar] at hψmem
    refine ⟨L.normalizerMonoidHom ⟨g, hg⟩ y', hψmem, ?_⟩
    simp
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key g hg y hy, fun hy => by
    have := key g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem normal_le_center_or_eq_top_aux {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) (hN : N.Normal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let qt := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map qt).Normal := Subgroup.Normal.map hN qt (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ qt.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq qt N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem pCore_le_center_of_isQuasisimple {p : ℕ} (hp : p.Prime) {Q : Type*} [Group Q] [Finite Q]
    (hq : CFSG.Open.IsQuasisimple Q) : CFSG.pCore p Q ≤ Subgroup.center Q := by
  have : Fact p.Prime := ⟨hp⟩
  have hperf : Group.IsPerfect Q := ⟨hq.1⟩
  have := hq.2
  rcases normal_le_center_or_eq_top_aux hperf hq.2 _ CFSG.pCore_normal with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup p (CFSG.pCore p Q) := CFSG.pCore_isPGroup
    have hQ : IsPGroup p Q := fun g => by
      have hg : g ∈ CFSG.pCore p Q := h ▸ Subgroup.mem_top g
      obtain ⟨n, hn⟩ := h2 ⟨g, hg⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    have : Group.IsNilpotent Q := hQ.isNilpotent
    have : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
    exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (h : GLAPComponent p X L) {y x : G} (hy : y ∈ oPrimePOf p L) (hx : x ∈ L) :
    x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p L := by
  have hq := isQuasisimple_barOf hp h
  obtain ⟨y', hy', rfl⟩ := hy
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥L) y' ∈ CFSG.pCore p (↥L ⧸ GLAPPrimeCore p ↥L) :=
    hy'
  have hc := pCore_le_center_of_isQuasisimple hp hq hmem
  refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹ * y'⁻¹, ?_, by simp⟩
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show QuotientGroup.mk' (GLAPPrimeCore p ↥L) _ = 1
  simp only [map_mul, map_inv]
  have hcomm := (Subgroup.mem_center_iff.1 hc) (QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨x, hx⟩)
  rw [hcomm]
  group

theorem oPrimePOf_le_centralizerQuot {p : ℕ} (hp : p.Prime) {X L : Subgroup G}
    (h : GLAPComponent p X L) : oPrimePOf p L ≤ centralizerQuot L (GLAPPrimeCoreOf p L) := by
  intro y hy
  have hyL : y ∈ L := oPrimePOf_le_self p L hy
  exact ⟨Subgroup.le_normalizer hyL, le_normalizer_glaPPrimeCoreOf p L hyL,
    fun x hx => comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf hp h hy hx⟩

omit [Finite G] in
theorem barAut_eq_one_of_mem_centralizerQuot {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ centralizerQuot L (GLAPPrimeCoreOf p L)) : barAut p L ⟨g, hg.1⟩ = 1 := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAut_mk]
  show _ = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  have h1 := hg.2.2 (x : G)⁻¹ (L.inv_mem x.2)
  have h2 : ((x : G)⁻¹ * g * ((x : G)⁻¹)⁻¹ * g⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p L :=
    (GLAPPrimeCoreOf p L).inv_mem h1
  refine (Subgroup.mem_map_iff_mem L.subtype_injective).1
    (?_ : L.subtype _ ∈ GLAPPrimeCoreOf p L)
  have : L.subtype ((L.normalizerMonoidHom ⟨g, hg.1⟩ x)⁻¹ * x) =
      ((x : G)⁻¹ * g * ((x : G)⁻¹)⁻¹ * g⁻¹)⁻¹ := by
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
  rw [this]
  exact h2

omit [Finite G] in
theorem inducesFieldAut_of_mem_centralizerQuot {L : Subgroup G} {g : G}
    (hg : g ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L)) : InducesFieldAut 3 L g :=
  ⟨hg.1, Or.inl (barAut_eq_one_of_mem_centralizerQuot hg)⟩

omit [Finite G] in
theorem inducesFieldAut_of_mul {L : Subgroup G} {g a l : G} (hg : g = a * l)
    (ha : InducesFieldAut 3 L a) (hgn : g ∈ Subgroup.normalizer (L : Set G))
    (hl : l ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L)) : InducesFieldAut 3 L g := by
  obtain ⟨han, hf⟩ := ha
  refine ⟨hgn, ?_⟩
  have h1 : barAut 3 L ⟨l, hl.1⟩ = 1 := barAut_eq_one_of_mem_centralizerQuot hl
  have h2 : (⟨g, hgn⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨a, han⟩ * ⟨l, hl.1⟩ :=
    Subtype.ext hg
  rw [h2, map_mul, h1, mul_one]
  exact hf

omit [Finite G] in
theorem barX_gLBConj_eq {p : ℕ} {X T : Subgroup G} {ℓ : G} (hℓ : ℓ ∈ X) (hT : T ≤ X)
    (h : ∀ t ∈ T, ℓ * t * ℓ⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p X) :
    barX p X (GLBConj ℓ T) = barX p X T := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπdef
  have hc : ∀ (t : ↥X), (t : G) ∈ T → π ⟨ℓ, hℓ⟩ * π t = π t * π ⟨ℓ, hℓ⟩ := by
    intro t ht
    obtain ⟨c, hc1, hc2⟩ := h t ht
    have hcc : c = ⟨ℓ, hℓ⟩ * t * ⟨ℓ, hℓ⟩⁻¹ * t⁻¹ := Subtype.ext (by simpa using hc2)
    have h1 : π c = 1 := (QuotientGroup.eq_one_iff c).2 hc1
    rw [hcc, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : (π ⟨ℓ, hℓ⟩ * π t * (π ⟨ℓ, hℓ⟩)⁻¹ * (π t)⁻¹) = 1 := h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : ℓ * (y : G) * ℓ⁻¹ ∈ T := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hy)
    have hyX : ℓ * (y : G) * ℓ⁻¹ ∈ X := hT hy'
    refine ⟨⟨ℓ * y * ℓ⁻¹, hyX⟩, Subgroup.mem_subgroupOf.2 hy', ?_⟩
    have h1 := hc ⟨ℓ * y * ℓ⁻¹, hyX⟩ hy'
    have h2 : (⟨ℓ * y * ℓ⁻¹, hyX⟩ : ↥X) = ⟨ℓ, hℓ⟩ * y * ⟨ℓ, hℓ⟩⁻¹ := rfl
    rw [h2, map_mul, map_mul, map_inv] at h1 ⊢
    set a := π ⟨ℓ, hℓ⟩
    set b := π y
    have h3 : a * (a * b * a⁻¹) = a * b := by rw [h1]; group
    exact mul_left_cancel h3
  · rintro ⟨t, ht, rfl⟩
    have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    have hyX : ℓ⁻¹ * (t : G) * ℓ ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hℓ) t.2) hℓ
    refine ⟨⟨ℓ⁻¹ * t * ℓ, hyX⟩, Subgroup.mem_subgroupOf.2 (mem_gLBConj.2 (by
      have e : ℓ * (ℓ⁻¹ * (t : G) * ℓ) * ℓ⁻¹ = t := by group
      rw [e]; exact ht')), ?_⟩
    have h1 := hc t ht'
    have h2 : (⟨ℓ⁻¹ * (t : G) * ℓ, hyX⟩ : ↥X) = ⟨ℓ, hℓ⟩⁻¹ * t * ⟨ℓ, hℓ⟩ := rfl
    show π ⟨ℓ⁻¹ * (t : G) * ℓ, hyX⟩ = π t
    rw [h2, map_mul, map_mul, map_inv]
    set a := π ⟨ℓ, hℓ⟩
    set b := π t
    have h3 : a * b = b * a := h1
    calc a⁻¹ * b * a = a⁻¹ * (b * a) := by group
      _ = a⁻¹ * (a * b) := by rw [h3]
      _ = b := by group

theorem le_centralizerQuot_of_ne {p : ℕ} (hp : p.Prime) {X L L' : Subgroup G}
    (hL : GLAPComponent p X L) (hL' : GLAPComponent p X L') (hne : L ≠ L') :
    L ≤ centralizerQuot L' (GLAPPrimeCoreOf p L') := by
  intro ℓ hℓ
  have hℓX : ℓ ∈ X := hL.1 hℓ
  have hcomm : ∀ t ∈ L', ℓ * t * ℓ⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p X := fun t ht =>
    commutator_le_gLAPPrimeCore_of_ne hp hL hL' hne (Subgroup.commutator_mem_commutator hℓ ht)
  have hnorm : ℓ ∈ Subgroup.normalizer (L' : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have hX : GLBConj ℓ X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hℓX)
    have hA : GLAPComponent p X (GLBConj ℓ L') := by
      have := glaPComponent_gLBConj ℓ hL'
      rwa [hX] at this
    exact glaPComponent_uniqueAux hA hL' (barX_gLBConj_eq hℓX hL'.1 hcomm)
  refine ⟨hnorm, normalizer_le_normalizer_gLAPPrimeCoreOf p L' hnorm, fun x hx => ?_⟩
  have h1 : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ L' := by
    have : ℓ * x⁻¹ * ℓ⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.1 hnorm _).1 (L'.inv_mem hx)
    have h2 := L'.mul_mem hx this
    simpa [mul_assoc] using h2
  have h2 : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ GLAPPrimeCoreOf p X := by
    have := commutator_le_gLAPPrimeCore_of_ne hp hL' hL (Ne.symm hne)
      (Subgroup.commutator_mem_commutator hx hℓ)
    simpa [commutatorElement_def] using this
  have h3 := glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hL'.2.1
  rw [← h3]
  exact ⟨h1, h2⟩

theorem mem_of_le_sSup_components {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (S : Set (Subgroup G)) (hS : ∀ L ∈ S, GLAPComponent p X L) (hK : GLAPComponent p X K)
    (h : K ≤ sSup S) : K ∈ S := by
  by_contra hKS
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  set E : Subgroup G := ((Subgroup.centralizer
    (barX p X K : Set (↥X ⧸ GLAPPrimeCore p ↥X))).comap π).map X.subtype with hE
  have hLE : ∀ L ∈ S, L ≤ E := by
    intro L hL l hl
    have hne : L ≠ K := fun h' => hKS (h' ▸ hL)
    have hl' : l ∈ X := (hS L hL).1 hl
    refine ⟨⟨l, hl'⟩, ?_, rfl⟩
    have hcent := barX_le_centralizer (p := p) (C := X) (S := L) (T := K)
      (fun s hs t ht _ _ => by
        have := commutator_le_gLAPPrimeCore_of_ne hp (hS L hL) hK hne
          (Subgroup.commutator_mem_commutator hs ht)
        simpa [commutatorElement_def] using this)
    exact hcent ⟨⟨l, hl'⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  have hKE : K ≤ E := h.trans (sSup_le hLE)
  have hq : CFSG.Open.IsQuasisimple ↥(barX p X K) := hK.2.2.1.2.2
  have hcomm : ∀ a b : ↥(barX p X K), a * b = b * a := by
    rintro ⟨_, k1, hk1, rfl⟩ ⟨_, k2, hk2, rfl⟩
    have hk1' : (k1 : G) ∈ K := Subgroup.mem_subgroupOf.1 hk1
    obtain ⟨k1', hk1'', hk1e⟩ := hKE hk1'
    have hk1e' : k1' = k1 := Subtype.ext hk1e
    subst hk1e'
    have := Subgroup.mem_centralizer_iff.1 hk1'' (π k2) ⟨k2, hk2, rfl⟩
    exact Subtype.ext this.symm
  have hbot : commutator ↥(barX p X K) ≤ ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b)
  rw [hq.1] at hbot
  have hsub : Subsingleton ↥(barX p X K) :=
    ⟨fun a b => by
      have ha : a ∈ (⊥ : Subgroup ↥(barX p X K)) := hbot (Subgroup.mem_top a)
      have hb : b ∈ (⊥ : Subgroup ↥(barX p X K)) := hbot (Subgroup.mem_top b)
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]⟩
  have := hq.2.toNontrivial
  have : Subsingleton (↥(barX p X K) ⧸ Subgroup.center ↥(barX p X K)) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) this

theorem exists_normalized_sylow_aux {H A : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    ∃ S : Subgroup G, S ≤ H ∧ Nat.card S = 3 ^ (Nat.card H).factorization 3 ∧
      ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : A →* MulAut H := (Subgroup.normalizerMonoidHom H).comp (Subgroup.inclusion hAH)
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H φ
  obtain ⟨S, hS⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card (α := Sylow 3 H)
    (not_dvd_card_sylow 3 H)
  refine ⟨(S : Subgroup H).map H.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact Sylow.card_eq_multiplicity S
  · intro a ha s hs
    obtain ⟨t, ht, rfl⟩ := hs
    have h1 : (⟨a, ha⟩ : A) • S = S := hS ⟨a, ha⟩
    have h2 : (⟨a, ha⟩ : A) • (S : Subgroup H) = S := by
      have := congrArg (fun T : Sylow 3 H => (T : Subgroup H)) h1
      exact this
    have h3 : φ ⟨a, ha⟩ t ∈ (S : Subgroup H) := by
      rw [← h2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ ht
    refine ⟨_, h3, ?_⟩
    simp [φ]

theorem exists_fixed_ne_one {A S : Subgroup G} (hA : IsPGroup 3 A) (hS : IsPGroup 3 S)
    (hSn : S ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ∃ s ∈ S, s ≠ 1 ∧ ∀ a ∈ A, a * s * a⁻¹ = s := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : A →* MulAut S := (Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hAS)
  let _ : MulDistribMulAction A S := MulDistribMulAction.compHom S φ
  have h3 : 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hSn (Subgroup.eq_bot_of_card_eq S (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 3 hn0
  have h1fix : (1 : S) ∈ MulAction.fixedPoints A S := by
    rw [MulAction.mem_fixedPoints]
    intro a
    exact smul_one a
  obtain ⟨b, hb, hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point S h3 h1fix
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun a ha => ?_⟩
  have h1 := congrArg Subtype.val ((MulAction.mem_fixedPoints.1 hb) ⟨a, ha⟩)
  have e : (((⟨a, ha⟩ : A) • b : S) : G) = a * b * a⁻¹ := by
    show ((φ ⟨a, ha⟩ b : S) : G) = _
    simp [φ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [e] at h1
  exact h1

omit [Finite G] in
theorem isElemAbelian_zpowers_of_pow_three {x : G} (hx : x ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem exists_ne_one_mem_inf_of_isSCp {B N : Subgroup G} (hB : IsSCp 3 ⊤ B)
    (hBN : B ≤ Subgroup.normalizer (N : Set G)) (h3 : 3 ∣ Nat.card N) :
    ∃ x ∈ B ⊓ N, x ≠ 1 := by
  have hBp : IsPGroup 3 B := isPGroup_three_of_isElemAbelian hB.2.1
  obtain ⟨S, hSN, hScard, hBS⟩ := exists_normalized_sylow_aux hBp hBN
  have hS3 : IsPGroup 3 S := IsPGroup.iff_card.2 ⟨_, hScard⟩
  have hfac : 0 < (Nat.card N).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have hSne : S ≠ ⊥ := by
    intro hbot
    have : Nat.card S = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hScard] at this
    have h1 : 3 ^ (Nat.card N).factorization 3 = 3 ^ 0 := by rw [this]; rfl
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
    omega
  have hBS' : B ≤ Subgroup.normalizer (S : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hBS a ha s hs, fun hs => ?_⟩
    have := hBS a⁻¹ (inv_mem ha) _ hs
    simpa [mul_assoc] using this
  obtain ⟨s, hsS, hs1, hsfix⟩ := exists_fixed_ne_one hBp hS3 hSne hBS'
  obtain ⟨n, hn⟩ := hS3 ⟨s, hsS⟩
  have hsn : s ^ (3 ^ n) = 1 := congrArg Subtype.val hn
  have hodvd : orderOf s ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hsn
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hodvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hjo
    exact hs1 hjo
  have h3o : 3 ∣ orderOf s := by rw [hjo]; exact dvd_pow_self 3 hj0
  have hord0 : orderOf s ≠ 0 := by rw [hjo]; positivity
  set x := s ^ (orderOf s / 3) with hxdef
  have hxo : orderOf x = 3 := orderOf_pow_orderOf_div hord0 h3o
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hxS : x ∈ S := S.pow_mem hsS _
  have hxfix : ∀ a ∈ B, a * x * a⁻¹ = x := by
    intro a ha
    rw [hxdef, ← conj_pow]
    rw [show a * s * a⁻¹ = s from hsfix a ha]
  have hcB : ∀ b ∈ B, Commute b x := by
    intro b hb
    have h := hxfix b hb
    show b * x = x * b
    calc b * x = (b * x * b⁻¹) * b := by group
      _ = x * b := by rw [h]
  have hEel : IsElemAbelian 3 (B ⊔ Subgroup.zpowers x) :=
    isElemAbelian_sup_of_commute hB.2.1 (isElemAbelian_zpowers_of_pow_three hx3) (by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      exact ((hcB b hb).zpow_right k).eq.symm)
  have hEB : B ⊔ Subgroup.zpowers x = B := hB.2.2 _ le_top hEel le_sup_left
  have hxB : x ∈ B := by
    rw [← hEB]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  exact ⟨x, ⟨hxB, hSN hxS⟩, hx1⟩

theorem three_dvd_card_oPrimePOf {L : Subgroup G}
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3) : 3 ∣ Nat.card (oPrimePOf 3 L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : Subgroup.center (barOf 3 L) ≤ CFSG.pCore 3 (barOf 3 L) :=
    le_sSup (show Subgroup.center (barOf 3 L) ∈
      {K : Subgroup (barOf 3 L) | K.Normal ∧ IsPGroup 3 K} from
      ⟨inferInstance, IsPGroup.iff_card.2 ⟨1, by simpa using hZ⟩⟩)
  have h3Z : 3 ∣ Nat.card (CFSG.pCore 3 (barOf 3 L)) := by
    have := Subgroup.card_dvd_of_le hZp
    rw [hZ] at this
    exact this
  set N' : Subgroup ↥L := oPrimeP 3 ↥L with hN'
  let f : ↥N' →* ↥(CFSG.pCore 3 (barOf 3 L)) :=
    ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp N'.subtype).codRestrict _ (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) z
    exact ⟨⟨y, hz⟩, rfl⟩
  have h1 : Nat.card (CFSG.pCore 3 (barOf 3 L)) ∣ Nat.card N' := Subgroup.card_dvd_of_surjective hf
  have h2 : Nat.card (oPrimePOf 3 L) = Nat.card N' :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [h2]
  exact h3Z.trans h1

theorem inf_oPrimePOf_eq_zpowers {X B L : Subgroup G} {b : G} (hL : GLAPComponent 3 X L)
    (hZ : Nat.card (Subgroup.center (barOf 3 L)) = 3) (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hbL : b ∈ L) (hbc : ∀ y ∈ L, b * y = y * b) :
    B ⊓ oPrimePOf 3 L = Subgroup.zpowers b := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hbO : b ∈ oPrimePOf 3 L := mem_oPrimePOf_of_forall_comm hp3 hbL hbc
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hcz : Nat.card (Subgroup.zpowers b) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hle : Subgroup.zpowers b ≤ B ⊓ oPrimePOf 3 L :=
    (Subgroup.zpowers_le).2 ⟨hbB, hbO⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcz]
  have hq := isQuasisimple_barOf hp3 hL
  have hcen : ∀ y ∈ oPrimePOf 3 L, ∀ hy : y ∈ L,
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨y, hy⟩ ∈ Subgroup.center (barOf 3 L) := by
    intro y hy hyL
    have : Fact (Nat.Prime 3) := ⟨hp3⟩
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = ⟨y, hyL⟩ := Subtype.ext hyy
    subst this
    exact pCore_le_center_of_isQuasisimple hp3 hq hy'
  let g : ↥(B ⊓ oPrimePOf 3 L) → ↥(Subgroup.center (barOf 3 L)) := fun y =>
    ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨y.1, oPrimePOf_le_self 3 L y.2.2⟩,
      hcen y.1 y.2.2 _⟩
  have hginj : Function.Injective g := by
    intro y1 y2 h
    have h' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨y1.1, oPrimePOf_le_self 3 L y1.2.2⟩ =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨y2.1, oPrimePOf_le_self 3 L y2.2.2⟩ :=
      congrArg Subtype.val h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
    have hmem : (y1.1)⁻¹ * y2.1 ∈ GLAPPrimeCoreOf 3 L :=
      ⟨_, h', by simp⟩
    have hB' : ((y1.1)⁻¹ * y2.1) ∈ B := B.mul_mem (B.inv_mem y1.2.1) y2.2.1
    have hord3 : ((y1.1)⁻¹ * y2.1) ^ 3 = 1 := hB.2 _ hB'
    have hord : orderOf ((y1.1)⁻¹ * y2.1) ∣ Nat.card (GLAPPrimeCoreOf 3 L) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    have h3 : orderOf ((y1.1)⁻¹ * y2.1) ∣ 3 := orderOf_dvd_of_pow_eq_one hord3
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 L)
    have h1 : orderOf ((y1.1)⁻¹ * y2.1) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop h3 hord
    have : (y1.1)⁻¹ * y2.1 = 1 := orderOf_eq_one_iff.1 h1
    exact Subtype.ext (inv_mul_eq_one.1 this)
  have := Nat.card_le_card_of_injective g hginj
  omega

omit [Finite G] in
theorem mem_zpowers_pow_of_coprime {w : G} (h : Nat.Coprime 3 (orderOf w)) :
    w ∈ Subgroup.zpowers (w ^ 3) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hab' : a * (3 : ℤ) + b * (orderOf w : ℤ) = 1 := by exact_mod_cast hab
  have e1 : w ^ (a * (3 : ℤ)) = (w ^ 3) ^ a := by
    rw [mul_comm, zpow_mul]
    simp
  have e2 : w ^ (b * (orderOf w : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hw : w = (w ^ 3) ^ a := by
    calc w = w ^ (a * (3 : ℤ) + b * (orderOf w : ℤ)) := by rw [hab', zpow_one]
      _ = (w ^ 3) ^ a := by rw [zpow_add, e1, e2, mul_one]
  have := Subgroup.zpow_mem _ (Subgroup.mem_zpowers (w ^ 3)) a
  rwa [← hw] at this

omit [Finite G] in
theorem mem_gLAPPrimeCoreOf_iff {p : ℕ} {X : Subgroup G} (y : ↥X) :
    (y : G) ∈ GLAPPrimeCoreOf p X ↔ y ∈ GLAPPrimeCore p ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

end Comp

section CompType

variable {G : Type} [Group G] [Finite G]

theorem mem_layer_of_central {X L : Subgroup G} {x : G} (hL : GLAPComponent 3 X L)
    (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hxO : x ∈ oPrimePOf 3 L) :
    x ∈ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  set N := GLAPPrimeCoreOf 3 L with hN
  set Q := L ⊓ Subgroup.centralizer ({x} : Set G) with hQ
  have hQL : Q ≤ L := inf_le_left
  have hxQ : x ∈ Q := ⟨hxL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hNL : N ≤ L := Subgroup.map_subtype_le _
  have hxord : IsPGroup 3 (Subgroup.zpowers x) :=
    isPGroup_three_of_isElemAbelian (isElemAbelian_zpowers_of_pow_three hx3)
  have hVp : ¬ 3 ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf hp3 L
  have hcov : ∀ ℓ ∈ L, ∃ v ∈ N, ℓ * v ∈ Q := by
    intro ℓ hℓ
    have hcomm : x * ℓ * x⁻¹ * ℓ⁻¹ ∈ N := by
      have h1 := comm_mem_gLAPPrimeCoreOf_of_mem_oPrimePOf hp3 hL hxO hℓ
      have e : x * ℓ * x⁻¹ * ℓ⁻¹ = (ℓ * x * ℓ⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact N.inv_mem h1
    obtain ⟨v, hv, hvc⟩ := exists_mul_mem_centralizer (p := 3) (d := x) (x := ℓ) (V := N) hxord
      hVp (le_normalizer_glaPPrimeCoreOf 3 L hxL) (le_normalizer_glaPPrimeCoreOf 3 L hℓ) hcomm
    exact ⟨v, hv, L.mul_mem hℓ (hNL hv), hvc⟩
  have hcover3 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Covers3
      (Subgroup.centralizer ({x} : Set G)) L := by
    intro ℓ hℓ
    obtain ⟨v, hv, hq⟩ := hcov ℓ hℓ
    have e : ℓ = (ℓ * v) * v⁻¹ := by group
    rw [e]
    refine Subgroup.mul_mem_sup ?_ (N.inv_mem hv)
    exact ⟨hq.2, hq.1⟩
  have hA : GLAPPrimeCoreOf 3 Q = Q ⊓ N :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.glaPPrimeCoreOf_inf_eq hcover3
  let φ : ↥Q →* barOf 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp (Subgroup.inclusion hQL)
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨v, hv, hq⟩ := hcov ℓ ℓ.2
    refine ⟨⟨ℓ * v, hq⟩, ?_⟩
    have hvL : v ∈ L := hNL hv
    have e : Subgroup.inclusion hQL ⟨(ℓ : G) * v, hq⟩ = ℓ * ⟨v, hvL⟩ := Subtype.ext rfl
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion hQL ⟨(ℓ : G) * v, hq⟩) =
      QuotientGroup.mk ℓ
    rw [e, map_mul]
    have hvn : (⟨v, hvL⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L :=
      (mem_gLAPPrimeCoreOf_iff (⟨v, hvL⟩ : ↥L)).1 hv
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) ⟨v, hvL⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := GLAPPrimeCore 3 ↥L) _).2 hvn
    rw [h1, mul_one]
    rfl
  have hker : φ.ker = GLAPPrimeCore 3 ↥Q := by
    ext q
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (Subgroup.inclusion hQL q : ↥L) ∈ GLAPPrimeCore 3 ↥L :=
        (QuotientGroup.eq_one_iff _).1 h
      have h2 : (q : G) ∈ N := (mem_gLAPPrimeCoreOf_iff (Subgroup.inclusion hQL q)).2 h1
      have h3 : (q : G) ∈ GLAPPrimeCoreOf 3 Q := by rw [hA]; exact ⟨q.2, h2⟩
      exact (mem_gLAPPrimeCoreOf_iff q).1 h3
    · intro h
      have h3 : (q : G) ∈ GLAPPrimeCoreOf 3 Q := (mem_gLAPPrimeCoreOf_iff q).2 h
      rw [hA] at h3
      have : Subgroup.inclusion hQL q ∈ GLAPPrimeCore 3 ↥L :=
        (mem_gLAPPrimeCoreOf_iff (Subgroup.inclusion hQL q)).1 h3.2
      exact (QuotientGroup.eq_one_iff _).2 this
  let e : (↥Q ⧸ GLAPPrimeCore 3 ↥Q) ≃* barOf 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  have hq := isQuasisimple_barOf hp3 hL
  have hQq : CFSG.Open.IsQuasisimple (↥Q ⧸ GLAPPrimeCore 3 ↥Q) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv e hq
  have hTop : IsComponentOf (⊤ : Subgroup (↥Q ⧸ GLAPPrimeCore 3 ↥Q)) ⊤ :=
    ⟨le_top, IsSubnormal.refl _,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv Subgroup.topEquiv hQq⟩
  obtain ⟨J₁, hJ₁, hbar⟩ := exists_glaPComponent_barX_eq (p := 3) Q hTop
  have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥Q) ⟨x, hxQ⟩ ∈ barX 3 Q J₁ := by
    rw [hbar]; exact Subgroup.mem_top _
  obtain ⟨j, hj, hjx⟩ := hmem
  have hjJ : (j : G) ∈ J₁ := Subgroup.mem_subgroupOf.1 hj
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hjx
  have hw : (j : G)⁻¹ * x ∈ GLAPPrimeCoreOf 3 Q := ⟨_, hjx, by simp⟩
  have hjc : (j : G) * x = x * j := Subgroup.mem_centralizer_singleton_iff.1 j.2.2
  have hcw : Commute (j : G) ((j : G)⁻¹ * x) := by
    show (j : G) * ((j : G)⁻¹ * x) = ((j : G)⁻¹ * x) * j
    calc (j : G) * ((j : G)⁻¹ * x) = x := by group
      _ = ((j : G)⁻¹ * x) * j := by rw [mul_assoc, ← hjc]; group
  have hx : x = (j : G) * ((j : G)⁻¹ * x) := by group
  have h1 : (j : G) ^ 3 * ((j : G)⁻¹ * x) ^ 3 = 1 := by
    rw [← hcw.mul_pow, ← hx]; exact hx3
  have h2 : ((j : G)⁻¹ * x) ^ 3 = ((j : G) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hw3J : ((j : G)⁻¹ * x) ^ 3 ∈ J₁ := by
    rw [h2]; exact J₁.inv_mem (J₁.pow_mem hjJ 3)
  have hword : orderOf ((j : G)⁻¹ * x) ∣ Nat.card (GLAPPrimeCoreOf 3 Q) :=
    Subgroup.orderOf_dvd_natCard _ hw
  have hcop : Nat.Coprime 3 (orderOf ((j : G)⁻¹ * x)) :=
    Nat.Coprime.coprime_dvd_right hword
      ((Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 Q))
  have hwJ : (j : G)⁻¹ * x ∈ J₁ :=
    ((Subgroup.zpowers_le).2 hw3J) (mem_zpowers_pow_of_coprime hcop)
  have hxJ : x ∈ J₁ := by
    rw [hx]; exact J₁.mul_mem hjJ hwJ
  exact (le_sSup hJ₁ : J₁ ≤ GLAPLayer 3 Q) hxJ

end CompType

structure Ctx (G : Type) [Group G] [Finite G] (m : ℕ) : Prop where
  hS : GLStanding G m 3
  hC : GLCaseFour G 3
  hNo : ¬ ∃ B : Subgroup G, IsExtremal B
  h52 : Lemma52
  h53 : Lemma53
  h54 : Lemma54
  h56 : Lemma56
  h510 : Lemma510
  h511 : Lemma511
  h513 : Lemma513

namespace Ctx

variable {G : Type} [Group G] [Finite G] {m : ℕ}

theorem bOne (_c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) : IsBOneMax 3 B :=
  CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB

theorem scp (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) : IsSCp 3 ⊤ B :=
  lemma23_proved G m 3 c.hS B (c.bOne hB)

theorem card_eq (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) : Nat.card B = 3 ^ 4 := by
  rw [hB.1.2.1, c.hC.2.1]

theorem type (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L) :
    IsSLThreeEps (barOf 3 L) :=
  c.h511 G m c.hS c.hC c.hNo B hB b hb hb1 L hL

theorem norm (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L) :
    B ≤ Subgroup.normalizer (L : Set G) :=
  (c.h56 G m c.hS c.hC B hB b hb hb1).2 L hL

theorem zcard (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L) :
    Nat.card (Subgroup.center (barOf 3 L)) = 3 :=
  card_center_of_isSLThreeEps (c.type hB hb hb1 hL)

theorem exists_upsilonComponent' {B : Subgroup G} {b : G} (h : upsilonOf B b ≠ ⊥) :
    ∃ L, IsUpsilonComponent B b L := by
  by_contra hno
  apply h
  have : {L | IsUpsilonComponent B b L} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun L hL => hno ⟨L, hL⟩
  unfold upsilonOf
  rw [this, sSup_empty]

theorem ups_ne_bot (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G} (_hb : b ∈ B)
    (_hb1 : b ≠ 1)
    (hiv : ∀ x ∈ B, x ≠ 1 → upsilonOf B x ≤ upsilonOf B b ⊔ GLAPPrimeCoreOf 3 (upsilonOf B x)) :
    upsilonOf B b ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx, hx1, hxne⟩ := c.h52 G m c.hS c.hC B hB
  obtain ⟨L', hL'⟩ := exists_upsilonComponent' hxne
  have h1 : L' ≤ upsilonOf B x := le_sSup hL'
  have h2 := hiv x hx hx1
  rw [hbot, bot_sup_eq] at h2
  have h3 : L' ≤ GLAPPrimeCoreOf 3 (upsilonOf B x) := h1.trans h2
  have h4 : ¬ 3 ∣ Nat.card L' := fun hd =>
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three _ (hd.trans (Subgroup.card_dvd_of_le h3))
  exact not_le_gLAPPrimeCoreOf_of_component Nat.prime_three hL'.1
    (le_gLAPPrimeCoreOf_of_coprime_of_isSubnormal Nat.prime_three hL'.1.2.1 h4)

theorem exists_mem_oPrimeP (c : Ctx G m) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G} (hL : IsUpsilonComponent B b L) :
    ∃ x ∈ B, x ≠ 1 ∧ x ∈ oPrimePOf 3 L := by
  have hBN : B ≤ Subgroup.normalizer (oPrimePOf 3 L : Set G) :=
    (c.norm hB hb hb1 hL).trans (normalizer_le_normalizer_oPrimePOf 3 L)
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_mem_inf_of_isSCp (c.scp hB) hBN
    (three_dvd_card_oPrimePOf (c.zcard hB hb hb1 hL))
  exact ⟨x, hx.1, hx1, hx.2⟩

theorem exists_good (c : Ctx G m) :
    ∃ (B : Subgroup G) (b : G) (L : Subgroup G), IsBZeroMax 3 B ∧ b ∈ B ∧ b ≠ 1 ∧
      IsUpsilonComponent B b L ∧ b ∈ L := by
  obtain ⟨B, hB⟩ := CFSG.HardMathSupport.Solomon.Proving.exists_isBZeroMax_of_not_glaDeltaZero
    (p := 3) c.hS.not_deltaZero
  obtain ⟨b, hb, hb1, hne⟩ := c.h52 G m c.hS c.hC B hB
  obtain ⟨L, hL⟩ := exists_upsilonComponent' hne
  obtain ⟨x, hxB, hx1, hxO⟩ := c.exists_mem_oPrimeP hB hb hb1 hL
  have hxL : x ∈ L := oPrimePOf_le_self 3 L hxO
  have hz := c.zcard hB hb hb1 hL
  have hfield : InducesFieldAut 3 L x :=
    inducesFieldAut_of_mem_centralizerQuot (oPrimePOf_le_centralizerQuot Nat.prime_three hL.1 hxO)
  obtain ⟨hK, -, -⟩ := (c.h510 G m c.hS c.hC B hB b hb hb1 L hL).2.2 x hxB hx1 hfield
  have hle : pumpUp L x ≤ upsilonOf B x :=
    c.h53 G m c.hS c.hC B (c.bOne hB) b hb hb1 L hL x hxB hx1 hfield
  have hKU : IsUpsilonComponent B x (pumpUp L x) :=
    mem_of_le_sSup_components Nat.prime_three {L' | IsUpsilonComponent B x L'}
      (fun L' hL' => hL'.1) hK hle
  have hx3 : x ^ 3 = 1 := hB.1.1.2 x hxB
  have hxJ := mem_layer_of_central hL.1 hxL hx3 hxO
  have hxK : x ∈ pumpUp L x := by
    refine (le_iSup₂_of_le (1 : G) (one_mem _) ?_ : _ ≤ pumpUp L x) hxJ
    intro y hy
    simpa [mem_gLBConj] using hy
  exact ⟨B, x, pumpUp L x, hB, hxB, hx1, hKU, hxK⟩

theorem no_good (c : Ctx G m) {B : Subgroup G} {b : G} {L : Subgroup G} (hB : IsBZeroMax 3 B)
    (hb : b ∈ B) (hb1 : b ≠ 1) (hL : IsUpsilonComponent B b L) (hbL : b ∈ L) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨B1, hB1, ⟨hbB1, hB1le, hnle, hcq⟩, ⟨A1, hA1, hA1f⟩, hnU, hiv⟩ :=
    c.h513 G m c.hS c.hC B hB b hb hb1 L hL hbL
  obtain ⟨L1, hL1⟩ := exists_upsilonComponent' (c.ups_ne_bot hB1 hbB1 hb1 hiv)
  have hne : L ≠ L1 := fun h => hnU (by subst h; exact hL1)
  have zL := c.zcard hB hb hb1 hL
  have hcommL : ∀ y ∈ L, b * y = y * b := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL.1.1 hy)).symm
  have hbO : B1 ⊓ oPrimePOf 3 L = Subgroup.zpowers b :=
    inf_oPrimePOf_eq_zpowers hL.1 zL hB1.1.1 hbB1 hb1 hbL hcommL
  have hbOL : b ∈ oPrimePOf 3 L := mem_oPrimePOf_of_forall_comm hp3 hbL hcommL
  have hB1n1 : B1 ≤ Subgroup.normalizer (L1 : Set G) := c.norm hB1 hbB1 hb1 hL1
  have hE1L : ∀ y ∈ B1 ⊓ oPrimePOf 3 L1, y ∈ L := by
    intro y hy
    by_contra hyL
    have hyB1 : y ∈ B1 := hy.1
    have hy3 : y ^ 3 = 1 := hB1.1.1.2 y hyB1
    have hyE : y ∉ (B1 ⊓ L : Subgroup G) := fun h => hyL h.2
    have hcard : Nat.card ↥((B1 ⊓ L : Subgroup G) ⊔ Subgroup.zpowers y) =
        3 * Nat.card ↥(B1 ⊓ L : Subgroup G) :=
      card_sup_zpowers_of_pow_three_eq_one hy3 hyE
        (fun h hh => elemAbelian_comm hB1.1.1 hh.1 hyB1)
    have hEel : IsElemAbelian 3 (B1 ⊓ L : Subgroup G) :=
      isElemAbelian_mono hB1.1.1 inf_le_left
    have hnine : 9 ≤ Nat.card ↥(B1 ⊓ L : Subgroup G) := by
      refine nine_le_card_of_not_le_zpowers hEel ⟨hbB1, hbL⟩ hb1 ?_
      intro hle
      exact hnle (hle.trans ((Subgroup.zpowers_le).2 hbOL))
    have hWB1 : (B1 ⊓ L : Subgroup G) ⊔ Subgroup.zpowers y ≤ B1 :=
      sup_le inf_le_left ((Subgroup.zpowers_le).2 hyB1)
    have hWel : IsElemAbelian 3 ((B1 ⊓ L : Subgroup G) ⊔ Subgroup.zpowers y) :=
      isElemAbelian_mono hB1.1.1 hWB1
    have hWcq : (B1 ⊓ L : Subgroup G) ⊔ Subgroup.zpowers y ≤
        centralizerQuot L1 (GLAPPrimeCoreOf 3 L1) := by
      refine sup_le ?_ ?_
      · exact inf_le_right.trans (le_centralizerQuot_of_ne hp3 hL.1 hL1.1 hne)
      · exact (Subgroup.zpowers_le).2
          (oPrimePOf_le_centralizerQuot hp3 hL1.1 hy.2)
    have hrk := c.h54 G m c.hS c.hC B1 (c.bOne hB1) b hbB1 hb1 L1 hL1 _ hWB1
      (fun a ha => inducesFieldAut_of_mem_centralizerQuot (hWcq ha))
    have := three_le_pRank_of_le_card hWel (by omega)
    omega
  obtain ⟨x1, hx1B, hx11, hx1O⟩ := c.exists_mem_oPrimeP hB1 hbB1 hb1 hL1
  have hbL1 : b ∈ L1 := by
    have hx1L : x1 ∈ L := hE1L x1 ⟨hx1B, hx1O⟩
    have hx1O' : x1 ∈ oPrimePOf 3 L :=
      inf_le_oPrimePOf_of_ne hp3 hL.1 hL1.1 hne ⟨hx1L, oPrimePOf_le_self 3 L1 hx1O⟩
    have hx1b : x1 ∈ Subgroup.zpowers b := by rw [← hbO]; exact ⟨hx1B, hx1O'⟩
    have hb3 : b ^ 3 = 1 := hB.1.1.2 b hb
    have : b ∈ Subgroup.zpowers x1 := mem_zpowers_of_mem_zpowers_ne_one hb3 hx1b hx11
    exact oPrimePOf_le_self 3 L1 (((Subgroup.zpowers_le).2 hx1O) this)
  obtain ⟨B2, hB2, ⟨hbB2, hB2le, hnle2, hcq2⟩, -, hnU2, hiv2⟩ :=
    c.h513 G m c.hS c.hC B1 hB1 b hbB1 hb1 L1 hL1 hbL1
  have hups2 : upsilonOf B2 b ≠ ⊥ := c.ups_ne_bot hB2 hbB2 hb1 hiv2
  have hnotL : ¬ IsUpsilonComponent B2 b L := by
    intro hLU2
    have hB2N : B2 ≤ Subgroup.normalizer (L : Set G) := c.norm hB2 hbB2 hb1 hLU2
    have hA1B1 : A1 ≤ B1 := hA1.1
    have hidx : Nat.card B1 = 3 * Nat.card A1 := by
      rw [c.card_eq hB1, hA1.2.2]; norm_num
    have hcardN : Nat.card B2 ≤ 3 * Nat.card (B2 ⊓ (A1 ⊔ L1) : Subgroup G) :=
      card_le_three_mul_card_inf hB2le hA1B1 hB1n1 hidx
    have hc27 : 27 ≤ Nat.card (B2 ⊓ (A1 ⊔ L1) : Subgroup G) := by
      have := c.card_eq hB2
      omega
    have hel : IsElemAbelian 3 (B2 ⊓ (A1 ⊔ L1) : Subgroup G) :=
      isElemAbelian_mono hB2.1.1 inf_le_left
    have hL1cq : L1 ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) :=
      le_centralizerQuot_of_ne hp3 hL1.1 hL.1 (Ne.symm hne)
    have hfield : ∀ g ∈ (B2 ⊓ (A1 ⊔ L1) : Subgroup G), InducesFieldAut 3 L g := by
      intro g hg
      obtain ⟨a, ha, l, hl, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (hA1B1.trans (c.norm hB1 hbB1 hb1 hL1)) hg.2
      exact inducesFieldAut_of_mul rfl (hA1f a ha) (hB2N hg.1) (hL1cq hl)
    have hrk := c.h54 G m c.hS c.hC B2 (c.bOne hB2) b hbB2 hb1 L hLU2 _ inf_le_left hfield
    have := three_le_pRank_of_le_card hel hc27
    omega
  have hPB2 : (B1 ⊓ L : Subgroup G) ≤ B2 := fun y hy =>
    hcq2 ⟨hy.1, le_centralizerQuot_of_ne hp3 hL.1 hL1.1 hne hy.2⟩
  have hcommL1 : ∀ y ∈ L1, b * y = y * b := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hL1.1.1 hy)).symm
  have hbOL1 : b ∈ oPrimePOf 3 L1 := mem_oPrimePOf_of_forall_comm hp3 hbL1 hcommL1
  have hPnine : 9 ≤ Nat.card ↥(B1 ⊓ L : Subgroup G) := by
    refine nine_le_card_of_not_le_zpowers (isElemAbelian_mono hB1.1.1 inf_le_left)
      ⟨hbB1, hbL⟩ hb1 ?_
    intro hle
    exact hnle (hle.trans ((Subgroup.zpowers_le).2 hbOL))
  have hQnine : 9 ≤ Nat.card ↥(B2 ⊓ L1 : Subgroup G) := by
    refine nine_le_card_of_not_le_zpowers (isElemAbelian_mono hB2.1.1 inf_le_left)
      ⟨hbB2, hbL1⟩ hb1 ?_
    intro hle
    exact hnle2 (hle.trans ((Subgroup.zpowers_le).2 hbOL1))
  have hPQ : (B1 ⊓ L : Subgroup G) ⊓ (B2 ⊓ L1 : Subgroup G) ≤ Subgroup.zpowers b := by
    intro y hy
    have hyLL1 : y ∈ L ⊓ L1 := ⟨hy.1.2, hy.2.2⟩
    have := inf_le_oPrimePOf_of_ne hp3 hL.1 hL1.1 hne hyLL1
    rw [← hbO]
    exact ⟨hy.1.1, this⟩
  have hPQcard : Nat.card ↥((B1 ⊓ L : Subgroup G) ⊓ (B2 ⊓ L1 : Subgroup G)) ≤ 3 := by
    have hcz : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_three_of_pow (hB.1.1.2 b hb) hb1]
    exact hcz ▸ Subgroup.card_le_of_le hPQ
  have hQB2 : (B2 ⊓ L1 : Subgroup G) ≤ B2 := inf_le_left
  have hPcentQ : (B1 ⊓ L : Subgroup G) ≤ Subgroup.normalizer ((B2 ⊓ L1 : Subgroup G) : Set G) := by
    intro g hg
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact elemAbelian_comm hB2.1.1 (hQB2 hq) (hPB2 hg)
  have hEcard := card_sup_mul_card_inf_aux hPcentQ
  have hE27 : 27 ≤ Nat.card ↥((B1 ⊓ L : Subgroup G) ⊔ (B2 ⊓ L1 : Subgroup G)) := by
    by_contra hlt
    have h1 : 9 * 9 ≤ Nat.card ↥(B1 ⊓ L : Subgroup G) * Nat.card ↥(B2 ⊓ L1 : Subgroup G) :=
      Nat.mul_le_mul hPnine hQnine
    rw [← hEcard] at h1
    have h2 := Nat.mul_le_mul_left
      (Nat.card ↥((B1 ⊓ L : Subgroup G) ⊔ (B2 ⊓ L1 : Subgroup G))) hPQcard
    omega
  have hEB2 : (B1 ⊓ L : Subgroup G) ⊔ (B2 ⊓ L1 : Subgroup G) ≤ B2 := sup_le hPB2 inf_le_left
  have hEel : IsElemAbelian 3 ((B1 ⊓ L : Subgroup G) ⊔ (B2 ⊓ L1 : Subgroup G)) :=
    isElemAbelian_mono hB2.1.1 hEB2
  apply hups2
  unfold upsilonOf
  rw [sSup_eq_bot]
  intro L2 hL2
  exfalso
  have hL2L : L ≠ L2 := fun h => hnotL (by subst h; exact hL2)
  have hL2L1 : L1 ≠ L2 := fun h => hnU2 (by subst h; exact hL2)
  have hEcq : (B1 ⊓ L : Subgroup G) ⊔ (B2 ⊓ L1 : Subgroup G) ≤
      centralizerQuot L2 (GLAPPrimeCoreOf 3 L2) :=
    sup_le (inf_le_right.trans (le_centralizerQuot_of_ne hp3 hL.1 hL2.1 hL2L))
      (inf_le_right.trans (le_centralizerQuot_of_ne hp3 hL1.1 hL2.1 hL2L1))
  have hrk := c.h54 G m c.hS c.hC B2 (c.bOne hB2) b hbB2 hb1 L2 hL2 _ hEB2
    (fun a ha => inducesFieldAut_of_mem_centralizerQuot (hEcq ha))
  have := three_le_pRank_of_le_card hEel hE27
  omega

end Ctx

end Prop51Ns

theorem prop51_of_lemmas (h52 : Lemma52) (h53 : Lemma53) (h54 : Lemma54) (h56 : Lemma56)
    (h510 : Lemma510) (h511 : Lemma511) (h513 : Lemma513) : Prop51 := by
  intro G _ _ m hS hC
  by_contra hNo
  have c : Prop51Ns.Ctx G m := ⟨hS, hC, hNo, h52, h53, h54, h56, h510, h511, h513⟩
  obtain ⟨B, b, L, hB, hb, hb1, hL, hbL⟩ := c.exists_good
  exact c.no_good hB hb hb1 hL hbL

end CFSG.HardMathSupport.Solomon.LocalBalance
