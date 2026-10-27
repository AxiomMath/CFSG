module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Core
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Levi

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section OTwo

variable {G : Type} [Group G]

@[expose] def oTwoIn (M : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 ↥M).map M.subtype

theorem oTwoIn_le (M : Subgroup G) : oTwoIn M ≤ M := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem isPGroup_oTwoIn (M : Subgroup G) : IsPGroup 2 (oTwoIn M) :=
  CFSG.pCore_isPGroup.map M.subtype

theorem le_normalizer_oTwoIn (M : Subgroup G) : M ≤ normalizer (oTwoIn M : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨⟨m, hm⟩ * x' * ⟨m, hm⟩⁻¹, (CFSG.pCore_normal).conj_mem _ hx' _, rfl⟩
  · rintro ⟨x', hx', hx'e⟩
    refine ⟨⟨m, hm⟩⁻¹ * x' * ⟨m, hm⟩⁻¹⁻¹, (CFSG.pCore_normal).conj_mem _ hx' _, ?_⟩
    have e : (x' : G) = m * x * m⁻¹ := hx'e
    simp only [inv_inv, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, e]
    group

theorem le_oTwoIn {M N : Subgroup G} (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set G))
    (hN : IsPGroup 2 N) : N ≤ oTwoIn M := by
  have hn : (N.subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hMN m.2) n).1 hn
  have hp : IsPGroup 2 (N.subgroupOf M) := hN.comap_of_injective M.subtype M.subtype_injective
  have hle : N.subgroupOf M ≤ CFSG.pCore 2 ↥M := le_sSup ⟨hn, hp⟩
  intro x hx
  exact ⟨⟨x, hNM hx⟩, hle (mem_subgroupOf.2 hx), rfl⟩

theorem rightConjugate_oTwoIn_le (M : Subgroup G) (x : G) :
    rightConjugate (oTwoIn M) x ≤ oTwoIn (rightConjugate M x) := by
  refine le_oTwoIn (map_mono (oTwoIn_le M)) ?_ ((isPGroup_oTwoIn M).map _)
  intro m hm
  rw [mem_rightConjugate_iff] at hm
  rw [mem_normalizer_rightConjugate_iff]
  exact le_normalizer_oTwoIn M hm

theorem rightConjugate_oTwoIn (M : Subgroup G) (x : G) :
    rightConjugate (oTwoIn M) x = oTwoIn (rightConjugate M x) := by
  refine le_antisymm (rightConjugate_oTwoIn_le M x) ?_
  have h := rightConjugate_oTwoIn_le (rightConjugate M x) x⁻¹
  rw [RankTwoClassical.rightConjugate_rightConjugate_inv] at h
  have h2 := (RankTwoClassical.rightConjugate_le_rightConjugate_iff (x := x)).2 h
  rwa [RankTwoClassical.rightConjugate_inv_rightConjugate] at h2

theorem mem_normalizer_oTwoIn {M : Subgroup G} {x : G} (hx : x ∈ normalizer (M : Set G)) :
    x ∈ normalizer (oTwoIn M : Set G) := by
  have h1 := rightConjugate_oTwoIn M x
  rw [(rightConjugate_eq_self_iff M x).2 hx] at h1
  exact (rightConjugate_eq_self_iff _ x).1 h1

end OTwo

section Rad

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}
  {K : Type} [Field K] [Finite K] [CharP K 2]
  {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}

omit [Finite G] [CharP K 2] in
theorem exists_shortCent_of_mem
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) {a : G} (ha : a ∈ A ⊓ centralizer (T : Set G)) :
    ∃ c : ↥(adjointGroup .G2 K), ψ ⟨a, le_normalizer (mem_inf.1 ha).1⟩ = MulAut.conj c ∧
      (c : ModGL .G2 K) ∈ g2ShortCent K := by
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  obtain ⟨haA, haT⟩ := mem_inf.1 ha
  obtain ⟨t₀, ht₀, -, ht₀N, y, hy1, hψt₀⟩ := hTp
  obtain ⟨c, hc⟩ := hψ.map_mem a haA
  refine ⟨c, hc.symm, mem_inf.2 ⟨c.2, mem_centralizer_singleton_iff.2 ?_⟩⟩
  have hat : t₀ * a = a * t₀ := mem_centralizer_iff.1 haT t₀ ht₀
  have hN : t₀ * a ∈ normalizer (A : Set G) := mul_mem ht₀N (le_normalizer haA)
  have h1 : ψ ⟨t₀, ht₀N⟩ * ψ ⟨a, le_normalizer haA⟩ = ψ ⟨a, le_normalizer haA⟩ * ψ ⟨t₀, ht₀N⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hat
  rw [hψt₀, ← hc, ← map_mul, ← map_mul] at h1
  have h2 := congrArg Subtype.val (hinj h1)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hy1] at h2
  exact h2.symm

omit [Finite G] [CharP K 2] in
theorem perfectCore_le_liftIn
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) :
    CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) ≤
      liftIn ψ (g2Inn K ⁅g2ShortCent K, g2ShortCent K⁆) := by
  refine (CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1).trans ?_
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero, commutator_le]
  intro a ha b hb
  obtain ⟨ca, hca, hcaS⟩ := exists_shortCent_of_mem hψ hTp ha
  obtain ⟨cb, hcb, hcbS⟩ := exists_shortCent_of_mem hψ hTp hb
  have hab := RankTwoL3Even.commutatorElement_mem' (mem_inf.1 ha).1 (mem_inf.1 hb).1
  refine mem_liftIn.2 ⟨hab, ?_⟩
  rw [psi_commutatorElement (mem_inf.1 ha).1 (mem_inf.1 hb).1, hca, hcb,
    ← map_commutatorElement]
  refine conj_mem_g2Inn ?_
  have e : ((⁅ca, cb⁆ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      ⁅(ca : ModGL .G2 K), (cb : ModGL .G2 K)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [e]
  exact commutator_mem_commutator hcaS hcbS

theorem leviLift_le_perfectCore
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184s : G2Centr184s) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    leviLift ψ (g2Inn K ⁅g2ShortCent K, g2ShortCent K⁆) ≤
      CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  obtain ⟨hperf, -⟩ := h184s K hK4
  have hSC : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ adjointGroup .G2 K :=
    ((commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb).trans
      inf_le_left
  have hP := commutator_g2Inn hSC hperf
  refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf leviLift_le ?_)
    (commutator_leviLift hψ (g2Inn_le_range _) hP)
  intro l hl
  refine mem_centralizer_iff.2 fun t ht => ?_
  have htN := hc.le_normalizer ht
  obtain ⟨x, hx⟩ := exists_psi_eq_conj hc h32 h4 h34 hψ ht htN
  have hxv := hTv t ht htN x hx
  have hw : ∀ s ∈ g2Inn K ⁅g2ShortCent K, g2ShortCent K⁆, ψ ⟨t, htN⟩ * s = s * ψ ⟨t, htN⟩ := by
    intro s hs
    obtain ⟨c, hcS, rfl⟩ := mem_g2Inn.1 hs
    obtain ⟨u, hu⟩ := mem_rootSubgroup.1 hxv
    rw [hx, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu]
    have h1 : (c : ModGL .G2 K) ∈ g2ShortCent K :=
      ((commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb) hcS
    exact (g2_commute_v_of_mem h1 u).symm
  have h1 := leviLift_le_centralizer hψ htN hw hl
  exact (mem_centralizer_singleton_iff.1 h1).symm

omit [Finite K] in
theorem g2ShortRadical_comm :
    ∀ u ∈ g2ShortRadical K, ∀ v ∈ g2ShortRadical K, u * v = v * u :=
  fun _ hu _ hv => (commute_of_mem_g2ShortRadical hu hv).eq

omit [Finite K] in
theorem g2ShortRadical_sq
    : ∀ u ∈ g2ShortRadical K, u ^ 2 = 1 := by
  rintro _ ⟨D, E, F, rfl⟩
  rw [sq, g2N_mul_self, ← g2N_zero]
  exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by ring)

theorem twoLift_bc_le_perfectCore
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184s : G2Centr184s) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    twoLift ψ (g2BCGroup K) ≤ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  obtain ⟨hperf, -⟩ := h184s K hK4
  have hSC : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ adjointGroup .G2 K :=
    ((commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb).trans
      inf_le_left
  have hP := commutator_g2Inn hSC hperf
  refine le_trans ?_ (leviLift_le_perfectCore h4 h32 h184s hK4 hc hψ hTv)
  intro w hw
  obtain ⟨hwA, hw2, y, hy, hyU⟩ := (mem_twoLift hψ hZ
    (fun u hu v hv => g2ShortRadical_comm u (g2BCGroup_le hu) v (g2BCGroup_le hv))).1 hw
  refine mem_leviLift_of_pow hψ (g2Inn_le_range _) hP hZ (mem_liftIn.2 ⟨hwA, ?_⟩) (k := 1)
    (by rw [pow_one]; exact hw2)
  rw [hy]
  exact conj_mem_g2Inn (g2BCGroup_le_commutator hyU)

theorem oTwoIn_perfectCore_eq
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184s : G2Centr184s) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hTp : G2Pinned ψ T g2v) (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    oTwoIn (CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G))) =
      twoLift ψ (g2BCGroup K) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hUc : ∀ u ∈ g2BCGroup K, ∀ v ∈ g2BCGroup K, u * v = v * u :=
    fun u hu v hv => g2ShortRadical_comm u (g2BCGroup_le hu) v (g2BCGroup_le hv)
  have hU2 : ∀ u ∈ g2BCGroup K, u ^ 2 = 1 := fun u hu => g2ShortRadical_sq u (g2BCGroup_le hu)
  obtain ⟨hperf, -⟩ := h184s K hK4
  have hSS : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ g2ShortCent K :=
    (commutator_le).2 fun a ha b hb => RankTwoL3Even.commutatorElement_mem' ha hb
  have hSC : ⁅g2ShortCent K, g2ShortCent K⁆ ≤ adjointGroup .G2 K := hSS.trans inf_le_left
  have hP := commutator_g2Inn hSC hperf
  set M := CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) with hMdef
  have hMA : M ≤ A := (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hWM := twoLift_bc_le_perfectCore h4 h32 h184s hK4 hc hZA hψ hTv
  have hMlift := perfectCore_le_liftIn hψ hTp
  have himM : ∀ m ∈ M, ∃ hmA : m ∈ A, ∃ c : ↥(adjointGroup .G2 K),
      ψ ⟨m, le_normalizer hmA⟩ = MulAut.conj c ∧
        (c : ModGL .G2 K) ∈ ⁅g2ShortCent K, g2ShortCent K⁆ := by
    intro m hm
    obtain ⟨hmA, hmS⟩ := mem_liftIn.1 (hMlift hm)
    obtain ⟨c, hcS, hc'⟩ := mem_g2Inn.1 hmS
    exact ⟨hmA, c, hc'.symm, hcS⟩
  refine le_antisymm (fun n hn => ?_) (le_oTwoIn hWM ?_ ?_)
  ·
    set N := oTwoIn M with hNdef
    have hNM : N ≤ M := oTwoIn_le M
    have hN2 := isPGroup_oTwoIn M
    let Nbar : Subgroup (ModGL .G2 K) :=
      (((N.subgroupOf (normalizer (A : Set G))).map ψ).comap
        (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K))).map
          (adjointGroup .G2 K).subtype
    have hmemNbar : ∀ c : ↥(adjointGroup .G2 K), (c : ModGL .G2 K) ∈ Nbar ↔
        ∃ n ∈ N, ∃ hnA : n ∈ A, ψ ⟨n, le_normalizer hnA⟩ = MulAut.conj c := by
      intro c
      constructor
      · rintro ⟨c', ⟨⟨n', hn'N⟩, hn', hψn'⟩, hcc'⟩
        have hcc : c' = c := Subtype.ext hcc'
        subst hcc
        refine ⟨n', mem_subgroupOf.1 hn', oTwoIn_le M (mem_subgroupOf.1 hn') |> hMA, ?_⟩
        exact hψn'
      · rintro ⟨n, hnN, hnA, hψn⟩
        exact ⟨c, ⟨⟨n, le_normalizer hnA⟩, mem_subgroupOf.2 hnN, hψn⟩, rfl⟩
    have hNbarC : ∀ x ∈ Nbar, x ∈ adjointGroup .G2 K := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have hNbarS : Nbar ≤ ⁅g2ShortCent K, g2ShortCent K⁆ := by
      intro x hx
      obtain ⟨n, hnN, hnA, hψn⟩ := (hmemNbar ⟨x, hNbarC x hx⟩).1 hx
      obtain ⟨_, c, hc', hcS⟩ := himM n (hNM hnN)
      rw [hψn] at hc'
      have hx' : x = (c : ModGL .G2 K) := congrArg Subtype.val (hinj hc')
      rw [hx']
      exact hcS
    have hNbar2 : IsPGroup 2 Nbar := by
      rintro ⟨x, hx⟩
      obtain ⟨n, hnN, hnA, hψn⟩ := (hmemNbar ⟨x, hNbarC x hx⟩).1 hx
      obtain ⟨k, hk⟩ := hN2 ⟨n, hnN⟩
      have hk' : n ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : MulAut.conj ((⟨x, hNbarC x hx⟩ : ↥(adjointGroup .G2 K)) ^ 2 ^ k) = 1 := by
        rw [map_pow, ← hψn, ← map_pow]
        have e : (⟨n, le_normalizer hnA⟩ : normalizer (A : Set G)) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using hk')
        rw [e, map_one]
      have h2 := congrArg Subtype.val ((map_eq_one_iff _ hinj).1 h1)
      simpa using h2
    have hLN : ∀ l ∈ g2RankOne K g2ia, ∀ x ∈ Nbar, l * x * l⁻¹ ∈ Nbar := by
      intro l hl x hx
      have hlC : l ∈ adjointGroup .G2 K := (g2RankOne_le_shortCent hl).1
      obtain ⟨m, hm, hmψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range _) hP
        (conj_mem_g2Inn (y := ⟨l, hlC⟩) (g2RankOne_le_commutator hK4 hl))
      have hmM : m ∈ M := leviLift_le_perfectCore h4 h32 h184s hK4 hc hψ hTv hm
      obtain ⟨n, hnN, hnA, hψn⟩ := (hmemNbar ⟨x, hNbarC x hx⟩).1 hx
      have hmnN : m * n * m⁻¹ ∈ N :=
        (mem_normalizer_iff.1 (le_normalizer_oTwoIn M hmM) n).1 hnN
      have hmnA : m * n * m⁻¹ ∈ A := hMA (hNM hmnN)
      have h1 := psi_conj_eq_conj (le_normalizer (leviLift_le hm)) hnA hψn hmnA
      rw [hmψ, MulAut.conj_apply] at h1
      have h2 := (hmemNbar (⟨l, hlC⟩ * ⟨x, hNbarC x hx⟩ * ⟨l, hlC⟩⁻¹)).2 ⟨_, hmnN, hmnA, h1⟩
      simpa using h2
    have hNbarBC := le_g2BCGroup_of_normal hK4 hNbarS hNbar2 hLN
    have hnA : n ∈ A := hMA (hNM hn)
    obtain ⟨c, hc'⟩ := hψ.map_mem n hnA
    have hcN : (c : ModGL .G2 K) ∈ Nbar := (hmemNbar c).2 ⟨n, hn, hnA, hc'.symm⟩
    have hcBC := hNbarBC hcN
    refine mem_twoLift_of hnA ?_ hc'.symm hcBC
    obtain ⟨k, hk⟩ := hN2 ⟨n, hn⟩
    have hk' : n ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hn2 : n ^ 2 ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.2 ⟨pow_mem hnA 2, (hψ.eq_one_iff ⟨_, pow_mem (le_normalizer hnA) 2⟩).1 ?_⟩
      have e : (⟨n ^ 2, pow_mem (le_normalizer hnA) 2⟩ : normalizer (A : Set G)) =
          ⟨n, le_normalizer hnA⟩ ^ 2 := rfl
      rw [e, map_pow, ← hc', ← map_pow]
      have hc2 : c ^ 2 = 1 := Subtype.ext (by simpa using hU2 _ hcBC)
      rw [hc2, map_one]
    refine RankTwoL3Even.eq_one_of_odd_of_pow_two (RankTwoL3Even.odd_orderOf_of_mem hZ hn2)
      (k := k) ?_
    rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
  ·
    intro m hm
    obtain ⟨hmA, c, hc', hcS⟩ := himM m hm
    refine mem_normalizer_twoLift hψ hZ hUc (le_normalizer hmA) fun y => ?_
    rw [hc', MulAut.conj_apply]
    have hcS' : (c : ModGL .G2 K) ∈ g2ShortCent K := hSS hcS
    constructor
    · intro hy
      simpa using conj_mem_g2BCGroup hcS' hy
    · intro hy
      have h1 := conj_mem_g2BCGroup (inv_mem hcS') hy
      simpa [mul_assoc] using h1
  ·
    intro w
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact sq_eq_one_of_mem_twoLift hψ hZ hUc w.2

omit [Finite G] [Finite K] in
theorem twoLift_radical_eq_sup
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (α γ : K) :
    twoLift ψ (g2ShortRadical K) = twoLift ψ (g2YGroup K α γ) ⊔ twoLift ψ (g2BCGroup K) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hAvC : g2ShortRadical K ≤ adjointGroup .G2 K := fun q hq =>
    g2LongRadical_le_adjointGroup (g2ShortRadical_le_g2LongRadical hq)
  refine twoLift_eq_sup hψ hZ g2ShortRadical_sq g2ShortRadical_comm (g2YGroup_le α γ)
    g2BCGroup_le fun y hy => ?_
  obtain ⟨y₁, hy₁, w, hw, he⟩ := exists_mul_of_mem_g2ShortRadical α γ hy
  exact ⟨⟨y₁, hAvC (g2YGroup_le α γ hy₁)⟩, ⟨w, hAvC (g2BCGroup_le hw)⟩, hy₁, hw,
    Subtype.ext he⟩

theorem sup_twoLift_radical
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184s : G2Centr184s) (hK4 : 4 ≤ Nat.card K) (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hRq : Nat.card R = Nat.card K) (hTp : G2Pinned ψ T g2v)
    (hTv : ActsIn ψ T (rootSubgroup .G2 K g2v)) :
    R ⊔ twoLift ψ (g2ShortRadical K) =
      (R ⊔ T) ⊔ oTwoIn (CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G))) := by
  have h34 : Asc08Lemma34 := asc08Lemma34
  rw [oTwoIn_perfectCore_eq h4 h32 h184s hK4 hc hZA hψ hTp hTv,
    twoLift_radical_eq_sup hZA hψ 0 0, g2YGroup_zero,
    ← inf_eq_twoLift_of_actsIn h4 h32 hc hZA hψ hRq hTv, ← sup_assoc, sup_inf_sec3 hc h32 h4 h34]

omit [Finite K] in
theorem isElemAbelian_sup_twoLift
    (h32 : Lemma32) (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) :
    IsElemAbelian 2 (R ⊔ twoLift ψ (g2ShortRadical K) : Subgroup G) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  refine isElemAbelian_sup_of_commute (hc.elemR h32)
    (isElemAbelian_twoLift hψ hZ g2ShortRadical_comm) fun r hr => ?_
  rw [mem_centralizer_iff]
  intro b hb
  exact mem_centralizer_iff.1 (hc.sylowR.le hr) b (twoLift_le hb)

omit [Finite K] in
theorem sup_twoLift_inf_centralizer
    (hc : Sec3 A R T g)
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ) :
    (R ⊔ twoLift ψ (g2ShortRadical K)) ⊓ centralizer (A : Set G) = R := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left hc.sylowR.le)
  obtain ⟨hxRB, hxK⟩ := mem_inf.1 hx
  have hN : twoLift ψ (g2ShortRadical K) ≤ normalizer (R : Set G) := by
    intro b hb
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun r hr => ?_)
    exact (mem_centralizer_iff.1 (hc.sylowR.le hr) b (twoLift_le hb)).symm
  have hx' : x ∈ ((R ⊔ twoLift ψ (g2ShortRadical K) : Subgroup G) : Set G) := hxRB
  rw [coe_mul_of_right_le_normalizer_left R _ hN, Set.mem_mul] at hx'
  obtain ⟨r, hr, b, hb, rfl⟩ := hx'
  have hbK : b ∈ centralizer (A : Set G) := by
    have h1 := mul_mem (inv_mem (hc.sylowR.le hr)) hxK
    rwa [inv_mul_cancel_left] at h1
  have hb1 : b = 1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨twoLift_le hb, hbK⟩)) (k := 1)
    (by rw [pow_one]; exact sq_eq_one_of_mem_twoLift hψ hZ g2ShortRadical_comm hb)
  rw [hb1, mul_one]
  exact hr

@[expose] def unipStab (A B W : Subgroup G) : Subgroup G where
  carrier := {d | d ∈ A ∧ d ∈ normalizer (B : Set G) ∧ (∀ b ∈ B, d * b * d⁻¹ * b⁻¹ ∈ W) ∧
    ∀ w ∈ W, d * w = w * d}
  one_mem' := ⟨one_mem _, one_mem _, fun b _ => by simp, fun w _ => by simp⟩
  mul_mem' := by
    rintro d₁ d₂ ⟨h₁A, h₁N, h₁B, h₁W⟩ ⟨h₂A, h₂N, h₂B, h₂W⟩
    refine ⟨mul_mem h₁A h₂A, mul_mem h₁N h₂N, fun b hb => ?_, fun w hw => ?_⟩
    · have e : d₁ * d₂ * b * (d₁ * d₂)⁻¹ * b⁻¹ =
          d₁ * (d₂ * b * d₂⁻¹ * b⁻¹) * d₁⁻¹ * (d₁ * b * d₁⁻¹ * b⁻¹) := by group
      have h1 : d₁ * (d₂ * b * d₂⁻¹ * b⁻¹) * d₁⁻¹ = d₂ * b * d₂⁻¹ * b⁻¹ := by
        rw [h₁W _ (h₂B b hb), mul_inv_cancel_right]
      rw [e, h1]
      exact mul_mem (h₂B b hb) (h₁B b hb)
    · rw [mul_assoc, h₂W w hw, ← mul_assoc, h₁W w hw, mul_assoc]
  inv_mem' := by
    rintro d ⟨hA, hN, hB, hW⟩
    refine ⟨inv_mem hA, inv_mem hN, fun b hb => ?_, fun w hw => ?_⟩
    · have hb' : d⁻¹ * b * d ∈ B := by
        have h1 := (mem_normalizer_iff.1 (inv_mem hN) b).1 hb
        simpa using h1
      have e : d⁻¹ * b * d⁻¹⁻¹ * b⁻¹ = (d * (d⁻¹ * b * d) * d⁻¹ * (d⁻¹ * b * d)⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (hB _ hb')
    · have h1 := hW w hw
      calc d⁻¹ * w = d⁻¹ * (w * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * w) * d⁻¹ := by rw [h1]
        _ = w * d⁻¹ := by group

omit [Finite G] [Finite K] in
theorem lift_mem_unipStab
    (hZA : Odd (Nat.card (center A)))
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    {a : G} (ha : a ∈ A) {c : ↥(adjointGroup .G2 K)} (hac : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj c)
    (hcN : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2ShortRadical K ↔
      ((c * y * c⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ g2ShortRadical K)
    (hcW : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2BCGroup K → c * y * c⁻¹ = y)
    (hcB : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2ShortRadical K →
      ((c * y * c⁻¹ * y⁻¹ : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈ g2BCGroup K) :
    a ∈ unipStab A (twoLift ψ (g2ShortRadical K)) (twoLift ψ (g2BCGroup K)) := by
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hUc : ∀ u ∈ g2BCGroup K, ∀ v ∈ g2BCGroup K, u * v = v * u :=
    fun u hu v hv => g2ShortRadical_comm u (g2BCGroup_le hu) v (g2BCGroup_le hv)
  have haN := le_normalizer ha
  have hBN : a ∈ normalizer (twoLift ψ (g2ShortRadical K) : Set G) := by
    refine mem_normalizer_twoLift hψ hZ g2ShortRadical_comm haN fun y => ?_
    rw [hac, MulAut.conj_apply]
    exact hcN y
  refine ⟨ha, hBN, fun b hb => ?_, fun w hw => ?_⟩
  · obtain ⟨hbA, hb2, y, hy, hyU⟩ := (mem_twoLift hψ hZ g2ShortRadical_comm).1 hb
    have hab : a * b * a⁻¹ ∈ twoLift ψ (g2ShortRadical K) :=
      (mem_normalizer_iff.1 hBN b).1 hb
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ twoLift ψ (g2ShortRadical K) := mul_mem hab (inv_mem hb)
    obtain ⟨hmA, hm2, -⟩ := (mem_twoLift hψ hZ g2ShortRadical_comm).1 hmem
    refine mem_twoLift_of hmA hm2 (y := c * y * c⁻¹ * y⁻¹) ?_ (hcB y hyU)
    have habA : a * b * a⁻¹ ∈ A := twoLift_le hab
    have h1 := psi_conj_eq_conj haN hbA hy habA
    have e : (⟨a * b * a⁻¹ * b⁻¹, le_normalizer hmA⟩ : normalizer (A : Set G)) =
        ⟨a * b * a⁻¹, le_normalizer habA⟩ * ⟨b, le_normalizer hbA⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, h1, hy, hac, MulAut.conj_apply, ← map_inv, ← map_mul]
  · obtain ⟨hwA, hw2, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc).1 hw
    have hBCN : a ∈ normalizer (twoLift ψ (g2BCGroup K) : Set G) := by
      refine mem_normalizer_twoLift hψ hZ hUc haN fun y' => ?_
      rw [hac, MulAut.conj_apply]
      constructor
      · intro h
        rw [hcW y' h]
        exact h
      · intro h
        have h2 : c⁻¹ * (c * y' * c⁻¹) * c⁻¹⁻¹ = c * y' * c⁻¹ := by
          have h3 := hcW _ h
          rw [inv_inv]
          calc c⁻¹ * (c * y' * c⁻¹) * c = c⁻¹ * (c * (c * y' * c⁻¹) * c⁻¹) * c := by rw [h3]
            _ = c * y' * c⁻¹ := by group
        have h4 : y' = c⁻¹ * (c * y' * c⁻¹) * c⁻¹⁻¹ := by group
        rw [h4, h2]
        exact h
    have haw : a * w * a⁻¹ ∈ twoLift ψ (g2BCGroup K) := (mem_normalizer_iff.1 hBCN w).1 hw
    have hawA : a * w * a⁻¹ ∈ A := twoLift_le haw
    have h1 := psi_conj_eq_conj haN hwA hy hawA
    rw [hac, MulAut.conj_apply, hcW y hyU] at h1
    have h2 : a * w * a⁻¹ = w := eq_of_mem_twoLift hψ hZ hUc haw hw (by rw [h1, hy])
    calc a * w = a * w * a⁻¹ * a := by group
      _ = w * a := by rw [h2]

end Rad

end CFSG.ComponentClassification.RankTwoExceptional
