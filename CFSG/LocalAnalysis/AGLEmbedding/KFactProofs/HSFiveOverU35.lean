module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.OverGood
public import CFSG.LocalAnalysis.AGLEmbeddingD2.OuterBorel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSMultiplier

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbeddingD2.OuterBorel
open scoped commutatorElement

theorem commutator_self_le' {G : Type*} [Group G] (A : Subgroup G) : ⁅A, A⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem commutator_subgroupOf {G : Type*} [Group G] {A K : Subgroup G} (hAK : A ≤ K) :
    (⁅A, A⁆).subgroupOf K = ⁅A.subgroupOf K, A.subgroupOf K⁆ := by
  apply Subgroup.map_injective K.subtype_injective
  have hAA : ⁅A, A⁆ ≤ K := (commutator_self_le' A).trans hAK
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAA,
    Subgroup.map_subgroupOf_eq_of_le hAK]

structure HSU35Facts : Prop where
  card_UA : Nat.card hsOUA = 126000
  UA_le_UA2 : hsOUA ≤ hsOUA2
  card_UA2 : Nat.card hsOUA2 = 252000
  card_R0 : Nat.card hsOR0 = 125
  R0_le_UA : hsOR0 ≤ hsOUA
  card_Z : Nat.card (⁅hsOR0, hsOR0⁆ : Subgroup (Equiv.Perm (Fin 100))) = 5
  Z_le_centralizer : ⁅hsOR0, hsOR0⁆ ≤ Subgroup.centralizer (hsOR0 : Set (Equiv.Perm (Fin 100)))
  NU_le_UA : hsONU ≤ hsOUA
  UA_inf_normalizer :
    hsOUA ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) = hsONU
  orderOf_T : orderOf hsOT = 8
  T_commute : ∀ r ∈ hsOR0, hsOT * r = r * hsOT → r = 1
  T_irreducible : ∀ Y : Subgroup (Equiv.Perm (Fin 100)), ⁅hsOR0, hsOR0⁆ ≤ Y → Y ≤ hsOR0 →
    hsOT ∈ Subgroup.normalizer (Y : Set (Equiv.Perm (Fin 100))) →
      Y = ⁅hsOR0, hsOR0⁆ ∨ Y = hsOR0
  W_mem : hsOW ∈ hsOUA
  W_conj : hsOW * hsOT * hsOW⁻¹ ∈ Subgroup.zpowers hsOT
  closure_W : Subgroup.closure (insert hsOW (hsONU : Set (Equiv.Perm (Fin 100)))) = hsOUA
  centralizer_T :
    hsOUA ⊓ Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100))) = Subgroup.zpowers hsOT
  simple : IsSimpleGroup ↥hsOUA
  E9 : ∃ E : Subgroup (Equiv.Perm (Fin 100)), E ≤ hsOUA ∧ CFSG.Open.IsElemAbelian 3 E ∧
    Nat.card E = 3 ^ 2

theorem hsONU_eq_sup : hsONU = hsOR0 ⊔ Subgroup.zpowers hsOT := by
  rw [hsONU, hsOR0, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_union,
    Set.singleton_union]

theorem not_dvd_card_outer_hsOUA_of (h : HSU35Facts) : ¬ 5 ∣ Nat.card (Outer ↥hsOUA) := by
  classical
  have : IsSimpleGroup ↥hsOUA := h.simple
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set U := hsOUA with hUdef
  have hperf : Group.IsPerfect ↥U := isPerfect_of_isSimpleGroup_of_not_prime (by
    rw [h.card_UA]
    norm_num)
  have hZU : Subgroup.center ↥U = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥U) with hc | hc
    · exact hc
    · exfalso
      have hcomm : commutator ↥U = ⊥ := by
        rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
        intro a _ b _
        have hb : b ∈ Subgroup.center ↥U := hc ▸ Subgroup.mem_top b
        rw [Subgroup.mem_center_iff] at hb
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hb a
      have h1 := hperf.commutator_eq_top
      rw [hcomm] at h1
      have : Nat.card ↥U = 1 := by
        rw [← Subgroup.card_top (G := ↥U), ← h1, Subgroup.card_bot]
      rw [h.card_UA] at this
      norm_num at this
  have hfU : (Nat.card ↥U).factorization 5 = 3 := by
    rw [h.card_UA]
    have h3 : 3 ≤ (126000 : ℕ).factorization 5 :=
      (Nat.prime_five.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)
    have h4 : ¬ 4 ≤ (126000 : ℕ).factorization 5 := fun h =>
      absurd ((Nat.prime_five.pow_dvd_iff_le_factorization (by norm_num)).2 h) (by norm_num)
    omega
  have hR0card : Nat.card (hsOR0.subgroupOf U) = 5 ^ (Nat.card ↥U).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R0_le_UA).toEquiv, h.card_R0, hfU]
    norm_num
  let R : Sylow 5 ↥U := Sylow.ofCard (hsOR0.subgroupOf U) hR0card
  have hRdef : (R : Subgroup ↥U) = hsOR0.subgroupOf U := rfl
  let Z : Subgroup ↥U := (⁅hsOR0, hsOR0⁆).subgroupOf U
  have hZle : ⁅hsOR0, hsOR0⁆ ≤ U := (commutator_self_le' hsOR0).trans h.R0_le_UA
  have hNUsub : Subgroup.normalizer ((R : Subgroup ↥U) : Set ↥U) = hsONU.subgroupOf U := by
    rw [hRdef, ← Subgroup.subgroupOf_normalizer_eq h.R0_le_UA, ← h.UA_inf_normalizer,
      Subgroup.inf_subgroupOf_left]
  have hT : hsOT ∈ U := h.NU_le_UA (Subgroup.subset_closure (by simp))
  let t : ↥U := ⟨hsOT, hT⟩
  let w : ↥U := ⟨hsOW, h.W_mem⟩
  have hmemNU : ∀ x : ↥U, x ∈ hsONU.subgroupOf U ↔ (x : Equiv.Perm (Fin 100)) ∈ hsONU :=
    fun x => Subgroup.mem_subgroupOf
  refine not_dvd_card_outer_of_borel hZU R Z ?_ ?_ ?_ t ?_ ?_ ?_ ?_ ?_ w ?_ ?_ ?_
  ·
    rw [hRdef]
    exact commutator_subgroupOf h.R0_le_UA
  ·
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hz' : (z : Equiv.Perm (Fin 100)) ∈ ⁅hsOR0, hsOR0⁆ := hz
    have hr' : (r : Equiv.Perm (Fin 100)) ∈ hsOR0 := hr
    have := (Subgroup.mem_centralizer_iff.mp (h.Z_le_centralizer hz')) _ hr'
    exact Subtype.ext this
  ·
    have h1 : Nat.card Z = 5 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv, h.card_Z]
    have h2 : Nat.card (R : Subgroup ↥U) = 125 := by
      rw [hRdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R0_le_UA).toEquiv, h.card_R0]
    rw [h1, h2]
    norm_num
  ·
    rw [hNUsub]
    apply Subgroup.map_injective U.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le h.NU_le_UA, hRdef,
      Subgroup.map_subgroupOf_eq_of_le h.R0_le_UA, MonoidHom.map_zpowers, hsONU_eq_sup]
    rfl
  ·
    rw [Subgroup.orderOf_mk, h.orderOf_T]
    norm_num
  ·
    rw [Subgroup.orderOf_mk, h.orderOf_T]
    decide
  ·
    intro r hr htr
    have hr' : (r : Equiv.Perm (Fin 100)) ∈ hsOR0 := hr
    have := h.T_commute _ hr' (congrArg Subtype.val htr)
    exact Subtype.ext this
  ·
    intro Y hZY hYR htY
    have h1 : ⁅hsOR0, hsOR0⁆ ≤ Y.map U.subtype := by
      intro x hx
      exact ⟨⟨x, hZle hx⟩, hZY hx, rfl⟩
    have h2 : Y.map U.subtype ≤ hsOR0 := by
      rintro _ ⟨y, hy, rfl⟩
      exact hYR hy
    have h3 : hsOT ∈ Subgroup.normalizer ((Y.map U.subtype : Subgroup _) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp htY y).mp hy, rfl⟩
      · rintro ⟨y, hy, hye⟩
        have hgU : g ∈ U := by
          have : g = hsOT⁻¹ * (y : Equiv.Perm (Fin 100)) * hsOT := by
            rw [show (y : Equiv.Perm (Fin 100)) = hsOT * g * hsOT⁻¹ from hye]
            group
          rw [this]
          exact U.mul_mem (U.mul_mem (U.inv_mem hT) y.2) hT
        refine ⟨⟨g, hgU⟩, ?_, rfl⟩
        apply (Subgroup.mem_normalizer_iff.mp htY ⟨g, hgU⟩).mpr
        have : t * ⟨g, hgU⟩ * t⁻¹ = y := Subtype.ext hye.symm
        rw [this]
        exact hy
    rcases h.T_irreducible _ h1 h2 h3 with h4 | h4
    · left
      apply Subgroup.map_injective U.subtype_injective
      rw [h4, Subgroup.map_subgroupOf_eq_of_le hZle]
    · right
      apply Subgroup.map_injective U.subtype_injective
      rw [h4, hRdef, Subgroup.map_subgroupOf_eq_of_le h.R0_le_UA]
  ·
    rw [hNUsub]
    apply Subgroup.map_injective U.subtype_injective
    rw [MonoidHom.map_closure, Set.image_insert_eq, ← Subgroup.coe_map,
      Subgroup.map_subgroupOf_eq_of_le h.NU_le_UA, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact h.closure_W
  ·
    rw [hNUsub, hmemNU]
    exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) h.W_conj
  ·
    intro c hc
    have hc' : (c : Equiv.Perm (Fin 100)) ∈ U ⊓
        Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100))) := by
      refine ⟨c.2, ?_⟩
      show (c : Equiv.Perm (Fin 100)) ∈ Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100)))
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact congrArg Subtype.val (hc t (Set.mem_singleton t))
    rw [h.centralizer_T] at hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [← hk]
    rfl

theorem overGood_hsOUA2_of (h : HSU35Facts) : OverGood hsOR0 hsOUA2 := by
  classical
  have : IsSimpleGroup ↥hsOUA := h.simple
  have hperf : Group.IsPerfect ↥hsOUA := isPerfect_of_isSimpleGroup_of_not_prime (by
    rw [h.card_UA]
    norm_num)
  set N := hsOUA.subgroupOf hsOUA2 with hNdef
  have hindex : N.index = 2 := by
    have h1 : N.index * Nat.card N = Nat.card hsOUA2 := N.index_mul_card
    have h2 : Nat.card N = 126000 := by
      rw [hNdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.UA_le_UA2).toEquiv, h.card_UA]
    rw [h2, h.card_UA2] at h1
    omega
  have hNn : N.Normal := Subgroup.normal_of_index_eq_two hindex
  refine ⟨hsOUA, h.UA_le_UA2, ?_, Subgroup.isPerfect_iff.mp hperf, h.R0_le_UA, ?_, ?_,
    not_dvd_card_outer_hsOUA_of h, h.E9⟩
  ·
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.UA_le_UA2).mp hNn
  ·
    intro W hWU hUW
    have hn : (W.subgroupOf hsOUA).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWU).mpr hUW
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf hsOUA) with hb | ht
    · left
      rw [Subgroup.subgroupOf_eq_bot] at hb
      exact disjoint_iff.mp hb ▸ (inf_eq_left.mpr hWU).symm
    · right
      exact le_antisymm hWU (Subgroup.subgroupOf_eq_top.mp ht)
  ·
    intro W hWX hWW
    have hcomm : ⁅hsOUA2, hsOUA2⁆ ≤ hsOUA := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have hQ : Nat.card (↥hsOUA2 ⧸ N) = 2 := hindex
      have : IsCyclic (↥hsOUA2 ⧸ N) := isCyclic_of_prime_card (p := 2) hQ
      have hc := (isMulCommutative_iff.mp (inferInstance : IsMulCommutative (↥hsOUA2 ⧸ N)))
        (QuotientGroup.mk ⟨a, ha⟩) (QuotientGroup.mk ⟨b, hb⟩)
      have h1 : ((⁅(⟨a, ha⟩ : ↥hsOUA2), ⟨b, hb⟩⁆ : ↥hsOUA2) : ↥hsOUA2 ⧸ N) = 1 := by
        rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc]
        group
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      exact h2
    calc W = ⁅W, W⁆ := hWW.symm
      _ ≤ ⁅hsOUA2, hsOUA2⁆ := Subgroup.commutator_mono hWX hWX
      _ ≤ hsOUA := hcomm

theorem overGood_hsOUB2_of (hA : OverGood hsOR0 hsOUA2)
    (hw : hsOW0 ∈ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))))
    (hB : hsOUB2 = hsOUA2.map (MulAut.conj hsOW0).toMonoidHom) : OverGood hsOR0 hsOUB2 := by
  have hR : hsOR0.map (MulAut.conj hsOW0).toMonoidHom = hsOR0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have h := hA.map_equiv (G' := Equiv.Perm (Fin 100)) (MulAut.conj hsOW0)
  rw [hR, ← hB] at h
  exact h

end CFSG.AGLEmbeddingD2
