module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentInitial.KProperLocal
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isComponentOf_eq_or_commute [Finite G] {K L H : Subgroup G}
    (hK : CFSG.Assembly.IsComponentOf K H) (hL : CFSG.Assembly.IsComponentOf L H) :
    K = L ∨ ⁅K, L⁆ = ⊥ := by
  have hK' := (isComponentOf_iff_isComponent_subgroupOf hK.1).1 hK
  have hL' := (isComponentOf_iff_isComponent_subgroupOf hL.1).1 hL
  rcases CFSG.LocalCores.distinct_components_commute hK' hL' with h | h
  · left
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hK.1, Subgroup.map_subgroupOf_eq_of_le hL.1] at this
  · right
    have := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hK.1,
      Subgroup.map_subgroupOf_eq_of_le hL.1, Subgroup.map_bot] at this

theorem isComponentOf_map_conj {K H : Subgroup G} (hK : CFSG.Assembly.IsComponentOf K H)
    (g : G) : CFSG.Assembly.IsComponentOf (K.map (MulAut.conj g).toMonoidHom)
      (H.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hKH, hs, hq⟩ := hK
  refine ⟨Subgroup.map_mono hKH, ?_, ?_⟩
  · have := Components.chain_map (MulAut.conj g).toMonoidHom
      ((AssemblyBPredicates.isSubnormal_iff_open K H).1 hs)
    exact (AssemblyBPredicates.isSubnormal_iff_open _ _).2 this
  · rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    exact (isQuasisimple_congr (K.equivMapOfInjective _ (MulAut.conj g).injective)).1 hq

theorem map_conj_centralizer_singleton (g t : G) :
    (centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * t * g⁻¹} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hy
    rw [mem_centralizer_iff]
    rintro _ rfl
    have := hy t rfl
    change g * t * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * t * g⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc t, this, mul_assoc]
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    rw [mem_centralizer_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have := hx (g * t * g⁻¹) rfl
    have h2 : t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
    have h3 : g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
    rw [h2, h3, this]

theorem assembly_isSubnormal_inf {A B : Subgroup G} (h : CFSG.Assembly.IsSubnormal A B)
    (C : Subgroup G) : CFSG.Assembly.IsSubnormal (A ⊓ C) (B ⊓ C) :=
  h.inf C

theorem isComponentOf_of_le {K H H' : Subgroup G} (hK : CFSG.Assembly.IsComponentOf K H)
    (hKH' : K ≤ H') (hH'H : H' ≤ H) : CFSG.Assembly.IsComponentOf K H' :=
  hK.of_le_of_le hKH' hH'H

abbrev conjSub (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem conjSub_mul (g h : G) (K : Subgroup G) :
    conjSub (g * h) K = conjSub g (conjSub h K) := by
  rw [conjSub, conjSub, conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjSub_inv_conjSub (g : G) (K : Subgroup G) : conjSub g⁻¹ (conjSub g K) = K := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub, show (MulAut.conj (1 : G)).toMonoidHom =
    MonoidHom.id G from by ext; simp, Subgroup.map_id]

theorem conjSub_conjSub_inv (g : G) (K : Subgroup G) : conjSub g (conjSub g⁻¹ K) = K := by
  have := conjSub_inv_conjSub g⁻¹ K
  rwa [inv_inv] at this

theorem commutator_conjSub (g : G) (K L : Subgroup G) :
    ⁅conjSub g K, conjSub g L⁆ = conjSub g ⁅K, L⁆ := (Subgroup.map_commutator _ _ _).symm

theorem conjSub_eq_bot_iff (g : G) (K : Subgroup G) : conjSub g K = ⊥ ↔ K = ⊥ := by
  refine ⟨fun h => ?_, fun h => by rw [h, conjSub, Subgroup.map_bot]⟩
  rw [← conjSub_inv_conjSub g K, h, conjSub, Subgroup.map_bot]

theorem conjSub_centralizer (g : G) (K : Subgroup G) :
    conjSub g (centralizer (K : Set G)) = centralizer (conjSub g K : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff] at hy
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    change g * k * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * k * g⁻¹)
    have := hy k hk
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc k, this, mul_assoc]
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
    rw [mem_centralizer_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro k hk
    have := hx (g * k * g⁻¹) ⟨k, hk, rfl⟩
    have h2 : k * (g⁻¹ * x * g) = g⁻¹ * ((g * k * g⁻¹) * x) * g := by group
    have h3 : g⁻¹ * x * g * k = g⁻¹ * (x * (g * k * g⁻¹)) * g := by group
    rw [h2, h3, this]

abbrev IsUniversalComponent (J : Subgroup G) : Prop :=
  ∀ t : G, t ∈ centralizer (J : Set G) → orderOf t = 2 →
    CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))

theorem isUniversalComponent_conjSub {J : Subgroup G} (hJ : IsUniversalComponent J) (g : G) :
    IsUniversalComponent (conjSub g J) := by
  intro t ht ht2
  have ht' : g⁻¹ * t * g ∈ centralizer (J : Set G) := by
    have : g⁻¹ * t * g⁻¹⁻¹ ∈ conjSub g⁻¹ (centralizer (conjSub g J : Set G)) := ⟨t, ht, rfl⟩
    rw [conjSub_centralizer, conjSub_inv_conjSub, inv_inv] at this
    exact this
  have ht2' : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp, MulEquiv.orderOf_eq, ht2]
  have := isComponentOf_map_conj (hJ _ ht' ht2') g
  rwa [map_conj_centralizer_singleton, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this

theorem card_conjSub (g : G) (K : Subgroup G) : Nat.card (conjSub g K) = Nat.card K :=
  (Nat.card_congr (K.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

section Block

variable [Finite G] {J : Subgroup G}

theorem isComponentOf_centralizer_of_commute (hJ : IsUniversalComponent J) {g h : G}
    (heven : Even (Nat.card J)) (hKL : ⁅conjSub g J, conjSub h J⁆ = ⊥) :
    CFSG.Assembly.IsComponentOf (conjSub h J) (centralizer (conjSub g J : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : 2 ∣ Nat.card (conjSub g J) := by
    rw [card_conjSub]; exact even_iff_two_dvd.1 heven
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := conjSub g J) 2 hK2
  have hv2 : orderOf (v : G) = 2 := by rw [Subgroup.orderOf_coe, hv]
  have hLC : conjSub h J ≤ centralizer (conjSub g J : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hKL))
  have hvL : (v : G) ∈ centralizer (conjSub h J : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact (mem_centralizer_iff.1 (hLC hy) v v.2).symm
  have hcomp := isUniversalComponent_conjSub hJ h v hvL hv2
  refine isComponentOf_of_le hcomp hLC ?_
  intro x hx
  rw [mem_centralizer_iff] at hx ⊢
  rintro _ rfl
  exact hx v v.2

abbrev IsConjOf (J K : Subgroup G) : Prop := ∃ g : G, K = conjSub g J

abbrev CommRel (K L : Subgroup G) : Prop := K = L ∨ ⁅K, L⁆ = ⊥

theorem commRel_trans (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    {K L M : Subgroup G} (hK : IsConjOf J K) (hL : IsConjOf J L) (hM : IsConjOf J M)
    (hKL : CommRel K L) (hLM : CommRel L M) : CommRel K M := by
  rcases hKL with rfl | hKL
  · exact hLM
  rcases hLM with rfl | hLM
  · exact Or.inr hKL
  obtain ⟨a, rfl⟩ := hK
  obtain ⟨b, rfl⟩ := hL
  obtain ⟨c, rfl⟩ := hM
  have h1 := isComponentOf_centralizer_of_commute hJ heven
    (show ⁅conjSub b J, conjSub a J⁆ = ⊥ by rw [commutator_comm]; exact hKL)
  have h2 := isComponentOf_centralizer_of_commute hJ heven hLM
  exact isComponentOf_eq_or_commute h1 h2

omit [Finite G] in
theorem commRel_conjSub {K L : Subgroup G} (g : G) (h : CommRel K L) :
    CommRel (conjSub g K) (conjSub g L) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    rw [commutator_conjSub, h, conjSub, Subgroup.map_bot]

omit [Finite G] in
theorem isConjOf_conjSub {K : Subgroup G} (hK : IsConjOf J K) (g : G) :
    IsConjOf J (conjSub g K) := by
  obtain ⟨a, rfl⟩ := hK
  exact ⟨g * a, (conjSub_mul g a J).symm⟩

end Block

section BlockData

variable [Finite G] {J : Subgroup G}

abbrev block (J : Subgroup G) : Set (Subgroup G) := {K | IsConjOf J K ∧ CommRel J K}

abbrev blockGroup (J : Subgroup G) : Subgroup G := ⨆ K ∈ block J, K

omit [Finite G] in
theorem commRel_symm {K L : Subgroup G} (h : CommRel K L) : CommRel L K := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (by rw [commutator_comm]; exact h)

omit [Finite G] in
theorem mem_block_self : J ∈ block J := ⟨⟨1, by
  rw [conjSub, show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G from by ext; simp,
    Subgroup.map_id]⟩, Or.inl rfl⟩

theorem commRel_of_mem_block (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    {K L : Subgroup G} (hK : K ∈ block J) (hL : L ∈ block J) : CommRel K L :=
  commRel_trans hJ heven hK.1 mem_block_self.1 hL.1 (commRel_symm hK.2) hL.2

omit [Finite G] in
theorem le_blockGroup {K : Subgroup G} (hK : K ∈ block J) : K ≤ blockGroup J :=
  le_iSup₂ (f := fun K (_ : K ∈ block J) => K) K hK

omit [Finite G] in
theorem isQuasisimple_of_isConjOf (hq : CFSG.Assembly.IsQuasisimple J) {K : Subgroup G}
    (hK : IsConjOf J K) : CFSG.Assembly.IsQuasisimple K := by
  obtain ⟨g, rfl⟩ := hK
  rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact (isQuasisimple_congr (J.equivMapOfInjective _ (MulAut.conj g).injective)).1 hq

theorem normal_of_mem_block (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    {K : Subgroup G} (hK : K ∈ block J) : (K.subgroupOf (blockGroup J)).Normal := by
  refine (normal_subgroupOf_iff_le_normalizer (le_blockGroup hK)).2 (iSup₂_le fun L hL => ?_)
  rcases commRel_of_mem_block hJ heven hK hL with rfl | h
  · exact le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact h)).trans (centralizer_le_normalizer _)

theorem isComponentOf_blockGroup (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {K : Subgroup G}
    (hK : K ∈ block J) : CFSG.Assembly.IsComponentOf K (blockGroup J) :=
  ⟨le_blockGroup hK, CFSG.Assembly.IsSubnormal.step (le_blockGroup hK)
    (normal_of_mem_block hJ heven hK) (CFSG.Assembly.IsSubnormal.refl _),
    isQuasisimple_of_isConjOf hq hK.1⟩

omit [Finite G] in
theorem not_le_centralizer_self_of_isQuasisimple {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) : ¬ L ≤ centralizer (L : Set G) := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := (AssemblyBPredicates.isQuasisimple_iff_native L).1 hL
  apply hab
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hab' : a' * b' = b' * a' := Subtype.ext (mem_centralizer_iff.1 (h b'.2) a' a'.2)
  rw [← QuotientGroup.mk_mul, hab', QuotientGroup.mk_mul]

theorem mem_block_of_isComponentOf (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {L : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L (blockGroup J)) : L ∈ block J := by
  by_contra hLΔ
  apply not_le_centralizer_self_of_isQuasisimple hL.2.2
  have hM : blockGroup J ≤ centralizer (L : Set G) := iSup₂_le fun K hK => by
    rcases isComponentOf_eq_or_commute (isComponentOf_blockGroup hq hJ heven hK) hL with
      rfl | h
    · exact absurd hK hLΔ
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  exact hL.1.trans hM

omit [Finite G] in
theorem blockGroup_perfect (hq : CFSG.Assembly.IsQuasisimple J) :
    ⁅blockGroup J, blockGroup J⁆ = blockGroup J := by
  refine le_antisymm (commutator_le_self _) (iSup₂_le fun K hK => ?_)
  have hKK : ⁅K, K⁆ = K := by
    have hqK := isQuasisimple_of_isConjOf hq hK.1
    have h := congrArg (Subgroup.map K.subtype) hqK.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  rw [← hKK]
  exact commutator_mono (le_blockGroup hK) (le_blockGroup hK)

end BlockData

section BlockNormalizer

variable [Finite G] {J : Subgroup G}

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ normalizer (K : Set G)) : conjSub g K = K := by
  ext x
  rw [mem_normalizer_iff] at hg
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (hg _).2 (by simpa [mul_assoc] using hx), by simp [mul_assoc]⟩

omit [Finite G] in
theorem mem_normalizer_of_conjSub_le {g : G} {K : Subgroup G} (h1 : conjSub g K ≤ K)
    (h2 : conjSub g⁻¹ K ≤ K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact h1 ⟨x, hx, rfl⟩
  · intro hx
    have : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ K := h2 ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

theorem conjSub_mem_block (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {g : G}
    {K : Subgroup G} (hK : K ∈ block J) (hKg : conjSub g K ∈ block J) {L : Subgroup G}
    (hL : L ∈ block J) : conjSub g L ∈ block J := by
  refine ⟨isConjOf_conjSub hL.1 g, ?_⟩
  have h1 : CommRel (conjSub g K) (conjSub g L) :=
    commRel_conjSub g (commRel_of_mem_block hJ heven hK hL)
  exact commRel_trans hJ heven mem_block_self.1 hKg.1 (isConjOf_conjSub hL.1 g) hKg.2 h1

omit [Finite G] in
theorem conjSub_blockGroup_le {g : G} (hstab : ∀ L ∈ block J, conjSub g L ∈ block J) :
    conjSub g (blockGroup J) ≤ blockGroup J := by
  rw [conjSub, Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  exact iSup_le fun hL => le_blockGroup (hstab L hL)

theorem mem_normalizer_blockGroup (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    {g : G} {K : Subgroup G} (hK : K ∈ block J) (hKg : conjSub g K ∈ block J) :
    g ∈ normalizer (blockGroup J : Set G) := by
  have hKg' : conjSub g⁻¹ (conjSub g K) ∈ block J := by rw [conjSub_inv_conjSub]; exact hK
  exact mem_normalizer_of_conjSub_le
    (conjSub_blockGroup_le fun L hL => conjSub_mem_block hJ heven hK hKg hL)
    (conjSub_blockGroup_le fun L hL => conjSub_mem_block hJ heven hKg hKg' hL)

theorem mem_normalizer_blockGroup_iff (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) (g : G) :
    g ∈ normalizer (blockGroup J : Set G) ↔ ∀ K, K ∈ block J ↔ conjSub g K ∈ block J := by
  constructor
  · intro hg K
    have hM := conjSub_eq_of_mem_normalizer hg
    have hg' : g⁻¹ ∈ normalizer (blockGroup J : Set G) := inv_mem hg
    have hM' := conjSub_eq_of_mem_normalizer hg'
    constructor
    · intro hK
      have := isComponentOf_map_conj (isComponentOf_blockGroup hq hJ heven hK) g
      change CFSG.Assembly.IsComponentOf (conjSub g K) (conjSub g (blockGroup J)) at this
      rw [hM] at this
      exact mem_block_of_isComponentOf hq hJ heven this
    · intro hK
      have := isComponentOf_map_conj (isComponentOf_blockGroup hq hJ heven hK) g⁻¹
      change CFSG.Assembly.IsComponentOf (conjSub g⁻¹ (conjSub g K))
        (conjSub g⁻¹ (blockGroup J)) at this
      rw [hM', conjSub_inv_conjSub] at this
      exact mem_block_of_isComponentOf hq hJ heven this
  · intro h
    exact mem_normalizer_blockGroup hJ heven mem_block_self ((h J).1 mem_block_self)

theorem normalizer_le_normalizer_blockGroup (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {K : Subgroup G} (hK : K ∈ block J) :
    normalizer (K : Set G) ≤ normalizer (blockGroup J : Set G) := fun g hg =>
  mem_normalizer_blockGroup hJ heven hK (by rw [conjSub_eq_of_mem_normalizer hg]; exact hK)

theorem isComponentOf_normalizer_blockGroup (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {K : Subgroup G}
    (hK : K ∈ block J) :
    CFSG.Assembly.IsComponentOf K (normalizer (blockGroup J : Set G)) := by
  have hKM := isComponentOf_blockGroup hq hJ heven hK
  refine ⟨hKM.1.trans le_normalizer, ?_, hKM.2.2⟩
  exact assembly_isSubnormal_trans hKM.2.1 (CFSG.Assembly.IsSubnormal.step le_normalizer
    (Subgroup.normal_in_normalizer) (CFSG.Assembly.IsSubnormal.refl _))

theorem centralizer_le_normalizer_blockGroup (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {K : Subgroup G} (hK : K ∈ block J) {t : G}
    (ht : t ∈ centralizer (K : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (blockGroup J : Set G) := by
  intro g hg
  obtain ⟨a, rfl⟩ := hK.1
  have hcomp := isUniversalComponent_conjSub hJ a t ht ht2
  have hcomp' := isComponentOf_map_conj hcomp g
  have hgt : g * t * g⁻¹ = t := by
    rw [(mem_centralizer_iff.1 hg t rfl).symm, mul_inv_cancel_right]
  rw [map_conj_centralizer_singleton, hgt, ← conjSub] at hcomp'
  have hrel := isComponentOf_eq_or_commute hcomp hcomp'
  have hKg : conjSub g (conjSub a J) ∈ block J :=
    ⟨isConjOf_conjSub hK.1 g, commRel_trans hJ heven mem_block_self.1 hK.1
      (isConjOf_conjSub hK.1 g) hK.2 hrel⟩
  exact mem_normalizer_blockGroup hJ heven hK hKg

theorem centralizer_le_normalizer_blockGroup_of_mem (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : L ∈ block J) {t : G} (htL : t ∈ L) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (blockGroup J : Set G) := by
  obtain ⟨K, hK, hKL⟩ := hΔ.exists_ne L
  rcases commRel_of_mem_block hJ heven hK hL with h | h
  · exact absurd h hKL
  · refine centralizer_le_normalizer_blockGroup hJ heven hK ?_ ht2
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact h)) htL

theorem normalizer_blockGroup_lt_top {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hCeven : Even (Nat.card (centralizer (J : Set G)))) :
    normalizer (blockGroup J : Set G) < ⊤ ∧
      (CFSG.IsKProper G → CFSG.IsKGroup (normalizer (blockGroup J : Set G))) := by
  have hlt : normalizer (blockGroup J : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hMn : (blockGroup J).Normal := normalizer_eq_top_iff.1 htop
    have hJne : J ≠ ⊥ := by
      intro h
      apply not_le_centralizer_self_of_isQuasisimple hq
      rw [h]; exact bot_le
    have hMtop : blockGroup J = ⊤ := by
      have := hs
      rcases hMn.eq_bot_or_eq_top with h | h
      · exact absurd (eq_bot_iff.2 (h ▸ le_blockGroup mem_block_self)) hJne
      · exact h
    have hJn : J.Normal := by
      have hn := normal_of_mem_block hJ heven (mem_block_self (J := J))
      rw [hMtop] at hn
      have : (J.subgroupOf ⊤).Normal := hn
      rwa [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, top_le_iff,
        normalizer_eq_top_iff] at this
    have hJtop : J = ⊤ := by
      have := hs
      rcases hJn.eq_bot_or_eq_top with h | h
      · exact absurd h hJne
      · exact h
    have hcbot : centralizer (J : Set G) = ⊥ := by
      rw [hJtop, coe_top, centralizer_univ]
      have := hs
      rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, b, hab⟩ := hnab
        exact absurd (mem_center_iff.1 (h ▸ mem_top b : b ∈ center G) a) hab
    rw [hcbot, Subgroup.card_bot] at hCeven
    exact Nat.not_even_one hCeven
  exact ⟨hlt, fun hKP => (k_proper_local hKP).1 _ hlt⟩

end BlockNormalizer

section CentralProduct

variable [Finite G] {J : Subgroup G}

theorem blockGroup_centralProduct (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    ∃ (_ : Fintype (block J))
      (φ : ((K : block J) → (K : Subgroup G)) →* G), φ.range = blockGroup J ∧
        ∀ x ∈ φ.ker, ∀ K : block J, x K ∈ center (K : Subgroup G) := by
  classical
  have : Finite (Subgroup G) := Finite.of_injective_finite_range fun ⦃a₁ a₂⦄ a => a
  let : Fintype (block J) := Fintype.ofFinite _
  have hcomm : Pairwise fun (K L : block J) => ∀ (x : (K : Subgroup G)) (y : (L : Subgroup G)),
      Commute ((K : Subgroup G).subtype x) ((L : Subgroup G).subtype y) := by
    intro K L hKL x y
    rcases commRel_of_mem_block hJ heven K.2 L.2 with h | h
    · exact absurd (Subtype.ext h) hKL
    · exact mem_centralizer_iff.1
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (by rw [commutator_comm]; exact h)) y.2) x x.2
  refine ⟨this, MonoidHom.noncommPiCoprod (fun K : block J => (K : Subgroup G).subtype) hcomm,
    ?_, ?_⟩
  · rw [MonoidHom.noncommPiCoprod_range]
    simp only [Subgroup.range_subtype]
    exact (iSup_subtype' (p := fun K => K ∈ block J) (f := fun K _ => K)).symm
  · intro x hx K
    set φ := MonoidHom.noncommPiCoprod (fun K : block J => (K : Subgroup G).subtype) hcomm
    set y := Function.update x K 1
    have hxy : x = Pi.mulSingle K (x K) * y := by
      funext L
      by_cases hL : L = K
      · subst hL; simp [y]
      · simp [y, hL]
    have hφy : φ y ∈ centralizer ((K : Subgroup G) : Set G) := by
      rw [MonoidHom.noncommPiCoprod_apply]
      refine Subgroup.noncommProd_mem _ _ fun L _ => ?_
      by_cases hL : L = K
      · subst hL; simp [y]
      · rw [show y L = x L from Function.update_of_ne hL _ _]
        rcases commRel_of_mem_block hJ heven K.2 L.2 with h | h
        · exact absurd (Subtype.ext h).symm hL
        · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
            (by rw [commutator_comm]; exact h)) (x L).2
    have h1 : φ x = 1 := hx
    rw [hxy, map_mul, MonoidHom.noncommPiCoprod_mulSingle] at h1
    have hxK : ((x K : (K : Subgroup G)) : G) = (φ y)⁻¹ := eq_inv_of_mul_eq_one_left h1
    refine mem_center_iff.2 fun z => Subtype.ext ?_
    have hz : ((x K : (K : Subgroup G)) : G) ∈ centralizer ((K : Subgroup G) : Set G) := by
      rw [hxK]; exact inv_mem hφy
    exact mem_centralizer_iff.1 hz z z.2

end CentralProduct

theorem universal_component_commuting_block_normalizer {G : Type} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : ∀ t : G, t ∈ centralizer (J : Set G) → orderOf t = 2 →
      CFSG.Assembly.IsComponentOf J (centralizer ({t} : Set G))) :
    (∀ K L M : Subgroup G, IsConjOf J K → IsConjOf J L → IsConjOf J M →
      CommRel K K ∧ (CommRel K L → CommRel L K) ∧ (CommRel K L → CommRel L M → CommRel K M)) ∧
    (∀ (g : G) (K L : Subgroup G), CommRel K L → CommRel (conjSub g K) (conjSub g L)) ∧
    (∀ K ∈ block J, ∀ L ∈ block J, K ≠ L → ⁅K, L⁆ = ⊥) ∧
    (∀ K ∈ block J, (K.subgroupOf (blockGroup J)).Normal) ∧
    (∀ L : Subgroup G, CFSG.Assembly.IsComponentOf L (blockGroup J) ↔ L ∈ block J) ∧
    ⁅blockGroup J, blockGroup J⁆ = blockGroup J ∧
    (∃ (_ : Fintype (block J)) (φ : ((K : block J) → (K : Subgroup G)) →* G),
      φ.range = blockGroup J ∧ ∀ x ∈ φ.ker, ∀ K : block J, x K ∈ center (K : Subgroup G)) ∧
    (∀ g : G, g ∈ normalizer (blockGroup J : Set G) ↔
      ∀ K, K ∈ block J ↔ conjSub g K ∈ block J) ∧
    (∀ K ∈ block J, normalizer (K : Set G) ≤ normalizer (blockGroup J : Set G)) ∧
    (∀ K ∈ block J, CFSG.Assembly.IsComponentOf K (normalizer (blockGroup J : Set G))) ∧
    (∀ K ∈ block J, ∀ t : G, t ∈ centralizer (K : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (blockGroup J : Set G)) ∧
    ((block J).Nontrivial → ∀ L ∈ block J, ∀ t ∈ L, orderOf t = 2 →
      centralizer ({t} : Set G) ≤ normalizer (blockGroup J : Set G)) ∧
    (IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      Even (Nat.card (centralizer (J : Set G))) →
      normalizer (blockGroup J : Set G) < ⊤ ∧
        (CFSG.IsKProper G → CFSG.IsKGroup (normalizer (blockGroup J : Set G)))) := by
  refine ⟨fun K L M hK hL hM => ⟨Or.inl rfl, commRel_symm, commRel_trans hJ heven hK hL hM⟩,
    fun g K L h => commRel_conjSub g h,
    fun K hK L hL hKL => (commRel_of_mem_block hJ heven hK hL).resolve_left hKL,
    fun K hK => normal_of_mem_block hJ heven hK,
    fun L => ⟨mem_block_of_isComponentOf hq hJ heven, isComponentOf_blockGroup hq hJ heven⟩,
    blockGroup_perfect hq, blockGroup_centralProduct hJ heven,
    mem_normalizer_blockGroup_iff hq hJ heven,
    fun K hK => normalizer_le_normalizer_blockGroup hJ heven hK,
    fun K hK => isComponentOf_normalizer_blockGroup hq hJ heven hK,
    fun K hK t ht ht2 => centralizer_le_normalizer_blockGroup hJ heven hK ht ht2,
    fun hΔ L hL t htL ht2 => centralizer_le_normalizer_blockGroup_of_mem hJ heven hΔ hL htL ht2,
    fun hs hnab hCeven => normalizer_blockGroup_lt_top hq hJ heven hs hnab hCeven⟩

end CFSG.LocalAnalysis.ComponentInitial
