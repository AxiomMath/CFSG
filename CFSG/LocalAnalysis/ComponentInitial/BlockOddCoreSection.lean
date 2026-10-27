module

public import CFSG.LocalAnalysis.ComponentInitial.BlockTransporter
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Conjugation
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.Open (aschbacherThm5OddCore aschbacherThm5Core aschbacherThm5Preimage
  aschbacherThm5Centralizes)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_self_eq_of_assemblyQuasisimple {K : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple K) : ⁅K, K⁆ = K := by
  have h := congrArg (Subgroup.map K.subtype) hq.1
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem mem_centralizer_of_centralizes_modulo {K C : Subgroup G} [Group.IsPerfect K]
    (hCK : ⁅C, K⁆ = ⊥) (hCC : ⁅C, C⁆ = ⊥) {y : G}
    (hy : ∀ a ∈ K, y⁻¹ * a⁻¹ * y * a ∈ C) : y ∈ centralizer (K : Set G) := by
  have hCK' : C ≤ centralizer (K : Set G) := commutator_eq_bot_iff_le_centralizer.1 hCK
  have hCC' : C ≤ centralizer (C : Set G) := commutator_eq_bot_iff_le_centralizer.1 hCC
  have hmem : ∀ a ∈ K, y⁻¹ * a * y * a⁻¹ ∈ C := fun a ha => by
    simpa only [inv_inv] using hy a⁻¹ (inv_mem ha)
  have hcomm : IsMulCommutative C :=
    ⟨⟨fun c d => Subtype.ext (mem_centralizer_iff.1 (hCC' c.2) d d.2).symm⟩⟩
  let δ : K →* C :=
    { toFun := fun a => ⟨y⁻¹ * a * y * a⁻¹, hmem a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change y⁻¹ * (a * b : G) * y * (a * b : G)⁻¹ =
          (y⁻¹ * a * y * (a : G)⁻¹) * (y⁻¹ * b * y * (b : G)⁻¹)
        have hb := hmem b b.2
        have hba : (a : G) * (y⁻¹ * b * y * (b : G)⁻¹) = (y⁻¹ * b * y * (b : G)⁻¹) * a :=
          (mem_centralizer_iff.1 (hCK' hb) a a.2)
        have hbc : (y⁻¹ * a * y * (a : G)⁻¹) * (y⁻¹ * b * y * (b : G)⁻¹) =
            (y⁻¹ * b * y * (b : G)⁻¹) * (y⁻¹ * a * y * (a : G)⁻¹) :=
          (mem_centralizer_iff.1 (hCC' hb) _ (hmem a a.2))
        calc y⁻¹ * (a * b : G) * y * (a * b : G)⁻¹
            = (y⁻¹ * a * y * (a : G)⁻¹) * ((a : G) * (y⁻¹ * b * y * (b : G)⁻¹)) * (a : G)⁻¹ := by
              group
          _ = (y⁻¹ * a * y * (a : G)⁻¹) * (y⁻¹ * b * y * (b : G)⁻¹) := by
              rw [hba]
              group
          _ = _ := rfl }
  have hδ : δ = 1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative δ
  rw [mem_centralizer_iff]
  intro a ha
  have h1 : y⁻¹ * a * y * a⁻¹ = 1 := by
    have := congrArg (fun φ : K →* C => ((φ ⟨a, ha⟩ : C) : G)) hδ
    simpa [δ] using this
  have h2 : y⁻¹ * a * y = a := by
    rw [mul_inv_eq_one] at h1
    exact h1
  calc a * y = y * (y⁻¹ * a * y) := by group
    _ = y * a := by rw [h2]

theorem le_of_forall_eq_mul_mem {K C X : Subgroup G} (hK : ⁅K, K⁆ = K) (hCK : ⁅C, K⁆ = ⊥)
    (hCC : ⁅C, C⁆ = ⊥) (hcover : ∀ a ∈ K, ∃ x ∈ X, ∃ o ∈ C, a = x * o) : K ≤ X := by
  have hCK' : C ≤ centralizer (K : Set G) := commutator_eq_bot_iff_le_centralizer.1 hCK
  have hCC' : C ≤ centralizer (C : Set G) := commutator_eq_bot_iff_le_centralizer.1 hCC
  have hcx : ∀ o ∈ C, ∀ a ∈ K, ∀ o' ∈ C, Commute o (a * o'⁻¹) := fun o ho a ha o' ho' => by
    have h1 : Commute o a := (mem_centralizer_iff.1 (hCK' ho) a ha).symm
    have h2 : Commute o o' := (mem_centralizer_iff.1 (hCC' ho) o' ho').symm
    exact h1.mul_right h2.inv_right
  rw [← hK]
  refine commutator_le.2 fun a ha b hb => ?_
  obtain ⟨x, hx, o, ho, rfl⟩ := hcover a ha
  obtain ⟨x', hx', o', ho', rfl⟩ := hcover b hb
  have hxa : x = x * o * o⁻¹ := by group
  have hxb : x' = x' * o' * o'⁻¹ := by group
  have h1 : Commute o (x' * o') := Commute.mul_right
    (by rw [hxb]; exact hcx o ho _ hb o' ho')
    ((mem_centralizer_iff.1 (hCC' ho) o' ho').symm)
  have h2 : Commute x o' := by
    rw [hxa]
    exact (hcx o' ho' _ ha o ho).symm
  have heq : ⁅x * o, x' * o'⁆ = ⁅x, x'⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq,
      commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq]
    group
  rw [heq, commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx hx') (X.inv_mem hx)) (X.inv_mem hx')

section OddCore

variable [Finite G] {J : Subgroup G}

omit [Finite G] in
theorem blockGroup_le_normalizer_core (J : Subgroup G) :
    blockGroup J ≤ normalizer (aschbacherThm5Core (blockGroup J) : Set G) := by
  have hle := CFSG.ComponentClassification.AschbacherTheorem5.core_le (blockGroup J)
  rw [← normal_subgroupOf_iff_le_normalizer hle]
  have : (aschbacherThm5Core (blockGroup J)).subgroupOf (blockGroup J) =
      aschbacherThm5OddCore (blockGroup J) :=
    Subgroup.comap_map_eq_self_of_injective (blockGroup J).subtype_injective _
  rw [this]
  infer_instance

theorem commutator_eq_bot_core_of_mem_block (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {K : Subgroup G}
    (hK : K ∈ block J) : ⁅K, aschbacherThm5Core (blockGroup J)⁆ = ⊥ := by
  set D := blockGroup J
  set O := aschbacherThm5Core D
  have hOD : O ≤ D := CFSG.ComponentClassification.AschbacherTheorem5.core_le D
  have hKD : K ≤ D := le_blockGroup hK
  have hDK : D ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKD).1 (normal_of_mem_block hJ heven hK)
  have hDO : D ≤ normalizer (O : Set G) := blockGroup_le_normalizer_core J
  have hqK : CFSG.Assembly.IsQuasisimple K := isQuasisimple_of_isConjOf hq hK.1
  have hCK : ⁅K, O⁆ ≤ K := le_normalizer_iff_commutator_le_left.1 (hOD.trans hDK)
  have hCO : ⁅K, O⁆ ≤ O := le_normalizer_iff_commutator_le_right.1 (hKD.trans hDO)
  have hnormal : (⁅K, O⁆.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left K O)
  rcases quasisimple_normal_subgroups_assembly hqK hnormal with htop | hcen
  · exfalso
    have hKO : K ≤ O := (subgroupOf_eq_top.1 htop).trans hCO
    have hodd := CFSG.ComponentClassification.AschbacherTheorem5.core_odd D
    have hevenK : Even (Nat.card K) := by
      obtain ⟨g, rfl⟩ := hK.1
      rwa [card_conjSub]
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (hevenK.two_dvd.trans (Subgroup.card_dvd_of_le hKO)))
  · apply perfect_double_commutator (commutator_self_eq_of_assemblyQuasisimple hqK)
    rw [commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (mem_center_iff.1
      (hcen (show (⟨c, hCK hc⟩ : K) ∈ ⁅K, O⁆.subgroupOf K from hc)) ⟨k, hk⟩)

theorem core_blockGroup_le_centralizer (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    aschbacherThm5Core (blockGroup J) ≤ centralizer (blockGroup J : Set G) := by
  rw [le_centralizer_iff]
  exact iSup₂_le fun K hK => commutator_eq_bot_iff_le_centralizer.1
    (commutator_eq_bot_core_of_mem_block hq hJ heven hK)

theorem commutator_core_blockGroup_eq_bot (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    ⁅aschbacherThm5Core (blockGroup J), aschbacherThm5Core (blockGroup J)⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  exact (core_blockGroup_le_centralizer hq hJ heven).trans
    (centralizer_le (CFSG.ComponentClassification.AschbacherTheorem5.core_le (blockGroup J)))

@[expose] def blockSection (J K : Subgroup G) :
    Subgroup (blockGroup J ⧸ aschbacherThm5OddCore (blockGroup J)) :=
  (K.subgroupOf (blockGroup J)).map (QuotientGroup.mk' (aschbacherThm5OddCore (blockGroup J)))

omit [Finite G] in
theorem preimage_blockSection {K : Subgroup G} (hK : K ≤ blockGroup J) :
    aschbacherThm5Preimage (blockGroup J) (blockSection J K) =
      K ⊔ aschbacherThm5Core (blockGroup J) := by
  rw [aschbacherThm5Preimage, blockSection, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hK]
  rfl

omit [Finite G] in
theorem le_preimage_blockSection {K : Subgroup G} (hK : K ≤ blockGroup J) :
    K ≤ aschbacherThm5Preimage (blockGroup J) (blockSection J K) := by
  rw [preimage_blockSection hK]
  exact le_sup_left

theorem isQuasisimple_blockSection (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {K : Subgroup G}
    (hK : K ∈ block J) : CFSG.Open.IsQuasisimple (blockSection J K) := by
  set D := blockGroup J
  have hKD : K ≤ D := le_blockGroup hK
  have hqK : CFSG.Assembly.IsQuasisimple K := isQuasisimple_of_isConjOf hq hK.1
  let f : K →* D ⧸ aschbacherThm5OddCore D :=
    (QuotientGroup.mk' (aschbacherThm5OddCore D)).comp (Subgroup.inclusion hKD)
  have hrange : f.range = blockSection J K := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  rcases quasisimple_homomorphic_images
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hqK) f
    with hbot | hfq
  · exfalso
    apply not_le_centralizer_self_of_isQuasisimple hqK
    have hKO : K ≤ aschbacherThm5Core D := by
      intro k hk
      have h1 : f ⟨k, hk⟩ = 1 := by rw [MonoidHom.range_eq_bot_iff.1 hbot]; rfl
      have h2 : (Subgroup.inclusion hKD ⟨k, hk⟩ : D) ∈ aschbacherThm5OddCore D :=
        (QuotientGroup.eq_one_iff _).1 h1
      exact ⟨_, h2, rfl⟩
    exact hKO.trans ((core_blockGroup_le_centralizer hq hJ heven).trans (centralizer_le hKD))
  · rw [← hrange]
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hfq

theorem commute_of_mem_blockSection (hJ : IsUniversalComponent J) (heven : Even (Nat.card J))
    {K L : Subgroup G} (hK : K ∈ block J) (hL : L ∈ block J) (hKL : K ≠ L)
    {x y : blockGroup J ⧸ aschbacherThm5OddCore (blockGroup J)}
    (hx : x ∈ blockSection J K) (hy : y ∈ blockSection J L) : x * y = y * x := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hcomm : ⁅K, L⁆ = ⊥ := (commRel_of_mem_block hJ heven hK hL).resolve_left hKL
  have hab : a * b = b * a := Subtype.ext
    ((mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm ha) b hb).symm)
  rw [← map_mul, hab, map_mul]

omit [Finite G] in
theorem iSup_blockSection :
    ⨆ K : block J, blockSection J (K : Subgroup G) = ⊤ := by
  set D := blockGroup J
  have htop : ⨆ K : block J, (K : Subgroup G).subgroupOf D = ⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmap : ∀ K : block J, ((K : Subgroup G).subgroupOf D).map D.subtype = K :=
      fun K => Subgroup.map_subgroupOf_eq_of_le (le_blockGroup K.2)
    simp only [hmap]
    exact (iSup_subtype' (p := fun K => K ∈ block J) (f := fun K _ => K)).symm
  have hmap' : (⨆ K : block J, blockSection J (K : Subgroup G)) =
      (⨆ K : block J, (K : Subgroup G).subgroupOf D).map
        (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    rw [Subgroup.map_iSup]
    rfl
  rw [hmap', htop]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem blockSection_injective (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) :
    Function.Injective fun K : block J => blockSection J (K : Subgroup G) :=
  CFSG.ComponentClassification.AschbacherTheorem5.quasisimple_factors_injective
    (fun K : block J => blockSection J (K : Subgroup G))
    (fun K => isQuasisimple_blockSection hq hJ heven K.2)
    (fun K L hKL _ hx _ hy => commute_of_mem_blockSection hJ heven K.2 L.2
      (fun h => hKL (Subtype.ext h)) hx hy)

theorem map_conj_preimage_blockSection (hq : CFSG.Assembly.IsQuasisimple J)
    (hJ : IsUniversalComponent J) (heven : Even (Nat.card J)) {h : G}
    (hh : h ∈ normalizer (blockGroup J : Set G)) {K : Subgroup G} (hK : K ∈ block J) :
    conjSub h K ∈ block J ∧
      (aschbacherThm5Preimage (blockGroup J) (blockSection J K)).map
          (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage (blockGroup J) (blockSection J (conjSub h K)) := by
  have hKh : conjSub h K ∈ block J := ((mem_normalizer_blockGroup_iff hq hJ heven h).1 hh K).1 hK
  refine ⟨hKh, ?_⟩
  rw [preimage_blockSection (le_blockGroup hK), preimage_blockSection (le_blockGroup hKh),
    Subgroup.map_sup,
    CFSG.ComponentClassification.AschbacherTheorem5.core_conjugate_eq (blockGroup J) ⟨h, hh⟩]

theorem pRank_le_pRank_preimage_blockSection {K : Subgroup G} (hK : K ∈ block J) :
    CFSG.Open.pRank 2 J ≤
      CFSG.Open.pRank 2 (aschbacherThm5Preimage (blockGroup J) (blockSection J K)) := by
  obtain ⟨g, rfl⟩ := hK.1
  obtain ⟨E, hEJ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two J
  refine CFSG.SectionRank.le_pRank one_lt_two (E := E.map (MulAut.conj g).toMonoidHom) ?_
    (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  · exact (Subgroup.map_mono hEJ).trans (le_preimage_blockSection (le_blockGroup hK))
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

end OddCore

section Transporter

variable [Finite G] {J : Subgroup G}

theorem mem_normalizer_blockGroup_of_two_element (hJ : IsUniversalComponent J)
    (heven : Even (Nat.card J)) {K L : Subgroup G} (hK : K ∈ block J) (hL : L ∈ block J)
    {t g : G} (ht : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htK : t ∈ centralizer (K : Set G)) (htL : g⁻¹ * t * g ∈ centralizer (L : Set G)) :
    g ∈ normalizer (blockGroup J : Set G) := by
  obtain ⟨k, hk⟩ := ht
  have hord : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact ht1 hm
  have h2 : 2 ∣ orderOf t := by
    rw [hm]
    exact dvd_pow_self 2 hm0
  have hpos : orderOf t ≠ 0 := by rw [hm]; positivity
  set t₀ := t ^ (orderOf t / 2) with ht₀
  have ht₀2 : orderOf t₀ = 2 := orderOf_pow_orderOf_div hpos h2
  have ht₀K : t₀ ∈ centralizer (K : Set G) := pow_mem htK _
  have hconj : g⁻¹ * t₀ * g = (g⁻¹ * t * g) ^ (orderOf t / 2) := by
    rw [show g⁻¹ * t * g = (MulAut.conj g⁻¹) t by simp,
      show g⁻¹ * t₀ * g = (MulAut.conj g⁻¹) t₀ by simp, ht₀, map_pow]
  have ht₀L : g⁻¹ * t₀ * g ∈ centralizer (L : Set G) := by
    rw [hconj]
    exact pow_mem htL _
  have hD : t₀ ∈ blockInvolutions J := ⟨ht₀2, K, hK, ht₀K⟩
  have hDg : g⁻¹ * t₀ * g ∈ blockInvolutions J :=
    ⟨by rw [orderOf_inv_mul_mul, ht₀2], L, hL, ht₀L⟩
  exact mem_normalizer_of_inv_mul_mul_mem hJ heven hD hDg

end Transporter

end CFSG.LocalAnalysis.ComponentInitial
