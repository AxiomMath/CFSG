module

public import CFSG.LocalAnalysis.SteinbergBNCyclicStandardOddCoreSplitting
public import CFSG.LocalAnalysis.SteinbergBNCyclicStandardSylowEscape
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section General

variable {G : Type*} [Group G]

theorem exists_sylow_centralizer_mem_of_orderOf_eq_two {L : Subgroup G} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ S : Sylow 2 (centralizer (L : Set G)),
      (⟨t, htC⟩ : centralizer (L : Set G)) ∈ (S : Subgroup (centralizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htC2 : orderOf (⟨t, htC⟩ : centralizer (L : Set G)) = 2 := by rw [orderOf_mk, ht]
  have hp : IsPGroup 2 (zpowers (⟨t, htC⟩ : centralizer (L : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  exact ⟨S, hS (mem_zpowers _)⟩

theorem normalizer_zpowers_eq_centralizer_of_involution {t : G} (ht : orderOf t = 2) :
    normalizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have htt : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, ← ht, pow_orderOf_eq_one]
  apply le_antisymm
  · intro g hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ((mem_normalizer_iff.mp hg t).mp (mem_zpowers t))
    have hconj : g * t * g⁻¹ = t := by
      rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [← two_mul, zpow_mul, htt, one_zpow] at hk
        refine absurd ?_ ht1
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = 1 := by rw [← hk]; group
      · rw [← hk, zpow_add, zpow_mul, htt, one_zpow, one_mul, zpow_one]
    rw [mem_centralizer_singleton_iff]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hconj]
  · intro g hg
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp hg) k).symm.eq

end General

section Finite

variable {G : Type*} [Group G] [Finite G]

theorem inf_centralizer_eq_zpowers_of_card_sylow_eq_two {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  obtain ⟨S, htS⟩ := exists_sylow_centralizer_mem_of_orderOf_eq_two htC ht
  have hScyc : IsCyclic (S : Subgroup (centralizer (L : Set G))) :=
    isCyclic_of_prime_card (hS2 S)
  obtain ⟨-, -, -, -, -, -, hCH, -, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hL S hScyc htS htC2 hcore
  have hSeq : (S : Subgroup (centralizer (L : Set G))) = zpowers tC :=
    (eq_of_le_of_card_ge (zpowers_le.mpr htS) (by
      rw [hS2 S, Nat.card_zpowers, htC2])).symm
  rw [hCH, hSeq, MonoidHom.map_zpowers]
  rfl

theorem exists_sylow_eq_zpowers_of_card_sylow_eq_two {L : Subgroup G}
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∃ S : Sylow 2 (centralizer (L : Set G)),
      (S : Subgroup (centralizer (L : Set G))) =
        (zpowers t).subgroupOf (centralizer (L : Set G)) := by
  obtain ⟨S, htS⟩ := exists_sylow_centralizer_mem_of_orderOf_eq_two htC ht
  refine ⟨S, ?_⟩
  have htC2 : orderOf (⟨t, htC⟩ : centralizer (L : Set G)) = 2 := by rw [orderOf_mk, ht]
  have hSeq : (S : Subgroup (centralizer (L : Set G))) = zpowers ⟨t, htC⟩ :=
    (eq_of_le_of_card_ge (zpowers_le.mpr htS) (by
      rw [hS2 S, Nat.card_zpowers, htC2])).symm
  rw [hSeq]
  apply map_injective (centralizer (L : Set G)).subtype_injective
  rw [MonoidHom.map_zpowers, subgroupOf_map_subtype, inf_of_le_left (zpowers_le.mpr htC)]
  rfl

theorem sylow_centralizer_start_of_card_sylow_eq_two {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hZ : center L = ⊥)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥) {T : Subgroup G}
    (hTH : T ≤ centralizer ({t} : Set G))
    (hT : ∃ P : Sylow 2 (centralizer ({t} : Set G)),
      (P : Subgroup (centralizer ({t} : Set G))) = T.subgroupOf (centralizer ({t} : Set G))) :
    (∃ P : Sylow 2 (normalizer (L : Set G)),
      (P : Subgroup (normalizer (L : Set G))) = T.subgroupOf (normalizer (L : Set G))) ∧
    t ∈ T ∧ T ⊓ centralizer (L : Set G) = zpowers t ∧
    (∀ m ∈ normalizer (L : Set G), m⁻¹ * t * m ∈ T → m⁻¹ * t * m = t) ∧
    (∃ U : Sylow 2 L, (U : Subgroup L) = T.subgroupOf L) ∧
    T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) ∧
    T ⊓ L ⊓ zpowers t = ⊥ ∧
    ((T ⊓ L ⊔ zpowers t).subgroupOf T).Normal ∧
    ∀ x ∈ T, ∀ l ∈ L, (∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) → x ∈ T ⊓ L ⊔ zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set G) with hHdef
  set M := normalizer (L : Set G) with hMdef
  set C := centralizer (L : Set G) with hCdef
  obtain ⟨P, hP⟩ := hT
  have hPT : (P : Subgroup H).map H.subtype = T := by
    rw [hP, subgroupOf_map_subtype, inf_of_le_left hTH]
  have hCH : C ⊓ H = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hL hS2 htC ht hcore
  obtain ⟨hHM, hLH, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htC ht
  set tC : C := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  obtain ⟨S, htS⟩ := exists_sylow_centralizer_mem_of_orderOf_eq_two htC ht
  have hScyc : IsCyclic (S : Subgroup C) := isCyclic_of_prime_card (hS2 S)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsyl⟩ :=
    CFSG.LocalAnalysis.cyclic_standard_full_normalizer_odd_core_splitting hL S hScyc htS htC2
      hcore
  obtain ⟨hST, T', hT'⟩ := hsyl P
  rw [hPT] at hST hT'
  have htT : t ∈ T := hST ⟨tC, htS, rfl⟩
  have hztT : zpowers t ≤ T := zpowers_le.mpr htT
  have hTM : T ≤ M := hTH.trans hHM
  have hTC : T ⊓ C = zpowers t := by
    refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr (mem_inf.mpr ⟨htT, htC⟩))
    rw [← hCH]
    exact mem_inf.mpr ⟨(mem_inf.mp hx).2, hTH (mem_inf.mp hx).1⟩
  have hCnorm : ∀ m ∈ M, ∀ c ∈ C, m⁻¹ * c * m ∈ C := fun m hm c hc => by
    rw [mem_centralizer_iff] at hc ⊢
    intro l hl
    have hl' : m * l * m⁻¹ ∈ L := (mem_normalizer_iff.mp hm l).mp hl
    have h1 := hc _ hl'
    calc l * (m⁻¹ * c * m) = m⁻¹ * ((m * l * m⁻¹) * c) * m := by group
      _ = m⁻¹ * (c * (m * l * m⁻¹)) * m := by rw [h1]
      _ = m⁻¹ * c * m * l := by group
  have hfus : ∀ m ∈ M, m⁻¹ * t * m ∈ T → m⁻¹ * t * m = t := fun m hm hmT => by
    have h1 : m⁻¹ * t * m ∈ zpowers t := by
      rw [← hTC]
      exact mem_inf.mpr ⟨hmT, hCnorm m hm t htC⟩
    have h2 : orderOf (m⁻¹ * t * m) = 2 := by
      rw [show m⁻¹ * t * m = MulAut.conj m⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    exact CFSG.LocalAnalysis.eq_of_orderOf_eq_two_of_isCyclic_subgroup
      (X := zpowers t) inferInstance h1 (mem_zpowers t) h2 ht
  have hU : ∃ U : Sylow 2 L, (U : Subgroup L) = T.subgroupOf L := by
    obtain ⟨Q, hQ⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hLn.isSubnormal
    let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨Q.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective]
    apply map_injective L.subtype_injective
    have hcomp : L.subtype.comp e.toMonoidHom = H.subtype.comp (L.subgroupOf H).subtype := by
      ext x
      rfl
    rw [subgroupOf_map_subtype, map_map, hcomp, ← map_map, hQ,
      map_inf_eq _ _ H.subtype H.subtype_injective, hPT, subgroupOf_map_subtype,
      inf_of_le_left hLH]
  have hTU : T ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hTM).trans inf_normalizer_le_normalizer_inf
  have hTt : T ≤ normalizer ((zpowers t : Subgroup G) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_involution ht]
    exact hTH
  have hUt : T ⊓ L ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨-, hxL⟩, hxt⟩ := mem_inf.mp hx
    have hxC : x ∈ C := zpowers_le.mpr htC hxt
    have hxZ : (⟨x, hxL⟩ : L) ∈ center L :=
      mem_center_iff.mpr fun l => Subtype.ext (mem_centralizer_iff.mp hxC l l.2)
    rw [hZ, mem_bot] at hxZ
    exact mem_bot.mpr (congrArg Subtype.val hxZ)
  have hUtn : ((T ⊓ L ⊔ zpowers t).subgroupOf T).Normal :=
    (normal_subgroupOf_iff_le_normalizer (sup_le inf_le_left hztT)).mpr
      ((le_inf hTU hTt).trans (inf_normalizer_le_normalizer_sup _ _))
  have hinner : ∀ x ∈ T, ∀ l ∈ L, (∀ y ∈ L, x * y * x⁻¹ = l * y * l⁻¹) →
      x ∈ T ⊓ L ⊔ zpowers t := by
    intro x hx l hl hxl
    have hc : l⁻¹ * x ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_,
        mul_mem (inv_mem (hLH hl)) (hTH hx)⟩
      calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
        _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [hxl y hy]
        _ = l⁻¹ * x * y := by group
    have hlT : l ∈ T := by
      have h1 := mul_mem hx (inv_mem (hztT hc))
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h1
    have hx' : x = l * (l⁻¹ * x) := by group
    rw [hx']
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hlT, hl⟩)) (mem_sup_right hc)
  exact ⟨⟨T', hT'⟩, htT, hTC, hfus, hU, hTU, hUt, hUtn, hinner⟩

end Finite

section Simple

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_ne_mem_sylow_centralizer [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({t} : Set G)) = ⊥)
    (T : Sylow 2 (centralizer ({t} : Set G))) :
    ∃ g : G, g ∉ normalizer (L : Set G) ∧
      g⁻¹ * t * g ∈ (T : Subgroup _).map (centralizer ({t} : Set G)).subtype ∧
        g⁻¹ * t * g ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, htC⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, ht]
  obtain ⟨S, htS⟩ := exists_sylow_centralizer_mem_of_orderOf_eq_two htC ht
  have hScyc : IsCyclic (S : Subgroup (centralizer (L : Set G))) := by
    obtain ⟨S', hS'⟩ := hcyc
    exact (Sylow.equiv S S').isCyclic.mpr hS'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsyl⟩ :=
    CFSG.LocalAnalysis.cyclic_standard_full_normalizer_odd_core_splitting hL S hScyc htS htC2
      hcore
  obtain ⟨hST, T', hT'⟩ := hsyl T
  have hHM : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htC ht).1
  have hTM : (T : Subgroup _).map (centralizer ({t} : Set G)).subtype ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans hHM
  have hT'eq : (T' : Subgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype =
      (T : Subgroup _).map (centralizer ({t} : Set G)).subtype := by
    rw [hT', subgroupOf_map_subtype, inf_of_le_left hTM]
  obtain ⟨-, -, -, g, hgM, -, -, -, -, -, -, -, hgT, hgS⟩ :=
    CFSG.LocalAnalysis.cyclic_standard_original_Sylow_conjugate_escape hnonab hL S hScyc htS
      htC2 T' (hT'eq ▸ hST)
  refine ⟨g, hgM, hT'eq ▸ hgT, fun h => hgS ?_⟩
  rw [h]
  exact ⟨tC, htS, rfl⟩

end Simple

end CFSG.SeitzReduction.RankOne
