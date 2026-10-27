module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Subgroup
open scoped Pointwise

section Corefree

variable {H : Type*} [Group H] [Finite H]

theorem normal_cyclic_sylow_corefree_two_group (hcore : CFSG.oddCore H = ⊥) {R : Subgroup H}
    (hR : R.Normal) (S : Sylow 2 R) (hS : IsCyclic (S : Subgroup R)) :
    (S : Subgroup R).map R.subtype = R ∧ IsCyclic R ∧ IsPGroup 2 R ∧
      ∀ P : Sylow 2 R, (P : Subgroup R).map R.subtype = R := by
  obtain ⟨K, -, ⟨hKodd, -⟩, -, hKchar, -, hmul, -, -⟩ :=
    CFSG.Semidihedral.Principal.cyclicSylowTwo_normal_odd_complement S hS
  have hKn : (K.map R.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hK : K = ⊥ := by
    have hle : K.map R.subtype ≤ CFSG.oddCore H :=
      le_sSup ⟨hKn, by rwa [card_map_of_injective R.subtype_injective]⟩
    rwa [hcore, le_bot_iff, map_eq_bot_iff_of_injective _ R.subtype_injective] at hle
  have hStop : (S : Subgroup R) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨k, hk, s, hs, rfl⟩ : x ∈ (K : Set R) * (S : Set R) := hmul ▸ Set.mem_univ x
    rw [hK, coe_bot, Set.mem_singleton_iff] at hk
    show k * s ∈ (S : Subgroup R)
    rwa [hk, one_mul]
  have htop : IsPGroup 2 (⊤ : Subgroup R) := hStop ▸ S.isPGroup'
  refine ⟨by rw [hStop, ← MonoidHom.range_eq_map, range_subtype],
    isCyclic_of_surjective (S : Subgroup R).subtype fun x => ⟨⟨x, hStop ▸ mem_top x⟩, rfl⟩,
    htop.of_equiv topEquiv, fun P => ?_⟩
  rw [← P.is_maximal' htop le_top, ← MonoidHom.range_eq_map, range_subtype]

theorem eq_of_isCyclic_of_odd_relIndex (hcore : CFSG.oddCore H = ⊥) {R : Subgroup H}
    (hR : R.Normal) {P : Subgroup H} (hPR : P ≤ R) (hP2 : IsPGroup 2 P) (hPc : IsCyclic P)
    (hPi : ¬ 2 ∣ P.relIndex R) : P = R := by
  have e : P.subgroupOf R ≃* P := subgroupOfEquivOfLe hPR
  have h := (normal_cyclic_sylow_corefree_two_group hcore hR
    (IsPGroup.toSylow (hP2.of_equiv e.symm) hPi) (e.isCyclic.2 hPc)).1
  change (P.subgroupOf R).map R.subtype = R at h
  rwa [subgroupOf_map_subtype, inf_of_le_left hPR] at h

end Corefree

section Kernel

variable {G : Type*} [Group G] [Finite G]

private theorem eq_of_orderOf_eq_two_of_isCyclic {Z : Type*} [Group Z] [Finite Z] [IsCyclic Z]
    {x y : Z} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  have := Fintype.ofFinite Z
  have h := IsCyclic.card_orderOf_eq_totient (hx ▸ orderOf_dvd_card : 2 ∣ Fintype.card Z)
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset Z) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset Z) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

theorem standard_cyclic_sylow_unique_involution {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) :
    (S : Subgroup (centralizer (L : Set G))) ≠ ⊥ ∧
      ∃ t ∈ S, orderOf t = 2 ∧ ∀ x ∈ S, orderOf x = 2 → x = t := by
  have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := even_iff_two_dvd.1 hL.2.1
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (S.dvd_card_of_dvd_card h2)
  refine ⟨S.ne_bot_of_dvd_card h2, u, u.2, by rwa [orderOf_coe], fun x hx hx2 => ?_⟩
  exact congrArg Subtype.val
    (eq_of_orderOf_eq_two_of_isCyclic (x := ⟨x, hx⟩) (by rwa [orderOf_mk]) hu)

theorem standard_cyclic_local_centralizer_kernel {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htS : t ∈ S) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({(t : G)} : Set G)) = ⊥) :
    (S : Subgroup (centralizer (L : Set G))) ≠ ⊥ ∧
      (∀ x ∈ S, orderOf x = 2 → x = t) ∧
      L ≤ centralizer ({(t : G)} : Set G) ∧
      (L.subgroupOf (centralizer ({(t : G)} : Set G))).Normal ∧
      CFSG.Assembly.IsComponentOf L (centralizer ({(t : G)} : Set G)) ∧
      (centralizer (L.subgroupOf (centralizer ({(t : G)} : Set G)) :
          Set (centralizer ({(t : G)} : Set G)))).map (centralizer ({(t : G)} : Set G)).subtype =
        centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) ∧
      centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) =
        (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype ∧
      (((S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype).subgroupOf
        (centralizer ({(t : G)} : Set G))).Normal ∧
      L ⊓ (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype =
        (center L).map L.subtype := by
  set H := centralizer ({(t : G)} : Set G)
  set T := (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype with hT
  have ht2 : orderOf (t : G) = 2 := by rwa [orderOf_coe]
  obtain ⟨-, hLH, hLn, hcomp, hRn⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL t.2 ht2
  have hTH : T ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    have h : (⟨s, hs⟩ : (S : Subgroup (centralizer (L : Set G)))) * ⟨t, htS⟩ =
        ⟨t, htS⟩ * ⟨s, hs⟩ :=
      IsMulCommutative.is_comm.comm _ _
    have h' : ((s : centralizer (L : Set G)) : G) * t = t * s :=
      congrArg (fun z : (S : Subgroup (centralizer (L : Set G))) =>
        ((z : centralizer (L : Set G)) : G)) h
    exact mem_centralizer_singleton_iff.2 h'
  have hTCH : T ≤ centralizer (L : Set G) ⊓ H := le_inf (map_subtype_le _) hTH
  have hidx : T.relIndex (centralizer (L : Set G)) =
      (S : Subgroup (centralizer (L : Set G))).index := by
    rw [relIndex, hT, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _)]
  have hTeq : T = centralizer (L : Set G) ⊓ H := by
    have h := eq_of_isCyclic_of_odd_relIndex hcore hRn (subgroupOf_mono H hTCH)
      (S.isPGroup'.map _).comap_subtype
      (((subgroupOfEquivOfLe hTH).trans
        (equivMapOfInjective _ _ (subtype_injective _)).symm).isCyclic.2 hS)
      (by
        rw [relIndex_subgroupOf inf_le_right]
        intro h2
        apply S.not_dvd_index
        rw [← hidx, ← relIndex_mul_relIndex T _ _ hTCH inf_le_left]
        exact dvd_mul_of_dvd_left h2 _)
    rwa [subgroupOf_inj, inf_of_le_left hTH, inf_of_le_left inf_le_right] at h
  refine ⟨fun h => ?_, fun x hx hx2 => ?_, hLH, hLn, hcomp, ?_, hTeq.symm, hTeq ▸ hRn, ?_⟩
  ·
    have h1 : t = 1 := (mem_bot).1 (h ▸ htS)
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  ·
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic (x := ⟨x, hx⟩)
      (y := ⟨t, htS⟩) (by rwa [orderOf_mk]) (by rwa [orderOf_mk]))
  ·
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨mem_centralizer_iff.2 fun l hl =>
        congrArg Subtype.val (mem_centralizer_iff.1 hh ⟨l, hLH hl⟩ (mem_subgroupOf.2 hl)), h.2⟩
    · rintro ⟨hxC, hxH⟩
      exact ⟨⟨x, hxH⟩, mem_centralizer_iff.2 fun m hm =>
        Subtype.ext (mem_centralizer_iff.1 hxC m (mem_subgroupOf.1 hm)), rfl⟩
  ·
    rw [hTeq]
    apply le_antisymm
    · rintro x ⟨hxL, hxC, -⟩
      exact ⟨⟨x, hxL⟩, mem_center_iff.2 fun l =>
        Subtype.ext (mem_centralizer_iff.1 hxC l l.2), rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hzC : (z : G) ∈ centralizer (L : Set G) := mem_centralizer_iff.2 fun l hl =>
        congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩)
      exact ⟨z.2, hzC, hLH z.2⟩

theorem standard_cyclic_local_centralizer_kernel_two_group {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htS : t ∈ S) (ht : orderOf t = 2)
    (hcore : CFSG.oddCore (centralizer ({(t : G)} : Set G)) = ⊥) :
    (centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) ≠ ⊥ ∧
      IsCyclic (centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)) ∧
      IsCyclic (center L) ∧ IsPGroup 2 (center L) := by
  obtain ⟨hne, -, -, -, -, -, hR, -, hZ⟩ :=
    standard_cyclic_local_centralizer_kernel hL S hS htS ht hcore
  have hT2 : IsPGroup 2
      ((S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype) :=
    S.isPGroup'.map _
  have hTc : IsCyclic
      ((S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype) :=
    isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  have hZle : (center L).map L.subtype ≤
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype :=
    hZ ▸ inf_le_right
  have eZ := equivMapOfInjective (center L) L.subtype L.subtype_injective
  have hZc : IsCyclic ((center L).map L.subtype) := isCyclic_of_le hZle
  refine ⟨⟨?_, hR ▸ hTc, hR ▸ hT2⟩, eZ.isCyclic.2 hZc, (hT2.to_le hZle).of_equiv eZ.symm⟩
  rw [hR, Ne, map_eq_bot_iff_of_injective _ (subtype_injective _)]
  exact hne

end Kernel

end CFSG.ComponentClassification.StandardRecognition
