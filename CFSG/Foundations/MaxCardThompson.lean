module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG

open Subgroup

universe u v

section General

variable {G : Type u} [Group G]

theorem center_map_subtype_eq_inf_centralizer (K : Subgroup G) :
    (center K).map K.subtype = K ⊓ centralizer (K : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp hc y y.2), rfl⟩

@[expose] def IsMaxCardAbelian (A : Subgroup G) : Prop :=
  IsMulCommutative A ∧ ∀ B : Subgroup G, IsMulCommutative B → Nat.card B ≤ Nat.card A

variable (G) in
@[expose] def maxCardThompson : Subgroup G :=
  sSup {A : Subgroup G | IsMaxCardAbelian A}

variable (G) in
@[expose] def maxCardZJ : Subgroup G :=
  (center (maxCardThompson G)).map (maxCardThompson G).subtype

theorem le_maxCardThompson {A : Subgroup G} (hA : IsMaxCardAbelian A) : A ≤ maxCardThompson G :=
  le_sSup hA

theorem maxCardThompson_eq_iSup :
    maxCardThompson G = ⨆ A ∈ {A : Subgroup G | IsMaxCardAbelian A}, A :=
  sSup_eq_iSup

theorem maxCardZJ_le_maxCardThompson : maxCardZJ G ≤ maxCardThompson G :=
  map_subtype_le _

theorem maxCardZJ_eq_inf_centralizer :
    maxCardZJ G = maxCardThompson G ⊓ centralizer (maxCardThompson G : Set G) :=
  center_map_subtype_eq_inf_centralizer _

theorem IsMaxCardAbelian.subgroupOf {A H : Subgroup G} (hA : IsMaxCardAbelian A) (hAH : A ≤ H) :
    IsMaxCardAbelian (A.subgroupOf H) := by
  have : IsMulCommutative A := hA.1
  refine ⟨inferInstance, fun B hB => ?_⟩
  have : IsMulCommutative B := hB
  have bound := hA.2 (B.map H.subtype) inferInstance
  rw [card_map_of_injective H.subtype_injective] at bound
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]

theorem IsMaxCardAbelian.map_subtype {H M : Subgroup G} (hM : IsMaxCardAbelian M) (hMH : M ≤ H)
    {B : Subgroup H} (hB : IsMaxCardAbelian B) : IsMaxCardAbelian (B.map H.subtype) := by
  have : IsMulCommutative B := hB.1
  refine ⟨inferInstance, fun C hC => ?_⟩
  have bound := hB.2 (M.subgroupOf H) (hM.subgroupOf hMH).1
  rw [Nat.card_congr (subgroupOfEquivOfLe hMH).toEquiv] at bound
  rw [card_map_of_injective H.subtype_injective]
  exact (hM.2 C hC).trans bound

section MulEquiv

variable {H : Type v} [Group H]

theorem IsMaxCardAbelian.map_mulEquiv (e : G ≃* H) {A : Subgroup G} (hA : IsMaxCardAbelian A) :
    IsMaxCardAbelian (A.map e.toMonoidHom) := by
  have : IsMulCommutative A := hA.1
  refine ⟨inferInstance, fun B hB => ?_⟩
  have : IsMulCommutative B := hB
  have bound := hA.2 (B.map e.symm.toMonoidHom) inferInstance
  rw [card_map_of_injective e.symm.injective] at bound
  rw [card_map_of_injective e.injective]
  exact bound

theorem maxCardThompson_map_le (e : G ≃* H) :
    (maxCardThompson G).map e.toMonoidHom ≤ maxCardThompson H := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  exact map_le_iff_le_comap.mp (le_maxCardThompson (IsMaxCardAbelian.map_mulEquiv e hA))

theorem maxCardThompson_map_mulEquiv (e : G ≃* H) :
    (maxCardThompson G).map e.toMonoidHom = maxCardThompson H := by
  apply le_antisymm (maxCardThompson_map_le e)
  have reverse := map_mono (f := e.toMonoidHom) (maxCardThompson_map_le e.symm)
  have composite : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.apply_symm_apply x
  rwa [map_map, composite, map_id] at reverse

theorem maxCardZJ_map_mulEquiv (e : G ≃* H) :
    (maxCardZJ G).map e.toMonoidHom = maxCardZJ H := by
  rw [maxCardZJ_eq_inf_centralizer, maxCardZJ_eq_inf_centralizer, ← maxCardThompson_map_mulEquiv e]
  ext x
  simp only [mem_map_equiv, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  refine and_congr_right fun _ => ⟨fun h y hy => ?_, fun h y hy => ?_⟩
  · simpa using congrArg e (h _ hy)
  · simpa using congrArg e.symm (h (e y) (by simpa using hy))

end MulEquiv

instance maxCardZJ_isMulCommutative : IsMulCommutative (maxCardZJ G) := by
  unfold maxCardZJ
  infer_instance

instance maxCardThompson_characteristic : (maxCardThompson G).Characteristic :=
  characteristic_iff_map_eq.mpr maxCardThompson_map_mulEquiv

instance maxCardZJ_characteristic : (maxCardZJ G).Characteristic :=
  characteristic_iff_map_eq.mpr maxCardZJ_map_mulEquiv

theorem normalizer_le_normalizer_image_of_characteristic (S : Subgroup G)
    (K : Subgroup S) [K.Characteristic] :
    normalizer (S : Set G) ≤ normalizer (K.map S.subtype : Set G) := by
  intro g hg
  let e : S ≃* S := ((MulAut.conj g).subgroupMap S).trans
    (MulEquiv.subgroupCongr (mem_normalizer_iff_map_conj_eq.mp hg))
  have hK : K.map e.toMonoidHom = K := characteristic_iff_map_eq.mp ‹_› e
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hcompose : (MulAut.conj g).toMonoidHom.comp S.subtype = S.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  have himage : (K.map S.subtype).map (MulAut.conj g).toMonoidHom =
      (K.map e.toMonoidHom).map S.subtype := by
    rw [map_map, map_map]
    exact congrArg (fun f => K.map f) hcompose
  exact himage.trans (by rw [hK])

@[expose] def ambientMaxCardAbelianFamily (S : Subgroup G) : Set (Subgroup G) :=
  {A : Subgroup G |
    A ≤ S ∧
      IsMulCommutative A ∧
        ∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A}

@[expose] def ambientMaxCardThompson (S : Subgroup G) : Subgroup G :=
  sSup (ambientMaxCardAbelianFamily S)

@[expose] def ambientMaxCardZJ (S : Subgroup G) : Subgroup G :=
  ambientMaxCardThompson S ⊓ centralizer (ambientMaxCardThompson S : Set G)

theorem le_ambientMaxCardThompson {S A : Subgroup G} (hA : A ∈ ambientMaxCardAbelianFamily S) :
    A ≤ ambientMaxCardThompson S :=
  le_sSup hA

theorem ambientMaxCardThompson_le (S : Subgroup G) : ambientMaxCardThompson S ≤ S :=
  sSup_le fun _ hA => hA.1

theorem ambientMaxCardZJ_le_ambientMaxCardThompson (S : Subgroup G) :
    ambientMaxCardZJ S ≤ ambientMaxCardThompson S :=
  inf_le_left

theorem ambientMaxCardZJ_le (S : Subgroup G) : ambientMaxCardZJ S ≤ S :=
  (ambientMaxCardZJ_le_ambientMaxCardThompson S).trans (ambientMaxCardThompson_le S)

theorem map_subtype_mem_ambientMaxCardAbelianFamily {S : Subgroup G} {A : Subgroup S}
    (hA : IsMaxCardAbelian A) : A.map S.subtype ∈ ambientMaxCardAbelianFamily S := by
  have : IsMulCommutative A := hA.1
  refine ⟨map_subtype_le A, inferInstance, fun B hBS hB => ?_⟩
  have : IsMulCommutative B := hB
  rw [card_map_of_injective S.subtype_injective,
    ← Nat.card_congr (subgroupOfEquivOfLe hBS).toEquiv]
  exact hA.2 _ inferInstance

theorem isMaxCardAbelian_subgroupOf_of_mem {S A : Subgroup G}
    (hA : A ∈ ambientMaxCardAbelianFamily S) : IsMaxCardAbelian (A.subgroupOf S) := by
  obtain ⟨hAS, hAc, hmax⟩ := hA
  refine ⟨inferInstance, fun B hB => ?_⟩
  have : IsMulCommutative B := hB
  rw [Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv,
    ← card_map_of_injective S.subtype_injective]
  exact hmax _ (map_subtype_le B) inferInstance

theorem ambientMaxCardAbelianFamily_top :
    ambientMaxCardAbelianFamily (⊤ : Subgroup G) = {A : Subgroup G | IsMaxCardAbelian A} := by
  ext A
  exact ⟨fun ⟨_, hA, hmax⟩ => ⟨hA, fun B hB => hmax B le_top hB⟩,
    fun ⟨hA, hmax⟩ => ⟨le_top, hA, fun B _ hB => hmax B hB⟩⟩

theorem ambientMaxCardThompson_top : ambientMaxCardThompson (⊤ : Subgroup G) = maxCardThompson G := by
  unfold ambientMaxCardThompson maxCardThompson
  rw [ambientMaxCardAbelianFamily_top]

theorem ambientMaxCardThompson_eq_map (S : Subgroup G) :
    ambientMaxCardThompson S = (maxCardThompson S).map S.subtype := by
  unfold ambientMaxCardThompson maxCardThompson
  rw [(gc_map_comap S.subtype).l_sSup, sSup_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    calc A = (A.subgroupOf S).map S.subtype := (map_subgroupOf_eq_of_le hA.1).symm
      _ ≤ _ := le_iSup₂_of_le (A.subgroupOf S) (isMaxCardAbelian_subgroupOf_of_mem hA) le_rfl
  · exact iSup₂_le fun A hA =>
      le_iSup₂_of_le (A.map S.subtype) (map_subtype_mem_ambientMaxCardAbelianFamily hA) le_rfl

theorem map_subtype_inf_centralizer_self (S : Subgroup G) (K : Subgroup S) :
    K.map S.subtype ⊓ centralizer (K.map S.subtype : Set G) =
      (K ⊓ centralizer (K : Set S)).map S.subtype := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, mem_centralizer_iff.mpr fun k hk => Subtype.ext ?_⟩, rfl⟩
    exact mem_centralizer_iff.mp hc _ ⟨k, hk, rfl⟩
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc k hk)

theorem ambientMaxCardZJ_eq_map (S : Subgroup G) :
    ambientMaxCardZJ S = (maxCardZJ S).map S.subtype := by
  unfold ambientMaxCardZJ
  rw [maxCardZJ_eq_inf_centralizer, ambientMaxCardThompson_eq_map, map_subtype_inf_centralizer_self]

theorem ambientMaxCardZJ_top : ambientMaxCardZJ (⊤ : Subgroup G) = maxCardZJ G := by
  unfold ambientMaxCardZJ
  rw [ambientMaxCardThompson_top, maxCardZJ_eq_inf_centralizer]

instance ambientMaxCardZJ_isMulCommutative (S : Subgroup G) :
    IsMulCommutative (ambientMaxCardZJ S) := by
  rw [ambientMaxCardZJ_eq_map]
  infer_instance

theorem normalizer_le_normalizer_ambientMaxCardThompson (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ambientMaxCardThompson S : Set G) :=
  ambientMaxCardThompson_eq_map S ▸
    normalizer_le_normalizer_image_of_characteristic S (maxCardThompson S)

theorem normalizer_le_normalizer_ambientMaxCardZJ (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (ambientMaxCardZJ S : Set G) :=
  ambientMaxCardZJ_eq_map S ▸ normalizer_le_normalizer_image_of_characteristic S (maxCardZJ S)

section Injective

variable {H : Type v} [Group H]

private theorem exists_mulEquiv_map_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    ∃ e : S ≃* S.map f, f.comp S.subtype = (S.map f).subtype.comp e.toMonoidHom :=
  ⟨MulEquiv.ofBijective (f.subgroupMap S)
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.subgroupMap_surjective S⟩, by ext; rfl⟩

theorem map_ambientMaxCardThompson_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (ambientMaxCardThompson S).map f = ambientMaxCardThompson (S.map f) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_map_of_injective f S hf
  rw [ambientMaxCardThompson_eq_map, ambientMaxCardThompson_eq_map, map_map, he, ← map_map,
    maxCardThompson_map_mulEquiv e]

theorem map_ambientMaxCardZJ_of_injective (f : G →* H) (S : Subgroup G)
    (hf : Function.Injective (f.comp S.subtype)) :
    (ambientMaxCardZJ S).map f = ambientMaxCardZJ (S.map f) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_map_of_injective f S hf
  rw [ambientMaxCardZJ_eq_map, ambientMaxCardZJ_eq_map, map_map, he, ← map_map,
    maxCardZJ_map_mulEquiv e]

end Injective

end General

end CFSG
