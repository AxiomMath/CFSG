module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Sub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24F
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Two
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24PWreath

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a t : G}

theorem aY_mem_center (a : G) : aY a ∈ Subgroup.center (Y24 a) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : G) * a = a * (g : G)
  exact Subgroup.mem_centralizer_singleton_iff.mp g.2

theorem orderOf_aY (ha3 : orderOf a = 3) : orderOf (aY a) = 3 := by
  rw [aY, Subgroup.orderOf_mk, ha3]

theorem tY_sq (hat : a ∈ centralizer ({t} : Set G)) (ht : t ^ 2 = 1) : tY hat ^ 2 = 1 := by
  apply Subtype.ext
  show (tY hat : G) ^ 2 = 1
  rw [show (tY hat : G) = t from rfl, ht]

theorem tY_ne_one (hat : a ∈ centralizer ({t} : Set G)) (ht : t ≠ 1) : tY hat ≠ 1 := by
  intro h
  exact ht (by simpa [tY] using congrArg Subtype.val h)

theorem τY_conj (a t : G) : ∀ y s : Y24 a, τY a t s → τY a t (y * s * y⁻¹) := by
  intro y s hs
  rw [τY] at hs ⊢
  rw [isConj_iff] at hs ⊢
  obtain ⟨c, hc⟩ := hs
  refine ⟨(y : G) * c, ?_⟩
  calc (y : G) * c * t * ((y : G) * c)⁻¹
      = (y : G) * (c * t * c⁻¹) * (y : G)⁻¹ := by group
    _ = (y : G) * (s : G) * (y : G)⁻¹ := by rw [hc]
    _ = (↑(y * s * y⁻¹) : G) := by simp

theorem FY_perfect (h : Setting24 ι a) : ⁅FY ι a, FY ι a⁆ = FY ι a := by
  rw [FY, commutator_subgroupOf_of_le (Y := centralizer ({a} : Set G)) (K := F24 ι a)
    (L := F24 ι a) inf_le_right inf_le_right, F24_perfect h]

theorem FY_inf (h : Setting24 ι a) : FY ι a ⊓ zpowers (aY a) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxF, hxpow⟩ := Subgroup.mem_inf.mp hx
  have hxG_F : (x : G) ∈ F24 ι a := by
    rw [FY] at hxF
    exact Subgroup.mem_subgroupOf.mp hxF
  have hxG_pow : (x : G) ∈ zpowers a := by
    have hmap : (Subgroup.subtype (centralizer ({a} : Set G))) x
        ∈ (zpowers (aY a)).map (Subgroup.subtype (centralizer ({a} : Set G))) :=
      Subgroup.mem_map.mpr ⟨x, hxpow, rfl⟩
    rw [map_subtype_zpowers] at hmap
    simpa [aY] using hmap
  have hxG : (x : G) = 1 := by
    have hmem : (x : G) ∈ F24 ι a ⊓ zpowers a := Subgroup.mem_inf.mpr ⟨hxG_F, hxG_pow⟩
    rw [F24_inf_zpowers h] at hmem
    simpa using hmem
  exact Subtype.ext (by simpa using hxG)

theorem FY_center (h : Setting24 ι a) :
    ∀ x ∈ FY ι a, (∀ f ∈ FY ι a, x * f = f * x) → x = 1 := by
  intro x hx hxcent
  have hxG : (x : G) ∈ F24 ι a := by
    rw [FY] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  have hcent : ∀ f ∈ F24 ι a, (x : G) * f = f * (x : G) := by
    intro f hf
    have hfY : f ∈ centralizer ({a} : Set G) := (Subgroup.mem_inf.mp hf).2
    have hf' : (⟨f, hfY⟩ : Y24 a) ∈ FY ι a := by
      rw [FY]
      exact Subgroup.mem_subgroupOf.mpr hf
    have h1 := hxcent ⟨f, hfY⟩ hf'
    simpa using congrArg Subtype.val h1
  have hx1 : (x : G) = 1 := F24_center h (x : G) hxG hcent
  exact Subtype.ext (by simpa using hx1)

theorem PY_le_FY (h : Setting24 ι a) : PY ι a ≤ FY ι a := by
  rw [PY, FY]
  exact Subgroup.subgroupOf_mono (centralizer ({a} : Set G)) (P24_le_F24 (ι := ι) (a := a))

theorem card_PY (h : Setting24 ι a) : Nat.card ↥(PY ι a) = 64 := by
  rw [PY, card_subgroupOf_of_le (Y := centralizer ({a} : Set G)) (K := P24 ι a) inf_le_right,
    card_P24 h]

theorem isA8Type_PY (h : Setting24 ι a) : IsA8Type ↥(PY ι a) := by
  rw [PY]
  exact isA8Type_subgroupOf (centralizer ({a} : Set G)) inf_le_right (isA8Type_P24 h)

theorem card_two_subgroup_le_Y [Finite G] {z z₁ : G} (h : Setting24 ι a) (hD3 : HData3 G t z z₁)
    (ht : coordElt ι tv = t) (hat : a ∈ centralizer ({t} : Set G)) (ha3 : orderOf a = 3)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) :
    ∀ R : Subgroup (Y24 a), IsPGroup 2 R → Nat.card R ≤ 64 := by
  intro R hR2
  have hle : R.map (Subgroup.subtype (centralizer ({a} : Set G))) ≤ centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hR2' : IsPGroup 2 (R.map (Subgroup.subtype (centralizer ({a} : Set G)))) := hR2.map _
  have hcard := card_two_subgroup_le (ι := ι) (a := a) h hD3 ht hat ha3 hconj
    (R.map (Subgroup.subtype (centralizer ({a} : Set G)))) hle hR2'
  rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective (centralizer ({a} : Set G)))]
    at hcard

end CFSG.EvenSporadicStandard.HNRecog.Harada
