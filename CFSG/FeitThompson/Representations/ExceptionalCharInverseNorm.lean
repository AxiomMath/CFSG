module

public import CFSG.FeitThompson.Representations.InverseDadeNormQuadraticForm
public import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
import CFSG.FeitThompson.Representations.NonprincipalInducedOrthPrincipalInduced
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open ComplexConjugate
open CrossFamilyProjection (coherentImage coherentImage_apply)

private theorem index_ne_zero' {K : Type*} [Group K] [Finite K] (H : Subgroup K) :
    (H.index : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'

private theorem sum_sum_eq_of_row_col_eq_zero {α : Type*} (s : Finset α)
    (F : α → α → ℂ) {p q : α} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q)
    (hrow : ∀ x ∈ s, x ≠ p → x ≠ q → ∀ y, F x y = 0)
    (hcol : ∀ y ∈ s, y ≠ p → y ≠ q → ∀ x, F x y = 0) :
    ∑ x ∈ s, ∑ y ∈ s, F x y = F p p + F p q + (F q p + F q q) := by
  rw [Finset.sum_eq_add_of_mem p q hp hq hpq
    (fun x hx hne => Finset.sum_eq_zero fun y _ => hrow x hx hne.1 hne.2 y),
    Finset.sum_eq_add_of_mem p q hp hq hpq (fun y hy hne => hcol y hy hne.1 hne.2 p),
    Finset.sum_eq_add_of_mem p q hp hq hpq (fun y hy hne => hcol y hy hne.1 hne.2 q)]

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L] {A : Set G}
  {R : G → Subgroup G} {H : Subgroup ↥L} [H.Normal] {ι : Type*} {ξ : ι → (↥L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {k₀ : ι}

variable (hD : IsDadeData L A R)
  (hA : A = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}))
  (hS : Set.range ξ = indFam H (Irr ↥H \ {1}))
  (hinj : Function.Injective ξ)
  (hν : IsCoherentWith (Set.range ξ) τ ν)
  (hτ : ∀ (f : charSpanZero (Set.range ξ)) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (τ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζIrr : ξ k₀ ∈ Irr ↥L) (hζ1 : ξ k₀ 1 = (H.index : ℂ))

omit [Fintype G] [Fintype ↥L] [H.Normal] in
theorem coe_map_subtype_sdiff_one (H : Subgroup ↥L) :
    ((H.map L.subtype : Subgroup G) : Set G) \ {1}
      = (fun x : ↥L => (x : G)) '' ((H : Set ↥L) \ {1}) := by
  ext x
  constructor
  · rintro ⟨hx, hx1⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨y, ⟨hy, ?_⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    intro h
    exact hx1 (by simp [h])
  · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
    refine ⟨Subgroup.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩
    simp only [Set.mem_singleton_iff] at hy1 ⊢
    intro h
    exact hy1 (Subtype.ext h)

omit [Fintype G] in
include hS in
theorem exists_apply_one_eq_index_mul (l : ι) :
    ∃ m : ℕ, 0 < m ∧ ξ l 1 = (m : ℂ) * (H.index : ℂ) := by
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  obtain ⟨d, hd0, hdvd, hd⟩ := exists_apply_one_eq_of_mem_indFam H (hSsub ⟨l, rfl⟩)
  obtain ⟨m, rfl⟩ := hdvd
  refine ⟨m, ?_, by rw [hd]; push_cast; ring⟩
  rcases Nat.eq_zero_or_pos m with h | h
  · rw [h, Nat.mul_zero] at hd0; exact absurd hd0 (lt_irrefl 0)
  · exact h

omit [Fintype G] in
include hS in
theorem apply_one_ne_zero (l : ι) : ξ l 1 ≠ 0 := by
  obtain ⟨m, hm0, hm⟩ := exists_apply_one_eq_index_mul hS l
  rw [hm]
  exact mul_ne_zero (Nat.cast_ne_zero.2 hm0.ne') (index_ne_zero' H)

include hD hν hτ in
theorem coe_nu_eq_coe_dadeMap (f : Submodule.span ℤ (Set.range ξ)) (F : dadeDomain L A)
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have hF1 : (F : ↥L → ℂ) 1 = 0 :=
    dadeDomain.apply_eq_zero F.2 (by simpa using hD.one_notMem)
  have hf1 : (f : ↥L → ℂ) 1 = 0 := by rw [h, hF1]
  set f₀ : charSpanZero (Set.range ξ) := ⟨(f : ↥L → ℂ), mem_charSpanZero.2 ⟨f.2, hf1⟩⟩ with hf₀
  have hincl : Submodule.inclusion (charSpanZero_le (Set.range ξ)) f₀ = f := Subtype.ext rfl
  rw [← hincl, hν.eq_on_zero f₀, hτ f₀ F h]

include hD hS hν hτ in
theorem coe_dadeMap_of_coe_eq_puncturedDiff (F : dadeDomain L A) (k l : ι)
    (hF : (F : ↥L → ℂ) = puncturedDiff (ξ k) (ξ l)) :
    ((dadeMap hD F : classFun G) : G → ℂ)
      = coherentImage ξ ν l - (ξ l 1 / ξ k 1) • coherentImage ξ ν k := by
  obtain ⟨mk, hmk0, hmk⟩ := exists_apply_one_eq_index_mul hS k
  obtain ⟨ml, hml0, hml⟩ := exists_apply_one_eq_index_mul hS l
  have hidx : (H.index : ℂ) ≠ 0 := index_ne_zero' H
  have hmkne : (mk : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hmk0.ne'
  have hk1 : ξ k 1 ≠ 0 := apply_one_ne_zero hS k
  have hratio : ξ l 1 / ξ k 1 = (ml : ℂ) / (mk : ℂ) := by
    rw [hmk, hml]; field_simp
  set vl : Submodule.span ℤ (Set.range ξ) := ⟨ξ l, Submodule.subset_span ⟨l, rfl⟩⟩ with hvl
  set vk : Submodule.span ℤ (Set.range ξ) := ⟨ξ k, Submodule.subset_span ⟨k, rfl⟩⟩ with hvk
  set g : Submodule.span ℤ (Set.range ξ) := (mk : ℤ) • vl - (ml : ℤ) • vk with hg
  have hgcoe : (g : ↥L → ℂ) = (mk : ℂ) • (F : ↥L → ℂ) := by
    have h1 : (g : ↥L → ℂ) = (mk : ℤ) • (ξ l) - (ml : ℤ) • (ξ k) := by rw [hg]; rfl
    rw [h1, hF, puncturedDiff_eq, ← Int.cast_smul_eq_zsmul ℂ (mk : ℤ),
      ← Int.cast_smul_eq_zsmul ℂ (ml : ℤ)]
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Int.cast_natCast]
    rw [hratio]
    field_simp
  have hFcoe : (((mk : ℂ) • F : dadeDomain L A) : ↥L → ℂ) = (mk : ℂ) • (F : ↥L → ℂ) := rfl
  have key := coe_nu_eq_coe_dadeMap hD hν hτ g ((mk : ℂ) • F) (by rw [hgcoe, hFcoe])
  have hleft : (ν g : G → ℂ)
      = (mk : ℂ) • coherentImage ξ ν l - (ml : ℂ) • coherentImage ξ ν k := by
    rw [hg, map_sub, map_zsmul, map_zsmul]
    have h2 : ((((mk : ℤ) • ν vl - (ml : ℤ) • ν vk : virtualChars G)) : G → ℂ)
        = (mk : ℤ) • (ν vl : G → ℂ) - (ml : ℤ) • (ν vk : G → ℂ) := by simp
    rw [h2, ← Int.cast_smul_eq_zsmul ℂ (mk : ℤ), ← Int.cast_smul_eq_zsmul ℂ (ml : ℤ)]
    simp [coherentImage_apply, hvl, hvk]
  have hright : ((dadeMap hD ((mk : ℂ) • F) : classFun G) : G → ℂ)
      = (mk : ℂ) • ((dadeMap hD F : classFun G) : G → ℂ) := by
    rw [map_smul]; rfl
  rw [hleft, hright] at key
  funext x
  have hx := congrFun key x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hx ⊢
  rw [hratio]
  field_simp
  linear_combination -hx

open scoped Classical in
include hD hS hinj hν hτ hζIrr in
theorem cfInner_dadeMap_puncturedDiff_coherentImage (F : dadeDomain L A) {k : ι} (l : ι)
    (hk : k ≠ k₀) (hF : (F : ↥L → ℂ) = puncturedDiff (ξ k) (ξ l)) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) (coherentImage ξ ν k₀)
      = if l = k₀ then 1 else 0 := by
  rw [coe_dadeMap_of_coe_eq_puncturedDiff hD hS hν hτ F k l hF, cfInner_sub_left,
    cfInner_smul_left, NormalInducedWeightedNorm.cfInner_coherentImage_eq_ite H hinj hS hν l k₀,
    NormalInducedWeightedNorm.cfInner_coherentImage_eq_ite H hinj hS hν k k₀, if_neg hk]
  by_cases hl : l = k₀
  · subst hl
    rw [if_pos rfl, if_pos rfl, cfInner_self_of_mem_Irr hζIrr]
    ring
  · rw [if_neg hl, if_neg hl]
    ring

include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_dadeMap_puncturedDiff_one_coherentImage (F : dadeDomain L A) {k : ι}
    (hk : k ≠ k₀) (hF : (F : ↥L → ℂ) = puncturedDiff (ξ k) (indClassFun H (1 : ↥H → ℂ))) :
    cfInner ((dadeMap hD F : classFun G) : G → ℂ) (coherentImage ξ ν k₀)
      = dadeBetaCoeff A R H ξ ν k₀ := by
  classical
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  set Fβ : dadeDomain L A :=
    ⟨indClassFun H (1 : ↥H → ℂ) - ξ k₀, indClassFun_one_sub_mem_dadeDomain hA hζS hζ1⟩ with hFβ
  have hA' : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1} := by
    rw [hA, coe_map_subtype_sdiff_one]
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  set Fφζ : dadeDomain L A :=
    ⟨puncturedDiff (ξ k) (ξ k₀),
      puncturedDiff_mem_dadeDomain hA' (hSsub ⟨k, rfl⟩) (hSsub ⟨k₀, rfl⟩)⟩ with hFφζ
  have hsum : F = Fβ + Fφζ := by
    refine Subtype.ext ?_
    have h1 : ((Fβ + Fφζ : dadeDomain L A) : ↥L → ℂ)
        = (indClassFun H (1 : ↥H → ℂ) - ξ k₀) + puncturedDiff (ξ k) (ξ k₀) := rfl
    rw [hF, h1, puncturedDiff_eq, puncturedDiff_eq,
      NormalInducedWeightedNorm.indClassFun_one_apply_one, hζ1]
    ring
  rw [hsum, map_add]
  have hcoe : ((dadeMap hD Fβ + dadeMap hD Fφζ : classFun G) : G → ℂ)
      = ((dadeMap hD Fβ : classFun G) : G → ℂ) + ((dadeMap hD Fφζ : classFun G) : G → ℂ) := rfl
  rw [hcoe, cfInner_add_left,
    ← dadeBeta_eq_dadeMap (R := R) (H := H) (ζ := ξ k₀) hD
      (indClassFun_one_sub_mem_dadeDomain hA hζS hζ1),
    cfInner_dadeBeta_coherentImage_self,
    cfInner_dadeMap_puncturedDiff_coherentImage hD hS hinj hν hτ hζIrr Fφζ k₀ hk rfl, if_pos rfl]
  ring

open scoped Classical in
include hD hA hS hinj hν hτ hζIrr hζ1 in
theorem cfInner_self_dadeAverage_coherentImage (hS2 : (Set.range ξ).Nontrivial) :
    cfInner (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
        (fun y : ↥L => dadeAverage A R (coherentImage ξ ν k₀) (y : G))
      = 1 - (H.index : ℂ) / (Nat.card ↥H : ℂ)
        + ((dadeBetaCoeff A R H ξ ν k₀) ^ 2 * ((Nat.card ↥H : ℂ) - 1) / (H.index : ℂ)
            - 2 * dadeBetaCoeff A R H ξ ν k₀) / (Nat.card ↥H : ℂ) := by
  have hA' : A = ((H.map L.subtype : Subgroup G) : Set G) \ {1} := by
    rw [hA, coe_map_subtype_sdiff_one]
  have hχ : coherentImage ξ ν k₀ ∈ classFun G := by
    refine virtualChars_le_classFun ?_
    rw [coherentImage_apply]; exact (ν _).2
  have : Fintype (indFam H (Irr ↥H)) := Fintype.ofFinite _
  have hζS : ξ k₀ ∈ indFam H (Irr ↥H \ {1}) := hS ▸ Set.mem_range_self k₀
  have hidx : (H.index : ℂ) ≠ 0 := index_ne_zero' H
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hcardL : (Nat.card ↥L : ℂ) = (H.index : ℂ) * (Nat.card ↥H : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  obtain ⟨k, hk⟩ : ∃ k : ι, k ≠ k₀ := by
    obtain ⟨a, ha, b, hb, hab⟩ := hS2
    obtain ⟨ka, rfl⟩ := ha
    obtain ⟨kb, rfl⟩ := hb
    by_cases h : ka = k₀
    · exact ⟨kb, fun hkb => hab (by rw [h, hkb])⟩
    · exact ⟨ka, h⟩
  have hSsub : Set.range ξ ⊆ indFam H (Irr ↥H) := hS ▸ indFam_mono H Set.sdiff_subset
  set φT : indFam H (Irr ↥H) := ⟨ξ k, hSsub ⟨k, rfl⟩⟩ with hφT
  set ζT : indFam H (Irr ↥H) := ⟨ξ k₀, hSsub ⟨k₀, rfl⟩⟩ with hζT
  set ηT : indFam H (Irr ↥H) := ⟨indClassFun H (1 : ↥H → ℂ), indClassFun_one_mem_indFam H⟩ with hηT
  have hcη : cfInner ((dadeMap hD (puncturedDiffDade hA' φT ηT) : classFun G) : G → ℂ)
      (coherentImage ξ ν k₀) = dadeBetaCoeff A R H ξ ν k₀ :=
    cfInner_dadeMap_puncturedDiff_one_coherentImage hD hA hS hinj hν hτ hζIrr hζ1 _ hk
      (coe_puncturedDiffDade hA' φT ηT)
  have hcζ : cfInner ((dadeMap hD (puncturedDiffDade hA' φT ζT) : classFun G) : G → ℂ)
      (coherentImage ξ ν k₀) = 1 := by
    simpa using
      cfInner_dadeMap_puncturedDiff_coherentImage hD hS hinj hν hτ hζIrr
        (puncturedDiffDade hA' φT ζT) k₀ hk (coe_puncturedDiffDade hA' φT ζT)
  have hczero : ∀ X : indFam H (Irr ↥H), X ≠ ηT → X ≠ ζT →
      cfInner ((dadeMap hD (puncturedDiffDade hA' φT X) : classFun G) : G → ℂ)
        (coherentImage ξ ν k₀) = 0 := by
    intro X hXη hXζ
    have hXr : (X : ↥L → ℂ) ∈ Set.range ξ := by
      rw [NormalInducedWeightedNorm.range_eq_sdiff hS]
      exact ⟨X.2, fun h => hXη (Subtype.ext h)⟩
    obtain ⟨l, hl⟩ := hXr
    have hlk : l ≠ k₀ := by
      intro h
      exact hXζ (Subtype.ext (by rw [← hl, h]))
    have hFcoe : ((puncturedDiffDade hA' φT X : dadeDomain L A) : ↥L → ℂ)
        = puncturedDiff (ξ k) (ξ l) := by
      rw [coe_puncturedDiffDade, hl]
    simpa [hlk] using
      cfInner_dadeMap_puncturedDiff_coherentImage hD hS hinj hν hτ hζIrr
        (puncturedDiffDade hA' φT X) l hk hFcoe
  have hareal : conj (dadeBetaCoeff A R H ξ ν k₀) = dadeBetaCoeff A R H ξ ν k₀ := by
    obtain ⟨n, hn⟩ := exists_int_dadeBetaCoeff hD hA hS hζ1
    rw [hn]; simp
  have hηmem : ηT ∈ Finset.univ.erase φT := by
    refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩
    have h2 : indClassFun H (1 : ↥H → ℂ) ∈ Set.range ξ := by
      rw [show indClassFun H (1 : ↥H → ℂ) = ξ k from congrArg Subtype.val h]
      exact ⟨k, rfl⟩
    rw [NormalInducedWeightedNorm.range_eq_sdiff hS] at h2
    simp at h2
  have hζmem : ζT ∈ Finset.univ.erase φT := by
    refine Finset.mem_erase.2
      ⟨fun h => hk (hinj ((congrArg Subtype.val h : ξ k₀ = ξ k))).symm, Finset.mem_univ _⟩
  have hηζ : ηT ≠ ζT := by
    intro h
    have h2 : indClassFun H (1 : ↥H → ℂ) ∈ Set.range ξ := by
      rw [show indClassFun H (1 : ↥H → ℂ) = ξ k₀ from congrArg Subtype.val h]
      exact ⟨k₀, rfl⟩
    rw [NormalInducedWeightedNorm.range_eq_sdiff hS] at h2
    simp at h2
  rw [cfInner_self_dadeAverage_eq_sum_sum hD hA' hχ φT]
  rw [sum_sum_eq_of_row_col_eq_zero _ _ hηmem hζmem hηζ
    (fun X _ hXη hXζ Y => by rw [hczero X hXη hXζ]; simp)
    (fun Y _ hYη hYζ X => by rw [hczero Y hYη hYζ]; simp)]
  have hηη : cfInner (ηT : ↥L → ℂ) (ηT : ↥L → ℂ) = (H.index : ℂ) :=
    NormalInducedWeightedNorm.cfInner_self_indClassFun_one H
  have hζζ : cfInner (ζT : ↥L → ℂ) (ζT : ↥L → ℂ) = 1 := cfInner_self_of_mem_Irr hζIrr
  have hηζ0 : cfInner (ηT : ↥L → ℂ) (ζT : ↥L → ℂ) = 0 :=
    cfInner_indClassFun_one_left_of_mem_indFam_sdiff hζS
  have hζη0 : cfInner (ζT : ↥L → ℂ) (ηT : ↥L → ℂ) = 0 := by
    rw [← conj_cfInner, hηζ0, map_zero]
  have hη1 : (ηT : ↥L → ℂ) 1 = (H.index : ℂ) :=
    NormalInducedWeightedNorm.indClassFun_one_apply_one H
  have hζ1' : (ζT : ↥L → ℂ) 1 = (H.index : ℂ) := hζ1
  rw [hcη, hcζ, hηη, hζζ, hηζ0, hζη0, hη1, hζ1', hcardL, hareal, map_one]
  field_simp
  ring

end NormalInducedFamily

end CFSG.FeitThompson
