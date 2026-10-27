module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.CoprimeNormalizerSup

public section

namespace CFSG.GroupTheory

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem inf_sup_le_gpsm {S L Z : Subgroup G} [Z.Normal]
    (hZ : Nat.Coprime (Nat.card Z) 2) (hZL : Z ≤ centralizer (L : Set G))
    (hS : IsPGroup 2 S) : S ⊓ (L ⊔ Z) ≤ L := by
  exact le_of_le_sup_of_isPGroup_of_not_dvd_card (p := 2) Nat.prime_two
    (K := L) (C := Z) (Q := S ⊓ (L ⊔ Z))
    (hZL.trans (Subgroup.centralizer_le_normalizer (L : Set G))) hS.to_inf_left
    inf_le_right ((Nat.prime_two.coprime_iff_not_dvd).mp hZ.symm)

omit [Finite G] in
private theorem commutator_sup_le_gpsm {L Z : Subgroup G} [Z.Normal] (hL : ⁅L, L⁆ = L)
    (hZL : Z ≤ centralizer (L : Set G)) (hZZ : Z ≤ centralizer (Z : Set G)) :
    ⁅L ⊔ Z, L ⊔ Z⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hu
  obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hv
  have hz₁l₂ : z₁ * l₂ = l₂ * z₁ :=
    ((Subgroup.mem_centralizer_iff.1 (hZL hz₁)) l₂ hl₂).symm
  have hz₁z₂ : z₁ * z₂ = z₂ * z₁ :=
    ((Subgroup.mem_centralizer_iff.1 (hZZ hz₁)) z₂ hz₂).symm
  have hz₂l₁ : z₂ * l₁⁻¹ = l₁⁻¹ * z₂ :=
    ((Subgroup.mem_centralizer_iff.1 (hZL hz₂)) l₁⁻¹ (L.inv_mem hl₁)).symm
  have h1 : z₁ * (l₂ * z₂) = (l₂ * z₂) * z₁ := by
    calc z₁ * (l₂ * z₂) = (z₁ * l₂) * z₂ := by rw [← mul_assoc]
      _ = (l₂ * z₁) * z₂ := by rw [hz₁l₂]
      _ = l₂ * (z₁ * z₂) := by rw [mul_assoc]
      _ = l₂ * (z₂ * z₁) := by rw [hz₁z₂]
      _ = (l₂ * z₂) * z₁ := by rw [← mul_assoc]
  have e : ⁅l₁ * z₁, l₂ * z₂⁆ = ⁅l₁, l₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc l₁ * z₁ * (l₂ * z₂) * (l₁ * z₁)⁻¹ * (l₂ * z₂)⁻¹
        = l₁ * (z₁ * (l₂ * z₂)) * z₁⁻¹ * l₁⁻¹ * z₂⁻¹ * l₂⁻¹ := by group
      _ = l₁ * l₂ * (z₂ * l₁⁻¹) * z₂⁻¹ * l₂⁻¹ := by rw [h1]; group
      _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [hz₂l₁]; group
  rw [e]
  exact hL ▸ Subgroup.commutator_mem_commutator hl₁ hl₂

private theorem map_inf_gpsm {S L Z : Subgroup G} [Z.Normal]
    (hZ : Nat.Coprime (Nat.card Z) 2) (hZL : Z ≤ centralizer (L : Set G))
    (hS : IsPGroup 2 S) :
    (S.map (QuotientGroup.mk' Z)) ⊓ (L.map (QuotientGroup.mk' Z))
      = (S ⊓ L).map (QuotientGroup.mk' Z) := by
  refine le_antisymm ?_ (Subgroup.map_inf_le S L (QuotientGroup.mk' Z))
  rintro x ⟨hxS, hxL⟩
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.1 hxS
  obtain ⟨l, hl, hls⟩ := Subgroup.mem_map.1 hxL
  have hsZ : l⁻¹ * s ∈ Z := by
    have h1 : (QuotientGroup.mk' Z) (l⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, hls, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (l⁻¹ * s)).mp h1
  have hs_sup : s ∈ L ⊔ Z :=
    Subgroup.mem_sup_of_normal_right.mpr ⟨l, hl, l⁻¹ * s, hsZ, by group⟩
  exact Subgroup.mem_map.mpr
    ⟨s, ⟨hsS, inf_sup_le_gpsm hZ hZL hS ⟨hsS, hs_sup⟩⟩, rfl⟩

omit [Finite G] in
private theorem inf_comap_map_gpsm {L Z : Subgroup G} [Z.Normal] {Pbar : Subgroup (G ⧸ Z)}
    (hPle : Pbar ≤ L.map (QuotientGroup.mk' Z)) :
    (L ⊓ Pbar.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = Pbar := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, ⟨hyL, hyP⟩, rfl⟩
    exact Subgroup.mem_comap.1 hyP
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 (hPle hx)
    exact Subgroup.mem_map.mpr ⟨l, ⟨hl, Subgroup.mem_comap.mpr hx⟩, rfl⟩

omit [Finite G] in
private theorem conj_le_gpsm {L Z : Subgroup G} [Z.Normal] (hL : ⁅L, L⁆ = L)
    (hZL : Z ≤ centralizer (L : Set G)) (hZZ : Z ≤ centralizer (Z : Set G)) {g : G}
    (hg : (QuotientGroup.mk' Z) g ∈ Subgroup.normalizer
      ((L.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z))) :
    L.map (MulAut.conj g).toMonoidHom ≤ L := by
  have hconj_le : L.map (MulAut.conj g).toMonoidHom ≤ L ⊔ Z := by
    rintro x ⟨l, hl, rfl⟩
    have hπ : (QuotientGroup.mk' Z) (g * l * g⁻¹) ∈ L.map (QuotientGroup.mk' Z) := by
      have h := (Subgroup.mem_normalizer_iff.1 hg) ((QuotientGroup.mk' Z) l)
      simpa using h.mp (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)
    have hmem : g * l * g⁻¹ ∈ L ⊔ Z := by
      rw [← sup_comm, ← QuotientGroup.comap_map_mk' Z L]
      exact hπ
    simpa [MulAut.conj_apply] using hmem
  have hperf : L.map (MulAut.conj g).toMonoidHom
      = ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom), hL]
  calc L.map (MulAut.conj g).toMonoidHom
      = ⁅L.map (MulAut.conj g).toMonoidHom, L.map (MulAut.conj g).toMonoidHom⁆ := hperf
    _ ≤ ⁅L ⊔ Z, L ⊔ Z⁆ := Subgroup.commutator_mono hconj_le hconj_le
    _ ≤ L := commutator_sup_le_gpsm hL hZL hZZ

omit [Finite G] in
private theorem mem_normalizer_gpsm {L Z : Subgroup G} [Z.Normal] (hL : ⁅L, L⁆ = L)
    (hZL : Z ≤ centralizer (L : Set G)) (hZZ : Z ≤ centralizer (Z : Set G)) {g : G}
    (hg : (QuotientGroup.mk' Z) g ∈ Subgroup.normalizer
      ((L.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z))) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hg' : L.map (MulAut.conj g).toMonoidHom ≤ L := conj_le_gpsm hL hZL hZZ hg
  have hginv : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
    apply conj_le_gpsm hL hZL hZZ
    rw [map_inv]
    exact (Subgroup.normalizer
      ((L.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z))).inv_mem hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    simpa [MulAut.conj_apply] using hg' (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
  · intro hh
    have hmem : (MulAut.conj g⁻¹).toMonoidHom (g * h * g⁻¹) ∈ L :=
      hginv (Subgroup.mem_map.mpr ⟨g * h * g⁻¹, hh, rfl⟩)
    have hcalc : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    simpa [MulAut.conj_apply, hcalc] using hmem

omit [Finite G] in
private theorem inf_normalizer_lt_gpsm {S L Z : Subgroup G} [Z.Normal] {Pbar : Subgroup (G ⧸ Z)}
    (hPbar_le : Pbar ≤ L.map (QuotientGroup.mk' Z))
    (hlt : L.map (QuotientGroup.mk' Z) ⊓ Subgroup.normalizer
      (((S ⊓ L).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) < Pbar) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) <
      L ⊓ Pbar.comap (QuotientGroup.mk' Z) := by
  have hle : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤
      L ⊓ Pbar.comap (QuotientGroup.mk' Z) := by
    intro x hx
    obtain ⟨hxL, hxN⟩ := hx
    refine ⟨hxL, ?_⟩
    have hxL' : (QuotientGroup.mk' Z) x ∈ L.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map.mpr ⟨x, hxL, rfl⟩
    have hxN' : (QuotientGroup.mk' Z) x ∈ Subgroup.normalizer
        (((S ⊓ L).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) :=
      Subgroup.le_normalizer_map (QuotientGroup.mk' Z)
        (Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩)
    exact Subgroup.mem_comap.mpr (le_of_lt hlt ⟨hxL', hxN'⟩)
  refine lt_of_le_of_ne hle ?_
  intro hEq
  have hmap : (L ⊓ Pbar.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = Pbar :=
    inf_comap_map_gpsm hPbar_le
  have : Pbar ≤ L.map (QuotientGroup.mk' Z) ⊓ Subgroup.normalizer
      (((S ⊓ L).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) := by
    calc Pbar = (L ⊓ Pbar.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) := hmap.symm
      _ = (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)).map
            (QuotientGroup.mk' Z) := by rw [← hEq]
      _ ≤ L.map (QuotientGroup.mk' Z) ⊓ Subgroup.normalizer
            (((S ⊓ L).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) := by
          refine le_inf ?_ ?_
          · exact Subgroup.map_mono inf_le_left
          · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map _)
  exact (not_lt_of_ge this) hlt

omit [Finite G] in
private theorem inf_comap_lt_gpsm {L Z : Subgroup G} [Z.Normal] {Pbar : Subgroup (G ⧸ Z)}
    (hPbar_lt : Pbar < L.map (QuotientGroup.mk' Z)) :
    L ⊓ Pbar.comap (QuotientGroup.mk' Z) < L := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro hEq
  have : Pbar = L.map (QuotientGroup.mk' Z) := by
    rw [← inf_comap_map_gpsm (le_of_lt hPbar_lt), hEq]
  exact (ne_of_lt hPbar_lt) this

omit [Finite G] in
private theorem not_mem_normalizer_gpsm {Z : Subgroup G} [Z.Normal] {Pbar : Subgroup (G ⧸ Z)}
    {P : Subgroup G} {s : G} (hPmap : P.map (QuotientGroup.mk' Z) = Pbar)
    (hs : (QuotientGroup.mk' Z) s ∉ Subgroup.normalizer (Pbar : Set (G ⧸ Z))) :
    s ∉ Subgroup.normalizer (P : Set G) := by
  intro hsP
  have hmem : (QuotientGroup.mk' Z) s ∈ Subgroup.normalizer
      ((P.map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z)) : Set (G ⧸ Z)) :=
    Subgroup.le_normalizer_map (QuotientGroup.mk' Z)
      (Subgroup.mem_map.mpr ⟨s, hsP, rfl⟩)
  rw [hPmap] at hmem
  exact hs hmem

theorem IsGomiParabolicSwap.of_map_mk' {S L Z : Subgroup G} [Z.Normal]
    (hZ : Nat.Coprime (Nat.card Z) 2) (hZZ : Z ≤ centralizer (Z : Set G))
    (hZL : Z ≤ centralizer (L : Set G)) (hL : ⁅L, L⁆ = L) (hS : IsPGroup 2 S)
    (h : IsGomiParabolicSwap (S.map (QuotientGroup.mk' Z)) (L.map (QuotientGroup.mk' Z))) :
    IsGomiParabolicSwap S L := by
  obtain ⟨sbar, hsbar, Pbar, hPbar_gt, hPbar_lt, hsbar_not⟩ := h
  obtain ⟨hsbarS, hsbarN⟩ := hsbar
  obtain ⟨s, hsS, hs_eq⟩ := Subgroup.mem_map.1 hsbarS
  rw [← hs_eq] at hsbarN hsbar_not
  rw [map_inf_gpsm hZ hZL hS] at hPbar_gt
  have hsNL : s ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_gpsm hL hZL hZZ hsbarN
  exact ⟨s, ⟨hsS, hsNL⟩, L ⊓ Pbar.comap (QuotientGroup.mk' Z),
    inf_normalizer_lt_gpsm (le_of_lt hPbar_lt) hPbar_gt,
    inf_comap_lt_gpsm hPbar_lt,
    not_mem_normalizer_gpsm (inf_comap_map_gpsm (le_of_lt hPbar_lt)) hsbar_not⟩

end CFSG.GroupTheory
