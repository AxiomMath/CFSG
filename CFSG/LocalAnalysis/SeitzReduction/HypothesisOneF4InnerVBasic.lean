module

public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Tr
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

variable {K : Type} [Field K]

theorem f4_even_of_iform_eq_four {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot .F4 γ) (h4 : iform γ γ = 4) :
    Even (γ ⟨2, by decide⟩) ∧ Even (γ ⟨3, by decide⟩) := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hγ
  clear hγ
  revert h4
  revert k
  decide +kernel

theorem f4_even_coords_smul
    (w : WeylGroup .F4) {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (h4 : iform γ γ = 4) :
    Even ((w • γ) ⟨2, by decide⟩) ∧ Even ((w • γ) ⟨3, by decide⟩) :=
  f4_even_of_iform_eq_four (IsRoot.smul hγ w) (by rw [iform_smul, h4])

theorem exists_conj_f4x_central_of_mem_borel [CharP K 2] {k : ℕ} (hk : k = 44 ∨ k = 47)
    {b : ModGL .F4 K} (hb : b ∈ borelGroup .F4 K) (c : K) :
    ∃ d : K, b * f4x K k c * b⁻¹ = f4x K k d := by
  have hb' : b ∈ (borelGroup .F4 K : Set (ModGL .F4 K)) := hb
  rw [(triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.1] at hb'
  obtain ⟨t, ht, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  have hcomm := f4x_central hk c hu
  refine ⟨torusRootChar t (orbitCertRoot .F4 k) * c, ?_⟩
  have e : t * u * f4x K k c * (t * u)⁻¹ = t * f4x K k c * t⁻¹ := by
    rw [mul_assoc t u, hcomm]
    group
  rw [e, f4x, conj_pinnedX_of_mem_torusGroup ht (f4_isRoot_pos ⟨by omega, by omega⟩).1]
  rfl

theorem conj_f4x_47_ne_f4x_44 [CharP K 2] {g : ModGL .F4 K} (hg : g ∈ adjointGroup .F4 K) :
    g * f4x K 47 1 * g⁻¹ ≠ f4x K 44 1 := by
  intro h
  have hrank := congrArg CFSG.RankThree.PartOne.F106.ShortRank.rankSubOne h
  rw [CFSG.RankThree.PartOne.F106.ShortRank.rankSubOne_conj g _ hg,
    CFSG.RankThree.PartOne.F106.ShortRank.rankSubOne_f4x47,
    CFSG.RankThree.PartOne.F106.ShortRank.rankSubOne_f4x44] at hrank
  omega

theorem borelGroup_le_normalizer_heightSeries (τ : Tag) (h : ℤ) :
    borelGroup τ K ≤ Subgroup.normalizer (heightSeries τ K h : Set (ModGL τ K)) :=
  sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1) (heightSeries_le_normalizer K h)

@[expose] def f4HeightThreeList : List ℕ := [30, 35, 36, 37, 40]

theorem f4HeightThreeList_spec :
    ∀ p ∈ f4HeightThreeList, (24 ≤ p ∧ p ≤ 47) ∧ 3 ≤ height (orbitCertRoot .F4 p) := by
  decide

theorem f4_single_eq_sub :
    ∀ i : Fin Tag.F4.rank, ∃ p ∈ f4HeightThreeList, ∃ q ∈ f4HeightThreeList,
      (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = orbitCertRoot .F4 p - orbitCertRoot .F4 q := by
  decide

theorem mem_borelGroup_of_normalizes_heightSeries_F4 {g : ModGL .F4 K}
    (hg : g ∈ adjointGroup .F4 K)
    (hN : ∀ h : ℤ, 3 ≤ h → ∀ x ∈ heightSeries .F4 K h, g * x * g⁻¹ ∈ heightSeries .F4 K h) :
    g ∈ borelGroup .F4 K := by
  have hg' : g ∈ ⋃ w, bruhatCell .F4 K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem .F4) K w with hn
  have hBN : ∀ h : ℤ, ∀ y ∈ borelGroup .F4 K, ∀ x ∈ heightSeries .F4 K h,
      y * x * y⁻¹ ∈ heightSeries .F4 K h := fun h y hy x hx =>
    (Subgroup.mem_normalizer_iff.1 (borelGroup_le_normalizer_heightSeries .F4 h hy) x).1 hx
  have hnN : ∀ h : ℤ, 3 ≤ h → ∀ x ∈ heightSeries .F4 K h, n * x * n⁻¹ ∈ heightSeries .F4 K h := by
    intro h hh x hx
    have e : n * x * n⁻¹ =
        b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) * b⁻¹⁻¹ := by
      group
    rw [e]
    exact hBN h _ (inv_mem hb) _ (hN h hh _ (hBN h _ (inv_mem hb') x hx))
  have hpos : ∀ γ, IsRoot .F4 γ → 3 ≤ height γ → 0 < height (w • γ) := by
    intro γ hγ hγ3
    rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg (IsRoot.smul hγ w) with hp | hneg
    · exact hp
    · exfalso
      have hx := hnN (height γ) hγ3 (pinnedX .F4 K γ 1)
        (pinnedX_mem_rootSpan (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ height γ ≤ height α})
          ⟨hγ, by omega, le_rfl⟩ 1)
      have hm : n * pinnedX .F4 K γ 1 * n⁻¹ ∈ rootSubgroup .F4 K (w • γ) := by
        rw [← (canonical_weyl_root_transport .F4 K).2.1 w γ hγ]
        exact ⟨_, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
      have hneg' : n * pinnedX .F4 K γ 1 * n⁻¹ ∈ negUnipotent .F4 K :=
        Subgroup.mem_iSup_of_mem (w • γ) (Subgroup.mem_iSup_of_mem ⟨IsRoot.smul hγ w, hneg⟩ hm)
      have hB : n * pinnedX .F4 K γ 1 * n⁻¹ ∈ borelGroup .F4 K :=
        Subgroup.mem_sup_right (heightSeries_le_posUnipotent _ hx)
      have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
      rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at h0
      exact one_ne_zero (pinnedX_injective .F4 K γ (h0.trans (pinnedX_zero .F4 K γ).symm))
  have htail : ∀ h : ℤ, 3 ≤ h →
      ∀ γ ∈ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α ∧ h ≤ height α},
        w • γ ∈ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α ∧ h ≤ height α} := by
    intro h hh
    refine smul_mem_of_map_conj_rootSpan_le (K := K) w (fun α hα => hα.1)
      (fun α hα => hpos α hα.1 (hh.trans hα.2.2)) (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
      heightSeriesSet_closed ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hnN h hh x hx
  have hht : ∀ γ, IsRoot .F4 γ → 3 ≤ height γ → height (w • γ) = height γ := by
    intro γ hγ hγ3
    have hge := (htail (height γ) hγ3 γ ⟨hγ, by omega, le_rfl⟩).2.2
    by_contra hne
    have hgt : height γ + 1 ≤ height (w • γ) := by omega
    have hfin : {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α ∧
        height γ + 1 ≤ height α}.Finite :=
      (finite_setOf_isRoot .F4).subset fun β hβ => hβ.1
    have hmaps : Set.MapsTo (fun β => w • β) {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧
        0 < height α ∧ height γ + 1 ≤ height α} {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β hβ => htail _ (by omega) β hβ
    have hinj : Set.InjOn (fun β => w • β) {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β _ γ' _ h => smul_left_cancel w h
    have hsurj := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj |>.surjOn
    obtain ⟨β, hβ, hβγ⟩ := hsurj ⟨IsRoot.smul hγ w, by omega, hgt⟩
    have hβγ' := smul_left_cancel w hβγ
    rw [hβγ'] at hβ
    exact absurd hβ.2.2 (by omega)
  have hw1 : w = 1 := by
    refine eq_one_of_forall_height_pos fun i => ?_
    obtain ⟨p, hp, q, hq, he⟩ := f4_single_eq_sub i
    obtain ⟨hp1, hp2⟩ := f4HeightThreeList_spec p hp
    obtain ⟨hq1, hq2⟩ := f4HeightThreeList_spec q hq
    rw [he, smul_sub, height_sub, hht _ (f4_isRoot_pos hp1).1 hp2,
      hht _ (f4_isRoot_pos hq1).1 hq2, ← height_sub, ← he, height_single]
    exact one_pos
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem exists_eq_conj_of_mem_actors_of_fix_heightSeries {β : MulAut (adjointGroup .F4 K)}
    (hβ : β ∈ diagonalFieldActors .F4 K)
    (hfix : ∀ x : adjointGroup .F4 K, (x : ModGL .F4 K) ∈ heightSeries .F4 K 3 → β x = x) :
    ∃ u ∈ posUnipotent .F4 K, ∃ hu : u ∈ adjointGroup .F4 K, β = MulAut.conj ⟨u, hu⟩ := by
  have hQC : heightSeries .F4 K 3 ≤ adjointGroup .F4 K :=
    (heightSeries_le_posUnipotent 3).trans posUnipotent_le_adjointGroup
  obtain ⟨g, hg, a, δ, hα⟩ := ((Chevalley_diagonal_field_actor_data.1 .F4 K).1 β).1 hβ
  have hfix' : ∀ x ∈ heightSeries .F4 K 3, g * diagFieldAut .F4 a δ x * g⁻¹ = x := by
    intro x hx
    have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
    rw [hα] at h1
    rw [diagFieldAut_apply]
    simpa only [mul_assoc] using h1
  have hgN : ∀ h : ℤ, 3 ≤ h → ∀ x ∈ heightSeries .F4 K h,
      g * x * g⁻¹ ∈ heightSeries .F4 K h := by
    intro h hh x hx
    have hle : heightSeries .F4 K h ≤ heightSeries .F4 K 3 :=
      iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩ le_rfl
    have hN := mem_normalizer_of_fixes (H := heightSeries .F4 K h)
      (map_diagFieldAut_rootSpan a δ fun γ hγ => hγ.1) (fun y hy => hfix' y (hle hy))
    exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx
  have hgB' : g ∈ (borelGroup .F4 K : Set (ModGL .F4 K)) :=
    mem_borelGroup_of_normalizes_heightSeries_F4 hg hgN
  rw [(triangular_borel_structure.{0, 0} .F4 K).2.2.2.2.2.1] at hgB'
  obtain ⟨u, hu, t, ht, rfl⟩ := hgB'
  beta_reduce at hg hα hfix'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set c := b * a with hc
  have hkey : ∀ γ, IsRoot .F4 γ → 3 ≤ height γ → ∀ s : K, (rootChar c γ : K) * δ s = s := by
    intro γ hγr hγ3 s
    have h1 := hfix' _ (pinnedX_mem_rootSpan
      (S := {α | IsRoot .F4 α ∧ 0 < height α ∧ 3 ≤ height α}) ⟨hγr, by omega, hγ3⟩ s)
    rw [diagFieldAut_pinnedX a δ hγr] at h1
    have h2 : u * pinnedX .F4 K γ ((rootChar c γ : K) * δ s) * u⁻¹ = pinnedX .F4 K γ s := by
      have e : pinnedX .F4 K γ ((rootChar c γ : K) * δ s) = rootDiagUnit .F4 b *
          pinnedX .F4 K γ ((rootChar a γ : K) * δ s) * (rootDiagUnit .F4 b)⁻¹ := by
        rw [rootDiagUnit_conj_pinnedX b hγr, hc, rootChar_mul_tuple, Units.val_mul, mul_assoc]
      rw [e]
      conv_rhs => rw [← h1]
      group
    exact eq_of_conj_pinnedX_eq hu hγr (by omega) h2
  have hchar : ∀ γ, IsRoot .F4 γ → 3 ≤ height γ → rootChar c γ = 1 := fun γ hγ hγ3 =>
    Units.ext (by
      have h1 := hkey γ hγ hγ3 1
      rwa [map_one, mul_one] at h1)
  have hc1 : c = 1 := funext fun i => by
    obtain ⟨p, hp, q, hq, he⟩ := f4_single_eq_sub i
    obtain ⟨hp1, hp2⟩ := f4HeightThreeList_spec p hp
    obtain ⟨hq1, hq2⟩ := f4HeightThreeList_spec q hq
    have e : orbitCertRoot .F4 p = Pi.single i 1 + orbitCertRoot .F4 q := by
      rw [he, sub_add_cancel]
    have h1 := hchar _ (f4_isRoot_pos hp1).1 hp2
    rw [e, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add, rootChar_single,
      hchar _ (f4_isRoot_pos hq1).1 hq2, mul_one] at h1
    exact h1
  have hδ : δ = 1 := RingEquiv.ext fun s => by
    have hr := (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
    have h1 := hkey _ hr (by decide) s
    rwa [hchar _ hr (by decide), Units.val_one, one_mul] at h1
  subst hδ
  have hba : rootDiagUnit .F4 b * rootDiagUnit .F4 a = 1 := by
    rw [← rootDiagUnit_mul, ← hc, hc1, rootDiagUnit_one]
  have hαu : ∀ x : adjointGroup .F4 K, (β x : ModGL .F4 K) = u * x * u⁻¹ := by
    intro x
    rw [hα, units_map_entrywiseHom_one_ringEquiv]
    calc u * rootDiagUnit .F4 b * rootDiagUnit .F4 a * x * (rootDiagUnit .F4 a)⁻¹ *
          (u * rootDiagUnit .F4 b)⁻¹ =
        u * (rootDiagUnit .F4 b * rootDiagUnit .F4 a) * x *
          (rootDiagUnit .F4 b * rootDiagUnit .F4 a)⁻¹ * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hba]; group
  refine ⟨u, hu, posUnipotent_le_adjointGroup hu, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [hαu]
  rfl

end CFSG.SeitzReduction
