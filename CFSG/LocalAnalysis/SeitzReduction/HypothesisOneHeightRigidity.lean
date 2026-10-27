module

public import CFSG.LieType.Chevalley.ParabolicRadicalPointwiseRigidity
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

variable {K : Type} [Field K]

@[expose] def SimpleDiffTail (τ : Tag) (h : ℤ) : Prop :=
  ∀ i : Fin τ.rank, ∃ γ δ : Fin τ.rank → ℤ, IsRoot τ γ ∧ IsRoot τ δ ∧ h ≤ height γ ∧
    h ≤ height δ ∧ (Pi.single i 1 : Fin τ.rank → ℤ) = γ - δ

theorem SimpleDiffTail.mono {τ : Tag} {h h' : ℤ} (hd : SimpleDiffTail τ h) (hh : h' ≤ h) :
    SimpleDiffTail τ h' := fun i => by
  obtain ⟨γ, δ, hγ, hδ, hγh, hδh, he⟩ := hd i
  exact ⟨γ, δ, hγ, hδ, hh.trans hγh, hh.trans hδh, he⟩

@[expose] def simpleDiffTailMax : Tag → ℤ
  | .G2 => 3
  | .F4 => 7
  | .D4 => 3
  | .E6 => 7
  | .E7 => 11
  | .E8 => 22

@[expose] def simpleDiffTailWitnesses : (τ : Tag) →
    List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))
  | .G2 => [((![2, 3] : Fin 2 → ℤ), (![1, 3] : Fin 2 → ℤ)),
      ((![1, 3] : Fin 2 → ℤ), (![1, 2] : Fin 2 → ℤ))]
  | .F4 => [((![2, 3, 4, 2] : Fin 4 → ℤ), (![1, 3, 4, 2] : Fin 4 → ℤ)),
      ((![1, 3, 4, 2] : Fin 4 → ℤ), (![1, 2, 4, 2] : Fin 4 → ℤ)),
      ((![1, 2, 4, 2] : Fin 4 → ℤ), (![1, 2, 3, 2] : Fin 4 → ℤ)),
      ((![1, 2, 3, 2] : Fin 4 → ℤ), (![1, 2, 3, 1] : Fin 4 → ℤ))]
  | .D4 => [((![1, 1, 1, 1] : Fin 4 → ℤ), (![0, 1, 1, 1] : Fin 4 → ℤ)),
      ((![1, 1, 1, 1] : Fin 4 → ℤ), (![1, 0, 1, 1] : Fin 4 → ℤ)),
      ((![1, 1, 2, 1] : Fin 4 → ℤ), (![1, 1, 1, 1] : Fin 4 → ℤ)),
      ((![1, 1, 1, 1] : Fin 4 → ℤ), (![1, 1, 1, 0] : Fin 4 → ℤ))]
  | .E6 => [((![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ), (![0, 1, 1, 2, 2, 1] : Fin 6 → ℤ)),
      ((![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)),
      ((![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)),
      ((![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ)),
      ((![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ)),
      ((![1, 1, 2, 2, 1, 1] : Fin 6 → ℤ), (![1, 1, 2, 2, 1, 0] : Fin 6 → ℤ))]
  | .E7 => [((![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ), (![1, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ)),
      ((![1, 2, 2, 3, 3, 2, 1] : Fin 7 → ℤ), (![1, 1, 2, 3, 3, 2, 1] : Fin 7 → ℤ)),
      ((![1, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ), (![1, 2, 2, 4, 3, 2, 1] : Fin 7 → ℤ)),
      ((![1, 2, 2, 4, 3, 2, 1] : Fin 7 → ℤ), (![1, 2, 2, 3, 3, 2, 1] : Fin 7 → ℤ)),
      ((![1, 2, 2, 3, 3, 2, 1] : Fin 7 → ℤ), (![1, 2, 2, 3, 2, 2, 1] : Fin 7 → ℤ)),
      ((![1, 2, 2, 3, 2, 2, 1] : Fin 7 → ℤ), (![1, 2, 2, 3, 2, 1, 1] : Fin 7 → ℤ)),
      ((![1, 2, 2, 3, 2, 1, 1] : Fin 7 → ℤ), (![1, 2, 2, 3, 2, 1, 0] : Fin 7 → ℤ))]
  | .E8 => [((![2, 3, 3, 5, 4, 3, 2, 1] : Fin 8 → ℤ), (![1, 3, 3, 5, 4, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 5, 4, 3, 2, 1] : Fin 8 → ℤ), (![2, 2, 4, 5, 4, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 5, 4, 3, 2, 1] : Fin 8 → ℤ), (![2, 3, 3, 5, 4, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 6, 4, 3, 2, 1] : Fin 8 → ℤ), (![2, 3, 4, 5, 4, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 6, 5, 3, 2, 1] : Fin 8 → ℤ), (![2, 3, 4, 6, 4, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 6, 5, 4, 2, 1] : Fin 8 → ℤ), (![2, 3, 4, 6, 5, 3, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 6, 5, 4, 3, 1] : Fin 8 → ℤ), (![2, 3, 4, 6, 5, 4, 2, 1] : Fin 8 → ℤ)),
      ((![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ), (![2, 3, 4, 6, 5, 4, 3, 1] : Fin 8 → ℤ))]

@[expose] def listedRootCheck (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  (List.range τ.rootCertificate.roots.length).any fun k =>
    List.ofFn (τ.rootCertificate.root k) == List.ofFn v

@[expose] def simpleDiffTailCheck (τ : Tag) (h : ℤ)
    (W : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))) : Bool :=
  (List.finRange τ.rank).all fun i => W.any fun p =>
    (List.ofFn (p.1 - p.2) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ)) &&
      decide (h ≤ height p.1) && decide (h ≤ height p.2) && listedRootCheck τ p.1 &&
        listedRootCheck τ p.2

theorem isRoot_of_listedRootCheck {τ : Tag}
    {v : Fin τ.rank → ℤ} (h : listedRootCheck τ v = true) : IsRoot τ v := by
  simp only [listedRootCheck, List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, he⟩ := h
  rw [← RootCertificate.eq_of_ofFn_beq he]
  exact RootCertificate.isRoot_root τ.rootCertificate_check k hk

theorem simpleDiffTail_of_check {τ : Tag} {h : ℤ}
    {W : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ))} (hW : simpleDiffTailCheck τ h W = true) :
    SimpleDiffTail τ h := fun i => by
  simp only [simpleDiffTailCheck, List.all_eq_true, List.mem_finRange, true_implies,
    List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hW
  obtain ⟨p, -, ⟨⟨⟨he, hγh⟩, hδh⟩, hγ⟩, hδ⟩ := hW i
  exact ⟨p.1, p.2, isRoot_of_listedRootCheck hγ, isRoot_of_listedRootCheck hδ, hγh, hδh,
    (RootCertificate.eq_of_ofFn_beq he).symm⟩

theorem simpleDiffTailCheck_eq_true : ∀ τ : Tag,
    simpleDiffTailCheck τ (simpleDiffTailMax τ) (simpleDiffTailWitnesses τ) = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel

@[expose] def tailRootList (τ : Tag) (h : ℤ) : List (Fin τ.rank → ℤ) :=
  ((List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root).filter
    fun v => decide (h ≤ height v)

@[expose] def notSimpleDiffTailCheck (τ : Tag) (h : ℤ) (i : Fin τ.rank) : Bool :=
  (tailRootList τ h).all fun γ => (tailRootList τ h).all fun δ =>
    !(List.ofFn (γ - δ) == List.ofFn (Pi.single i 1 : Fin τ.rank → ℤ))

theorem not_simpleDiffTail_of_check {τ : Tag} {h : ℤ}
    (i : Fin τ.rank) (hc : notSimpleDiffTailCheck τ h i = true) : ¬SimpleDiffTail τ h := by
  intro hd
  obtain ⟨γ, δ, hγ, hδ, hγh, hδh, he⟩ := hd i
  have hmem : ∀ v, IsRoot τ v → h ≤ height v → v ∈ tailRootList τ h := by
    intro v hv hvh
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
    simp only [tailRootList, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    exact ⟨⟨k, hk, rfl⟩, hvh⟩
  simp only [notSimpleDiffTailCheck, List.all_eq_true] at hc
  have h1 := hc γ (hmem γ hγ hγh) δ (hmem δ hδ hδh)
  rw [← he] at h1
  simp at h1

@[expose] def simpleDiffTailMaxIdx : (τ : Tag) → Fin τ.rank
  | .G2 => ⟨1, by decide⟩
  | .F4 => ⟨3, by decide⟩
  | .D4 => ⟨0, by decide⟩
  | .E6 => ⟨0, by decide⟩
  | .E7 => ⟨6, by decide⟩
  | .E8 => ⟨0, by decide⟩

theorem notSimpleDiffTailCheck_eq_true : ∀ τ : Tag,
    notSimpleDiffTailCheck τ (simpleDiffTailMax τ + 1) (simpleDiffTailMaxIdx τ) = true
  | .G2 => by decide +kernel
  | .F4 => by decide +kernel
  | .D4 => by decide +kernel
  | .E6 => by decide +kernel
  | .E7 => by decide +kernel
  | .E8 => by decide +kernel


theorem simpleDiffTail_of_le {τ : Tag} {h : ℤ} (hh : h ≤ simpleDiffTailMax τ) :
    SimpleDiffTail τ h :=
  (simpleDiffTail_of_check (simpleDiffTailCheck_eq_true τ)).mono hh

theorem simpleDiffTail_iff {τ : Tag} {h : ℤ} : SimpleDiffTail τ h ↔ h ≤ simpleDiffTailMax τ := by
  refine ⟨fun hd => ?_, simpleDiffTail_of_le⟩
  by_contra hlt
  exact not_simpleDiffTail_of_check _ (notSimpleDiffTailCheck_eq_true τ) (hd.mono (by omega))

theorem simpleDiffTail_one (τ : Tag) : SimpleDiffTail τ 1 :=
  simpleDiffTail_of_le (by cases τ <;> decide)

theorem simpleDiffTail_E6_4 : SimpleDiffTail .E6 4 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E6_5 : SimpleDiffTail .E6 5 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E7_5 : SimpleDiffTail .E7 5 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E7_7 : SimpleDiffTail .E7 7 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E7_10 : SimpleDiffTail .E7 10 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E8_7 : SimpleDiffTail .E8 7 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E8_11 : SimpleDiffTail .E8 11 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_E8_13 : SimpleDiffTail .E8 13 := simpleDiffTail_of_le (by decide)

theorem simpleDiffTail_F4_3 : SimpleDiffTail .F4 3 := simpleDiffTail_of_le (by decide)

theorem mem_borelGroup_of_normalizes_heightSeries {τ : Tag} {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail τ h) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries τ K h', g * x * g⁻¹ ∈ heightSeries τ K h') :
    g ∈ borelGroup τ K := by
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  set n := canonicalRep (coxeterSystem τ) K w with hn
  have hBN : ∀ h' : ℤ, ∀ y ∈ borelGroup τ K, ∀ x ∈ heightSeries τ K h',
      y * x * y⁻¹ ∈ heightSeries τ K h' := fun h' y hy x hx =>
    (Subgroup.mem_normalizer_iff.1 ((sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
      (heightSeries_le_normalizer K h') : borelGroup τ K ≤ _) hy) x).1 hx
  have hnN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries τ K h',
      n * x * n⁻¹ ∈ heightSeries τ K h' := by
    intro h' hh x hx
    have e : n * x * n⁻¹ =
        b⁻¹ * ((b * n * b') * (b'⁻¹ * x * b'⁻¹⁻¹) * (b * n * b')⁻¹) * b⁻¹⁻¹ := by
      group
    rw [e]
    exact hBN h' _ (inv_mem hb) _ (hN h' hh _ (hBN h' _ (inv_mem hb') x hx))
  have hpos : ∀ γ, IsRoot τ γ → h ≤ height γ → 0 < height (w • γ) := by
    intro γ hγ hγh
    rcases CFSG.LieType.Chevalley.IsRoot.height_pos_or_neg (IsRoot.smul hγ w) with hp | hneg
    · exact hp
    · exfalso
      have hx := hnN (height γ) hγh (pinnedX τ K γ 1)
        (pinnedX_mem_rootSpan (S := {α | IsRoot τ α ∧ 0 < height α ∧ height γ ≤ height α})
          ⟨hγ, by omega, le_rfl⟩ 1)
      have hm : n * pinnedX τ K γ 1 * n⁻¹ ∈ rootSubgroup τ K (w • γ) := by
        rw [← (canonical_weyl_root_transport τ K).2.1 w γ hγ]
        exact ⟨_, Subgroup.subset_closure ⟨1, rfl⟩, rfl⟩
      have hneg' : n * pinnedX τ K γ 1 * n⁻¹ ∈ negUnipotent τ K :=
        Subgroup.mem_iSup_of_mem (w • γ) (Subgroup.mem_iSup_of_mem ⟨IsRoot.smul hγ w, hneg⟩ hm)
      have hB : n * pinnedX τ K γ 1 * n⁻¹ ∈ borelGroup τ K :=
        Subgroup.mem_sup_right (heightSeries_le_posUnipotent _ hx)
      have h0 := Subgroup.mem_inf.2 ⟨hB, hneg'⟩
      rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at h0
      exact one_ne_zero (pinnedX_injective τ K γ (h0.trans (pinnedX_zero τ K γ).symm))
  have htail : ∀ h' : ℤ, h ≤ h' →
      ∀ γ ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ h' ≤ height α},
        w • γ ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ h' ≤ height α} := by
    intro h' hh
    refine smul_mem_of_map_conj_rootSpan_le (K := K) w (fun α hα => hα.1)
      (fun α hα => hpos α hα.1 (hh.trans hα.2.2)) (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
      heightSeriesSet_closed ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hnN h' hh x hx
  have hht : ∀ γ, IsRoot τ γ → h ≤ height γ → height (w • γ) = height γ := by
    intro γ hγ hγh
    have hge := (htail (height γ) hγh γ ⟨hγ, by omega, le_rfl⟩).2.2
    by_contra hne
    have hgt : height γ + 1 ≤ height (w • γ) := by omega
    have hfin : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧
        height γ + 1 ≤ height α}.Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
    have hmaps : Set.MapsTo (fun β => w • β) {α : Fin τ.rank → ℤ | IsRoot τ α ∧
        0 < height α ∧ height γ + 1 ≤ height α} {α : Fin τ.rank → ℤ | IsRoot τ α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β hβ => htail _ (by omega) β hβ
    have hinj : Set.InjOn (fun β => w • β) {α : Fin τ.rank → ℤ | IsRoot τ α ∧
        0 < height α ∧ height γ + 1 ≤ height α} := fun β _ γ' _ h => smul_left_cancel w h
    have hsurj := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj |>.surjOn
    obtain ⟨β, hβ, hβγ⟩ := hsurj ⟨IsRoot.smul hγ w, by omega, hgt⟩
    have hβγ' := smul_left_cancel w hβγ
    rw [hβγ'] at hβ
    exact absurd hβ.2.2 (by omega)
  have hw1 : w = 1 := by
    refine eq_one_of_forall_height_pos fun i => ?_
    obtain ⟨γ, δ, hγ, hδ, hγh, hδh, he⟩ := hd i
    rw [he, smul_sub, height_sub, hht γ hγ hγh, hht δ hδ hδh, ← height_sub, ← he,
      height_single]
    exact one_pos
  rw [hn, hw1, canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem exists_eq_conj_of_mem_actors_of_fix_heightSeries' {τ : Tag} {h : ℤ} (h1 : 1 ≤ h)
    (hd : SimpleDiffTail τ h) {β : MulAut (adjointGroup τ K)} (hβ : β ∈ diagonalFieldActors τ K)
    (hfix : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) :
    ∃ u ∈ posUnipotent τ K, ∃ hu : u ∈ adjointGroup τ K, β = MulAut.conj ⟨u, hu⟩ := by
  have hQC : heightSeries τ K h ≤ adjointGroup τ K :=
    (heightSeries_le_posUnipotent h).trans posUnipotent_le_adjointGroup
  obtain ⟨g, hg, a, δ, hα⟩ := ((Chevalley_diagonal_field_actor_data.1 τ K).1 β).1 hβ
  have hfix' : ∀ x ∈ heightSeries τ K h, g * diagFieldAut τ a δ x * g⁻¹ = x := by
    intro x hx
    have h1 := congrArg Subtype.val (hfix ⟨x, hQC hx⟩ hx)
    rw [hα] at h1
    rw [diagFieldAut_apply]
    simpa only [mul_assoc] using h1
  have hgN : ∀ h' : ℤ, h ≤ h' → ∀ x ∈ heightSeries τ K h',
      g * x * g⁻¹ ∈ heightSeries τ K h' := by
    intro h' hh x hx
    have hle : heightSeries τ K h' ≤ heightSeries τ K h :=
      iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩ le_rfl
    have hN := mem_normalizer_of_fixes (H := heightSeries τ K h')
      (map_diagFieldAut_rootSpan a δ fun γ hγ => hγ.1) (fun y hy => hfix' y (hle hy))
    exact (Subgroup.mem_normalizer_iff.1 hN x).1 hx
  have hgB' : g ∈ (borelGroup τ K : Set (ModGL τ K)) :=
    mem_borelGroup_of_normalizes_heightSeries h1 hd hg hgN
  rw [(triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.1] at hgB'
  obtain ⟨u, hu, t, ht, rfl⟩ := hgB'
  beta_reduce at hg hα hfix'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  set c := b * a with hc
  have hkey : ∀ γ, IsRoot τ γ → h ≤ height γ → ∀ s : K, (rootChar c γ : K) * δ s = s := by
    intro γ hγr hγh s
    have h1 := hfix' _ (pinnedX_mem_rootSpan
      (S := {α | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α}) ⟨hγr, by omega, hγh⟩ s)
    rw [diagFieldAut_pinnedX a δ hγr] at h1
    have h2 : u * pinnedX τ K γ ((rootChar c γ : K) * δ s) * u⁻¹ = pinnedX τ K γ s := by
      have e : pinnedX τ K γ ((rootChar c γ : K) * δ s) = rootDiagUnit τ b *
          pinnedX τ K γ ((rootChar a γ : K) * δ s) * (rootDiagUnit τ b)⁻¹ := by
        rw [rootDiagUnit_conj_pinnedX b hγr, hc, rootChar_mul_tuple, Units.val_mul, mul_assoc]
      rw [e]
      conv_rhs => rw [← h1]
      group
    exact eq_of_conj_pinnedX_eq hu hγr (by omega) h2
  have hchar : ∀ γ, IsRoot τ γ → h ≤ height γ → rootChar c γ = 1 := fun γ hγ hγh =>
    Units.ext (by
      have h1 := hkey γ hγ hγh 1
      rwa [map_one, mul_one] at h1)
  have hc1 : c = 1 := funext fun i => by
    obtain ⟨γ, γ', hγ, hγ', hγh, hγ'h, he⟩ := hd i
    have e : γ = Pi.single i 1 + γ' := by rw [he, sub_add_cancel]
    have h1 := hchar γ hγ hγh
    rw [e, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add, rootChar_single,
      hchar γ' hγ' hγ'h, mul_one] at h1
    exact h1
  have hδ : δ = 1 := RingEquiv.ext fun s => by
    obtain ⟨γ, -, hγ, -, hγh, -, -⟩ := hd ⟨0, by cases τ <;> decide⟩
    have h1 := hkey γ hγ hγh s
    rwa [hchar γ hγ hγh, Units.val_one, one_mul] at h1
  subst hδ
  have hba : rootDiagUnit τ b * rootDiagUnit τ a = 1 := by
    rw [← rootDiagUnit_mul, ← hc, hc1, rootDiagUnit_one]
  have hαu : ∀ x : adjointGroup τ K, (β x : ModGL τ K) = u * x * u⁻¹ := by
    intro x
    rw [hα, units_map_entrywiseHom_one_ringEquiv]
    calc u * rootDiagUnit τ b * rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹ *
          (u * rootDiagUnit τ b)⁻¹ =
        u * (rootDiagUnit τ b * rootDiagUnit τ a) * x *
          (rootDiagUnit τ b * rootDiagUnit τ a)⁻¹ * u⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hba]; group
  refine ⟨u, hu, posUnipotent_le_adjointGroup hu, MulEquiv.ext fun x => Subtype.ext ?_⟩
  rw [hαu]
  rfl

theorem exists_eq_conj_commute_of_mem_actors_of_fix_heightSeries {τ : Tag} {h : ℤ}
    (h1 : 1 ≤ h) (hd : SimpleDiffTail τ h) {β : MulAut (adjointGroup τ K)}
    (hβ : β ∈ diagonalFieldActors τ K)
    (hfix : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) :
    ∃ u ∈ posUnipotent τ K, ∃ hu : u ∈ adjointGroup τ K, β = MulAut.conj ⟨u, hu⟩ ∧
      ∀ x ∈ heightSeries τ K h, u * x = x * u := by
  obtain ⟨u, hu, hu', rfl⟩ := exists_eq_conj_of_mem_actors_of_fix_heightSeries' h1 hd hβ hfix
  refine ⟨u, hu, hu', rfl, fun x hx => ?_⟩
  have hxC : x ∈ adjointGroup τ K :=
    ((heightSeries_le_posUnipotent h).trans posUnipotent_le_adjointGroup) hx
  have e := congrArg Subtype.val (hfix ⟨x, hxC⟩ hx)
  rw [MulAut.conj_apply] at e
  calc u * x = u * x * u⁻¹ * u := by group
    _ = x * u := by rw [show u * x * u⁻¹ = x from e]

end CFSG.SeitzReduction
