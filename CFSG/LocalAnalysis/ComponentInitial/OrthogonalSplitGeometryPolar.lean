module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryMonomial
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFlagTransitivity
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)

variable {r : ℕ} {K : Type*} [Field K]

section General

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def PolarOrtho (L M : Submodule K V) : Prop :=
  ∀ x ∈ L, ∀ y ∈ M, polar Q x y = 0

variable (Q) in
@[expose] def ptsIn (W : Submodule K V) : Set (Points Q) :=
  {L | L.val ≤ W}

variable (Q) in
@[expose] def ptSpan (S : Set (Points Q)) : Submodule K V :=
  span K (⋃ L ∈ S, (L.val : Set V))

variable (Q) in
@[expose] def IsMaxSing (W : Submodule K V) : Prop :=
  (∀ v ∈ W, Q v = 0) ∧ ∀ W' : Submodule K V, W ≤ W' → (∀ v ∈ W', Q v = 0) → W' = W

variable (Q) in
@[expose] def IsMaxClique (S : Set (Points Q)) : Prop :=
  (∀ L ∈ S, ∀ M ∈ S, PolarOrtho Q L.val M.val) ∧
    ∀ L : Points Q, (∀ M ∈ S, PolarOrtho Q L.val M.val) → L ∈ S

theorem ptSpan_le_iff {S : Set (Points Q)} {W : Submodule K V} :
    ptSpan Q S ≤ W ↔ ∀ L ∈ S, L.val ≤ W := by
  rw [ptSpan, span_le, Set.iUnion₂_subset_iff]
  rfl

theorem le_ptSpan {S : Set (Points Q)} {L : Points Q} (hL : L ∈ S) : L.val ≤ ptSpan Q S :=
  ptSpan_le_iff.1 le_rfl L hL

theorem ptSpan_mono {S T : Set (Points Q)} (h : S ⊆ T) : ptSpan Q S ≤ ptSpan Q T :=
  ptSpan_le_iff.2 fun _ hL => le_ptSpan (h hL)

theorem ptsIn_mono {W W' : Submodule K V} (h : W ≤ W') : ptsIn Q W ⊆ ptsIn Q W' :=
  fun _ hL => le_trans hL h

theorem ptsIn_bot : ptsIn Q (⊥ : Submodule K V) = ∅ := by
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hL
  have hL' : L.val ≤ ⊥ := hL
  have h1 := L.2.1
  rw [le_bot_iff.1 hL', finrank_bot] at h1
  exact zero_ne_one h1

theorem ptSpan_empty : ptSpan Q (∅ : Set (Points Q)) = ⊥ :=
  le_bot_iff.1 (ptSpan_le_iff.2 fun _ h => absurd h (Set.notMem_empty _))

theorem polarOrtho_self (L : Points Q) : PolarOrtho Q L.val L.val :=
  fun _ hx _ hy => polar_eq_zero_of_singular L.2.2 hx hy

theorem PolarOrtho.symm {L M : Submodule K V} (h : PolarOrtho Q L M) : PolarOrtho Q M L :=
  fun x hx y hy => by rw [polar_comm]; exact h y hy x hx

theorem polarOrtho_of_le {W : Submodule K V} (hW : ∀ v ∈ W, Q v = 0) {L M : Submodule K V}
    (hL : L ≤ W) (hM : M ≤ W) : PolarOrtho Q L M :=
  fun _ hx _ hy => polar_eq_zero_of_singular hW (hL hx) (hM hy)

theorem ptSpan_ptsIn {W : Submodule K V} (hW : ∀ v ∈ W, Q v = 0) : ptSpan Q (ptsIn Q W) = W := by
  refine le_antisymm (ptSpan_le_iff.2 fun _ hL => hL) fun v hv => ?_
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  let L : Points Q := ⟨K ∙ v, finrank_span_singleton hv0, fun x hx => by
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hx
    rw [map_smul_eq_sq, hW v hv, mul_zero]⟩
  have hL : L ∈ ptsIn Q W := (span_singleton_le_iff_mem v W).2 hv
  exact le_ptSpan hL (mem_span_singleton_self v)

theorem totSing_ptSpan {S : Set (Points Q)} (hS : ∀ L ∈ S, ∀ M ∈ S, PolarOrtho Q L.val M.val) :
    ∀ v ∈ ptSpan Q S, Q v = 0 := by
  have h1 : ∀ v ∈ ptSpan Q S, ∀ M ∈ S, ∀ y ∈ M.val, polar Q v y = 0 := by
    intro v hv M hM y hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨L, hL, hx⟩ := Set.mem_iUnion₂.1 hx
      exact hS L hL M hM x hx y hy
    | zero => exact polar_zero_left Q y
    | add x z _ _ hx hz => rw [polar_add_left, hx, hz, add_zero]
    | smul a x _ hx => rw [polar_smul_left_eq, hx, mul_zero]
  have h2 : ∀ v ∈ ptSpan Q S, ∀ w ∈ ptSpan Q S, polar Q v w = 0 := by
    intro v hv w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨M, hM, hx⟩ := Set.mem_iUnion₂.1 hx
      exact h1 v hv M hM x hx
    | zero => exact polar_zero_right Q v
    | add x z _ _ hx hz => rw [polar_add_right, hx, hz, add_zero]
    | smul a x _ hx => rw [polar_smul_right_eq, hx, mul_zero]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, hL, hx⟩ := Set.mem_iUnion₂.1 hx
    exact L.2.2 x hx
  | zero => exact QuadraticMap.map_zero Q
  | add x z hx' hz' hx hz => rw [QuadraticMap.map_add Q, hx, hz, h2 x hx' z hz', add_zero, add_zero]
  | smul a x _ hx => rw [map_smul_eq_sq, hx, mul_zero]

theorem isMaxClique_ptsIn {W : Submodule K V} (hW : IsMaxSing Q W) : IsMaxClique Q (ptsIn Q W) := by
  refine ⟨fun L hL M hM => polarOrtho_of_le hW.1 hL hM, fun L hL => ?_⟩
  have hcl : ∀ A ∈ insert L (ptsIn Q W), ∀ B ∈ insert L (ptsIn Q W),
      PolarOrtho Q A.val B.val := by
    intro A hA B hB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · rw [hA, hB]
      exact polarOrtho_self L
    · rw [hA]
      exact hL B hB
    · rw [hB]
      exact (hL A hA).symm
    · exact polarOrtho_of_le hW.1 hA hB
  have hle : W ≤ ptSpan Q (insert L (ptsIn Q W)) :=
    le_trans (ptSpan_ptsIn hW.1).ge (ptSpan_mono (Set.subset_insert _ _))
  have heq := hW.2 _ hle (totSing_ptSpan hcl)
  change L.val ≤ W
  rw [← heq]
  exact le_ptSpan (Set.mem_insert _ _)

theorem isMaxSing_ptSpan {S : Set (Points Q)} (hS : IsMaxClique Q S) :
    IsMaxSing Q (ptSpan Q S) ∧ ptsIn Q (ptSpan Q S) = S := by
  have hsing := totSing_ptSpan hS.1
  have hpts : ptsIn Q (ptSpan Q S) = S :=
    Set.Subset.antisymm (fun L hL => hS.2 L fun M hM => polarOrtho_of_le hsing hL (le_ptSpan hM))
      fun L hL => le_ptSpan hL
  refine ⟨⟨hsing, fun W' hle hW' => le_antisymm ?_ hle⟩, hpts⟩
  rw [← ptSpan_ptsIn hW']
  exact ptSpan_le_iff.2 fun L hL =>
    le_ptSpan (hS.2 L fun M hM => polarOrtho_of_le hW' hL (le_trans (le_ptSpan hM) hle))

variable (φ : Points Q ≃ Points Q)
  (hφ : ∀ L M : Points Q, PolarOrtho Q L.val M.val ↔ PolarOrtho Q (φ L).val (φ M).val)
include hφ

theorem isMaxClique_image {S : Set (Points Q)} (hS : IsMaxClique Q S) : IsMaxClique Q (φ '' S) := by
  refine ⟨?_, fun L hL => ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact (hφ A B).1 (hS.1 A hA B hB)
  · refine ⟨φ.symm L, hS.2 _ fun M hM => ?_, φ.apply_symm_apply L⟩
    rw [hφ, φ.apply_symm_apply]
    exact hL _ ⟨M, hM, rfl⟩

theorem polarOrtho_symm_iff (L M : Points Q) :
    PolarOrtho Q L.val M.val ↔ PolarOrtho Q (φ.symm L).val (φ.symm M).val := by
  rw [hφ (φ.symm L) (φ.symm M), φ.apply_symm_apply, φ.apply_symm_apply]

theorem ptsIn_ptSpan_image_of_eq_inf {W M₁ M₂ : Submodule K V} (h1 : IsMaxSing Q M₁)
    (h2 : IsMaxSing Q M₂) (hW : W = M₁ ⊓ M₂) :
    ptsIn Q (ptSpan Q (φ '' ptsIn Q W)) = φ '' ptsIn Q W := by
  obtain ⟨-, hp₁⟩ := isMaxSing_ptSpan (isMaxClique_image φ hφ (isMaxClique_ptsIn h1))
  obtain ⟨-, hp₂⟩ := isMaxSing_ptSpan (isMaxClique_image φ hφ (isMaxClique_ptsIn h2))
  have hptsW : ptsIn Q W = ptsIn Q M₁ ∩ ptsIn Q M₂ := by
    ext L
    simp only [ptsIn, Set.mem_inter_iff, Set.mem_ofPred_eq, hW, le_inf_iff]
  refine Set.Subset.antisymm (fun L hL => ?_) fun L hL => le_ptSpan hL
  have hL1 : L ∈ ptsIn Q (ptSpan Q (φ '' ptsIn Q M₁)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_left)))
  have hL2 : L ∈ ptsIn Q (ptSpan Q (φ '' ptsIn Q M₂)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_right)))
  rw [hp₁] at hL1
  rw [hp₂] at hL2
  rw [hptsW, Set.image_inter φ.injective]
  exact ⟨hL1, hL2⟩

end General

section Split

theorem finrank_le_of_totSing {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) : finrank K W ≤ r := by
  have hrefl : (polarBilin (quadPlus r K)).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [polar_comm]
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl W
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot (nondegenerate_polarBilin_quadPlus r K),
    inf_bot_eq, finrank_bot, add_zero, finrank_split] at h
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadPlus r K)) W := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
      rw [polarBilin_apply_apply]
      exact polar_eq_zero_of_singular hW hy hx
  have := Submodule.finrank_mono hle
  omega

theorem mem_coordSpan_iff {S : Set (Fin r ⊕ Fin r)} {v : Fin r ⊕ Fin r → K} :
    v ∈ coordSpan K S ↔ ∀ x ∉ S, v x = 0 := by
  refine ⟨fun hv x hx => apply_eq_zero_of_mem_coordSpan hv hx, fun h => ?_⟩
  rw [← Finset.univ_sum_single v]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ S
  · have : (Pi.single x (v x) : Fin r ⊕ Fin r → K) = v x • Pi.single x 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · rw [h x hx, Pi.single_zero]
    exact zero_mem _

theorem coordSpan_inf (S T : Set (Fin r ⊕ Fin r)) :
    coordSpan K S ⊓ coordSpan K T = coordSpan K (S ∩ T) := by
  ext v
  simp only [Submodule.mem_inf, mem_coordSpan_iff, Set.mem_inter_iff, not_and_or]
  constructor
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

theorem isMaxSing_coordSpan {S : Set (Fin r ⊕ Fin r)} (hS : ∀ x, x ∈ S ↔ x.swap ∉ S) :
    IsMaxSing (quadPlus r K) (coordSpan K S) := by
  refine ⟨fun v hv => ?_, fun W' hle hW' => le_antisymm (fun v hv => ?_) hle⟩
  · rw [mem_coordSpan_iff] at hv
    rw [quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (Sum.inl i : Fin r ⊕ Fin r) ∈ S
    · rw [hv (Sum.inr i) ((hS _).1 hi), mul_zero]
    · rw [hv (Sum.inl i) hi, zero_mul]
  · rw [mem_coordSpan_iff]
    intro x hx
    have hxs : x.swap ∈ S := by
      by_contra h
      exact hx ((hS x).2 h)
    have h0 := polar_eq_zero_of_singular hW' hv (hle (Submodule.subset_span ⟨x.swap, hxs, rfl⟩))
    rwa [polar_single, Sum.swap_swap] at h0

theorem isMaxSing_map {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K)) {M : Submodule K _}
    (hM : IsMaxSing (quadPlus r K) M) :
    IsMaxSing (quadPlus r K) (M.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K))) := by
  have hginv : ∀ x, quadPlus r K (g.symm x) = quadPlus r K x := fun x => by
    rw [← map_of_mem hg (g.symm x), LinearEquiv.apply_symm_apply]
  refine ⟨?_, fun W' hle hW' => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, map_of_mem hg]
    exact hM.1 v hv
  · have hle' : M ≤ W'.map (g.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
      intro x hx
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
      exact hle ⟨x, hx, rfl⟩
    have hs : ∀ v ∈ W'.map (g.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)),
        quadPlus r K v = 0 := by
      rintro _ ⟨v, hv, rfl⟩
      rw [LinearEquiv.coe_coe, hginv]
      exact hW' v hv
    have heq := hM.2 _ hle' hs
    ext v
    rw [Submodule.mem_map_equiv, ← heq, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]

theorem exists_isMaxSing_inf {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    ∃ M₁ M₂, IsMaxSing (quadPlus r K) M₁ ∧ IsMaxSing (quadPlus r K) M₂ ∧ W = M₁ ⊓ M₂ := by
  set k := finrank K W with hk
  obtain ⟨g, hg, hgW⟩ := exists_isometry_map_eq (finrank_le_of_totSing hW) ⟨hk.symm, hW⟩
  set S₁ : Set (Fin r ⊕ Fin r) := Set.range Sum.inl with hS₁
  set S₂ : Set (Fin r ⊕ Fin r) :=
    Sum.inl '' {j : Fin r | (j : ℕ) < k} ∪ Sum.inr '' {j : Fin r | k ≤ (j : ℕ)} with hS₂
  have h₁ : ∀ x, x ∈ S₁ ↔ x.swap ∉ S₁ := by
    rintro (i | i) <;> simp [hS₁]
  have h₂ : ∀ x, x ∈ S₂ ↔ x.swap ∉ S₂ := by
    rintro (i | i) <;> simp [hS₂]
  have hF : flag r K k = coordSpan K S₁ ⊓ coordSpan K S₂ := by
    rw [flag_eq_coordSpan, coordSpan_inf]
    congr 1
    ext x
    rcases x with i | i <;> simp [hS₁, hS₂]
  refine ⟨_, _, isMaxSing_map hg (isMaxSing_coordSpan h₁),
    isMaxSing_map hg (isMaxSing_coordSpan h₂), ?_⟩
  rw [← hgW, hF, Submodule.map_inf _ g.injective]

variable (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))

variable (r K) in
@[expose] noncomputable def polarImage (W : Submodule K (Fin r ⊕ Fin r → K)) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  ptSpan (quadPlus r K) (φ '' ptsIn (quadPlus r K) W)

variable (hφ : ∀ L M : Points (quadPlus r K),
  PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val)
include hφ

theorem totSing_polarImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) : ∀ v ∈ polarImage r K φ W, quadPlus r K v = 0 :=
  totSing_ptSpan (by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    exact (hφ A B).1 (polarOrtho_of_le hW hA hB))

theorem ptsIn_polarImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    ptsIn (quadPlus r K) (polarImage r K φ W) = φ '' ptsIn (quadPlus r K) W := by
  obtain ⟨M₁, M₂, h1, h2, hM⟩ := exists_isMaxSing_inf hW
  exact ptsIn_ptSpan_image_of_eq_inf φ hφ h1 h2 hM

omit hφ in
theorem eq_polarImage {W W' : Submodule K (Fin r ⊕ Fin r → K)}
    (hW' : ∀ v ∈ W', quadPlus r K v = 0)
    (h : φ '' ptsIn (quadPlus r K) W = ptsIn (quadPlus r K) W') : W' = polarImage r K φ W := by
  rw [polarImage, h, ptSpan_ptsIn hW']

theorem polarImage_symm_polarImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    polarImage r K φ.symm (polarImage r K φ W) = W := by
  rw [polarImage, ptsIn_polarImage φ hφ hW, Equiv.symm_image_image, ptSpan_ptsIn hW]

theorem polarImage_le_iff {W₁ W₂ : Submodule K (Fin r ⊕ Fin r → K)}
    (h1 : ∀ v ∈ W₁, quadPlus r K v = 0) (h2 : ∀ v ∈ W₂, quadPlus r K v = 0) :
    polarImage r K φ W₁ ≤ polarImage r K φ W₂ ↔ W₁ ≤ W₂ := by
  refine ⟨fun h => ?_, fun h => ptSpan_mono (Set.image_mono (ptsIn_mono h))⟩
  have hs := ptsIn_mono (Q := quadPlus r K) h
  rw [ptsIn_polarImage φ hφ h1, ptsIn_polarImage φ hφ h2,
    Set.image_subset_image_iff φ.injective] at hs
  rw [← ptSpan_ptsIn h1, ← ptSpan_ptsIn h2]
  exact ptSpan_mono hs

theorem polarImage_injective {W₁ W₂ : Submodule K (Fin r ⊕ Fin r → K)}
    (h1 : ∀ v ∈ W₁, quadPlus r K v = 0) (h2 : ∀ v ∈ W₂, quadPlus r K v = 0)
    (h : polarImage r K φ W₁ = polarImage r K φ W₂) : W₁ = W₂ :=
  le_antisymm ((polarImage_le_iff φ hφ h1 h2).1 h.le) ((polarImage_le_iff φ hφ h2 h1).1 h.ge)

omit hφ in
theorem polarImage_bot : polarImage r K φ ⊥ = ⊥ := by
  rw [polarImage, ptsIn_bot, Set.image_empty, ptSpan_empty]

theorem finrank_le_finrank_polarImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) :
    finrank K W ≤ finrank K (polarImage r K φ W) := by
  set k := finrank K W with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]
    exact Nat.zero_le _
  obtain ⟨F, ⟨hFd, hFm, hFs⟩, hFW⟩ := exists_mem_singularFlags_eq (k := k) ⟨hk.symm, hW⟩ hk0
  have hchain : ∀ i (hi : i < k), i + 1 ≤ finrank K (polarImage r K φ (F ⟨i, hi⟩)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [Nat.zero_add, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro h0
      rw [← polarImage_bot φ] at h0
      have := polarImage_injective φ hφ (hFs _) (fun v hv => by rw [(mem_bot K).1 hv, map_zero]) h0
      have hd := hFd ⟨0, hi⟩
      rw [this, finrank_bot] at hd
      simp at hd
    | succ i ih =>
      intro hi
      have hlt : F ⟨i, by omega⟩ < F ⟨i + 1, hi⟩ := by
        refine lt_of_le_of_ne (hFm (Fin.le_def.2 (by simp only; omega))) fun he => ?_
        have h1 := hFd ⟨i, by omega⟩
        rw [he, hFd ⟨i + 1, hi⟩] at h1
        simp at h1
      have hlt' : polarImage r K φ (F ⟨i, by omega⟩) < polarImage r K φ (F ⟨i + 1, hi⟩) :=
        lt_of_le_of_ne ((polarImage_le_iff φ hφ (hFs _) (hFs _)).2 hlt.le) fun he =>
          hlt.ne (polarImage_injective φ hφ (hFs _) (hFs _) he)
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      have := ih (by omega)
      omega
  have := hchain (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega, hFW] at this
  exact this

theorem finrank_polarImage {W : Submodule K (Fin r ⊕ Fin r → K)}
    (hW : ∀ v ∈ W, quadPlus r K v = 0) : finrank K (polarImage r K φ W) = finrank K W := by
  refine le_antisymm ?_ (finrank_le_finrank_polarImage φ hφ hW)
  have h := finrank_le_finrank_polarImage φ.symm (polarOrtho_symm_iff φ hφ)
    (totSing_polarImage φ hφ hW)
  rwa [polarImage_symm_polarImage φ hφ hW] at h

omit hφ in
theorem polarImage_point (L : Points (quadPlus r K)) : polarImage r K φ L.val = (φ L).val := by
  have hpts : ptsIn (quadPlus r K) L.val = {L} := by
    ext M
    simp only [ptsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hM => Subtype.ext (Submodule.eq_of_le_of_finrank_eq hM ?_), fun h => h ▸ le_rfl⟩
    rw [M.2.1, L.2.1]
  rw [polarImage, hpts, Set.image_singleton]
  exact le_antisymm (ptSpan_le_iff.2 fun M hM => by rw [Set.mem_singleton_iff.1 hM])
    (le_ptSpan (Set.mem_singleton _))

end Split


theorem orthogonal_geometry_split_polar_subspaces {K : Type*} [Field K] {r : ℕ}
    (φ : Points (quadPlus r K) ≃ Points (quadPlus r K))
    (hφ : ∀ L M : Points (quadPlus r K),
      PolarOrtho (quadPlus r K) L.val M.val ↔ PolarOrtho (quadPlus r K) (φ L).val (φ M).val) :
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ v ∈ W, quadPlus r K v = 0) →
      (∀ v ∈ polarImage r K φ W, quadPlus r K v = 0) ∧
      φ '' ptsIn (quadPlus r K) W = ptsIn (quadPlus r K) (polarImage r K φ W) ∧
      ∀ W' : Submodule K (Fin r ⊕ Fin r → K), (∀ v ∈ W', quadPlus r K v = 0) →
        φ '' ptsIn (quadPlus r K) W = ptsIn (quadPlus r K) W' → W' = polarImage r K φ W) ∧
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ v ∈ W, quadPlus r K v = 0) →
      finrank K (polarImage r K φ W) = finrank K W) ∧
    (∀ W₁ W₂ : Submodule K (Fin r ⊕ Fin r → K), (∀ v ∈ W₁, quadPlus r K v = 0) →
      (∀ v ∈ W₂, quadPlus r K v = 0) → (W₁ ≤ W₂ ↔ polarImage r K φ W₁ ≤ polarImage r K φ W₂)) ∧
    ∀ W : Submodule K (Fin r ⊕ Fin r → K), IsMaxSing (quadPlus r K) W →
      (∀ L : Points (quadPlus r K), L.val ≤ W ↔ (φ L).val ≤ polarImage r K φ W) ∧
      (∀ H : Submodule K (Fin r ⊕ Fin r → K), H ≤ W → finrank K H + 1 = finrank K W →
        polarImage r K φ H ≤ polarImage r K φ W ∧
          finrank K (polarImage r K φ H) + 1 = finrank K (polarImage r K φ W) ∧
          ∀ L : Points (quadPlus r K), (L.val ≤ H ↔ (φ L).val ≤ polarImage r K φ H)) ∧
      ∀ H' : Submodule K (Fin r ⊕ Fin r → K), H' ≤ polarImage r K φ W →
        finrank K H' + 1 = finrank K (polarImage r K φ W) →
        ∃ H : Submodule K (Fin r ⊕ Fin r → K), H ≤ W ∧ finrank K H + 1 = finrank K W ∧
          polarImage r K φ H = H' := by
  refine ⟨fun W hW => ⟨totSing_polarImage φ hφ hW, (ptsIn_polarImage φ hφ hW).symm,
    fun W' hW' h => eq_polarImage φ hW' h⟩, fun W hW => finrank_polarImage φ hφ hW,
    fun W₁ W₂ h1 h2 => (polarImage_le_iff φ hφ h1 h2).symm, fun W hW => ⟨?_, ?_, ?_⟩⟩
  · intro L
    rw [← polarImage_point φ L]
    exact (polarImage_le_iff φ hφ L.2.2 hW.1).symm
  · intro H hH hd
    have hHs : ∀ v ∈ H, quadPlus r K v = 0 := fun v hv => hW.1 v (hH hv)
    refine ⟨(polarImage_le_iff φ hφ hHs hW.1).2 hH, by
      rw [finrank_polarImage φ hφ hHs, finrank_polarImage φ hφ hW.1, hd], fun L => ?_⟩
    rw [← polarImage_point φ L]
    exact (polarImage_le_iff φ hφ L.2.2 hHs).symm
  · intro H' hH' hd
    have hWs := totSing_polarImage φ hφ hW.1
    have hHs : ∀ v ∈ H', quadPlus r K v = 0 := fun v hv => hWs v (hH' hv)
    have hφ' := polarOrtho_symm_iff φ hφ
    set H := polarImage r K φ.symm H' with hHdef
    have hHs' := totSing_polarImage φ.symm hφ' hHs
    have hHH : polarImage r K φ H = H' := by
      have := polarImage_symm_polarImage φ.symm hφ' hHs
      rwa [Equiv.symm_symm] at this
    refine ⟨H, ?_, ?_, hHH⟩
    · rw [← polarImage_le_iff φ hφ hHs' hW.1, hHH]
      exact hH'
    · rw [← finrank_polarImage φ hφ hHs', hHH, hd, finrank_polarImage φ hφ hW.1]

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
