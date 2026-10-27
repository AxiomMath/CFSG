module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open Module Submodule

universe u

variable {p f : ℕ} {K : Type*} [Field K] {V : Type u} [AddCommGroup V] [Module K V]

section General

variable {σ : K →+* K} (B : V →ₛₗ[σ] V →ₗ[K] K)

@[expose] def isoLines : Set (Submodule K V) :=
  {L | finrank K L = 1 ∧ ∀ a ∈ L, B a a = 0}

@[expose] def SubOrtho (L M : Submodule K V) : Prop :=
  ∀ x ∈ L, ∀ y ∈ M, B x y = 0

@[expose] def ptsIn (W : Submodule K V) : Set (isoLines B) :=
  {L | (L : Submodule K V) ≤ W}

@[expose] def ptSpan (S : Set (isoLines B)) : Submodule K V :=
  span K (⋃ L ∈ S, ((L : Submodule K V) : Set V))

@[expose] def IsMaxTotIso (W : Submodule K V) : Prop :=
  (∀ x ∈ W, ∀ y ∈ W, B x y = 0) ∧
    ∀ W' : Submodule K V, W ≤ W' → (∀ x ∈ W', ∀ y ∈ W', B x y = 0) → W' = W

@[expose] def IsMaxClique (S : Set (isoLines B)) : Prop :=
  (∀ L ∈ S, ∀ M ∈ S, SubOrtho B L M) ∧
    ∀ L : isoLines B, (∀ M ∈ S, SubOrtho B L M) → L ∈ S

@[expose] def polarImage (φ : isoLines B ≃ isoLines B) (W : Submodule K V) : Submodule K V :=
  ptSpan B (φ '' ptsIn B W)

variable {B}

theorem mem_isoLines {L : Submodule K V} :
    L ∈ isoLines B ↔ finrank K L = 1 ∧ ∀ a ∈ L, B a a = 0 :=
  Iff.rfl

theorem isTotIso_span {T : Set V} (hT : ∀ x ∈ T, ∀ y ∈ T, B x y = 0) :
    ∀ x ∈ span K T, ∀ y ∈ span K T, B x y = 0 := by
  have h1 : ∀ y ∈ T, span K T ≤ LinearMap.ker (B.flip y) := fun y hy =>
    span_le.mpr fun x hx => LinearMap.mem_ker.mpr (by
      rw [LinearMap.flip_apply]
      exact hT x hx y hy)
  have h2 : ∀ x ∈ span K T, span K T ≤ LinearMap.ker (B x) := fun x hx =>
    span_le.mpr fun y hy => LinearMap.mem_ker.mpr (by
      have := LinearMap.mem_ker.mp (h1 y hy hx)
      rwa [LinearMap.flip_apply] at this)
  exact fun x hx y hy => LinearMap.mem_ker.mp (h2 x hx hy)

theorem isTotIso_of_mem_isoLines {L : Submodule K V} (hL : L ∈ isoLines B) :
    ∀ x ∈ L, ∀ y ∈ L, B x y = 0 := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := L) fun h0 => by
    have h1 := hL.1
    rw [h0, finrank_bot] at h1
    exact zero_ne_one h1
  have haa := hL.2 a ha
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hL.1 ha ha0]
  intro x hx y hy
  obtain ⟨c, rfl⟩ := mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := mem_span_singleton.mp hy
  simp [haa]

theorem subOrtho_self (L : isoLines B) : SubOrtho B L L :=
  isTotIso_of_mem_isoLines L.2

theorem SubOrtho.symm {L M : Submodule K V} (h : SubOrtho B L M) (hB : B.IsRefl) :
    SubOrtho B M L :=
  fun x hx y hy => hB y x (h y hy x hx)

theorem subOrtho_of_le {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0)
    {L M : Submodule K V} (hL : L ≤ W) (hM : M ≤ W) : SubOrtho B L M :=
  fun x hx y hy => hW x (hL hx) y (hM hy)

theorem ptSpan_le_iff {S : Set (isoLines B)} {W : Submodule K V} :
    ptSpan B S ≤ W ↔ ∀ L ∈ S, (L : Submodule K V) ≤ W := by
  rw [ptSpan, span_le, Set.iUnion₂_subset_iff]
  rfl

theorem le_ptSpan {S : Set (isoLines B)} {L : isoLines B} (hL : L ∈ S) :
    (L : Submodule K V) ≤ ptSpan B S :=
  ptSpan_le_iff.1 le_rfl L hL

theorem ptSpan_mono {S T : Set (isoLines B)} (h : S ⊆ T) : ptSpan B S ≤ ptSpan B T :=
  ptSpan_le_iff.2 fun _ hL => le_ptSpan (h hL)

theorem ptsIn_mono {W W' : Submodule K V} (h : W ≤ W') : ptsIn B W ⊆ ptsIn B W' :=
  fun _ hL => le_trans hL h

theorem ptSpan_ptsIn {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    ptSpan B (ptsIn B W) = W := by
  refine le_antisymm (ptSpan_le_iff.2 fun _ hL => hL) fun v hv => ?_
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  let L : isoLines B := ⟨K ∙ v, finrank_span_singleton hv0, fun x hx => by
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hx
    simp [hW v hv v hv]⟩
  have hL : L ∈ ptsIn B W := (span_singleton_le_iff_mem v W).2 hv
  exact le_ptSpan hL (mem_span_singleton_self v)

theorem isTotIso_ptSpan {S : Set (isoLines B)} (hS : ∀ L ∈ S, ∀ M ∈ S, SubOrtho B L M) :
    ∀ x ∈ ptSpan B S, ∀ y ∈ ptSpan B S, B x y = 0 :=
  isTotIso_span fun x hx y hy => by
    obtain ⟨L, hL, hx⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨M, hM, hy⟩ := Set.mem_iUnion₂.1 hy
    exact hS L hL M hM x hx y hy

theorem isMaxClique_ptsIn (hB : B.IsRefl) {W : Submodule K V} (hW : IsMaxTotIso B W) :
    IsMaxClique B (ptsIn B W) := by
  refine ⟨fun L hL M hM => subOrtho_of_le hW.1 hL hM, fun L hL => ?_⟩
  have hcl : ∀ A ∈ insert L (ptsIn B W), ∀ C ∈ insert L (ptsIn B W), SubOrtho B A C := by
    intro A hA C hC
    rcases hA with hA | hA <;> rcases hC with hC | hC
    · rw [hA, hC]
      exact subOrtho_self L
    · rw [hA]
      exact hL C hC
    · rw [hC]
      exact (hL A hA).symm hB
    · exact subOrtho_of_le hW.1 hA hC
  have hle : W ≤ ptSpan B (insert L (ptsIn B W)) :=
    le_trans (ptSpan_ptsIn hW.1).ge (ptSpan_mono (Set.subset_insert _ _))
  have heq := hW.2 _ hle (isTotIso_ptSpan hcl)
  change (L : Submodule K V) ≤ W
  rw [← heq]
  exact le_ptSpan (Set.mem_insert _ _)

theorem isMaxTotIso_ptSpan {S : Set (isoLines B)} (hS : IsMaxClique B S) :
    IsMaxTotIso B (ptSpan B S) ∧ ptsIn B (ptSpan B S) = S := by
  have hiso := isTotIso_ptSpan hS.1
  have hpts : ptsIn B (ptSpan B S) = S :=
    Set.Subset.antisymm (fun L hL => hS.2 L fun M hM => subOrtho_of_le hiso hL (le_ptSpan hM))
      fun L hL => le_ptSpan hL
  refine ⟨⟨hiso, fun W' hle hW' => le_antisymm ?_ hle⟩, hpts⟩
  rw [← ptSpan_ptsIn hW']
  exact ptSpan_le_iff.2 fun L hL =>
    le_ptSpan (hS.2 L fun M hM => subOrtho_of_le hW' hL (le_trans (le_ptSpan hM) hle))

section Image

variable (φ : isoLines B ≃ isoLines B)

theorem eq_polarImage {W W' : Submodule K V} (hW' : ∀ x ∈ W', ∀ y ∈ W', B x y = 0)
    (he : φ '' ptsIn B W = ptsIn B W') : W' = polarImage B φ W := by
  rw [polarImage, he, ptSpan_ptsIn hW']

theorem polarImage_point [FiniteDimensional K V] (L : isoLines B) :
    polarImage B φ L = φ L := by
  have hpts : ptsIn B (L : Submodule K V) = {L} := by
    ext M
    simp only [ptsIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun hM => Subtype.ext (Submodule.eq_of_le_of_finrank_eq hM ?_),
      fun he => he ▸ le_rfl⟩
    rw [M.2.1, L.2.1]
  rw [polarImage, hpts, Set.image_singleton]
  exact le_antisymm (ptSpan_le_iff.2 fun M hM => by rw [Set.mem_singleton_iff.1 hM])
    (le_ptSpan (Set.mem_singleton _))

variable (hφ : ∀ L M : isoLines B, SubOrtho B L M ↔ SubOrtho B (φ L) (φ M))
include hφ

theorem isTotIso_polarImage {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    ∀ x ∈ polarImage B φ W, ∀ y ∈ polarImage B φ W, B x y = 0 :=
  isTotIso_ptSpan (by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨C, hC, rfl⟩
    exact (hφ A C).1 (subOrtho_of_le hW hA hC))

theorem isMaxClique_image {S : Set (isoLines B)} (hS : IsMaxClique B S) :
    IsMaxClique B (φ '' S) := by
  refine ⟨?_, fun L hL => ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨C, hC, rfl⟩
    exact (hφ A C).1 (hS.1 A hA C hC)
  · refine ⟨φ.symm L, hS.2 _ fun M hM => ?_, φ.apply_symm_apply L⟩
    rw [hφ, φ.apply_symm_apply]
    exact hL _ ⟨M, hM, rfl⟩

theorem subOrtho_symm_iff (L M : isoLines B) :
    SubOrtho B L M ↔ SubOrtho B (φ.symm L) (φ.symm M) := by
  rw [hφ (φ.symm L) (φ.symm M), φ.apply_symm_apply, φ.apply_symm_apply]

theorem ptsIn_polarImage_of_eq_inf (hB : B.IsRefl) {W M₁ M₂ : Submodule K V}
    (h1 : IsMaxTotIso B M₁) (h2 : IsMaxTotIso B M₂) (hW : W = M₁ ⊓ M₂) :
    ptsIn B (polarImage B φ W) = φ '' ptsIn B W := by
  obtain ⟨-, hp₁⟩ := isMaxTotIso_ptSpan (isMaxClique_image φ hφ (isMaxClique_ptsIn hB h1))
  obtain ⟨-, hp₂⟩ := isMaxTotIso_ptSpan (isMaxClique_image φ hφ (isMaxClique_ptsIn hB h2))
  have hptsW : ptsIn B W = ptsIn B M₁ ∩ ptsIn B M₂ := by
    ext L
    simp only [ptsIn, Set.mem_inter_iff, Set.mem_ofPred_eq, hW, le_inf_iff]
  refine Set.Subset.antisymm (fun L hL => ?_) fun L hL => le_ptSpan hL
  have hL1 : L ∈ ptsIn B (ptSpan B (φ '' ptsIn B M₁)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_left)))
  have hL2 : L ∈ ptsIn B (ptSpan B (φ '' ptsIn B M₂)) :=
    le_trans hL (ptSpan_mono (Set.image_mono (by rw [hptsW]; exact Set.inter_subset_right)))
  rw [hp₁] at hL1
  rw [hp₂] at hL2
  rw [hptsW, Set.image_inter φ.injective]
  exact ⟨hL1, hL2⟩

end Image

end General

section Coordinates

@[expose] def mixIdx {r ε : ℕ} (k : ℕ) (j : Fin r) : HypIndex r ε :=
  if (j : ℕ) < k then .inl j else .inr (.inr j)

theorem mixIdx_injective {r ε : ℕ} (k : ℕ) :
    Function.Injective (mixIdx (r := r) (ε := ε) k) := by
  intro i j hij
  unfold mixIdx at hij
  split_ifs at hij <;> simp_all

theorem mixIdx_ne_hypPartner {r ε : ℕ} (k : ℕ) (i j : Fin r) :
    mixIdx (ε := ε) k j ≠ hypPartner (mixIdx k i) := by
  by_cases hi : (i : ℕ) < k <;> by_cases hj : (j : ℕ) < k <;>
    simp [mixIdx, hi, hj, Fin.ext_iff] <;> omega

theorem range_inl_inter_range_mixIdx {r ε : ℕ} (k : ℕ) :
    Set.range (Sum.inl : Fin r → HypIndex r ε) ∩ Set.range (mixIdx (ε := ε) k) =
      Sum.inl '' {j : Fin r | (j : ℕ) < k} := by
  ext x
  constructor
  · rintro ⟨⟨i, rfl⟩, j, hj⟩
    refine ⟨i, ?_, rfl⟩
    unfold mixIdx at hj
    split_ifs at hj with hjk
    obtain rfl := Sum.inl_injective hj
    exact hjk
  · rintro ⟨i, hi, rfl⟩
    have hi' : (i : ℕ) < k := hi
    exact ⟨⟨i, rfl⟩, i, by simp [mixIdx, hi']⟩

theorem span_image_inf_span_image {ι : Type*} (w : Basis ι K V) (s t : Set ι) :
    span K (w '' s) ⊓ span K (w '' t) = span K (w '' (s ∩ t)) := by
  ext m
  simp only [mem_inf, Module.Basis.mem_span_image, Set.subset_inter_iff]

theorem finrank_span_image_range {ι κ : Type*} [Fintype κ] (w : Basis ι K V) {τ : κ → ι}
    (hτ : Function.Injective τ) : finrank K (span K (w '' Set.range τ)) = Fintype.card κ := by
  rw [← Set.range_comp]
  exact finrank_span_eq_card (w.linearIndependent.comp τ hτ)

theorem isTotIso_span_image {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {r ε : ℕ}
    {w : HypIndex r ε → V} (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y)
    {s : Set (HypIndex r ε)} (hs : ∀ x ∈ s, ∀ y ∈ s, y ≠ hypPartner x) :
    ∀ x ∈ span K (w '' s), ∀ y ∈ span K (w '' s), B x y = 0 :=
  isTotIso_span (by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hw, hypGram_apply]
    simp [hs x hx y hy])

end Coordinates

section Witt

variable [FiniteDimensional K V]

theorem finrank_le_of_isTotIso (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {W : Submodule K V}
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) : finrank K W ≤ finrank K V / 2 := by
  obtain ⟨C, hC, -⟩ := exists_isotropicChain_eq W hW
  exact ((isotropic_flag_extension h hB hBl rfl).1 _ C hC).1

theorem isMaxTotIso_of_finrank (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {M : Submodule K V}
    (hM : ∀ x ∈ M, ∀ y ∈ M, B x y = 0) (hdim : finrank K V / 2 ≤ finrank K M) :
    IsMaxTotIso B M :=
  ⟨hM, fun _ hle hW' => (Submodule.eq_of_le_of_finrank_le hle
    ((finrank_le_of_isTotIso h hB hBl hW').trans hdim)).symm⟩

theorem isMaxTotIso_span_range (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {r ε : ℕ} (hr : finrank K V / 2 = r)
    (w : Basis (HypIndex r ε) K V) (hw : ∀ x y, B (w x) (w y) = hypGram r ε K x y)
    {τ : Fin r → HypIndex r ε} (hτ : Function.Injective τ)
    (hτp : ∀ i j, τ j ≠ hypPartner (τ i)) : IsMaxTotIso B (span K (w '' Set.range τ)) := by
  refine isMaxTotIso_of_finrank h hB hBl (isTotIso_span_image hw ?_) ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hτp i j
  · rw [finrank_span_image_range w hτ, Fintype.card_fin]
    omega

theorem exists_isMaxTotIso_inf (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {W : Submodule K V}
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    ∃ M₁ M₂, IsMaxTotIso B M₁ ∧ IsMaxTotIso B M₂ ∧ W = M₁ ⊓ M₂ := by
  obtain ⟨C, hC, hCW⟩ := exists_isotropicChain_eq W hW
  obtain ⟨-, w, hw, hCw⟩ := (isotropic_flag_extension h hB hBl rfl).1 _ C hC
  have hWa : W = aSpan w (finrank K W) := by rw [← hCw _ le_rfl, hCW]
  refine ⟨_, _, isMaxTotIso_span_range h hB hBl rfl w hw Sum.inl_injective
    (fun i j => by simp), isMaxTotIso_span_range h hB hBl rfl w hw
      (mixIdx_injective (finrank K W)) (mixIdx_ne_hypPartner (finrank K W)), ?_⟩
  rw [span_image_inf_span_image, range_inl_inter_range_mixIdx, Set.image_image]
  exact hWa

end Witt

section Recovery

variable [FiniteDimensional K V] (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
  (hB : B.IsSymm) (hBl : B.SeparatingLeft) {φ : isoLines B ≃ isoLines B}
  (hφ : ∀ L M : isoLines B, SubOrtho B L M ↔ SubOrtho B (φ L) (φ M))
include hB hBl hφ

theorem ptsIn_polarImage {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    ptsIn B (polarImage B φ W) = φ '' ptsIn B W := by
  obtain ⟨M₁, M₂, h1, h2, hM⟩ := exists_isMaxTotIso_inf h hB hBl hW
  exact ptsIn_polarImage_of_eq_inf φ hφ hB.isRefl h1 h2 hM

theorem polarImage_symm_polarImage {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    polarImage B φ.symm (polarImage B φ W) = W := by
  rw [polarImage, ptsIn_polarImage h hB hBl hφ hW, Equiv.symm_image_image, ptSpan_ptsIn hW]

theorem polarImage_le_iff {W₁ W₂ : Submodule K V} (h1 : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0)
    (h2 : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0) :
    polarImage B φ W₁ ≤ polarImage B φ W₂ ↔ W₁ ≤ W₂ := by
  refine ⟨fun hle => ?_, fun hle => ptSpan_mono (Set.image_mono (ptsIn_mono hle))⟩
  have hs := ptsIn_mono (B := B) hle
  rw [ptsIn_polarImage h hB hBl hφ h1, ptsIn_polarImage h hB hBl hφ h2,
    Set.image_subset_image_iff φ.injective] at hs
  rw [← ptSpan_ptsIn h1, ← ptSpan_ptsIn h2]
  exact ptSpan_mono hs

theorem polarImage_injective {W₁ W₂ : Submodule K V} (h1 : ∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0)
    (h2 : ∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0) (he : polarImage B φ W₁ = polarImage B φ W₂) :
    W₁ = W₂ :=
  le_antisymm ((polarImage_le_iff h hB hBl hφ h1 h2).1 he.le)
    ((polarImage_le_iff h hB hBl hφ h2 h1).1 he.ge)

theorem finrank_le_finrank_polarImage {W : Submodule K V}
    (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) : finrank K W ≤ finrank K (polarImage B φ W) := by
  obtain ⟨C, hC, hCW⟩ := exists_isotropicChain_eq W hW
  have key : ∀ i ≤ finrank K W, i ≤ finrank K (polarImage B φ (C i)) := by
    intro i
    induction i with
    | zero => exact fun _ => Nat.zero_le _
    | succ i ih =>
      intro hi
      have hlt : C i < C (i + 1) := by
        refine lt_of_le_of_ne (hC.2.1 i hi) fun he => ?_
        have h1 := hC.1 i (by omega)
        rw [he, hC.1 (i + 1) hi] at h1
        omega
      have hi1 := hC.2.2 i (by omega)
      have hi2 := hC.2.2 (i + 1) hi
      have hlt' : polarImage B φ (C i) < polarImage B φ (C (i + 1)) :=
        lt_of_le_of_ne ((polarImage_le_iff h hB hBl hφ hi1 hi2).2 hlt.le) fun he =>
          hlt.ne (polarImage_injective h hB hBl hφ hi1 hi2 he)
      have := Submodule.finrank_lt_finrank_of_lt hlt'
      have := ih (by omega)
      omega
  have := key _ le_rfl
  rwa [hCW] at this

theorem finrank_polarImage {W : Submodule K V} (hW : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    finrank K (polarImage B φ W) = finrank K W := by
  refine le_antisymm ?_ (finrank_le_finrank_polarImage h hB hBl hφ hW)
  have hle := finrank_le_finrank_polarImage h hB hBl (subOrtho_symm_iff φ hφ)
    (isTotIso_polarImage φ hφ hW)
  rwa [polarImage_symm_polarImage h hB hBl hφ hW] at hle

end Recovery

theorem coe_hypIsotropicLines {K : Type} [Field K] (h : UnitaryFieldData p f K) (r ε : ℕ) :
    (hypIsotropicLines h r ε : Set (Submodule K (HypIndex r ε → K))) =
      isoLines (hypForm h r ε) :=
  rfl

theorem unitary_polar_subspace_recovery (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (φ : isoLines B ≃ isoLines B)
    (hφ : ∀ L M : isoLines B, SubOrtho B L M ↔ SubOrtho B (φ L) (φ M)) :
    (∀ W : Submodule K V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) →
      (∀ x ∈ polarImage B φ W, ∀ y ∈ polarImage B φ W, B x y = 0) ∧
      φ '' ptsIn B W = ptsIn B (polarImage B φ W) ∧
      ∀ W' : Submodule K V, (∀ x ∈ W', ∀ y ∈ W', B x y = 0) →
        φ '' ptsIn B W = ptsIn B W' → W' = polarImage B φ W) ∧
    (∀ W : Submodule K V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) →
      finrank K (polarImage B φ W) = finrank K W) ∧
    (∀ W₁ W₂ : Submodule K V, (∀ x ∈ W₁, ∀ y ∈ W₁, B x y = 0) →
      (∀ x ∈ W₂, ∀ y ∈ W₂, B x y = 0) →
      (W₁ ≤ W₂ ↔ polarImage B φ W₁ ≤ polarImage B φ W₂)) ∧
    (∀ W : Submodule K V, (∀ x ∈ W, ∀ y ∈ W, B x y = 0) →
      polarImage B φ.symm (polarImage B φ W) = W) ∧
    (∀ L : isoLines B, polarImage B φ L = φ L) ∧
    ∀ M : Submodule K V, IsMaxTotIso B M →
      IsMaxTotIso B (polarImage B φ M) ∧
      (∀ L : isoLines B, (L : Submodule K V) ≤ M ↔ (φ L : Submodule K V) ≤ polarImage B φ M) ∧
      (∀ H : Submodule K V, H ≤ M → finrank K H + 1 = finrank K M →
        polarImage B φ H ≤ polarImage B φ M ∧
          finrank K (polarImage B φ H) + 1 = finrank K (polarImage B φ M) ∧
          ∀ L : isoLines B,
            ((L : Submodule K V) ≤ H ↔ (φ L : Submodule K V) ≤ polarImage B φ H)) ∧
      ∀ H' : Submodule K V, H' ≤ polarImage B φ M →
        finrank K H' + 1 = finrank K (polarImage B φ M) →
        ∃ H : Submodule K V, H ≤ M ∧ finrank K H + 1 = finrank K M ∧
          polarImage B φ H = H' := by
  have hφ' := subOrtho_symm_iff φ hφ
  refine ⟨fun W hW => ⟨isTotIso_polarImage φ hφ hW, (ptsIn_polarImage h hB hBl hφ hW).symm,
    fun W' hW' he => eq_polarImage φ hW' he⟩, fun W hW => finrank_polarImage h hB hBl hφ hW,
    fun W₁ W₂ h1 h2 => (polarImage_le_iff h hB hBl hφ h1 h2).symm,
    fun W hW => polarImage_symm_polarImage h hB hBl hφ hW, polarImage_point φ,
    fun M hM => ⟨(isMaxTotIso_ptSpan
      (isMaxClique_image φ hφ (isMaxClique_ptsIn hB.isRefl hM))).1, ?_, ?_, ?_⟩⟩
  · intro L
    rw [← polarImage_point φ L]
    exact (polarImage_le_iff h hB hBl hφ (isTotIso_of_mem_isoLines L.2) hM.1).symm
  · intro H hH hd
    have hHs : ∀ x ∈ H, ∀ y ∈ H, B x y = 0 := fun x hx y hy => hM.1 x (hH hx) y (hH hy)
    refine ⟨(polarImage_le_iff h hB hBl hφ hHs hM.1).2 hH, by
      rw [finrank_polarImage h hB hBl hφ hHs, finrank_polarImage h hB hBl hφ hM.1, hd],
      fun L => ?_⟩
    rw [← polarImage_point φ L]
    exact (polarImage_le_iff h hB hBl hφ (isTotIso_of_mem_isoLines L.2) hHs).symm
  · intro H' hH' hd
    have hMs := isTotIso_polarImage φ hφ hM.1
    have hHs : ∀ x ∈ H', ∀ y ∈ H', B x y = 0 := fun x hx y hy => hMs x (hH' hx) y (hH' hy)
    have hHs' := isTotIso_polarImage φ.symm hφ' hHs
    have hHH : polarImage B φ (polarImage B φ.symm H') = H' := by
      have := polarImage_symm_polarImage h hB hBl hφ' hHs
      rwa [Equiv.symm_symm] at this
    refine ⟨polarImage B φ.symm H', ?_, ?_, hHH⟩
    · rw [← polarImage_le_iff h hB hBl hφ hHs' hM.1, hHH]
      exact hH'
    · rw [← finrank_polarImage h hB hBl hφ hHs', hHH, hd, finrank_polarImage h hB hBl hφ hM.1]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
