module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCGeneration
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

@[expose] def adaptedShort (F : Type) [Field F] : Set (Subgroup (StatedSp 2 F)) :=
  {S | ∃ a₀ a₁ : SL(2, F), S = (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
      (MulAut.conj (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)).toMonoidHom}

@[expose] def shortNodes {F : Type} [Field F] {G : Type} [Group G] (Θ : StatedSp 2 F →* G) :
    Set (Subgroup G) :=
  {T | ∃ S ∈ adaptedShort F, T = S.map Θ}

structure C3Frame (G : Type) [Group G] (Ω : Set (Subgroup G)) where
  K₀ : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  Θ₀₁ : StatedSp 2 (GaloisField 3 1) →* G
  Θ₁₂ : StatedSp 2 (GaloisField 3 1) →* G
  inj₀₁ : Function.Injective Θ₀₁
  inj₁₂ : Function.Injective Θ₁₂
  hK₂ : K₂ ∈ Ω
  blk₀₁₀ : (planeGroup (stdPlane (GaloisField 3 1) 2 0)).map Θ₀₁ = K₀
  blk₀₁₁ : (planeGroup (stdPlane (GaloisField 3 1) 2 1)).map Θ₀₁ = K₁
  blk₁₂₀ : (planeGroup (stdPlane (GaloisField 3 1) 2 0)).map Θ₁₂ = K₁
  blk₁₂₁ : (planeGroup (stdPlane (GaloisField 3 1) 2 1)).map Θ₁₂ = K₂
  comm₀₁ : ∀ a ∈ Θ₀₁.range, ∀ b ∈ K₂, a * b = b * a
  comm₁₂ : ∀ a ∈ Θ₁₂.range, ∀ b ∈ K₀, a * b = b * a

namespace C3Frame

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} (fr : C3Frame G Ω)

theorem K₀_le_range : fr.K₀ ≤ fr.Θ₀₁.range :=
  fr.blk₀₁₀ ▸ Subgroup.map_le_range _ _

theorem K₁_le_range₀₁ : fr.K₁ ≤ fr.Θ₀₁.range :=
  fr.blk₀₁₁ ▸ Subgroup.map_le_range _ _

theorem K₁_le_range₁₂ : fr.K₁ ≤ fr.Θ₁₂.range :=
  fr.blk₁₂₀ ▸ Subgroup.map_le_range _ _

theorem K₂_le_range : fr.K₂ ≤ fr.Θ₁₂.range :=
  fr.blk₁₂₁ ▸ Subgroup.map_le_range _ _

theorem comm_K₀_K₁ : ∀ a ∈ fr.K₀, ∀ b ∈ fr.K₁, a * b = b * a :=
  fun a ha b hb => (fr.comm₁₂ b (fr.K₁_le_range₁₂ hb) a ha).symm

theorem comm_K₀_K₂ : ∀ a ∈ fr.K₀, ∀ b ∈ fr.K₂, a * b = b * a :=
  fun a ha b hb => fr.comm₀₁ a (fr.K₀_le_range ha) b hb

theorem comm_K₁_K₂ : ∀ a ∈ fr.K₁, ∀ b ∈ fr.K₂, a * b = b * a :=
  fun a ha b hb => fr.comm₀₁ a (fr.K₁_le_range₀₁ ha) b hb

end C3Frame

section Conj

variable {F : Type} [Field F]

private theorem longBlock_zero_comm_one (a b : SL(2, F)) :
    longBlock F 2 0 a * longBlock F 2 1 b = longBlock F 2 1 b * longBlock F 2 0 a :=
  (commute_longBlock_longBlock (zero_ne_one : (0 : Fin 2) ≠ 1) a b).eq

theorem longBlock_prod_mul (a₀ a₁ b₀ b₁ : SL(2, F)) :
    longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * (longBlock F 2 0 b₀ * longBlock F 2 1 b₁) =
      longBlock F 2 0 (a₀ * b₀) * longBlock F 2 1 (a₁ * b₁) := by
  rw [map_mul, map_mul]
  calc longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * (longBlock F 2 0 b₀ * longBlock F 2 1 b₁)
      = longBlock F 2 0 a₀ * (longBlock F 2 1 a₁ * longBlock F 2 0 b₀) * longBlock F 2 1 b₁ := by
        simp only [mul_assoc]
    _ = longBlock F 2 0 a₀ * (longBlock F 2 0 b₀ * longBlock F 2 1 a₁) * longBlock F 2 1 b₁ := by
        rw [← longBlock_zero_comm_one b₀ a₁]
    _ = longBlock F 2 0 a₀ * longBlock F 2 0 b₀ * (longBlock F 2 1 a₁ * longBlock F 2 1 b₁) := by
        simp only [mul_assoc]

theorem longBlock_prod_inv (a₀ a₁ : SL(2, F)) :
    (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)⁻¹ = longBlock F 2 0 a₀⁻¹ * longBlock F 2 1 a₁⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, longBlock_prod_mul, mul_inv_cancel, mul_inv_cancel, map_one, map_one,
    one_mul]

theorem conj_longBlock_zero (a₀ a₁ b : SL(2, F)) :
    longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * longBlock F 2 0 b *
        (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)⁻¹ = longBlock F 2 0 (a₀ * b * a₀⁻¹) := by
  rw [longBlock_prod_inv]
  have h1 := longBlock_zero_comm_one (b * a₀⁻¹) a₁
  calc longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * longBlock F 2 0 b *
        (longBlock F 2 0 a₀⁻¹ * longBlock F 2 1 a₁⁻¹)
      = longBlock F 2 0 a₀ * (longBlock F 2 1 a₁ * longBlock F 2 0 (b * a₀⁻¹)) *
          longBlock F 2 1 a₁⁻¹ := by rw [map_mul]; simp only [mul_assoc]
    _ = longBlock F 2 0 a₀ * (longBlock F 2 0 (b * a₀⁻¹) * longBlock F 2 1 a₁) *
          longBlock F 2 1 a₁⁻¹ := by rw [← h1]
    _ = longBlock F 2 0 (a₀ * b * a₀⁻¹) := by
        simp only [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem conj_longBlock_one (a₀ a₁ b : SL(2, F)) :
    longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * longBlock F 2 1 b *
        (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)⁻¹ = longBlock F 2 1 (a₁ * b * a₁⁻¹) := by
  rw [longBlock_prod_inv]
  have h1 := longBlock_zero_comm_one a₀⁻¹ (a₁ * b)
  calc longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * longBlock F 2 1 b *
        (longBlock F 2 0 a₀⁻¹ * longBlock F 2 1 a₁⁻¹)
      = longBlock F 2 0 a₀ * (longBlock F 2 1 (a₁ * b) * longBlock F 2 0 a₀⁻¹) *
          longBlock F 2 1 a₁⁻¹ := by rw [map_mul]; simp only [mul_assoc]
    _ = longBlock F 2 0 a₀ * (longBlock F 2 0 a₀⁻¹ * longBlock F 2 1 (a₁ * b)) *
          longBlock F 2 1 a₁⁻¹ := by rw [← h1]
    _ = longBlock F 2 1 (a₁ * b * a₁⁻¹) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, ← map_mul]

theorem map_conj_eq_self_of_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h₁ : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h₂ : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact ⟨fun hx => by simpa [mul_assoc] using h₁ _ hx, h₂ x⟩

theorem conj_mem_range_longBlock (a₀ a₁ : SL(2, F)) (k : Fin 2) {x : StatedSp 2 F}
    (hx : x ∈ (longBlock F 2 k).range) :
    longBlock F 2 0 a₀ * longBlock F 2 1 a₁ * x * (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)⁻¹ ∈
      (longBlock F 2 k).range := by
  obtain ⟨b, rfl⟩ := hx
  fin_cases k
  · exact ⟨_, (conj_longBlock_zero a₀ a₁ b).symm⟩
  · exact ⟨_, (conj_longBlock_one a₀ a₁ b).symm⟩

theorem map_conj_range_longBlock (a₀ a₁ : SL(2, F)) (k : Fin 2) :
    (longBlock F 2 k).range.map
        (MulAut.conj (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)).toMonoidHom =
      (longBlock F 2 k).range := by
  refine map_conj_eq_self_of_mem (fun x hx => conj_mem_range_longBlock a₀ a₁ k hx) fun x hx => ?_
  have h := conj_mem_range_longBlock a₀⁻¹ a₁⁻¹ k hx
  rw [longBlock_prod_inv a₀⁻¹ a₁⁻¹] at h
  simp only [inv_inv] at h
  rwa [← longBlock_prod_inv a₀ a₁] at h

theorem map_conj_range_longBlock_one (a₀ a₁ : SL(2, F)) :
    (longBlock F 2 1).range.map
        (MulAut.conj (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)).toMonoidHom =
      (longBlock F 2 1).range :=
  map_conj_range_longBlock a₀ a₁ 1

theorem map_conj_mem_adaptedShort {S : Subgroup (StatedSp 2 F)} (hS : S ∈ adaptedShort F)
    (a₀ a₁ : SL(2, F)) :
    S.map (MulAut.conj (longBlock F 2 0 a₀ * longBlock F 2 1 a₁)).toMonoidHom ∈
      adaptedShort F := by
  obtain ⟨b₀, b₁, rfl⟩ := hS
  refine ⟨a₀ * b₀, a₁ * b₁, ?_⟩
  rw [Subgroup.map_map, ← longBlock_prod_mul]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  simp only [mul_assoc]

theorem shortBlock_range_mem_adaptedShort :
    (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range ∈ adaptedShort F := by
  refine ⟨1, 1, ?_⟩
  simp only [map_one, mul_one]
  ext x
  simp

theorem le_range_of_mem_shortNodes {G : Type} [Group G] {Θ : StatedSp 2 F →* G}
    {T : Subgroup G} (h : T ∈ shortNodes Θ) : T ≤ Θ.range := by
  obtain ⟨S, -, rfl⟩ := h
  exact Subgroup.map_le_range Θ S

end Conj

theorem chain_of_frame_of_le {G : Type} [Group G] {Ω : Set (Subgroup G)} (fr : C3Frame G Ω)
    {T₀ T₁ : Subgroup G} (h₀ : T₀ ≤ fr.Θ₀₁.range) (h₁ : T₁ ∈ shortNodes fr.Θ₁₂)
    (hA : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W T₀ T₁) :
    ∃ U : Fin 3 → Subgroup G, U 2 ∈ Ω ∧ (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
      (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
        (U 1)) := by
  refine ⟨![T₀, T₁, fr.K₂], fr.hK₂, ?_, hA, ?_⟩
  · intro a ha b hb
    exact fr.comm₀₁ a (h₀ ha) b hb
  · obtain ⟨S, ⟨a₀, a₁, hS⟩, rfl⟩ := h₁
    refine ⟨fr.Θ₁₂.range, fr.Θ₁₂, (longBlock (GaloisField 3 1) 2 0 a₀ *
      longBlock (GaloisField 3 1) 2 1 a₁)⁻¹, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(MonoidHom.ker_eq_bot_iff _).2 fr.inj₁₂]
      exact bot_le
    · exact fr.inj₁₂.comp ((MulAut.conj _).injective.comp (longBlock_injective 1))
    · exact fr.inj₁₂.comp ((MulAut.conj _).injective.comp (shortBlock_injective _))
    · simp only [inv_inv, map_conj_range_longBlock_one]
      have h := fr.blk₁₂₁
      rw [planeGroup_stdPlane] at h
      exact h
    · simp only [inv_inv]
      exact (congrArg (Subgroup.map fr.Θ₁₂) hS).symm

theorem chain_of_frame {G : Type} [Group G] {Ω : Set (Subgroup G)} (fr : C3Frame G Ω)
    {T₀ T₁ : Subgroup G} (h₀ : T₀ ∈ shortNodes fr.Θ₀₁) (h₁ : T₁ ∈ shortNodes fr.Θ₁₂)
    (hA : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W T₀ T₁) :
    ∃ U : Fin 3 → Subgroup G, U 2 ∈ Ω ∧ (∀ a ∈ U 0, ∀ b ∈ U 2, a * b = b * a) ∧
      (∃ W, WeakCT.LinearBlockStandardPair (GaloisField 3 1) W (U 0) (U 1)) ∧
      (∃ W, Models.SymplecticPairs.SymplecticBlockStandardPair (GaloisField 3 1) W (U 2)
        (U 1)) :=
  chain_of_frame_of_le fr (le_range_of_mem_shortNodes h₀) h₁ hA

section Witt

variable {F : Type} [Field F] {n : ℕ}

theorem exists_conj_planes_of_orth {k l : Fin n} (hkl : k ≠ l)
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') (horth : ∀ u ∈ P, ∀ v ∈ P', form u v = 0) :
    ∃ g : StatedSp n F, (stdPlane F n k).map (Matrix.mulVecLin (mat n F g)) = P ∧
      (stdPlane F n l).map (Matrix.mulVecLin (mat n F g)) = P' := by
  obtain ⟨u₁, w₁, h₁, rfl⟩ := hP
  obtain ⟨u₂, w₂, h₂, rfl⟩ := hP'
  have hu₁ : u₁ ∈ Submodule.span F {u₁, w₁} := Submodule.subset_span (by simp)
  have hw₁ : w₁ ∈ Submodule.span F {u₁, w₁} := Submodule.subset_span (by simp)
  have hu₂ : u₂ ∈ Submodule.span F {u₂, w₂} := Submodule.subset_span (by simp)
  have hw₂ : w₂ ∈ Submodule.span F {u₂, w₂} := Submodule.subset_span (by simp)
  obtain ⟨g, a1, a2, a3, a4⟩ := exists_sp_apply_eq_two_at hkl u₁ w₁ u₂ w₂ h₁ h₂
    (horth _ hu₁ _ hu₂) (horth _ hu₁ _ hw₂) (horth _ hw₁ _ hu₂) (horth _ hw₁ _ hw₂)
  refine ⟨g, ?_, ?_⟩
  · rw [stdPlane, Submodule.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton, Matrix.mulVecLin_apply, a1, a2]
  · rw [stdPlane, Submodule.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton, Matrix.mulVecLin_apply, a3, a4]

theorem exists_conj_planeGroups_of_orth {k l : Fin n} (hkl : k ≠ l)
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') (horth : ∀ u ∈ P, ∀ v ∈ P', form u v = 0) :
    ∃ g : StatedSp n F,
      (planeGroup (stdPlane F n k)).map (MulAut.conj g).toMonoidHom = planeGroup P ∧
      (planeGroup (stdPlane F n l)).map (MulAut.conj g).toMonoidHom = planeGroup P' := by
  obtain ⟨g, h₀, h₁⟩ := exists_conj_planes_of_orth hkl hP hP' horth
  exact ⟨g, by rw [← planeGroup_map_conj, h₀], by rw [← planeGroup_map_conj, h₁]⟩

theorem exists_hom_sp4_of_orth {P P' : Submodule F (Fin 2 ⊕ Fin 2 → F)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P')
    (horth : ∀ u ∈ P, ∀ v ∈ P', form u v = 0) :
    ∃ h : StatedSp 2 F,
      (stdPlane F 2 0).map (Matrix.mulVecLin (mat 2 F h)) = P ∧
      (stdPlane F 2 1).map (Matrix.mulVecLin (mat 2 F h)) = P' ∧
      (planeGroup (stdPlane F 2 0)).map (MulAut.conj h).toMonoidHom = planeGroup P ∧
      (planeGroup (stdPlane F 2 1)).map (MulAut.conj h).toMonoidHom = planeGroup P' := by
  obtain ⟨g, h₀, h₁⟩ := exists_conj_planes_of_orth (zero_ne_one : (0 : Fin 2) ≠ 1) hP hP' horth
  exact ⟨g, h₀, h₁, by rw [← planeGroup_map_conj, h₀], by rw [← planeGroup_map_conj, h₁]⟩

theorem exists_normalized_layer {G : Type} [Group G] (Θ : StatedSp 2 F →* G)
    {P P' : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') (horth : ∀ u ∈ P, ∀ v ∈ P', form u v = 0) :
    ∃ Θ' : StatedSp 2 F →* G, Θ'.range = Θ.range ∧
      (Function.Injective Θ → Function.Injective Θ') ∧
      (planeGroup (stdPlane F 2 0)).map Θ' = (planeGroup P).map Θ ∧
      (planeGroup (stdPlane F 2 1)).map Θ' = (planeGroup P').map Θ := by
  obtain ⟨h, -, -, h₀, h₁⟩ := exists_hom_sp4_of_orth hP hP' horth
  refine ⟨Θ.comp (MulAut.conj h).toMonoidHom, ?_, fun hΘ => hΘ.comp (MulAut.conj h).injective,
    ?_, ?_⟩
  · ext x
    simp only [MonoidHom.mem_range, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨h⁻¹ * y * h, by simp [mul_assoc]⟩
  · rw [← Subgroup.map_map, h₀]
  · rw [← Subgroup.map_map, h₁]

theorem exists_noncomm_longBlock_range (k : Fin n) :
    ∃ x ∈ (longBlock F n k).range, ∃ y ∈ (longBlock F n k).range, x * y ≠ y * x :=
  ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, noncomm_longBlock_transv k⟩

theorem exists_noncomm_planeGroup (hn : 1 ≤ n) {P : Submodule F (Fin n ⊕ Fin n → F)}
    (hP : IsHyperbolicPlane P) : ∃ x ∈ planeGroup P, ∃ y ∈ planeGroup P, x * y ≠ y * x := by
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (⟨0, hn⟩ : Fin n)
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_longBlock_range (F := F) (⟨0, hn⟩ : Fin n)
  refine ⟨g * x * g⁻¹, ?_, g * y * g⁻¹, ?_, fun h => hxy ?_⟩
  · rw [hg]
    exact ⟨x, hx, rfl⟩
  · rw [hg]
    exact ⟨y, hy, rfl⟩
  · have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by simpa [mul_assoc] using h
    simpa using h'

theorem commute_planeGroup_iff (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n)
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') :
    (∀ x ∈ planeGroup P, ∀ y ∈ planeGroup P', x * y = y * x) ↔
      ∀ u ∈ P, ∀ v ∈ P', form u v = 0 := by
  constructor
  · intro hc
    by_cases hne : planeGroup P = planeGroup P'
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_planeGroup (by omega) hP
      exact hxy (hc x hx y (hne ▸ hy))
    · exact forall_form_eq_zero_of_commute_planeGroup h2 hP hP' hne hc
  · intro horth x hx y hy
    have hkl : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, hn⟩ := fun h => by simpa using congrArg Fin.val h
    obtain ⟨g, h₀, h₁⟩ := exists_conj_planeGroups_of_orth hkl hP hP' horth
    rw [← h₀] at hx
    rw [← h₁] at hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rw [planeGroup_stdPlane] at hx₀ hy₀
    have hc := (commute_longRootSp2 hkl hx₀ hy₀).eq
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc]

theorem planeGroup_ne_of_orth (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n)
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') (horth : ∀ u ∈ P, ∀ v ∈ P', form u v = 0) :
    planeGroup P ≠ planeGroup P' := by
  intro hne
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_planeGroup (by omega) hP
  exact hxy ((commute_planeGroup_iff h2 hn hP hP').2 horth x hx y (hne ▸ hy))

end Witt

section Center

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def negOne (n : ℕ) (F : Type) [Field F] : StatedSp n F :=
  ofSymplecticMat (-1) (by simp)

theorem mat_negOne : mat n F (negOne n F) = -1 := rfl

theorem negOne_mem_center : negOne n F ∈ Subgroup.center (StatedSp n F) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply mat_injective
  rw [map_mul, map_mul, mat_negOne, mul_neg, mul_one, neg_mul, one_mul]

theorem mem_center_iff_negOne (hn : 1 ≤ n) {g : StatedSp n F} :
    g ∈ Subgroup.center (StatedSp n F) ↔ g = 1 ∨ g = negOne n F := by
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hg
    have hmat : mat n F g = Matrix.diagonal (fun _ => (c : F)) := by
      change ((g : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
      rfl
    have h1 := mul_self_eq_one_of_mem_center hn hg
    have hcc : (c : F) * (c : F) = 1 := by
      have := congrArg (fun x => mat n F x (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩)) h1
      simpa [map_mul, hmat, Matrix.diagonal_mul_diagonal] using this
    rcases mul_self_eq_one_iff.1 hcc with h | h
    · left
      apply mat_injective
      rw [hmat, h, map_one]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    · right
      apply mat_injective
      rw [hmat, h, mat_negOne]
      ext a b
      by_cases hab : a = b <;> simp [hab]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact negOne_mem_center

theorem negOne_ne_one (h2 : (2 : F) ≠ 0) (hn : 1 ≤ n) : negOne n F ≠ 1 := by
  intro h
  have := congrArg (fun x => mat n F x (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩)) h
  simp only [mat_negOne, map_one, Matrix.neg_apply, Matrix.one_apply_eq] at this
  exact h2 (by linear_combination -this)

theorem negOne_two_eq : negOne 2 F = longInv F 2 0 * longInv F 2 1 := by
  apply mat_injective
  rw [map_mul, mat_negOne, mat_longInv, mat_longInv, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst hab
    rcases a with a | a <;> fin_cases a <;> simp [coords]
  · simp [hab]

theorem shortBlock_neg_one_eq_negOne :
    shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) (-1) = negOne 2 F :=
  (shortBlock_neg_one _).trans negOne_two_eq.symm

theorem negOne_mem_range_shortBlock :
    negOne 2 F ∈ (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range :=
  ⟨-1, shortBlock_neg_one_eq_negOne⟩

theorem negOne_notMem_planeGroup (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n)
    {P : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P) :
    negOne n F ∉ planeGroup P := by
  intro hmem
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (⟨0, by omega⟩ : Fin n)
  rw [hg] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hcen := negOne_mem_center (n := n) (F := F)
  have hy1 : y = negOne n F := by
    have h := Subgroup.mem_center_iff.1 hcen g⁻¹
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = g⁻¹ * negOne n F * g := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
        rw [hyx]
      _ = negOne n F := by rw [h]; group
  rw [hy1, range_longBlock] at hy
  have ht : (Sum.inl ⟨1, hn⟩ : Fin n ⊕ Fin n) ∉ coords (⟨0, by omega⟩ : Fin n) := by
    intro h
    rcases mem_coords.1 h with h | h
    · simpa using congrArg Fin.val (Sum.inl_injective h)
    · exact Sum.inl_ne_inr h
  exact negOne_ne_one h2 (by omega) (eq_one_of_mem_center_of_mem_suppGroup hcen hy ht)

theorem negOne_notMem_range_longBlock (h2 : (2 : F) ≠ 0) (hn : 2 ≤ n) (k : Fin n) :
    negOne n F ∉ (longBlock F n k).range := by
  have := negOne_notMem_planeGroup h2 hn (isHyperbolicPlane_stdPlane (K := F) (n := n) k)
  rwa [planeGroup_stdPlane] at this

theorem ker_eq_bot_of_longInv_ne {G : Type} [Group G] (Θ : StatedSp 2 F →* G)
    (hker : Θ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hne : Θ (longInv F 2 0) ≠ Θ (longInv F 2 1)) : Θ.ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  rcases (mem_center_iff_negOne (n := 2) (by norm_num)).1 (hker hx) with h | h
  · exact h
  · exfalso
    rw [h, negOne_two_eq] at hx
    have h1 : Θ (longInv F 2 0) * Θ (longInv F 2 1) = 1 := by
      rw [← map_mul]
      exact hx
    have hinv : Θ (longInv F 2 1) * Θ (longInv F 2 1) = 1 := by
      rw [← map_mul, longInv, ← map_mul]
      have : (-1 : SL(2, F)) * -1 = 1 := by
        ext i j
        simp
      rw [this, map_one, map_one]
    exact hne ((eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right hinv))

theorem injective_of_longInv_ne {G : Type} [Group G] (Θ : StatedSp 2 F →* G)
    (hker : Θ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hne : Θ (longInv F 2 0) ≠ Θ (longInv F 2 1)) : Function.Injective Θ :=
  (MonoidHom.ker_eq_bot_iff Θ).1 (ker_eq_bot_of_longInv_ne Θ hker hne)

theorem ker_eq_bot_of_injective_shortBlock (h2 : (2 : F) ≠ 0) {G : Type} [Group G]
    (Θ : StatedSp 2 F →* G) (hker : Θ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hinj : Function.Injective (Θ.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)))) :
    Θ.ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  rcases (mem_center_iff_negOne (n := 2) (by norm_num)).1 (hker hx) with h | h
  · exact h
  · exfalso
    rw [h, ← shortBlock_neg_one_eq_negOne] at hx
    have h1 : (Θ.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))) (-1) =
        (Θ.comp (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))) 1 := by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_one, map_one]
      exact MonoidHom.mem_ker.1 hx
    have h3 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) (hinj h1)
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h3
    exact h2 (by linear_combination -h3)

end Center

section GF3

theorem gf3_two_ne_zero : (2 : GaloisField 3 1) ≠ 0 := by
  have : ringChar (GaloisField 3 1) = 3 := ringChar.eq (GaloisField 3 1) 3
  exact Ring.two_ne_zero (by rw [this]; norm_num)

theorem commute_planeGroup_iff_sp4
    {P P' : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1)}
    (hP : IsHyperbolicPlane P) (hP' : IsHyperbolicPlane P') :
    (∀ x ∈ planeGroup P, ∀ y ∈ planeGroup P', x * y = y * x) ↔
      ∀ u ∈ P, ∀ v ∈ P', form u v = 0 :=
  commute_planeGroup_iff gf3_two_ne_zero le_rfl hP hP'

theorem coe_center_eq {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n) :
    (Subgroup.center (StatedSp n F) : Set (StatedSp n F)) = {1, negOne n F} := by
  ext g
  simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mem_center_iff_negOne hn

end GF3

end CFSG.ClassicalInvolution.Q3.Q3Z
