module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4A2Table
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi4
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality

set_option linter.unusedSectionVars false


namespace HeisA

variable {L : Type} [Field L]

@[expose] def ActsAs (h : ModGL Tag.E6 L)
    (φ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) : Prop :=
  ∀ β, IsRoot Tag.E6 β → IsRoot Tag.E6 (φ β) ∧ ∃ ε : L, ε ≠ 0 ∧
    ∀ c : L, h * pinnedX Tag.E6 L β c * h⁻¹ = pinnedX Tag.E6 L (φ β) (ε * c)

theorem actsAs_one : ActsAs (1 : ModGL Tag.E6 L) id := fun β hβ =>
  ⟨hβ, 1, one_ne_zero, fun c => by simp⟩

theorem ActsAs.mul {h₁ h₂ : ModGL Tag.E6 L} {φ₁ φ₂ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (H₁ : ActsAs h₁ φ₁) (H₂ : ActsAs h₂ φ₂) : ActsAs (h₁ * h₂) (φ₁ ∘ φ₂) := by
  intro β hβ
  obtain ⟨hr₂, ε₂, hε₂, h₂c⟩ := H₂ β hβ
  obtain ⟨hr₁, ε₁, hε₁, h₁c⟩ := H₁ (φ₂ β) hr₂
  refine ⟨hr₁, ε₁ * ε₂, mul_ne_zero hε₁ hε₂, fun c => ?_⟩
  have e : h₁ * h₂ * pinnedX Tag.E6 L β c * (h₁ * h₂)⁻¹ =
      h₁ * (h₂ * pinnedX Tag.E6 L β c * h₂⁻¹) * h₁⁻¹ := by group
  rw [e, h₂c, h₁c, mul_assoc]
  rfl

theorem ActsAs.pow {h : ModGL Tag.E6 L} {φ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (H : ActsAs h φ) (m : ℕ) : ActsAs (h ^ m) (φ^[m]) := by
  induction m with
  | zero => simpa using actsAs_one (L := L)
  | succ m ih =>
    rw [pow_succ', Function.iterate_succ']
    exact H.mul ih

theorem actsAs_rootDiagUnit (b : Fin Tag.E6.rank → Lˣ) :
    ActsAs (rootDiagUnit Tag.E6 b) id := fun β hβ =>
  ⟨hβ, (rootChar b β : L), Units.ne_zero _, fun c => rootDiagUnit_conj_pinnedX b hβ c⟩

theorem actsAs_canonicalRep (w : WeylGroup Tag.E6) :
    ActsAs (canonicalRep (coxeterSystem Tag.E6) L w) (fun v => w • v) := fun β hβ => by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hβ
  refine ⟨IsRoot.smul hβ w, ε, ?_, h⟩
  rintro rfl
  simp at hε

theorem actsAs_diagramMap :
    ActsAs (diagramMap TwistTag.E6 L) (permLattice TwistTag.E6.perm) := fun β hβ => by
  obtain ⟨ε, hε, h⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hβ
  refine ⟨hβ.permLattice (fun i j => TwistTag.cartan_perm TwistTag.E6 i j), ε, ?_, h⟩
  rintro rfl
  simp at hε

theorem pinnedX_pow (β : Fin Tag.E6.rank → ℤ) (c : L) (m : ℕ) :
    pinnedX Tag.E6 L β c ^ m = pinnedX Tag.E6 L β (m • c) := by
  induction m with
  | zero => simp [pinnedX_zero]
  | succ m ih => rw [pow_succ, ih, ← pinnedX_add, succ_nsmul]

theorem not_commute_xUnit_yUnit' (i : Fin Tag.E6.rank) {c d : L} (hc : c ≠ 0) (hd : d ≠ 0) :
    ¬ Commute (xUnit Tag.E6 L i c) (yUnit Tag.E6 L i d) := by
  intro h
  obtain ⟨h1, h2, -⟩ := opposite_simple_root_noncommutativity Tag.E6 L
  apply h2 i c d hc hd
  rw [← h1]
  have h' := congrArg Units.val h.eq
  rw [Units.val_mul, Units.val_mul, coe_xUnit, coe_yUnit] at h'
  rw [h', sub_self, LinearMap.zero_apply]

theorem not_commute_pinnedX_neg {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) {c d : L}
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ¬ Commute (pinnedX Tag.E6 L β c) (pinnedX Tag.E6 L (-β) d) := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  obtain ⟨ε₁, hε₁, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (isRoot_single Tag.E6 i)
  obtain ⟨ε₂, hε₂, hY⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w (isRoot_neg_single Tag.E6 i)
  intro h
  have hε₁0 : ε₁ ≠ 0 := by rintro rfl; simp at hε₁
  have hε₂0 : ε₂ ≠ 0 := by rintro rfl; simp at hε₂
  set n := canonicalRep (coxeterSystem Tag.E6) L w
  have e1 : pinnedX Tag.E6 L (w • Pi.single i 1) c = n * xUnit Tag.E6 L i (ε₁ * c) * n⁻¹ := by
    rw [← pinnedX_single, hX, ← mul_assoc, hε₁, one_mul]
  have e2 : pinnedX Tag.E6 L (-(w • Pi.single i 1)) d =
      n * yUnit Tag.E6 L i (ε₂ * d) * n⁻¹ := by
    rw [← smul_neg, ← pinnedX_neg_single, hY, ← mul_assoc, hε₂, one_mul]
  rw [e1, e2] at h
  refine not_commute_xUnit_yUnit' i (mul_ne_zero hε₁0 hc) (mul_ne_zero hε₂0 hd) ?_
  have h' : (n * xUnit Tag.E6 L i (ε₁ * c) * n⁻¹) * (n * yUnit Tag.E6 L i (ε₂ * d) * n⁻¹) =
      (n * yUnit Tag.E6 L i (ε₂ * d) * n⁻¹) * (n * xUnit Tag.E6 L i (ε₁ * c) * n⁻¹) := h.eq
  show xUnit Tag.E6 L i (ε₁ * c) * yUnit Tag.E6 L i (ε₂ * d) =
    yUnit Tag.E6 L i (ε₂ * d) * xUnit Tag.E6 L i (ε₁ * c)
  calc xUnit Tag.E6 L i (ε₁ * c) * yUnit Tag.E6 L i (ε₂ * d)
      = n⁻¹ * ((n * xUnit Tag.E6 L i (ε₁ * c) * n⁻¹) *
          (n * yUnit Tag.E6 L i (ε₂ * d) * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * yUnit Tag.E6 L i (ε₂ * d) * n⁻¹) *
          (n * xUnit Tag.E6 L i (ε₁ * c) * n⁻¹)) * n := by rw [h']
    _ = yUnit Tag.E6 L i (ε₂ * d) * xUnit Tag.E6 L i (ε₁ * c) := by group

theorem rootSpan_induction {S : Set (Fin Tag.E6.rank → ℤ)} {P : ModGL Tag.E6 L → Prop}
    {x : ModGL Tag.E6 L} (hx : x ∈ rootSpan Tag.E6 L S)
    (hgen : ∀ β ∈ S, ∀ c : L, P (pinnedX Tag.E6 L β c)) (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) : P x := by
  unfold rootSpan at hx
  refine Subgroup.iSup_induction (fun α => ⨆ _ : α ∈ S, rootSubgroup Tag.E6 L α) (C := P) hx ?_ h1
    hmul
  intro α y hy
  by_cases hα : α ∈ S
  · rw [iSup_pos hα] at hy
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    exact hgen α hα c
  · rw [iSup_neg hα, Subgroup.mem_bot] at hy
    rw [hy]
    exact h1

theorem commute_rootSpan_of_orth {S S' : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot Tag.E6 β) (hS' : ∀ γ ∈ S', IsRoot Tag.E6 γ)
    (h : ∀ β ∈ S, ∀ γ ∈ S', β ≠ γ ∧ β ≠ -γ ∧ ¬ IsRoot Tag.E6 (β + γ)) :
    ∀ s ∈ rootSpan Tag.E6 L S, ∀ t ∈ rootSpan Tag.E6 L S', Commute s t := by
  intro s hs t ht
  have hgen : ∀ β ∈ S, ∀ γ ∈ S', ∀ c d : L,
      Commute (pinnedX Tag.E6 L β c) (pinnedX Tag.E6 L γ d) := by
    intro β hβ γ hγ c d
    obtain ⟨h1, h2, h3⟩ := h β hβ γ hγ
    exact (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) (hS β hβ) (hS' γ hγ)
      h1 h2).2 h3 L _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)
  have h1 : ∀ β ∈ S, ∀ c : L, ∀ t ∈ rootSpan Tag.E6 L S',
      Commute (pinnedX Tag.E6 L β c) t := by
    intro β hβ c t ht
    refine rootSpan_induction (P := fun t => Commute (pinnedX Tag.E6 L β c) t) ht ?_
      (Commute.one_right _) (fun x y hx hy => hx.mul_right hy)
    intro γ hγ d
    exact hgen β hβ γ hγ c d
  refine rootSpan_induction (P := fun s => Commute s t) hs ?_ (Commute.one_left _)
    (fun x y hx hy => hx.mul_left hy)
  intro β hβ c
  exact h1 β hβ c t ht

theorem conj_mem_rootSpan_of_actsAs {h : ModGL Tag.E6 L}
    {φ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (H : ActsAs h φ)
    {S S' : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot Tag.E6 β)
    (hφ : ∀ β ∈ S, φ β ∈ S') :
    ∀ s ∈ rootSpan Tag.E6 L S, h * s * h⁻¹ ∈ rootSpan Tag.E6 L S' := by
  intro s hs
  refine rootSpan_induction (P := fun s => h * s * h⁻¹ ∈ rootSpan Tag.E6 L S') hs ?_
    (by simp) ?_
  · intro β hβ c
    obtain ⟨-, ε, -, hε⟩ := H β (hS β hβ)
    rw [hε c]
    exact rootSubgroup_le_rootSpan (hφ β hβ) (mem_rootSubgroup.2 ⟨_, rfl⟩)
  · intro x y hx hy
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact mul_mem hx hy

theorem conj_map_rootSpan_of_actsAs {h : ModGL Tag.E6 L}
    {φ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (H : ActsAs h φ)
    {S : Set (Fin Tag.E6.rank → ℤ)} (hS : ∀ β ∈ S, IsRoot Tag.E6 β) (himg : φ '' S = S) :
    (rootSpan Tag.E6 L S).map (MulAut.conj h).toMonoidHom = rootSpan Tag.E6 L S := by
  refine le_antisymm ?_ ?_
  · have hφ : ∀ β ∈ S, φ β ∈ S := fun β hβ => by
      have h' : φ β ∈ φ '' S := ⟨β, hβ, rfl⟩
      rwa [himg] at h'
    rintro _ ⟨s, hs, rfl⟩
    exact conj_mem_rootSpan_of_actsAs H hS hφ s hs
  · refine iSup₂_le fun β hβ => ?_
    have hβ' : β ∈ φ '' S := by rwa [himg]
    obtain ⟨β', hβ'S, rfl⟩ := hβ'
    obtain ⟨-, ε, hε, hc⟩ := H β' (hS β' hβ'S)
    rintro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    refine ⟨pinnedX Tag.E6 L β' (ε⁻¹ * c), rootSubgroup_le_rootSpan hβ'S
      (mem_rootSubgroup.2 ⟨_, rfl⟩), ?_⟩
    change h * pinnedX Tag.E6 L β' (ε⁻¹ * c) * h⁻¹ = _
    rw [hc, ← mul_assoc, mul_inv_cancel₀ hε, one_mul]

theorem mem_normalizer_familyGroup_of_actsAs {h : ModGL Tag.E6 L}
    {φ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (H : ActsAs h φ)
    {a : Fin Tag.E6.rank → Lˣ}
    (hT : h ∈ Subgroup.normalizer (torusGroup Tag.E6 L : Set (ModGL Tag.E6 L)))
    (himg : φ '' rootCharKernel a = rootCharKernel a) :
    h ∈ Subgroup.normalizer
      (familyGroup (K := L) (fun _ : Unit => a) : Set (ModGL Tag.E6 L)) := by
  have hker : familyKernel (fun _ : Unit => a) = rootCharKernel a := by
    ext β
    simp [familyKernel, rootCharKernel]
  have hmap : (familyGroup (K := L) (fun _ : Unit => a)).map (MulAut.conj h).toMonoidHom =
      familyGroup (fun _ : Unit => a) := by
    rw [familyGroup, Subgroup.map_sup, map_conj_eq_of_mem_normalizer hT, hker]
    rw [conj_map_rootSpan_of_actsAs H (fun β hβ => hβ.1) himg]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h' := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h'
  exact h'

theorem mem_normalizer_of_commute {G : Type*} [Group G] (H : Subgroup G) {x : G}
    (hx : ∀ s ∈ H, Commute x s) : x ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have e : x * g * x⁻¹ = g := by rw [(hx g hg).eq]; group
    rw [e]
    exact hg
  · intro hg
    have e : x⁻¹ * (x * g * x⁻¹) * x = x * g * x⁻¹ := by
      have := (hx _ hg).eq
      calc x⁻¹ * (x * g * x⁻¹) * x = x⁻¹ * ((x * g * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * g * x⁻¹)) := by rw [this]
        _ = x * g * x⁻¹ := by group
    have e' : g = x * g * x⁻¹ := by
      calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x * g * x⁻¹ := e
    rw [e']
    exact hg

theorem familyGroup_le_normalizer_rootSpan {C : Fin 3 → Set (Fin Tag.E6.rank → ℤ)}
    {a : Fin Tag.E6.rank → Lˣ} (hCroot : ∀ j, ∀ β ∈ C j, IsRoot Tag.E6 β)
    (hSig : ∀ β, β ∈ rootCharKernel a ↔ ∃ j, β ∈ C j)
    (hCorth : ∀ i j, i ≠ j → ∀ β ∈ C i, ∀ γ ∈ C j,
      β ≠ γ ∧ β ≠ -γ ∧ ¬ IsRoot Tag.E6 (β + γ)) (j : Fin 3) :
    familyGroup (K := L) (fun _ : Unit => a) ≤
      Subgroup.normalizer (rootSpan Tag.E6 L (C j) : Set (ModGL Tag.E6 L)) := by
  refine sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (hCroot j)) ?_
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨i, hi⟩ := (hSig β).1 ⟨hβ.1, hβ.2 ()⟩
  by_cases hij : i = j
  · subst hij
    exact (rootSubgroup_le_rootSpan hi).trans Subgroup.le_normalizer
  · intro x hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    refine mem_normalizer_of_commute _ fun s hs => ?_
    exact commute_rootSpan_of_orth (hCroot i) (hCroot j) (hCorth i j hij) _
      (rootSubgroup_le_rootSpan hi (mem_rootSubgroup.2 ⟨c, rfl⟩)) s hs

theorem iform_self_E6 : ∀ β ∈ rootFinset Tag.E6, iform β β = 2 := by decide +kernel

theorem root_pair_cases_E6 : ∀ β ∈ rootFinset Tag.E6, ∀ γ ∈ rootFinset Tag.E6,
    iform γ β = 0 ∨ γ = β ∨ γ = -β ∨ iform γ β = 1 ∨ iform γ β = -1 := by decide +kernel

theorem iform_neg_right_E6 (x y : Fin Tag.E6.rank → ℤ) : iform x (-y) = -iform x y := by
  have := iform_smul_right (τ := Tag.E6) (-1) x y
  simpa using this

theorem rootReflection_smul_E6' {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (x : Fin Tag.E6.rank → ℤ) : rootReflection β • x = x - iform β x • β := by
  rw [rootReflection_smul hβ]
  have h2 : iform β β = 2 := iform_self_E6 β (mem_rootFinset.2 hβ)
  simp [corootPair, h2]

theorem rootChar_add' (a : Fin Tag.E6.rank → Lˣ) (v w : Fin Tag.E6.rank → ℤ) :
    rootChar a (v + w) = rootChar a v * rootChar a w := by
  simp only [rootChar, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem rootChar_neg'' (a : Fin Tag.E6.rank → Lˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

theorem exists_reflection_word_of_iform_ne_zero {a : Fin Tag.E6.rank → Lˣ}
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ rootCharKernel a) (hγ : γ ∈ rootCharKernel a)
    (hne : iform γ β ≠ 0) :
    ∃ v ∈ Subgroup.closure ((fun α => rootReflection α) '' rootCharKernel a), v • γ = β := by
  have hβr : IsRoot Tag.E6 β := hβ.1
  have hγr : IsRoot Tag.E6 γ := hγ.1
  have hβ2 : iform β β = 2 := iform_self_E6 β (mem_rootFinset.2 hβr)
  have hγ2 : iform γ γ = 2 := iform_self_E6 γ (mem_rootFinset.2 hγr)
  have hrefl : ∀ {α : Fin Tag.E6.rank → ℤ}, α ∈ rootCharKernel a →
      rootReflection α ∈ Subgroup.closure ((fun α => rootReflection α) '' rootCharKernel a) :=
    fun hα => Subgroup.subset_closure ⟨_, hα, rfl⟩
  rcases root_pair_cases_E6 β (mem_rootFinset.2 hβr) γ (mem_rootFinset.2 hγr) with
    h | h | h | h | h
  · exact absurd h hne
  · exact ⟨1, one_mem _, by rw [h, one_smul]⟩
  · refine ⟨rootReflection β, hrefl hβ, ?_⟩
    rw [rootReflection_smul_E6' hβr, h, iform_neg_right_E6 β β, hβ2]
    ext i
    simp
    ring
  ·
    have hα : IsRoot Tag.E6 (γ - β) := by
      have := IsRoot.smul hγr (rootReflection β)
      rwa [rootReflection_smul_E6' hβr, iform_comm, h, one_smul] at this
    have hαk : γ - β ∈ rootCharKernel a := by
      refine ⟨hα, ?_⟩
      rw [sub_eq_add_neg, rootChar_add', rootChar_neg'', hβ.2, hγ.2]
      simp
    refine ⟨rootReflection (γ - β), hrefl hαk, ?_⟩
    rw [rootReflection_smul_E6' hα, iform_sub_left, iform_comm β γ, h, hγ2]
    ext i
    simp
  ·
    have hα : IsRoot Tag.E6 (γ + β) := by
      have := IsRoot.smul hγr (rootReflection β)
      rwa [rootReflection_smul_E6' hβr, iform_comm, h, sub_eq_add_neg, neg_smul, neg_neg,
        one_smul] at this
    have hαk : γ + β ∈ rootCharKernel a := by
      refine ⟨hα, ?_⟩
      rw [rootChar_add', hβ.2, hγ.2]
      simp
    refine ⟨rootReflection β * rootReflection (γ + β), (Subgroup.mul_mem _ (hrefl hβ) (hrefl hαk)),
      ?_⟩
    rw [mul_smul, rootReflection_smul_E6' hα, iform_add_left, iform_comm β γ, h, hγ2]
    have e : γ - (2 + -1) • (γ + β) = -β := by
      ext i
      simp
    rw [e, rootReflection_smul_E6' hβr, iform_neg_right_E6 β β, hβ2]
    ext i
    simp
    ring

end HeisA

end CFSG.LieType.SeitzGeneration.ExcWideThree
