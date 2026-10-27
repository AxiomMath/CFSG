module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Twist
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Lemma610
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Frame
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Phan.Parabolic.Generation

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Models
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] {Q : QuadraticForm K V}

structure UnitaryEmbedding.Adapted (D : UnitaryEmbedding Q σ) (F₁ F₂ : Frame Q) : Prop where
  left : ∀ x : Fin 3 → K', x 2 = 0 → D.incl x ∈ F₁.span
  right : ∀ x : Fin 3 → K', x 0 = 0 → D.incl x ∈ F₂.span

namespace UnitaryEmbedding.Adapted

variable {D : UnitaryEmbedding Q σ} {F₁ F₂ : Frame Q} (hD : D.Adapted F₁ F₂)
  (E : QuadExt K K' σ)

include hD in
theorem flip (j : Fin 3) : (D.flip E j).Adapted F₁ F₂ where
  left x hx := hD.left (E.flipAt j x) (by
    rw [E.flipAt_apply]
    split_ifs <;> simp [hx])
  right x hx := hD.right (E.flipAt j x) (by
    rw [E.flipAt_apply]
    split_ifs <;> simp [hx])

variable (h2 : (2 : K) ≠ 0) (W : WittData σ)

include hD E h2 W in
theorem map_block_two :
    (embSUid σ 2).range.map D.theta = F₁.La.range ∨
      (embSUid σ 2).range.map D.theta = F₁.swap.La.range := by
  rw [← D.hypFrame_La_range_block E h2 W 2]
  have hle := D.hypFrame_span_le_of_coord E h2 W 2 hD.left
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [Frame.finrank_span, Frame.finrank_span])
  exact Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq heq)

include hD E h2 W in
theorem map_block_zero :
    (embSUid σ 0).range.map D.theta = F₂.La.range ∨
      (embSUid σ 0).range.map D.theta = F₂.swap.La.range := by
  rw [← D.hypFrame_La_range_block E h2 W 0]
  have hle := D.hypFrame_span_le_of_coord E h2 W 0 hD.right
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [Frame.finrank_span, Frame.finrank_span])
  exact Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq heq)

include hD E h2 W in
theorem exists_fix_block_two :
    ∃ D' : UnitaryEmbedding Q σ, D'.Adapted F₁ F₂ ∧
      (embSUid σ 2).range.map D'.theta = F₁.La.range ∧
      ∀ g ∈ (embSUid σ 0).range, D'.theta g = D.theta g := by
  by_cases hX : (embSUid σ 2).range.map D.theta = F₁.La.range
  · exact ⟨D, hD, hX, fun _ _ => rfl⟩
  · refine ⟨D.flip E 0, hD.flip E 0, ?_, fun g hg => D.flip_theta_of_mem_range E 0 hg⟩
    obtain ⟨g, hg, hg0⟩ := exists_block_two E.isUnitary W E.tau_spec.2 E.tau_ne_zero
    have hne := D.flip_map_ne E E.isUnitary.exists_ne (by decide : (0 : Fin 3) ≠ 1) hg hg0
    rcases (hD.flip E 0).map_block_two E h2 W with h | h
    · exact h
    · exact absurd (h.trans ((hD.map_block_two E h2 W).resolve_left hX).symm) hne

include hD E h2 W in
theorem exists_fix_block_zero :
    ∃ D' : UnitaryEmbedding Q σ, D'.Adapted F₁ F₂ ∧
      (embSUid σ 0).range.map D'.theta = F₂.La.range ∧
      ∀ g ∈ (embSUid σ 2).range, D'.theta g = D.theta g := by
  by_cases hX : (embSUid σ 0).range.map D.theta = F₂.La.range
  · exact ⟨D, hD, hX, fun _ _ => rfl⟩
  · refine ⟨D.flip E 2, hD.flip E 2, ?_, fun g hg => D.flip_theta_of_mem_range E 2 hg⟩
    obtain ⟨g, hg, hg0⟩ := exists_block_zero E.isUnitary W E.tau_spec.2 E.tau_ne_zero
    have hne := D.flip_map_ne E E.isUnitary.exists_ne (by decide : (2 : Fin 3) ≠ 1) hg hg0
    rcases (hD.flip E 2).map_block_zero E h2 W with h | h
    · exact h
    · exact absurd (h.trans ((hD.map_block_zero E h2 W).resolve_left hX).symm) hne

end UnitaryEmbedding.Adapted

theorem exists_adapted [FiniteDimensional K V] (E : QuadExt K K' σ) (h2 : (2 : K) ≠ 0)
    {F₁ F₂ : Frame Q} (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2)
    (hs : ¬ HasSingularVector Q (F₁.span ⊓ F₂.span)) :
    ∃ D : UnitaryEmbedding Q σ, D.Adapted F₁ F₂ := by
  have hd₁ := Frame.finrank_span_inf_perp h2 hc h
  have hd₃ := Frame.finrank_perp_inf_span h2 hc h
  have hs₁ : ¬ HasSingularVector Q (F₁.span ⊓ F₂.perp) := fun h' => hs
    ((Frame.hasSingularVector_iff_of_decomp (Frame.span_eq_sup h2 hc) Frame.horth₁₂ hd₁ h).mp h')
  have hs₃ : ¬ HasSingularVector Q (F₁.perp ⊓ F₂.span) := fun h' => hs
    ((Frame.hasSingularVector_iff_of_decomp (Frame.span_eq_sup' h2 hc) Frame.horth₂₃ h hd₃).mpr h')
  obtain ⟨φ₁, hφ₁, -, hQ₁⟩ := E.exists_normIso h2 hd₁ hs₁
  obtain ⟨φ₂, hφ₂, -, hQ₂⟩ := E.exists_normIso h2 h hs
  obtain ⟨φ₃, hφ₃, -, hQ₃⟩ := E.exists_normIso h2 hd₃ hs₃
  have o12 : ∀ x y, polar Q (φ₁ x) (φ₂ y) = 0 := fun x y =>
    Frame.horth₁₂ _ (hφ₁ x) _ (hφ₂ y)
  have o13 : ∀ x y, polar Q (φ₁ x) (φ₃ y) = 0 := fun x y =>
    Frame.horth₁₃ _ (hφ₁ x) _ (hφ₃ y)
  have o23 : ∀ x y, polar Q (φ₂ x) (φ₃ y) = 0 := fun x y =>
    Frame.horth₂₃ _ (hφ₂ x) _ (hφ₃ y)
  let T : NormTriple Q σ :=
    { φ := ![φ₁, φ₂, φ₃]
      Q_φ := fun j x => by fin_cases j <;> simp [hQ₁, hQ₂, hQ₃]
      orth := fun j k hjk x y => by
        fin_cases j <;> fin_cases k
        · exact absurd rfl hjk
        · exact o12 x y
        · exact o13 x y
        · rw [polar_comm]; exact o12 y x
        · exact absurd rfl hjk
        · exact o23 x y
        · rw [polar_comm]; exact o13 y x
        · rw [polar_comm]; exact o23 y x
        · exact absurd rfl hjk }
  refine ⟨T.toEmbedding E.isUnitary, ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  · show T.incl x ∈ F₁.span
    rw [T.incl_apply, hx, map_zero, add_zero]
    exact F₁.span.add_mem (hφ₁ _).1 (hφ₂ _).1
  · show T.incl x ∈ F₂.span
    rw [T.incl_apply, hx]
    have : T.φ 0 0 = 0 := map_zero _
    rw [this, zero_add]
    exact F₂.span.add_mem (hφ₂ _).2 (hφ₃ _).2

theorem map_congr_of_forall {G H : Type*} [Group G] [Group H] {S : Subgroup G} {f g : G →* H}
    (h : ∀ x ∈ S, f x = g x) : S.map f = S.map g := by
  ext y
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (h x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, h x hx⟩

section Main

variable [Finite K] [FiniteDimensional K V] {p f : ℕ} [Fact p.Prime] [Finite K'] [CharP K' p]

theorem Frame.exists_hom_of_not_hasSingularVector (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K)) {F₁ F₂ : Frame Q}
    (hc : F₂.La (-1) * F₁.La (-1) = F₁.La (-1) * F₂.La (-1))
    (h : Module.finrank K ↥(F₁.span ⊓ F₂.span) = 2)
    (hs : ¬ HasSingularVector Q (F₁.span ⊓ F₂.span)) :
    ∃ θ : Su K' p f 3 →* (V ≃ₗ[K] V), Function.Injective θ ∧
      θ.range = F₁.La.range ⊔ F₂.La.range ∧
      (B12 K' p f).map θ = F₁.La.range ∧ (B23 K' p f).map θ = F₂.La.range := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have E : QuadExt K K' (unitaryInvolution K' p f) := QuadExt.of_card hK hK' hodd
  obtain ⟨W⟩ := E.isUnitary.nonempty_wittData
  obtain ⟨D, hD⟩ := exists_adapted E h2 hc h hs
  obtain ⟨D₁, hD₁, hB₁, -⟩ := hD.exists_fix_block_two E h2 W
  obtain ⟨D₂, hD₂, hB₂, hag⟩ := hD₁.exists_fix_block_zero E h2 W
  have hB₁' : (B12 K' p f).map D₂.theta = F₁.La.range := by
    rw [← hB₁]
    exact map_congr_of_forall hag
  have hB₂' : (B23 K' p f).map D₂.theta = F₂.La.range := hB₂
  have hq : p ^ f ≠ 2 := by
    intro h
    rw [hK, h] at hodd
    simp [Nat.odd_iff] at hodd
  refine ⟨D₂.theta, D₂.theta_injective, ?_, hB₁', hB₂'⟩
  rw [MonoidHom.range_eq_map, ← B12_sup_B23_eq_top hK' hq, Subgroup.map_sup, hB₁', hB₂']

variable {L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V}

omit [Algebra K K'] in
theorem exists_hom_of_lemma_6_10_unitary (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K))
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    ∃ θ : Su K' p f 3 →* (V ≃ₗ[K] V), Function.Injective θ ∧ θ.range = L₁ ⊔ L₂ ∧
      (B12 K' p f).map θ = L₁ ∧ (B23 K' p f).map θ = L₂ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have := Classical.choice (Aniso.nonempty_algebra hK hK')
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  have hdim := Frame.finrank_inf_span_eq_two h2 hc.symm (conjSubgroup_eq_of_mem_normalizer hN)
    (exists_ne_of_not_mem_centralizer hC)
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hs
  exact Frame.exists_hom_of_not_hasSingularVector hK hK' hodd hc.symm hdim hs

omit [Algebra K K'] in
theorem lemma_6_10_unitary (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (hc : i₁ * i₂ = i₂ * i₁) (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    UnitaryBlockStandardPair K' p f (L₁ ⊔ L₂) L₁ L₂ := by
  obtain ⟨θ, hinj, hrange, hU, hV⟩ :=
    exists_hom_of_lemma_6_10_unitary hK hK' hodd h₁ h₂ hc hN hC hs
  exact unitaryBlockStandardPair_of_normalized
    (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) hrange hU hV

omit [Algebra K K'] in
theorem lemma_6_10_dichotomy (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (hc : i₁ * i₂ = i₂ * i₁) (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V))) :
    PairDecomposition Q i₁ i₂ ∧
      ((HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          LinearBlockStandardPair K (L₁ ⊔ L₂) L₁ L₂) ∨
        (¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) ∧
          UnitaryBlockStandardPair K' p f (L₁ ⊔ L₂) L₁ L₂)) := by
  obtain ⟨hP, hlin⟩ := lemma_6_10 hodd h₁ h₂ hc hN hC
  by_cases hs : HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)
  · exact ⟨hP, Or.inl ⟨hs, hlin hs⟩⟩
  · exact ⟨hP, Or.inr ⟨hs, lemma_6_10_unitary hK hK' hodd h₁ h₂ hc hN hC hs⟩⟩

theorem unitaryBlockStandardPair_subgroupOf {X : Type} [Group X] {W U V : Subgroup X}
    (H : Subgroup X) (hW : W ≤ H) (h : UnitaryBlockStandardPair K' p f W U V) :
    UnitaryBlockStandardPair K' p f (W.subgroupOf H) (U.subgroupOf H) (V.subgroupOf H) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  have hθ : ∀ g, θ g ∈ H := fun g => hW (hrange ▸ ⟨g, rfl⟩)
  let θ' : Su K' p f 3 →* H := θ.codRestrict H hθ
  have hsub : ∀ S : Subgroup (Su K' p f 3), S.map θ ≤ W := fun S => by
    rintro _ ⟨g, -, rfl⟩
    exact hrange ▸ ⟨g, rfl⟩
  have hmap : ∀ (S : Subgroup (Su K' p f 3)) (T : Subgroup X), S.map θ = T →
      S.map θ' = T.subgroupOf H := fun S T hST => by
    have hTH : T ≤ H := hST ▸ (hsub S).trans hW
    refine Subgroup.map_injective (f := H.subtype) Subtype.val_injective ?_
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hTH, ← hST]
    rfl
  refine ⟨θ', c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact hmap ⊤ W (by rw [← MonoidHom.range_eq_map]; exact hrange)
  · rwa [MonoidHom.ker_codRestrict]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hmap _ _ h1, hmap _ _ h2⟩
    · exact Or.inr ⟨hmap _ _ h1, hmap _ _ h2⟩

omit [Algebra K K'] in
theorem lemma_6_10_unitary_subgroupOf (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K))
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[K] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[K] V)))
    (hs : ¬ HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂)) :
    UnitaryBlockStandardPair K' p f ((L₁ ⊔ L₂).subgroupOf (elementaryGroup Q))
      (L₁.subgroupOf (elementaryGroup Q)) (L₂.subgroupOf (elementaryGroup Q)) :=
  unitaryBlockStandardPair_subgroupOf (elementaryGroup Q)
    (sup_le h₁.le_elementaryGroup h₂.le_elementaryGroup)
    (lemma_6_10_unitary hK hK' hodd h₁ h₂ hc hN hC hs)

end Main

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
