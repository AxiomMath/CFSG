module

public import CFSG.ClassicalInvolution.WeakCT.Tree
public import CFSG.ClassicalInvolution.WeakCT.SignedLevis

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F]

theorem blk_zero_tv01 (c : F) : blk F 0 (tv 0 1 c) = tv 0 1 c := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  show ((blockSL F 3 2 0 (by omega) (tv 0 1 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_blockSL_three_zero, cm_tv01]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tv01_eq_sl2Upper, coe_sl2Upper]

theorem blk_zero_tv10 (c : F) : blk F 0 (tv 1 0 c) = tv 1 0 c := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  show ((blockSL F 3 2 0 (by omega) (tv 1 0 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_blockSL_three_zero, cm_tv10]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tv10_eq_sl2Lower, coe_sl2Lower]

theorem blk_one_tv01 (c : F) : blk F 1 (tv 0 1 c) = tv 1 2 c := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  show ((blockSL F 3 2 1 (by omega) (tv 0 1 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_blockSL_three_one, cm_tv12]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tv01_eq_sl2Upper, coe_sl2Upper]

theorem blk_one_tv10 (c : F) : blk F 1 (tv 1 0 c) = tv 2 1 c := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  show ((blockSL F 3 2 1 (by omega) (tv 1 0 c) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = _
  rw [coe_blockSL_three_one, cm_tv21]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tv10_eq_sl2Lower, coe_sl2Lower]

theorem tv_zero_one_one_ne_one : (tv 0 1 (1 : F) : SL(2, F)) ≠ 1 := by
  intro h
  have h' := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [tv01_eq_sl2Upper, coe_sl2Upper] at h'

theorem range_le_of_tv {H : Type*} [Group H] (ρ : SL(2, F) →* H) (T : Subgroup H)
    (hu : ∀ c, ρ (tv 0 1 c) ∈ T) (hv : ∀ c, ρ (tv 1 0 c) ∈ T) : ρ.range ≤ T := by
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c}) := by
    rw [closure_tv_two]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem y hy => rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> [exact hu c; exact hv c]
  | one => rw [map_one]; exact one_mem _
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  | inv y _ hy => rw [map_inv]; exact inv_mem hy

theorem map_blk {F' : Type} [Field F'] (e : F →+* F') (s : Fin 2) (A : SL(2, F)) :
    Matrix.SpecialLinearGroup.map e (blk F s A) = blk F' s (Matrix.SpecialLinearGroup.map e A) := by
  fin_cases s
  · apply Subtype.ext
    show e.mapMatrix ((blockSL F 3 2 0 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((blockSL F' 3 2 0 (by omega) (Matrix.SpecialLinearGroup.map e A) : SL(3, F')) :
        Matrix (Fin 3) (Fin 3) F')
    rw [coe_blockSL_three_zero, coe_blockSL_three_zero]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  · apply Subtype.ext
    show e.mapMatrix ((blockSL F 3 2 1 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((blockSL F' 3 2 1 (by omega) (Matrix.SpecialLinearGroup.map e A) : SL(3, F')) :
        Matrix (Fin 3) (Fin 3) F')
    rw [coe_blockSL_three_one, coe_blockSL_three_one]
    ext a b
    fin_cases a <;> fin_cases b <;> simp

theorem map_map_symm {F' : Type} [Field F'] {m : ℕ} (e : F ≃+* F') (A : SL(m, F)) :
    Matrix.SpecialLinearGroup.map e.symm.toRingHom (Matrix.SpecialLinearGroup.map e.toRingHom A) =
      A := by
  apply Subtype.ext
  ext i j
  simp

theorem map_symm_map {F' : Type} [Field F'] {m : ℕ} (e : F ≃+* F') (B : SL(m, F')) :
    Matrix.SpecialLinearGroup.map e.toRingHom (Matrix.SpecialLinearGroup.map e.symm.toRingHom B) =
      B := by
  apply Subtype.ext
  ext i j
  simp

end Blocks

section Recognition

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_of_frame {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  classical
  have hρU : ∀ k c, ρ k (tv 0 1 c) ∈ U k ∧ ρ k (tv 1 0 c) ∈ U k := fun k c => by
    rw [← (hρ k).2]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  have hfr : SimplyLacedFrame D F adj (fun k c => ρ k (tv 0 1 c)) (fun k c => ρ k (tv 1 0 c)) := by
    refine ⟨fun i j h => ?_, fun k => ⟨ρ k, fun c => ⟨rfl, rfl⟩⟩, fun i j hne h1 h2 c d => ?_⟩
    · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j h
      refine ⟨ψ, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
      · show ψ (tv 0 1 c) = ρ i (tv 0 1 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv01]
      · show ψ (tv 1 0 c) = ρ i (tv 1 0 c)
        rw [← hψ0, MonoidHom.comp_apply, blk_zero_tv10]
      · show ψ (tv 1 2 c) = ρ j (tv 0 1 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv01]
      · show ψ (tv 2 1 c) = ρ j (tv 1 0 c)
        rw [← hψ1, MonoidHom.comp_apply, blk_one_tv10]
    · have hc := hcomm i j hne h1 h2
      exact ⟨hc _ (hρU i c).1 _ (hρU j d).1, hc _ (hρU i c).1 _ (hρU j d).2,
        hc _ (hρU i c).2 _ (hρU j d).1, hc _ (hρU i c).2 _ (hρU j d).2⟩
  have hgen' : Subgroup.closure (⋃ k, Set.range (fun c => ρ k (tv 0 1 c)) ∪
      Set.range (fun c => ρ k (tv 1 0 c))) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup_le fun k => ?_
    rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inl ⟨c, rfl⟩⟩)
    · exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, Or.inr ⟨c, rfl⟩⟩)
  have hnt : ∃ k c, ρ k (tv 0 1 c) ≠ 1 := ⟨k₀, 1, fun h =>
    tv_zero_one_one_ne_one ((hρ k₀).1 (h.trans (map_one _).symm))⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen' hnt
  refine ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, fun k => ?_⟩
  have hk : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨single_mem_roots k, neg_mem_roots (single_mem_roots k)⟩
  rw [CurtisTits.rankOne, Subgroup.map_sup]
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hk k).1 g hg
      rw [hΨu]
      exact (hρU k c).1
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ (hk k).2 g hg
      rw [hΨv]
      exact (hρU k c).2
  · rw [← (hρ k).2]
    refine range_le_of_tv (ρ k) _ (fun c => ?_) (fun c => ?_)
    · refine Subgroup.mem_sup_left ⟨x (sroot k) c, hD.mem _ (hk k).1 c, ?_⟩
      exact hΨu k c
    · refine Subgroup.mem_sup_right ⟨x (-sroot k) c, hD.mem _ (hk k).2 c, ?_⟩
      exact hΨv k c

theorem weakCT_simplyLaced [Finite F] {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (hF : 4 ≤ Nat.card F)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨ρ, hρ, hψ⟩ := exists_frame_of_tree hF hT hroot hcomm hpair
  exact weakCT_of_frame hCT hL hD k₀ hgen hcomm hρ hψ

theorem weakCT_simplyLaced_of_equiv {F₀ : Type} [Field F₀] [Finite F₀] (e : F₀ ≃+* F)
    {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (hF : 4 ≤ Nat.card F₀)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F₀ W (U i) (U j)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨ρ, hρ, hψ⟩ := exists_frame_of_tree hF hT hroot hcomm hpair
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  refine weakCT_of_frame hCT hL hD k₀ hgen hcomm (ρ := fun k => (ρ k).comp φ₂)
    (fun k => ⟨(hρ k).1.comp hφ₂inj, ?_⟩) (fun i j hij => ?_)
  · rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
    refine ⟨ψ.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 1 A)

theorem weakCT_of_chevalleyExtras_of_equiv [Finite F] {F₀ : Type} [Field F₀] [Finite F₀]
    (e : F₀ ≃+* F) {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hE : Steinberg.ChevalleyExtras D F x C O) (hdiv : D.divisible = ∅)
    (hC : ∀ α ∈ D.roots, ∀ β ∈ D.roots, α + β ∈ D.roots → β - α ∉ D.roots →
      (C α β (1, 1)).natAbs = 1)
    (hasymm : ∀ i j, adj i j → ¬ adj j i)
    (hadj : ∀ i j, adj i j → D.cartan i j = -1 ∧ D.cartan j i = -1)
    (hnadj : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → D.cartan i j = 0 ∧ D.cartan j i = 0)
    (hnb : ∀ i j, adj i j → ∃ k, k ≠ i ∧ k ≠ j ∧
      ((adj j k ∨ adj k j) ∧ ¬ adj i k ∧ ¬ adj k i ∨
        (adj i k ∨ adj k i) ∧ ¬ adj j k ∧ ¬ adj k j))
    {H : Fin D.rank → Subgroup K} (hind : iSupIndep H)
    (hsq : ∀ k, Steinberg.weylElement x k 1 ^ 2 ∈ H k)
    {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hF : 4 ≤ Nat.card F₀)
    {par : Fin D.rank → Fin D.rank} {dep : Fin D.rank → ℕ} {k₀ : Fin D.rank}
    (hT : RootedTree adj par dep k₀) (hroot : ∃ c, adj k₀ c ∨ adj c k₀)
    {X : Type} [Group X] {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F₀ W (U i) (U j)) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE hdiv hC hasymm hadj hnadj hnb hind hsq
  exact weakCT_simplyLaced_of_equiv e hCT hL hD hF hT hroot hgen hcomm hpair

end Recognition

end CFSG.ClassicalInvolution.WeakCT
