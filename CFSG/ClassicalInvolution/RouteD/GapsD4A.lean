module

public import CFSG.ClassicalInvolution.RouteD.GapsD4ABasic
public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.WeakCT CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply det_blockMat blockMat_mul blockMat_one
  blockMat_comm)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

@[expose] def partnerEnt (m : ℕ) (μ : Fˣ) (i : Fin (m + 1)) : Fˣ :=
  if i.val = 0 then -1 else if i.val + 2 ≤ m then 1 else μ

@[expose] noncomputable def partnerDiag (m : ℕ) (μ : Fˣ) : GL (Fin (m + 1)) F :=
  diagGL (partnerEnt m μ)

@[expose] def partnerFixed (m : ℕ) (a : Fin m) : Prop :=
  a.val + 1 = m ∨ (1 ≤ a.val ∧ a.val + 3 ≤ m)

theorem exists_fixed_block_of_ne_zero {m : ℕ} (hm : 4 ≤ m) (k : Fin (m + 1)) (hk : k.val ≠ 0) :
    ∃ a : Fin m, partnerFixed m a ∧ (k = a.castSucc ∨ k = a.succ) := by
  have hkl := k.isLt
  by_cases h1 : m ≤ k.val + 1
  · refine ⟨⟨m - 1, by omega⟩, Or.inl (by show m - 1 + 1 = m; omega), ?_⟩
    by_cases h2 : k.val = m - 1
    · exact Or.inl (Fin.ext (by simpa using h2))
    · exact Or.inr (Fin.ext (by simp only [Fin.val_succ]; omega))
  · by_cases h2 : k.val + 3 ≤ m
    · exact ⟨⟨k.val, by omega⟩, Or.inr ⟨by show 1 ≤ k.val; omega, by show k.val + 3 ≤ m; omega⟩,
        Or.inl (Fin.ext (by simp))⟩
    · exact ⟨⟨m - 3, by omega⟩, Or.inr ⟨by show 1 ≤ m - 3; omega, by show m - 3 + 3 ≤ m; omega⟩,
        Or.inr (Fin.ext (by simp only [Fin.val_succ]; omega))⟩

theorem partner_pattern_of_innerDiag [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {m : ℕ} (hm : 4 ≤ m) {X : Type} [Group X]
    (θ : SL(m + 1, F) →* X) (hker : θ.ker ≤ Subgroup.center SL(m + 1, F))
    (σ : X ≃* X) (hσ : ∀ x, σ (σ x) = x)
    (g : GL (Fin (m + 1)) F) (hg : ∀ x, σ (θ x) = θ (slConjugation (m + 1) F g x))
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      σ (θ (blockSL2 F m a A)) = θ (blockSL2 F m a A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F m ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F m ⟨0, by omega⟩ A)) :
    ∃ μ : Fˣ, (μ = 1 ∨ μ = -1) ∧
      (∀ x, σ (θ x) = θ (slConjugation (m + 1) F (partnerDiag m μ) x)) ∧
      ((μ = 1) ↔ ∀ A : SL(2, F),
        σ (θ (blockSL2 F m ⟨m - 2, by omega⟩ A)) = θ (blockSL2 F m ⟨m - 2, by omega⟩ A)) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hPn : Group.IsPerfect SL(m + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hfixed : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      slConjugation (m + 1) F g (blockSL2 F m a A) = blockSL2 F m a A := by
    intro a ha A
    have := hom_eq_of_central_ker θ hker (L := SL(2, F))
      ((slConjugation (m + 1) F g).toMonoidHom.comp (blockSL2 F m a)) (blockSL2 F m a)
      (fun A => by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hg, hfix a ha])
    exact DFunLike.congr_fun this A
  have hblk : ∀ a : Fin m, partnerFixed m a →
      ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.castSucc a.castSucc =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.succ a.succ ∧
      (∀ i, i ≠ a.castSucc → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i a.castSucc = 0) ∧
      (∀ i, i ≠ a.succ → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i a.succ = 0) ∧
      (∀ j, j ≠ a.castSucc → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.castSucc j = 0) ∧
      (∀ j, j ≠ a.succ → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.succ j = 0)) := by
    intro a ha
    obtain ⟨c1, c2⟩ := commute_of_fixes_block g a (hfixed a ha)
    exact block_of_commute_single _ c1 c2
  have hoff : ∀ i j : Fin (m + 1), i ≠ j → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
    intro i j hij
    by_cases hj : j.val = 0
    · have hi : i.val ≠ 0 := fun hi => hij (Fin.ext (by omega))
      obtain ⟨a, ha, hia | hia⟩ := exists_fixed_block_of_ne_zero hm i hi
      · subst hia
        exact (hblk a ha).2.2.2.1 j (Ne.symm hij)
      · subst hia
        exact (hblk a ha).2.2.2.2 j (Ne.symm hij)
    · obtain ⟨a, ha, hja | hja⟩ := exists_fixed_block_of_ne_zero hm j hj
      · subst hja
        exact (hblk a ha).2.1 i hij
      · subst hja
        exact (hblk a ha).2.2.1 i hij
  obtain ⟨u, rfl⟩ := exists_diagGL_of_offdiag_zero g hoff
  have hu : ∀ a : Fin m, partnerFixed m a → u a.castSucc = u a.succ := fun a ha => by
    have := (hblk a ha).1
    rw [coe_diagGL, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
    exact Units.ext this
  have hmid : ∀ k : ℕ, ∀ hk : k < m + 1, 1 ≤ k → k + 2 ≤ m → u ⟨k, hk⟩ = u ⟨1, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _ h; omega
    | succ k ih =>
      intro hk h1 h2
      by_cases hk0 : k = 0
      · subst hk0; rfl
      · have := hu ⟨k, by omega⟩ (Or.inr ⟨by show 1 ≤ k; omega, by show k + 3 ≤ m; omega⟩)
        have e1 : (⟨k, by omega⟩ : Fin m).castSucc = ⟨k, by omega⟩ := rfl
        have e2 : (⟨k, by omega⟩ : Fin m).succ = ⟨k + 1, hk⟩ := rfl
        rw [e1, e2] at this
        rw [← this]
        exact ih (by omega) (by omega) (by omega)
  have hend : u ⟨m - 1, by omega⟩ = u ⟨m, by omega⟩ := by
    have := hu ⟨m - 1, by omega⟩ (Or.inl (by show m - 1 + 1 = m; omega))
    have e1 : (⟨m - 1, by omega⟩ : Fin m).castSucc = ⟨m - 1, by omega⟩ := rfl
    have e2 : (⟨m - 1, by omega⟩ : Fin m).succ = ⟨m, by omega⟩ := by
      apply Fin.ext; simp only [Fin.val_succ]; omega
    rw [e1, e2] at this
    exact this
  have hsq : ∀ x : SL(m + 1, F), slConjugation (m + 1) F (diagGL u)
      (slConjugation (m + 1) F (diagGL u) x) = x := by
    have := hom_eq_of_central_ker θ hker (L := SL(m + 1, F))
      ((slConjugation (m + 1) F (diagGL u)).toMonoidHom.comp
        (slConjugation (m + 1) F (diagGL u)).toMonoidHom) (MonoidHom.id _)
      (fun x => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [← hg, ← hg, hσ])
    intro x
    exact DFunLike.congr_fun this x
  have hsqe : ∀ i j : Fin (m + 1), (u i : F) ^ 2 = (u j : F) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · exact sq_eq_of_conj_sq u hij hsq
  have hz0 : u ⟨0, by omega⟩ = -u ⟨1, by omega⟩ := by
    have hne : u ⟨0, by omega⟩ ≠ u ⟨1, by omega⟩ := by
      intro h
      obtain ⟨A, hA⟩ := hmove
      apply hA
      rw [hg, slConjugation_diagGL_blockSL2 u ⟨0, by omega⟩ h A]
    have h1 := hsqe ⟨0, by omega⟩ ⟨1, by omega⟩
    have h3 : ((u ⟨0, by omega⟩ : Fˣ) : F) = ((u ⟨1, by omega⟩ : Fˣ) : F) ∨
        ((u ⟨0, by omega⟩ : Fˣ) : F) = -((u ⟨1, by omega⟩ : Fˣ) : F) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp h1
    rcases h3 with h3 | h3
    · exact absurd (Units.ext h3) hne
    · exact Units.ext (by rw [Units.val_neg]; exact h3)
  set μ : Fˣ := u ⟨m - 1, by omega⟩ * (u ⟨1, by omega⟩)⁻¹ with hμdef
  have hμ : μ = 1 ∨ μ = -1 := by
    have h1 := hsqe ⟨m - 1, by omega⟩ ⟨1, by omega⟩
    have h1' : (μ : F) * (μ : F) = 1 := by
      have hu1 : ((u ⟨1, by omega⟩ : Fˣ) : F) ≠ 0 := (u _).ne_zero
      rw [hμdef, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination h1
    rcases mul_self_eq_one_iff.mp h1' with h3 | h3
    · exact Or.inl (Units.ext h3)
    · exact Or.inr (Units.ext (by rw [Units.val_neg]; exact h3))
  have hentry : ∀ i : Fin (m + 1), u i = u ⟨1, by omega⟩ * partnerEnt m μ i := by
    intro i
    by_cases h0 : i.val = 0
    · simp only [partnerEnt, h0, ↓reduceIte]
      have : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [this, hz0, mul_neg, mul_one]
    · by_cases hmd : i.val + 2 ≤ m
      · simp only [partnerEnt, h0, hmd, ↓reduceIte, mul_one]
        exact hmid i.val i.isLt (by omega) hmd
      · simp only [partnerEnt, h0, hmd, ↓reduceIte]
        have hmem : i.val = m - 1 ∨ i.val = m := by have := i.isLt; omega
        have hi : u i = u ⟨m - 1, by omega⟩ := by
          rcases hmem with h | h
          · rw [show i = ⟨m - 1, by omega⟩ from Fin.ext h]
          · rw [show i = ⟨m, by omega⟩ from Fin.ext h, hend]
        rw [hi, hμdef, mul_left_comm, mul_inv_cancel, mul_one]
  have hconj : ∀ x, slConjugation (m + 1) F (diagGL u) x =
      slConjugation (m + 1) F (partnerDiag m μ) x := fun x =>
    slConjugation_diagGL_congr u _ (u ⟨1, by omega⟩) hentry x
  have hpd1 : partnerEnt m μ ⟨m - 2, by omega⟩ = 1 := by
    have h0 : ¬ (⟨m - 2, by omega⟩ : Fin (m + 1)).val = 0 := by simp only; omega
    have h1 : (⟨m - 2, by omega⟩ : Fin (m + 1)).val + 2 ≤ m := by simp only; omega
    simp only [partnerEnt, h0, h1, ↓reduceIte]
  have hpd2 : partnerEnt m μ ⟨m - 1, by omega⟩ = μ := by
    have h0 : ¬ (⟨m - 1, by omega⟩ : Fin (m + 1)).val = 0 := by simp only; omega
    have h1 : ¬ (⟨m - 1, by omega⟩ : Fin (m + 1)).val + 2 ≤ m := by simp only; omega
    simp only [partnerEnt, h0, h1, ↓reduceIte]
  refine ⟨μ, hμ, fun x => by rw [hg, hconj], ?_⟩
  have e1 : (⟨m - 2, by omega⟩ : Fin m).castSucc = ⟨m - 2, by omega⟩ := rfl
  have e2 : (⟨m - 2, by omega⟩ : Fin m).succ = ⟨m - 1, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_succ]; omega
  constructor
  · intro h1 A
    have hd : partnerEnt m μ (⟨m - 2, by omega⟩ : Fin m).castSucc =
        partnerEnt m μ (⟨m - 2, by omega⟩ : Fin m).succ := by
      rw [e1, e2, hpd1, hpd2, h1]
    rw [hg, hconj]
    exact congrArg θ (slConjugation_diagGL_blockSL2 _ ⟨m - 2, by omega⟩ hd A)
  · intro h
    have hfx := hom_eq_of_central_ker θ hker (L := SL(2, F))
      ((slConjugation (m + 1) F (partnerDiag m μ)).toMonoidHom.comp
        (blockSL2 F m ⟨m - 2, by omega⟩)) (blockSL2 F m ⟨m - 2, by omega⟩)
      (fun A => by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [← hconj, ← hg, h A])
    have h3 := DFunLike.congr_fun hfx
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h3
    rw [blockSL2_transvection_up] at h3
    have h4 := diag_eq_of_conj_fixed (partnerEnt m μ) (Fin.castSucc_lt_succ.ne) h3
    rw [e1, e2, hpd1, hpd2] at h4
    exact h4.symm

@[expose] def LinearAutClassification (F : Type) [Field F] (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (θ : SL(n, F) →* X), Function.Surjective θ →
    θ.ker ≤ Subgroup.center SL(n, F) → ∀ σ : X ≃* X,
    ∃ (α : SL(n, F) →* SL(n, F)) (g : GL (Fin n) F) (φ : F ≃+* F) (ε : Bool),
      (∀ x, θ (α x) = σ (θ x)) ∧
      ∀ x, ((α x : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
        (g : Matrix (Fin n) (Fin n) F) *
          φ.mapMatrix (if ε then (((x⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F))ᵀ
            else (x : Matrix (Fin n) (Fin n) F)) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)

theorem innerDiag_of_partner_blocks [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {m : ℕ} (hm : 3 ≤ m) (hcl : LinearAutClassification F (m + 1))
    {X : Type} [Group X] (θ : SL(m + 1, F) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center SL(m + 1, F)) (σ : X ≃* X) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      σ (θ (blockSL2 F m a A)) = θ (blockSL2 F m a A))
    (hmove : ∃ A : SL(2, F), σ (θ (blockSL2 F m ⟨0, by omega⟩ A)) ≠
      θ (blockSL2 F m ⟨0, by omega⟩ A)) :
    ∃ g : GL (Fin (m + 1)) F, ∀ x, σ (θ x) = θ (slConjugation (m + 1) F g x) := by
  have h4 : 4 ≤ Nat.card F := by omega
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard hodd
  have hP2 : Group.IsPerfect SL(2, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hPn : Group.IsPerfect SL(m + 1, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  obtain ⟨α, g, φ, ε, hαθ, hαmat⟩ := hcl X θ hθ hker σ
  have hαfix : ∀ a : Fin m, partnerFixed m a → ∀ A : SL(2, F),
      α (blockSL2 F m a A) = blockSL2 F m a A := by
    intro a ha A
    have := hom_eq_of_central_ker θ hker (L := SL(2, F)) (α.comp (blockSL2 F m a))
      (blockSL2 F m a) (fun A => by rw [MonoidHom.comp_apply, hαθ, hfix a ha])
    exact DFunLike.congr_fun this A
  have hup : ∀ a : Fin m, partnerFixed m a → ∀ c : F,
      α (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ.ne : a.castSucc ≠ a.succ) c) =
        Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ.ne : a.castSucc ≠ a.succ) c := by
    intro a ha c
    have := hαfix a ha (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
    rwa [blockSL2_transvection_up] at this
  have hdown : ∀ a : Fin m, partnerFixed m a → ∀ c : F,
      α (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ.ne' : a.succ ≠ a.castSucc) c) =
        Matrix.SpecialLinearGroup.transvection (Fin.castSucc_lt_succ.ne' : a.succ ≠ a.castSucc) c := by
    intro a ha c
    have := hαfix a ha (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c)
    rwa [blockSL2_transvection_down] at this
  have ha₀ : partnerFixed m ⟨m - 1, by omega⟩ := Or.inl (by show m - 1 + 1 = m; omega)
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte] at hαmat
    obtain ⟨hφ, -⟩ := fixed_transvection_false α g φ hαmat _ (hup _ ha₀)
    refine ⟨g, fun x => ?_⟩
    rw [← hαθ]
    congr 1
    refine Subtype.ext ?_
    rw [hαmat x, slConjugation_matrix]
    congr 2
    ext a b
    simp [RingEquiv.mapMatrix_apply, hφ]
  · exfalso
    simp only [↓reduceIte] at hαmat
    obtain ⟨hφ, -⟩ := fixed_transvection_true α g φ hαmat _ (hup _ ha₀)
    have hαmat' : ∀ x, ((α x : SL(m + 1, F)) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (((x⁻¹ : SL(m + 1, F)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F))ᵀ *
          ((g⁻¹ : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
      intro x
      rw [hαmat x]
      congr 2
      ext a b
      simp [RingEquiv.mapMatrix_apply, hφ]
    have hdet : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).mp g.isUnit).ne_zero
    have hgraph : ∀ a : Fin m, partnerFixed m a →
        ((∀ k, k ≠ a.castSucc → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k a.succ = 0) ∧
        (∀ l, l ≠ a.castSucc → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.succ l = 0) ∧
        (∀ k, k ≠ a.succ → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k a.castSucc = 0) ∧
        (∀ l, l ≠ a.succ → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.castSucc l = 0) ∧
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.castSucc a.succ =
          -(g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a.succ a.castSucc) := by
      intro a ha
      obtain ⟨-, h1⟩ := fixed_transvection_true α g φ hαmat _ (hup a ha)
      obtain ⟨-, h2⟩ := fixed_transvection_true α g φ hαmat _ (hdown a ha)
      exact block_of_graph_commute _ h1 h2
    by_cases hm5 : 5 ≤ m
    ·
      have hb1 : partnerFixed m ⟨1, by omega⟩ := Or.inr ⟨le_refl _, by show 1 + 3 ≤ m; omega⟩
      have hb2 : partnerFixed m ⟨2, by omega⟩ := Or.inr ⟨by show 1 ≤ 2; omega, by show 2 + 3 ≤ m; omega⟩
      have r1 := (hgraph _ hb1).2.1
      have r2 := (hgraph _ hb2).2.2.2.1
      apply hdet
      refine Matrix.det_eq_zero_of_row_eq_zero (⟨2, by omega⟩ : Fin (m + 1)) fun l => ?_
      by_cases hl : l = ⟨1, by omega⟩
      · refine r2 l ?_
        intro h
        rw [hl] at h
        simp [Fin.ext_iff] at h
      · exact r1 l hl
    · have hsq : ∀ x, α (α x) = x := by
        intro x
        have := hom_eq_of_central_ker θ hker (L := SL(m + 1, F)) (α.comp α) (MonoidHom.id _)
          (fun x => by rw [MonoidHom.comp_apply, hαθ, hαθ, hσ]; rfl)
        exact DFunLike.congr_fun this x
      obtain ⟨c, hgc⟩ := exists_eq_smul_transpose (by omega) α g hαmat' hsq
      by_cases hm4 : m = 4
      ·
        subst hm4
        have hb : partnerFixed 4 ⟨1, by omega⟩ := Or.inr ⟨le_refl _, by show 1 + 3 ≤ 4; omega⟩
        obtain ⟨-, -, hcol, -, hij⟩ := hgraph _ hb
        have hskew := eq_neg_transpose_of_graph_block g c hgc hcol hij
        apply hdet
        have h1 := congrArg Matrix.det hskew
        rw [Matrix.det_neg, Matrix.det_transpose] at h1
        simp only [Fintype.card_fin] at h1
        have h6 : (2 : F) * (g : Matrix (Fin (4 + 1)) (Fin (4 + 1)) F).det = 0 := by
          linear_combination h1
        rcases mul_eq_zero.mp h6 with h7 | h7
        · exact absurd h7 h2
        · exact h7
      ·
        have hm3 : m = 3 := by omega
        subst hm3
        have hb : partnerFixed 3 ⟨2, by omega⟩ := Or.inl (by show 2 + 1 = 3; omega)
        obtain ⟨ha1, ha2, ha3, ha4, hij⟩ := hgraph _ hb
        have e2 : (⟨2, by omega⟩ : Fin 3).castSucc = (2 : Fin (3 + 1)) := rfl
        have e3 : (⟨2, by omega⟩ : Fin 3).succ = (3 : Fin (3 + 1)) := rfl
        rw [e2, e3] at ha1 ha2 ha3 ha4 hij
        have hskew := eq_neg_transpose_of_graph_block g c hgc ha3 hij
        have hs : ∀ k l, (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) k l =
            -(g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) l k := fun k l => by
          have := congrFun (congrFun hskew k) l
          simpa using this
        have hdiag : ∀ k, (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) k k = 0 := fun k => by
          have h1 := hs k k
          have h3 : (2 : F) * (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) F) k k = 0 := by
            linear_combination h1
          exact (mul_eq_zero.mp h3).resolve_left h2
        have hkey : ∀ A : SL(2, F), α (blockSL2 F 3 ⟨0, by omega⟩ A) =
            blockSL2 F 3 ⟨0, by omega⟩ A := by
          intro A
          refine Subtype.ext ?_
          rw [hαmat' (blockSL2 F 3 ⟨0, by omega⟩ A), ← map_inv]
          have hid := skew_block_identity (g : Matrix (Fin 4) (Fin 4) F)
            (ha3 0 (by decide)) (ha1 0 (by decide)) (ha3 1 (by decide)) (ha1 1 (by decide))
            (ha4 0 (by decide)) (ha4 1 (by decide)) (ha2 0 (by decide)) (ha2 1 (by decide))
            (hdiag 0) (hdiag 1) (hs 1 0) A
          show (g : Matrix (Fin 4) (Fin 4) F) * (blockMat 4 0
            ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F))ᵀ *
              ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = blockMat 4 0 (A : Matrix (Fin 2) (Fin 2) F)
          rw [hid, Matrix.mul_assoc]
          have := Units.mul_inv g
          rw [this, Matrix.mul_one]
        obtain ⟨A, hA⟩ := hmove
        exact hA (by rw [← hαθ, hkey A])

end CFSG.ClassicalInvolution.RouteD.Gaps
