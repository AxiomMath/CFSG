module

public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Assembly.LowTwoRank Matrix
open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_coe glCongr_statedScalars statedProjCongr det_map_ringEquiv)

export CFSG.Adapters.RankTwoModelTransports (glCongr_statedSL glCongr_statedSp)

section Omega

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem glCongr_mulVec (φ : K ≃+* L) (A : GL ι K) (v : ι → K) :
    ((glCongr φ A : GL ι L) : Matrix ι ι L) *ᵥ (φ ∘ v) = φ ∘ ((A : Matrix ι ι K) *ᵥ v) := by
  funext i
  rw [glCongr_coe, Function.comp_apply]
  exact (RingHom.map_mulVec (φ : K →+* L) (A : Matrix ι ι K) v i).symm

variable {QK : (ι → K) → K} {QL : (ι → L) → L}

theorem glCongr_preserves_iff (φ : K ≃+* L) (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) (A : GL ι K) :
    (∀ w, QL (((glCongr φ A : GL ι L) : Matrix ι ι L) *ᵥ w) = QL w) ↔
      ∀ v, QK ((A : Matrix ι ι K) *ᵥ v) = QK v := by
  constructor
  · intro h v
    have h' := h (φ ∘ v)
    rw [glCongr_mulVec, hQ, hQ] at h'
    exact φ.injective h'
  · intro h w
    obtain ⟨v, rfl⟩ : ∃ v, φ ∘ v = w := ⟨φ.symm ∘ w, funext fun i => φ.apply_symm_apply _⟩
    rw [glCongr_mulVec, hQ, hQ, h]

theorem map_closure_preserving (φ : K ≃+* L) (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) :
    (Subgroup.closure {A : GL ι K | ∀ v, QK ((A : Matrix ι ι K) *ᵥ v) = QK v}).map
        (glCongr φ).toMonoidHom =
      Subgroup.closure {B : GL ι L | ∀ w, QL ((B : Matrix ι ι L) *ᵥ w) = QL w} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (glCongr_preserves_iff φ hQ A).2 hA
  · intro hB
    refine ⟨(glCongr φ).symm B, (glCongr_preserves_iff φ hQ _).1 ?_,
      (glCongr φ).apply_symm_apply B⟩
    rwa [MulEquiv.apply_symm_apply]

theorem map_statedOmega (φ : K ≃+* L) (hQ : ∀ v, QL (φ ∘ v) = φ (QK v)) :
    (StatedOmega QK).map (glCongr φ).toMonoidHom = StatedOmega QL := by
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, map_closure_preserving φ hQ]

theorem map_statedOmega_conj {Q Q' : (ι → K) → K} (g : GL ι K)
    (hg : ∀ v, Q' ((g : Matrix ι ι K) *ᵥ v) = Q v) :
    (StatedOmega Q).map (MulAut.conj g).toMonoidHom = StatedOmega Q' := by
  have hgi : ∀ w, (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hgi' : ∀ v, ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hiff : ∀ A : GL ι K, (∀ w, Q' ((((MulAut.conj g) A : GL ι K) : Matrix ι ι K) *ᵥ w) = Q' w) ↔
      ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v := by
    intro A
    have hc : ∀ w, ((((MulAut.conj g) A : GL ι K) : Matrix ι ι K) *ᵥ w) =
        (g : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)) := by
      intro w
      simp only [MulAut.conj_apply, Units.val_mul, ← Matrix.mulVec_mulVec]
    constructor
    · intro h v
      have h' := h ((g : Matrix ι ι K) *ᵥ v)
      rw [hc, hgi', hg, hg] at h'
      exact h'
    · intro h w
      rw [hc, hg, h]
      conv_rhs => rw [← hgi w]
      rw [hg]
  rw [StatedOmega, StatedOmega, Subgroup.map_commutator, MonoidHom.map_closure]
  have hset : (MulAut.conj g).toMonoidHom ''
      {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} =
      {B : GL ι K | ∀ w, Q' ((B : Matrix ι ι K) *ᵥ w) = Q' w} := by
    ext B
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact (hiff A).2 hA
    · intro hB
      refine ⟨(MulAut.conj g).symm B, ?_, (MulAut.conj g).apply_symm_apply B⟩
      exact (hiff ((MulAut.conj g).symm B)).1 (by rw [MulEquiv.apply_symm_apply]; exact hB)
  rw [hset]

theorem statedQuadOdd_comp (φ : K ≃+* L) {n : ℕ} (v : Fin n ⊕ Fin n ⊕ Unit → K) :
    StatedQuadOdd n L (φ ∘ v) = φ (StatedQuadOdd n K v) := by
  simp only [StatedQuadOdd, Function.comp_apply, map_add, map_mul, map_pow, map_sum]

theorem statedQuadPlus_comp (φ : K ≃+* L) {n : ℕ} (v : Fin n ⊕ Fin n → K) :
    StatedQuadPlus n L (φ ∘ v) = φ (StatedQuadPlus n K v) := by
  simp only [StatedQuadPlus, Function.comp_apply, map_mul, map_sum]

theorem statedQuadMinus_comp (φ : K ≃+* L) {n : ℕ} {b c : K} {b' c' : L} (hb : φ b = b')
    (hc : φ c = c') (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n L b' c' (φ ∘ v) = φ (StatedQuadMinus n K b c v) := by
  subst hb hc
  simp only [StatedQuadMinus, Function.comp_apply, map_add, map_mul, map_pow, map_sum]

end Omega

section Minus

variable {K : Type*} [Field K]

theorem exists_sq_eq_disc [Fintype K] (h2 : (2 : K) ≠ 0) {b₁ c₁ b₂ c₂ : K}
    (h₁ : ∀ s : K, s ^ 2 + b₁ * s + c₁ ≠ 0) (h₂ : ∀ s : K, s ^ 2 + b₂ * s + c₂ ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ (b₂ ^ 2 - 4 * c₂) * s ^ 2 = b₁ ^ 2 - 4 * c₁ := by
  classical
  have key : ∀ {b c : K}, (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ¬ IsSquare (b ^ 2 - 4 * c) := by
    rintro b c h ⟨δ, hδ⟩
    refine h ((-b + δ) / 2) ?_
    field_simp
    linear_combination -hδ
  have hd₁ := key h₁
  have hd₂ := key h₂
  have hq1 : quadraticChar K (b₁ ^ 2 - 4 * c₁) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.2 hd₁
  have hq2 : quadraticChar K (b₂ ^ 2 - 4 * c₂) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.2 hd₂
  have hz2 : b₂ ^ 2 - 4 * c₂ ≠ 0 := fun h => hd₂ (by rw [h]; exact ⟨0, by simp⟩)
  have hz1 : b₁ ^ 2 - 4 * c₁ ≠ 0 := fun h => hd₁ (by rw [h]; exact ⟨0, by simp⟩)
  have hsq : IsSquare ((b₁ ^ 2 - 4 * c₁) * (b₂ ^ 2 - 4 * c₂)) := by
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hz1 hz2), map_mul, hq1, hq2]
    norm_num
  obtain ⟨δ, hδ⟩ := hsq
  refine ⟨δ / (b₂ ^ 2 - 4 * c₂), ?_, ?_⟩
  · intro h
    have : δ = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hz2
    rw [this] at hδ
    exact mul_ne_zero hz1 hz2 (by simpa using hδ)
  · field_simp
    linear_combination -hδ

@[expose] def QuadM (ι₀ : Type) [Fintype ι₀] (b c : K) (v : ι₀ ⊕ ι₀ ⊕ Fin 2 → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr 0)) ^ 2 +
    b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2

theorem exists_isometry_quadM {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (h2 : (2 : K) ≠ 0)
    {b₁ c₁ b₂ c₂ s : K} (hs0 : s ≠ 0) (hs : (b₂ ^ 2 - 4 * c₂) * s ^ 2 = b₁ ^ 2 - 4 * c₁) :
    ∃ g : GL (ι₀ ⊕ ι₀ ⊕ Fin 2) K,
      ∀ v, QuadM ι₀ b₂ c₂ ((g : Matrix _ _ K) *ᵥ v) = QuadM ι₀ b₁ c₁ v := by
  classical
  set α : K := (b₁ - b₂ * s) / 2 with hα
  let u : ι₀ ⊕ ι₀ ⊕ Fin 2 := .inr (.inr 0)
  let w : ι₀ ⊕ ι₀ ⊕ Fin 2 := .inr (.inr 1)
  have hne : u ≠ w := by simp [u, w]
  let D : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K :=
    Matrix.diagonal fun i => if i = w then s else 1
  let T : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K := Matrix.transvection u w (α / s)
  have hdetD : D.det = s := by
    simp [D, Matrix.det_diagonal]
  have hdetT : T.det = 1 := Matrix.det_transvection_of_ne u w hne _
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (T * D)
    (by rw [Matrix.det_mul, hdetD, hdetT, one_mul]; exact hs0), ?_⟩
  intro v
  have hD : ∀ (x : ι₀ ⊕ ι₀ ⊕ Fin 2 → K) i, (D *ᵥ x) i = (if i = w then s else 1) * x i := by
    intro x i
    simp [D, Matrix.mulVec_diagonal]
  have hT : ∀ (x : ι₀ ⊕ ι₀ ⊕ Fin 2 → K) i,
      (T *ᵥ x) i = x i + if i = u then (α / s) * x w else 0 := by
    intro x i
    simp [T, Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]
  have hg : ∀ i, (((Matrix.GeneralLinearGroup.mkOfDetNeZero (T * D)
      (by rw [Matrix.det_mul, hdetD, hdetT, one_mul]; exact hs0) : GL _ K) : Matrix _ _ K) *ᵥ v)
        i = (if i = w then s else 1) * v i + if i = u then (α / s) * (s * v w) else 0 := by
    intro i
    show ((T * D) *ᵥ v) i = _
    rw [← Matrix.mulVec_mulVec, hT, hD, hD]
    simp [w, u]
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero (T * D)
    (by rw [Matrix.det_mul, hdetD, hdetT, one_mul]; exact hs0) with hgdef
  have hu0 : ((g : Matrix _ _ K) *ᵥ v) u = v u + α * v w := by
    rw [hg u]
    have : u ≠ w := hne
    simp only [this, ite_false, one_mul, ite_true]
    field_simp
  have hw0 : ((g : Matrix _ _ K) *ᵥ v) w = s * v w := by
    rw [hg w]
    have : w ≠ u := hne.symm
    simp [this]
  have hinl : ∀ i : ι₀,
      ((g : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K) *ᵥ v) (Sum.inl i) = v (Sum.inl i) := by
    intro i; rw [hg]; simp [u, w]
  have hinr : ∀ i : ι₀,
      ((g : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K) *ᵥ v) (Sum.inr (Sum.inl i)) =
        v (Sum.inr (Sum.inl i)) := by
    intro i; rw [hg]; simp [u, w]
  unfold QuadM
  have e1 : ((g : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K) *ᵥ v)
      (Sum.inr (Sum.inr (0 : Fin 2))) = v u + α * v w := hu0
  have e2 : ((g : Matrix (ι₀ ⊕ ι₀ ⊕ Fin 2) (ι₀ ⊕ ι₀ ⊕ Fin 2) K) *ᵥ v)
      (Sum.inr (Sum.inr (1 : Fin 2))) = s * v w := hw0
  rw [e1, e2]
  simp only [hinl, hinr]
  have e3 : v (Sum.inr (Sum.inr (0 : Fin 2))) = v u := rfl
  have e4 : v (Sum.inr (Sum.inr (1 : Fin 2))) = v w := rfl
  rw [e3, e4]
  have hα2 : 2 * α = b₁ - b₂ * s := by rw [hα]; field_simp
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  apply mul_left_cancel₀ h4
  clear_value α
  linear_combination (v w ^ 2 * (2 * α + b₂ * s + b₁) + 4 * v u * v w) * hα2 - (v w ^ 2) * hs

end Minus

section Unique

noncomputable def fieldIsoOfCard {K L : Type} [Field K] [Field L] [Finite K] [Finite L]
    (h : Nat.card K = Nat.card L) : K ≃+* L := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  exact FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact h)

theorem irreducible_map {K L : Type} [Field K] [Field L] (φ : K ≃+* L) {b c : K}
    (h : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ∀ s : L, s ^ 2 + φ b * s + φ c ≠ 0 := by
  intro s hs
  apply h (φ.symm s)
  apply φ.injective
  rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, hs, map_zero]

theorem map_conj_statedScalars {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : GL ι K) :
    (StatedScalars ι K).map (MulAut.conj g).toMonoidHom = StatedScalars ι K := by
  have hN := StatedScalars.normal ι K
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hN.conj_mem y hy g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using hN.conj_mem x hx g⁻¹
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem statedClassicalModel_unique {X Y : Type} [Group X] [Group Y] {t : StatedLieTag}
    {n r e : ℕ} (hr2 : r ≠ 2) (hX : StatedClassicalModel X t n r e)
    (hY : StatedClassicalModel Y t n r e) : Nonempty (X ≃* Y) := by
  have hprime : r.Prime := hX.1.1
  cases t
  case PSL =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSL φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case PSU =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ n (r ^ e))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case PSp =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSp φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaOdd =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (map_statedOmega φ (statedQuadOdd_comp φ))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaPlus =>
    obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (map_statedOmega φ (statedQuadPlus_comp φ))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  case POmegaMinus =>
    obtain ⟨-, K₁, _, _, hc₁, b₁, c₁, hirr₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, b₂, c₂, hirr₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    have := Fintype.ofFinite K₂
    have h2 : (2 : K₂) ≠ 0 := by
      refine Ring.two_ne_zero fun h => ?_
      have h1 := FiniteField.even_card_iff_char_two.mp h
      rw [← Nat.card_eq_fintype_card, hc₂] at h1
      have hodd : Odd (r ^ e) := (hprime.odd_of_ne_two hr2).pow
      exact absurd h1 (by rw [Nat.odd_iff.mp hodd]; omega)
    obtain ⟨s, hs0, hs⟩ := exists_sq_eq_disc h2 (irreducible_map φ hirr₁) hirr₂
    obtain ⟨g, hg⟩ := exists_isometry_quadM (ι₀ := Fin (n - 1)) h2 hs0 hs
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ)
      (map_statedOmega φ (statedQuadMinus_comp φ rfl rfl)) (glCongr_statedScalars φ)).trans
      ((statedProjCongr (MulAut.conj g) (map_statedOmega_conj g hg)
        (map_conj_statedScalars g)).trans e₂.symm))⟩
  all_goals exact hX.2.elim

end Unique

end CFSG.ClassicalInvolution.Upgrade
