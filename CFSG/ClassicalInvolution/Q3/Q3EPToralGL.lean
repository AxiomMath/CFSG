module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlusNormalized

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.Assembly.LowTwoRank
open scoped Matrix MatrixGroups

section CommutingGL

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m)

theorem gl_true_of_commute {g : V →ₗ[F] V} {a b b' : Fin m} (hab : a ≠ b) (hab' : a ≠ b')
    (hbb' : b ≠ b')
    (hcomm : ∀ x, g (eichler Q (Fr.vec b false) (Fr.vec a true) x) =
      eichler Q (Fr.vec b false) (Fr.vec a true) (g x))
    (hcomm' : ∀ x, g (eichler Q (Fr.vec b' false) (Fr.vec a true) x) =
      eichler Q (Fr.vec b' false) (Fr.vec a true) (g x)) :
    ∃ c : F, g (Fr.vec a true) = c • Fr.vec a true := by
  have h1 := map_vec_of_commute Fr hab true false hcomm
  have h2 := map_vec_of_commute Fr hab' true false hcomm'
  simp only [Bool.not_false] at h1 h2
  have hp : polar Q (g (Fr.vec a true)) (Fr.vec b true) = 0 := by
    rw [h2, polar_sub_left, polar_smul_left, polar_smul_left,
      Fr.polar_vec_of_ne hab true true, Fr.polar_vec_of_ne hbb'.symm false true]
    simp
  have hβ : polar Q (g (Fr.vec b true)) (Fr.vec a true) = 0 := by
    rw [h1, polar_sub_left, polar_smul_left, polar_smul_left,
      Fr.polar_vec_of_ne hab true true] at hp
    have h3 := Fr.polar_not_vec b true
    simp only [Bool.not_true] at h3
    rw [h3] at hp
    simpa using hp
  exact ⟨polar Q (g (Fr.vec b true)) (Fr.vec b false), by rw [h1, hβ, zero_smul, sub_zero]⟩

theorem gl_false_formula {g : V →ₗ[F] V} {a b : Fin m} (hab : a ≠ b)
    (hcomm : ∀ x, g (eichler Q (Fr.vec b false) (Fr.vec a true) x) =
      eichler Q (Fr.vec b false) (Fr.vec a true) (g x)) :
    g (Fr.vec b false) = polar Q (g (Fr.vec a false)) (Fr.vec a true) • Fr.vec b false -
      polar Q (g (Fr.vec a false)) (Fr.vec b false) • Fr.vec a true := by
  have hu : Q (Fr.vec b false) = 0 := Fr.map_vec b false
  have huw : polar Q (Fr.vec b false) (Fr.vec a true) = 0 :=
    Fr.polar_vec_of_ne hab.symm false true
  have hE : eichler Q (Fr.vec b false) (Fr.vec a true) (Fr.vec a false) =
      Fr.vec a false - Fr.vec b false := by
    rw [eichler_apply hu huw, Fr.polar_vec_of_ne hab false false]
    have h3 := Fr.polar_vec_not a false
    simp only [Bool.not_false] at h3
    rw [h3, Fr.map_vec a true]
    simp [sub_eq_add_neg]
  have h1 := hcomm (Fr.vec a false)
  rw [hE, map_sub, eichler_apply hu huw, Fr.map_vec a true] at h1
  simp only [zero_mul, add_zero] at h1
  have h2 : g (Fr.vec a false) - g (Fr.vec b false) =
      g (Fr.vec a false) + polar Q (g (Fr.vec a false)) (Fr.vec b false) • Fr.vec a true -
        polar Q (g (Fr.vec a false)) (Fr.vec a true) • Fr.vec b false := h1
  have h4 : g (Fr.vec b false) = -(polar Q (g (Fr.vec a false)) (Fr.vec b false) • Fr.vec a true) +
      polar Q (g (Fr.vec a false)) (Fr.vec a true) • Fr.vec b false := by
    have := congrArg (fun v => g (Fr.vec a false) - v) h2
    simp only [sub_sub_cancel] at this
    rw [this]
    abel
  rw [h4]
  abel

theorem gl_false_of_commute {g : V →ₗ[F] V} {a a' b : Fin m} (hab : a ≠ b) (ha'b : a' ≠ b)
    (haa' : a ≠ a')
    (hcomm : ∀ x, g (eichler Q (Fr.vec b false) (Fr.vec a true) x) =
      eichler Q (Fr.vec b false) (Fr.vec a true) (g x))
    (hcomm' : ∀ x, g (eichler Q (Fr.vec b false) (Fr.vec a' true) x) =
      eichler Q (Fr.vec b false) (Fr.vec a' true) (g x)) :
    ∃ c : F, g (Fr.vec b false) = c • Fr.vec b false := by
  have h1 := gl_false_formula Fr hab hcomm
  have h2 := gl_false_formula Fr ha'b hcomm'
  have hp : polar Q (g (Fr.vec b false)) (Fr.vec a false) = 0 := by
    rw [h2, polar_sub_left, polar_smul_left, polar_smul_left,
      Fr.polar_vec_of_ne hab.symm false false, Fr.polar_vec_of_ne haa'.symm true false]
    simp
  have hν : polar Q (g (Fr.vec a false)) (Fr.vec b false) = 0 := by
    rw [h1, polar_sub_left, polar_smul_left, polar_smul_left,
      Fr.polar_vec_of_ne hab.symm false false] at hp
    have h3 := Fr.polar_vec_not a true
    simp only [Bool.not_true] at h3
    rw [h3] at hp
    simpa using hp
  exact ⟨polar Q (g (Fr.vec a false)) (Fr.vec a true), by rw [h1, hν, zero_smul, sub_zero]⟩

theorem diag_of_commuting_gl (g : V →ₗ[F] V) {O : Fin m → Prop} {a₁ a₂ a₃ : Fin m}
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) (h1 : O a₁) (h2 : O a₂) (h3 : O a₃)
    (hcomm : ∀ a b, a ≠ b → O a → O b → ∀ x,
      g (eichler Q (Fr.vec b false) (Fr.vec a true) x) =
        eichler Q (Fr.vec b false) (Fr.vec a true) (g x)) :
    ∀ a, O a → ∀ s, ∃ c : F, g (Fr.vec a s) = c • Fr.vec a s := by
  classical
  have hother : ∀ a, O a → ∃ b b', O b ∧ O b' ∧ b ≠ a ∧ b' ≠ a ∧ b ≠ b' := by
    intro a ha
    by_cases e1 : a₁ = a
    · exact ⟨a₂, a₃, h2, h3, fun h => h12 (e1.trans h.symm), fun h => h13 (e1.trans h.symm), h23⟩
    · by_cases e2 : a₂ = a
      · exact ⟨a₁, a₃, h1, h3, e1, fun h => h23 (e2.trans h.symm), h13⟩
      · exact ⟨a₁, a₂, h1, h2, e1, e2, h12⟩
  intro a ha s
  obtain ⟨b, b', hb, hb', hba, hb'a, hbb'⟩ := hother a ha
  cases s
  ·
    obtain ⟨c, hc⟩ := gl_false_of_commute Fr (a := b) (a' := b') (b := a) hba hb'a hbb'
      (hcomm b a hba hb ha) (hcomm b' a hb'a hb' ha)
    exact ⟨c, hc⟩
  · obtain ⟨c, hc⟩ := gl_true_of_commute Fr (a := a) (b := b) (b' := b') hba.symm hb'a.symm hbb'
      (hcomm a b hba.symm ha hb) (hcomm a b' hb'a.symm ha hb')
    exact ⟨c, hc⟩

end CommutingGL

theorem exists_three_others {m : ℕ} (hm : 5 ≤ m) (i₀ i₁ : Fin m) :
    ∃ a₁ a₂ a₃ : Fin m, a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧ a₁ ≠ i₀ ∧ a₁ ≠ i₁ ∧ a₂ ≠ i₀ ∧
      a₂ ≠ i₁ ∧ a₃ ≠ i₀ ∧ a₃ ≠ i₁ := by
  classical
  have hcard : 2 < (Finset.univ \ {i₀, i₁} : Finset (Fin m)).card := by
    have h1 : (Finset.univ : Finset (Fin m)).card = m := by simp
    have h2 : ({i₀, i₁} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    have h3 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m)) {i₀, i₁}
    have h4 : ((Finset.univ : Finset (Fin m)) ∩ {i₀, i₁}).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans h2
    omega
  obtain ⟨a₁, h1, a₂, h2, a₃, h3, h12, h13, h23⟩ := Finset.two_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and,
    not_or] at h1 h2 h3
  exact ⟨a₁, a₂, a₃, h12, h13, h23, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩

section GroupLevel

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem hmul_of_gl_group (hm : 5 ≤ m) {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q}
    (hα : IsConj α g) (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c))
    (hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → b ≠ i₀ → b ≠ i₁ → ∀ c : F,
      conjTwist α k (Fr.longRoot hab true false (.ofAdd c)) =
        Fr.longRoot hab true false (.ofAdd c)) :
    ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g.conjSpin k (Fr.vec i s) = c • Fr.vec i s := by
  classical
  obtain ⟨gL, hφ, hgL, hconj, hμL, hginj, hI1⟩ := exists_linear_conj Fr h01 s₀ t₀ hα k hA1 hA1'
  have hcomm : ∀ a b : Fin m, a ≠ b → (a ≠ i₀ ∧ a ≠ i₁) → (b ≠ i₀ ∧ b ≠ i₁) → ∀ x,
      gL (eichler Q (Fr.vec b false) (Fr.vec a true) x) =
        eichler Q (Fr.vec b false) (Fr.vec a true) (gL x) := by
    intro a b hab ha hb x
    have e := Fr.spinAction_longRoot_eq_eichler hab true false 1
    rw [one_smul] at e
    rw [← e, ← hconj, hO a b hab ha.1 ha.2 hb.1 hb.2 1]
  obtain ⟨a₁, a₂, a₃, h12, h13, h23, h10, h11, h20, h21, h30, h31⟩ := exists_three_others hm i₀ i₁
  intro i hi0 hi1 s
  obtain ⟨c, hc⟩ := diag_of_commuting_gl Fr gL (O := fun a => a ≠ i₀ ∧ a ≠ i₁) h12 h13 h23
    ⟨h10, h11⟩ ⟨h20, h21⟩ ⟨h30, h31⟩ hcomm i ⟨hi0, hi1⟩ s
  exact ⟨c, by rw [← hgL]; exact hc⟩

end GroupLevel

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]


theorem toralNormal_plus_of_gl (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m := by omega)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool) (k : spinGroup (quadPlus m F))
    (H1 : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹)) =
      θ (k * (plusFrame m F hm3).longRoot h01 s₀ t₀ (.ofAdd c) * k⁻¹))
    (H1' : ∀ c : F, σ (θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) *
        k⁻¹)) = θ (k * (plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) * k⁻¹))
    (H2 : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → b ≠ i₀ → b ≠ i₁ → ∀ c : F,
      σ (θ (k * (plusFrame m F hm3).longRoot hab true false (.ofAdd c) * k⁻¹)) =
        θ (k * (plusFrame m F hm3).longRoot hab true false (.ofAdd c) * k⁻¹)) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  obtain ⟨hZ, -⟩ := plus_center_facts (F := F) hp2 hm3
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift hp2 hm hf hF θ hker σ hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadPlus m F)) := isPerfect_spinGroup_quadPlus hm3
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadPlus m F) →* _).comp
      (α : spinGroup (quadPlus m F) →* _)) (MonoidHom.id (spinGroup (quadPlus m F))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  set Fr := plusFrame m F hm3 with hFr
  have hfix : ∀ {i j : Fin m} (hij : i ≠ j) (s t : Bool) (c : F),
      σ (θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹)) =
        θ (k * Fr.longRoot hij s t (.ofAdd c) * k⁻¹) →
      conjTwist α k (Fr.longRoot hij s t (.ofAdd c)) = Fr.longRoot hij s t (.ofAdd c) :=
    fun hij s t c h => conjTwist_eq_of_sigma_eq hZ θ hker σ α hαθ k
      (longRoot_pow_char Fr hij s t c) (longRoot_pow_char Fr hij s t c) h
  have hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c) := fun c => hfix h01 s₀ t₀ c (H1 c)
  have hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c) := fun c => hfix h01.symm (!t₀) (!s₀) c (H1' c)
  have hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → b ≠ i₀ → b ≠ i₁ → ∀ c : F,
      conjTwist α k (Fr.longRoot hab true false (.ofAdd c)) =
        Fr.longRoot hab true false (.ofAdd c) :=
    fun a b hab ha0 ha1 hb0 hb1 c => hfix hab true false c (H2 a b hab ha0 ha1 hb0 hb1 c)
  have hmul := hmul_of_gl_group Fr h01 s₀ t₀ hm hα k hA1 hA1' hO
  obtain ⟨κ, lam, hprod, hdiag⟩ := exists_diag_form_of_diag Fr h01 s₀ t₀ hm3 h2 hp2
    (plus_hker2 m) hα hα2 k hA1 hA1' hmul
  exact toralNormal_plus_of_diag hm3 h2 hZ θ hker σ α hαθ hα2 g.μ κ lam hprod hdiag

theorem toralNormal_plus_of_gl_subgroups (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {m : ℕ} (hm : 5 ≤ m) (hm3 : 3 ≤ m := by omega)
    {X : Type} [Group X] (θ : spinGroup (quadPlus m F) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus m F)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) {s₀ t₀ : Bool} {γ₀ : Fin m → ℤ}
    (hγ₀ : toStdD m γ₀ = Pi.single i₀ (boolSign s₀) + Pi.single i₁ (boolSign t₀))
    (k : spinGroup (quadPlus m F))
    (H1 : ∀ y ∈ (((plusDatum m F hm3).rootGroup γ₀ ⊔ (plusDatum m F hm3).rootGroup (-γ₀)).map
        (MulAut.conj k).toMonoidHom), σ (θ y) = θ y)
    (H2 : ∀ (a b : Fin m), a ≠ b → a ≠ i₀ → a ≠ i₁ → b ≠ i₀ → b ≠ i₁ →
      ∀ {γ : Fin m → ℤ},
        toStdD m γ = Pi.single a (boolSign true) + Pi.single b (boolSign false) →
          ∀ y ∈ ((plusDatum m F hm3).rootGroup γ).map (MulAut.conj k).toMonoidHom,
            σ (θ y) = θ y) :
    ∃ (k₀ : spinGroup (quadPlus m F)) (v : Fin m → ZMod 2),
      ∀ γ : Fin m → ℤ, γ ∈ (plusDatum m F hm3).roots →
        ((((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum m F hm3).rootGroup γ ⊔ (plusDatum m F hm3).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  have hX1 : (plusDatum m F hm3).rootGroup γ₀ = ((plusFrame m F hm3).longRoot h01 s₀ t₀).range :=
    plusRootGroup_eq hm3 h01 s₀ t₀ hγ₀
  have hstd' : toStdD m (-γ₀) = Pi.single i₁ (boolSign (!t₀)) + Pi.single i₀ (boolSign (!s₀)) := by
    have e : toStdD m (-γ₀) = -toStdD m γ₀ := toStdD_neg m γ₀
    rw [e, hγ₀, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add, add_comm]
  have hX2 : (plusDatum m F hm3).rootGroup (-γ₀) =
      ((plusFrame m F hm3).longRoot h01.symm (!t₀) (!s₀)).range :=
    plusRootGroup_eq hm3 h01.symm (!t₀) (!s₀) hstd'
  refine toralNormal_plus_of_gl hp2 hf hF hm hm3 θ hker σ hσ2 hσr h01 s₀ t₀ k (fun c => ?_)
    (fun c => ?_) (fun a b hab ha0 ha1 hb0 hb1 c => ?_)
  · refine H1 _ ⟨_, Subgroup.mem_sup_left ?_, rfl⟩
    rw [hX1]
    exact ⟨_, rfl⟩
  · refine H1 _ ⟨_, Subgroup.mem_sup_right ?_, rfl⟩
    rw [hX2]
    exact ⟨_, rfl⟩
  · obtain ⟨γ, -, hγ⟩ := exists_mem_rootsD_toStdD_eq m hab (boolSign_eq_one_or_eq_neg_one true)
      (boolSign_eq_one_or_eq_neg_one false)
    have hXγ : (plusDatum m F hm3).rootGroup γ =
        ((plusFrame m F hm3).longRoot hab true false).range :=
      plusRootGroup_eq hm3 hab true false hγ
    exact H2 a b hab ha0 ha1 hb0 hb1 hγ _ ⟨_, by rw [hXγ]; exact ⟨_, rfl⟩, rfl⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
