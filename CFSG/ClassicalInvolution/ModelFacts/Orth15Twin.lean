module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Local
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Gen

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polarNondegOn_sup {A B : Submodule F V} (hA : PolarNondegOn Q A) (hB : PolarNondegOn Q B)
    (horth : ∀ x ∈ A, ∀ y ∈ B, polar Q x y = 0) : PolarNondegOn Q (A ⊔ B) := by
  intro x hx hxx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  have ha0 : a = 0 := by
    refine hA a ha fun y hy => ?_
    have h1 := hxx y (Submodule.mem_sup_left hy)
    rw [polar_add_left, polar_comm Q b y, horth y hy b hb, add_zero] at h1
    exact h1
  have hb0 : b = 0 := by
    refine hB b hb fun y hy => ?_
    have h1 := hxx y (Submodule.mem_sup_right hy)
    rw [polar_add_left, horth a ha y hy, zero_add] at h1
    exact h1
  rw [ha0, hb0, add_zero]

theorem layerGenOn_of_finrank_le_two [FiniteDimensional F V] {S : Submodule F V}
    (hS : PolarNondegOn Q S) (h2 : Module.finrank F S ≤ 2) : LayerGenOn Q S := by
  refine ⟨∅, by simp, ?_⟩
  rw [elemOn_eq_bot_of_finrank_le_two hS h2]
  simp

theorem layerGenOn_of_regular [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {S : Submodule F V} (hS : PolarNondegOn Q S) : LayerGenOn Q S := by
  by_cases h : Module.finrank F S ≤ 2
  · exact layerGenOn_of_finrank_le_two hS h
  · exact layerGenOn hodd h5 (nondegenerate_polarBilin_restrict hS) (by omega)

structure SplitDatum (Q : QuadraticForm F V) (U₁ U₂ W : Submodule F V)
    (u₁ u₂ : V ≃ₗ[F] V) : Prop where
  nd₁ : PolarNondegOn Q U₁
  nd₂ : PolarNondegOn Q U₂
  ndW : PolarNondegOn Q W
  o₁₂ : ∀ x ∈ U₁, ∀ y ∈ U₂, polar Q x y = 0
  o₁W : ∀ x ∈ U₁, ∀ y ∈ W, polar Q x y = 0
  o₂W : ∀ x ∈ U₂, ∀ y ∈ W, polar Q x y = 0
  top : U₁ ⊔ U₂ ⊔ W = ⊤
  neg₁ : ∀ x ∈ U₁, u₁ x = -x
  fix₁ : ∀ x ∈ U₂ ⊔ W, u₁ x = x
  neg₂ : ∀ x ∈ U₂, u₂ x = -x
  fix₂ : ∀ x ∈ U₁ ⊔ W, u₂ x = x
  mem₁ : u₁ ∈ elementaryGroup Q
  mem₂ : u₂ ∈ elementaryGroup Q

structure TwinDatum (Q : QuadraticForm F V) (U₁ U₂ W : Submodule F V)
    (u₁ u₂ : V ≃ₗ[F] V) : Prop extends SplitDatum Q U₁ U₂ W u₁ u₂ where
  ne₁ : U₁ ≠ ⊥
  ne₂ : U₂ ≠ ⊥
  d₁₂ : 3 ≤ Module.finrank F ↥(U₁ ⊔ U₂)
  dW : 3 ≤ Module.finrank F W

structure KleinDatum (Q : QuadraticForm F V) (U₁ U₂ W : Submodule F V)
    (u₁ u₂ : V ≃ₗ[F] V) : Prop extends SplitDatum Q U₁ U₂ W u₁ u₂ where
  ne₁ : U₁ ≠ ⊥
  ne₂ : U₂ ≠ ⊥
  neW : W ≠ ⊥
  d₁₂ : 3 ≤ Module.finrank F ↥(U₁ ⊔ U₂)
  d₁W : 3 ≤ Module.finrank F ↥(U₁ ⊔ W)
  d₂W : 3 ≤ Module.finrank F ↥(U₂ ⊔ W)
  gen : 3 ≤ Module.finrank F U₁ ∨ 3 ≤ Module.finrank F U₂ ∨ 3 ≤ Module.finrank F W

namespace SplitDatum

variable {U₁ U₂ W : Submodule F V} {u₁ u₂ : V ≃ₗ[F] V}

theorem nd_sup₂W (T : SplitDatum Q U₁ U₂ W u₁ u₂) : PolarNondegOn Q (U₂ ⊔ W) :=
  polarNondegOn_sup T.nd₂ T.ndW T.o₂W

theorem nd_sup₁W (T : SplitDatum Q U₁ U₂ W u₁ u₂) : PolarNondegOn Q (U₁ ⊔ W) :=
  polarNondegOn_sup T.nd₁ T.ndW T.o₁W

theorem nd_sup₁₂ (T : SplitDatum Q U₁ U₂ W u₁ u₂) : PolarNondegOn Q (U₁ ⊔ U₂) :=
  polarNondegOn_sup T.nd₁ T.nd₂ T.o₁₂

theorem split₁ (T : SplitDatum Q U₁ U₂ W u₁ u₂) : SplitInv Q U₁ (U₂ ⊔ W) u₁ where
  ndS := T.nd₁
  ndT := T.nd_sup₂W
  orth := fun x hx y hy => by
    obtain ⟨y₂, hy₂, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, T.o₁₂ x hx y₂ hy₂, T.o₁W x hx y₃ hy₃, add_zero]
  top := by rw [← sup_assoc]; exact T.top
  negS := T.neg₁
  fixT := T.fix₁

theorem split₂ (T : SplitDatum Q U₁ U₂ W u₁ u₂) : SplitInv Q U₂ (U₁ ⊔ W) u₂ where
  ndS := T.nd₂
  ndT := T.nd_sup₁W
  orth := fun x hx y hy => by
    obtain ⟨y₁, hy₁, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, polar_comm Q x y₁, T.o₁₂ y₁ hy₁ x hx, T.o₂W x hx y₃ hy₃, add_zero]
  top := by rw [sup_left_comm, ← sup_assoc]; exact T.top
  negS := T.neg₂
  fixT := T.fix₂

theorem split₃ (T : SplitDatum Q U₁ U₂ W u₁ u₂) : SplitInv Q (U₁ ⊔ U₂) W (u₁ * u₂) where
  ndS := T.nd_sup₁₂
  ndT := T.ndW
  orth := fun x hx y hy => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, T.o₁W x₁ hx₁ y hy, T.o₂W x₂ hx₂ y hy, add_zero]
  top := T.top
  negS := fun x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [LinearEquiv.mul_apply, map_add, T.fix₂ x₁ (Submodule.mem_sup_left hx₁), T.neg₂ x₂ hx₂,
      map_add, map_neg, T.neg₁ x₁ hx₁, T.fix₁ x₂ (Submodule.mem_sup_left hx₂), neg_add]
  fixT := fun x hx => by
    rw [LinearEquiv.mul_apply, T.fix₂ x (Submodule.mem_sup_right hx),
      T.fix₁ x (Submodule.mem_sup_right hx)]

theorem comm (T : SplitDatum Q U₁ U₂ W u₁ u₂) (x : V) : u₁ (u₂ x) = u₂ (u₁ x) := by
  obtain ⟨s, hs, t, ht, rfl⟩ := T.split₁.exists_decomp x
  obtain ⟨t₂, ht₂, t₃, ht₃, rfl⟩ := Submodule.mem_sup.mp ht
  have a1 : u₁ s = -s := T.neg₁ s hs
  have a2 : u₁ t₂ = t₂ := T.fix₁ t₂ (Submodule.mem_sup_left ht₂)
  have a3 : u₁ t₃ = t₃ := T.fix₁ t₃ (Submodule.mem_sup_right ht₃)
  have b1 : u₂ s = s := T.fix₂ s (Submodule.mem_sup_left hs)
  have b2 : u₂ t₂ = -t₂ := T.neg₂ t₂ ht₂
  have b3 : u₂ t₃ = t₃ := T.fix₂ t₃ (Submodule.mem_sup_right ht₃)
  simp only [map_add, map_neg, a1, a2, a3, b1, b2, b3]

end SplitDatum

theorem TwinDatum.toKlein [FiniteDimensional F V] {U₁ U₂ W : Submodule F V}
    {u₁ u₂ : V ≃ₗ[F] V} (T : TwinDatum Q U₁ U₂ W u₁ u₂) : KleinDatum Q U₁ U₂ W u₁ u₂ where
  toSplitDatum := T.toSplitDatum
  ne₁ := T.ne₁
  ne₂ := T.ne₂
  neW := fun h => by
    have := T.dW
    rw [h, finrank_bot] at this
    omega
  d₁₂ := T.d₁₂
  d₁W := T.dW.trans (Submodule.finrank_mono le_sup_right)
  d₂W := T.dW.trans (Submodule.finrank_mono le_sup_right)
  gen := Or.inr (Or.inr T.dW)

theorem mem_closure_pair_involutions {X : Type*} [Group X] {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) {b : X} (hb : b ∈ Subgroup.closure ({x, y} : Set X)) :
    b = 1 ∨ b = x ∨ b = y ∨ b = x * y := by
  have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
  have h3 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
  have h5 : x * y * (x * y) = 1 := by rw [mul_assoc, h2, hx]
  have h6 : y * x = x * y := hxy.symm
  induction hb using Subgroup.closure_induction with
  | mem b hb =>
    rcases hb with rfl | hb
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul b₁ b₂ _ _ ih₁ ih₂ =>
    rcases ih₁ with rfl | rfl | rfl | rfl <;> rcases ih₂ with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, h1, h2, h3, h4, h5, h6]
  | inv b _ ih =>
    rcases ih with rfl | rfl | rfl | rfl
    · simp
    · rw [inv_eq_of_mul_eq_one_right hx]; simp
    · rw [inv_eq_of_mul_eq_one_right hy]; simp
    · rw [inv_eq_of_mul_eq_one_right h5]; simp

section Main

variable [Finite F] [FiniteDimensional F V]

omit [Finite F] [FiniteDimensional F V] in
theorem range_le_of_img_le {X : Type} [Group X] (e : ↥(elementaryGroup Q) →* X)
    {J₁ J₂ : Subgroup (V ≃ₗ[F] V)} (h₁ : J₁ ≤ elementaryGroup Q) (h₂ : J₂ ≤ elementaryGroup Q)
    (hgen : elementaryGroup Q ≤ J₁ ⊔ J₂) {P : Subgroup X} (hP₁ : img e J₁ ≤ P)
    (hP₂ : img e J₂ ≤ P) : e.range ≤ P := by
  set K : Subgroup (V ≃ₗ[F] V) := (P.comap e).map (elementaryGroup Q).subtype with hK
  have hJ : ∀ J : Subgroup (V ≃ₗ[F] V), J ≤ elementaryGroup Q → img e J ≤ P → J ≤ K := by
    intro J hJE hJP y hy
    refine ⟨⟨y, hJE hy⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact hJP ((mem_img_iff e).mpr ⟨⟨y, hJE hy⟩, hy, rfl⟩)
  rintro _ ⟨g, rfl⟩
  have hgK : (g : V ≃ₗ[F] V) ∈ K := (sup_le (hJ J₁ h₁ hP₁) (hJ J₂ h₂ hP₂)) (hgen g.2)
  obtain ⟨g', hg', hg'g⟩ := hgK
  have : g' = g := Subtype.ext hg'g
  subst this
  exact hg'

theorem alphaOf_klein_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) {U₁ U₂ W : Submodule F V} {u₁ u₂ : V ≃ₗ[F] V}
    (T : KleinDatum Q U₁ U₂ W u₁ u₂) {X : Type} [Group X] [Finite X]
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    (hcent : ∀ x : X, (∀ y ∈ e.range, x * y = y * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨u₁, T.mem₁⟩, e ⟨u₂, T.mem₂⟩} : Set X)) = ⊥ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set a₁ : ↥(elementaryGroup Q) := ⟨u₁, T.mem₁⟩ with ha₁
  set a₂ : ↥(elementaryGroup Q) := ⟨u₂, T.mem₂⟩ with ha₂
  have ha₁sq : a₁ * a₁ = 1 := Subtype.ext (LinearEquiv.ext fun x => T.split₁.aa x)
  have ha₂sq : a₂ * a₂ = 1 := Subtype.ext (LinearEquiv.ext fun x => T.split₂.aa x)
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := Subtype.ext (LinearEquiv.ext fun x => T.comm x)
  have hx : e a₁ * e a₁ = 1 := by rw [← map_mul, ha₁sq, map_one]
  have hy : e a₂ * e a₂ = 1 := by rw [← map_mul, ha₂sq, map_one]
  have hxy : e a₁ * e a₂ = e a₂ * e a₁ := by rw [← map_mul, ← map_mul, ha₁₂]
  set B : Subgroup X := Subgroup.closure ({e a₁, e a₂} : Set X) with hB
  have hBmem := fun {b : X} (hb : b ∈ B) => mem_closure_pair_involutions hx hy hxy hb
  have hB2 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact hx
    · exact hy
    · have : (e a₁ * e a₂) * (e a₁ * e a₂) = e a₁ * (e a₂ * e a₁) * e a₂ := by group
      rw [this, ← hxy]
      calc e a₁ * (e a₁ * e a₂) * e a₂ = (e a₁ * e a₁) * (e a₂ * e a₂) := by group
        _ = 1 := by rw [hx, hy, one_mul]
  have hBL : B ≤ e.range := by
    rw [hB, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨a₁, rfl⟩
    · exact ⟨a₂, rfl⟩
  have he₁ : e a₁ ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have he₂ : e a₂ ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have he₃ : e (a₁ * a₂) = e a₁ * e a₂ := map_mul e a₁ a₂
  have he₃B : e (a₁ * a₂) ∈ B := by rw [he₃]; exact B.mul_mem he₁ he₂
  have lay₁ : LayerGenOn Q U₁ := layerGenOn_of_regular hodd h5 T.nd₁
  have lay₂ : LayerGenOn Q U₂ := layerGenOn_of_regular hodd h5 T.nd₂
  have layW : LayerGenOn Q W := layerGenOn_of_regular hodd h5 T.ndW
  have lay₂W : LayerGenOn Q (U₂ ⊔ W) := layerGenOn_of_regular hodd h5 T.nd_sup₂W
  have lay₁W : LayerGenOn Q (U₁ ⊔ W) := layerGenOn_of_regular hodd h5 T.nd_sup₁W
  have lay₁₂ : LayerGenOn Q (U₁ ⊔ U₂) := layerGenOn_of_regular hodd h5 T.nd_sup₁₂
  have hD₁ : LocalData e a₁ U₁ (U₂ ⊔ W) := ⟨T.split₁, hker, T.ne₁,
    fun h => T.ne₂ (eq_bot_iff.mpr (le_sup_left.trans h.le))⟩
  have hD₂ : LocalData e a₂ U₂ (U₁ ⊔ W) := ⟨T.split₂, hker, T.ne₂,
    fun h => T.ne₁ (eq_bot_iff.mpr (le_sup_left.trans h.le))⟩
  have hD₃ : LocalData e (a₁ * a₂) (U₁ ⊔ U₂) W := ⟨T.split₃, hker,
    fun h => T.ne₁ (eq_bot_iff.mpr (le_sup_left.trans h.le)), T.neW⟩
  set P₁ : Subgroup X := img e (elemOn Q U₁ ⊔ elemOn Q (U₂ ⊔ W)) with hP₁
  set P₂ : Subgroup X := img e (elemOn Q U₂ ⊔ elemOn Q (U₁ ⊔ W)) with hP₂
  set P₃ : Subgroup X := img e (elemOn Q (U₁ ⊔ U₂) ⊔ elemOn Q W) with hP₃
  have hfin : ∀ N : Subgroup X, (∀ n ∈ N, n * e a₁ = e a₁ * n ∧ n * e a₂ = e a₂ * n) →
      ⁅N, B⁆ = ⊥ := by
    intro N hN
    refine commutator_eq_bot_of_comm fun n hn b hb => ?_
    obtain ⟨c₁, c₂⟩ := hN n hn
    rcases hBmem hb with rfl | rfl | rfl | rfl
    · simp
    · exact c₁
    · exact c₂
    · rw [← mul_assoc, c₁, mul_assoc, c₂, ← mul_assoc]
  have hcomm_of : ∀ (g : ↥(elementaryGroup Q)) (b : ↥(elementaryGroup Q)),
      (g : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) = (b : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) →
      e g * e b = e b * e g := fun g b h => by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext h)
  have hbT₂ : ∀ x ∈ U₂ ⊔ W, u₂ x ∈ U₂ ⊔ W := fun x hx => by
    obtain ⟨y₂, hy₂, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, T.neg₂ y₂ hy₂, T.fix₂ y₃ (Submodule.mem_sup_right hy₃)]
    exact add_mem (neg_mem (Submodule.mem_sup_left hy₂)) (Submodule.mem_sup_right hy₃)
  have hbT₁ : ∀ x ∈ U₁ ⊔ W, u₁ x ∈ U₁ ⊔ W := fun x hx => by
    obtain ⟨y₁, hy₁, y₃, hy₃, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, T.neg₁ y₁ hy₁, T.fix₁ y₃ (Submodule.mem_sup_right hy₃)]
    exact add_mem (neg_mem (Submodule.mem_sup_left hy₁)) (Submodule.mem_sup_right hy₃)
  have hbT₁₂ : ∀ b : V ≃ₗ[F] V, (∀ x ∈ U₁, b x ∈ U₁) → (∀ x ∈ U₂, b x ∈ U₂) →
      ∀ x ∈ U₁ ⊔ U₂, b x ∈ U₁ ⊔ U₂ := fun b h₁ h₂ x hx => by
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (h₁ y₁ hy₁)) (Submodule.mem_sup_right (h₂ y₂ hy₂))
  refine alphaOf_eq_bot_of_layers e.range hcent B hBL hB2 {P₁, P₂, P₃} ?_ ?_ ?_
  ·
    intro P hP
    rcases hP with rfl | hP
    · refine ⟨e a₁, he₁, hD₁.ne_one h2, le_inf (img_le_range e _) (img_join_le_centralizer hD₁),
        fun x hx p hp => conj_mem_img h2 hD₁ hx hp, img_join_perfect hD₁ lay₁ lay₂W,
        fun N hNle hNnorm hodd' => commutator_img_eq_bot h2 hD₁ lay₁ lay₂W hNle hNnorm hodd'⟩
    · rcases hP with rfl | hP
      · refine ⟨e a₂, he₂, hD₂.ne_one h2,
          le_inf (img_le_range e _) (img_join_le_centralizer hD₂),
          fun x hx p hp => conj_mem_img h2 hD₂ hx hp, img_join_perfect hD₂ lay₂ lay₁W,
          fun N hNle hNnorm hodd' => commutator_img_eq_bot h2 hD₂ lay₂ lay₁W hNle hNnorm hodd'⟩
      · rw [Set.mem_singleton_iff] at hP
        subst hP
        refine ⟨e (a₁ * a₂), he₃B, hD₃.ne_one h2,
          le_inf (img_le_range e _) (img_join_le_centralizer hD₃),
          fun x hx p hp => conj_mem_img h2 hD₃ hx hp, img_join_perfect hD₃ lay₁₂ layW,
          fun N hNle hNnorm hodd' => commutator_img_eq_bot h2 hD₃ lay₁₂ layW hNle hNnorm hodd'⟩
  ·
    intro a ha ha1 N hNle hNnorm hodd'
    rcases hBmem ha with rfl | rfl | rfl | rfl
    · exact absurd rfl ha1
    ·
      refine hfin N fun n hn => ?_
      obtain ⟨g, rfl⟩ := (hNle hn).1
      refine ⟨((Subgroup.mem_centralizer_iff.mp (hNle hn).2) (e a₁) rfl).symm, ?_⟩
      obtain ⟨c, hc⟩ := exists_smul_right_of_odd hodd hD₁ lay₁ lay₂W hNle hNnorm hodd' hn T.d₂W
      obtain ⟨hgS, hgT⟩ := preserves_of_odd h2 hD₁ hNle hodd' hn
      refine hcomm_of g a₂ ?_
      exact commute_of_scalar_on_T (S := U₁) (T := U₂ ⊔ W) T.split₁.exists_decomp
        (fun x hx => (hgS x).mp hx) hc (fun x hx => T.fix₂ x (Submodule.mem_sup_left hx)) hbT₂
    ·
      refine hfin N fun n hn => ?_
      obtain ⟨g, rfl⟩ := (hNle hn).1
      refine ⟨?_, ((Subgroup.mem_centralizer_iff.mp (hNle hn).2) (e a₂) rfl).symm⟩
      obtain ⟨c, hc⟩ := exists_smul_right_of_odd hodd hD₂ lay₂ lay₁W hNle hNnorm hodd' hn T.d₁W
      obtain ⟨hgS, hgT⟩ := preserves_of_odd h2 hD₂ hNle hodd' hn
      refine hcomm_of g a₁ ?_
      exact commute_of_scalar_on_T (S := U₂) (T := U₁ ⊔ W) T.split₂.exists_decomp
        (fun x hx => (hgS x).mp hx) hc (fun x hx => T.fix₁ x (Submodule.mem_sup_left hx)) hbT₁
    ·
      rw [← he₃] at hNle hNnorm
      refine hfin N fun n hn => ?_
      obtain ⟨g, rfl⟩ := (hNle hn).1
      obtain ⟨c, hc⟩ := exists_smul_left_of_odd hodd hD₃ lay₁₂ layW hNle hNnorm hodd' hn
        T.d₁₂
      obtain ⟨hgS, hgT⟩ := preserves_of_odd h2 hD₃ hNle hodd' hn
      have hdec : ∀ x : V, ∃ s ∈ W, ∃ t ∈ U₁ ⊔ U₂, x = s + t := fun x => by
        obtain ⟨s, hs, t, ht, rfl⟩ := T.split₃.exists_decomp x
        exact ⟨t, ht, s, hs, add_comm _ _⟩
      have hu₁ : ∀ x ∈ U₁ ⊔ U₂, u₁ x ∈ U₁ ⊔ U₂ := hbT₁₂ u₁
        (fun x hx => by rw [T.neg₁ x hx]; exact neg_mem hx)
        (fun x hx => by rw [T.fix₁ x (Submodule.mem_sup_left hx)]; exact hx)
      have hu₂ : ∀ x ∈ U₁ ⊔ U₂, u₂ x ∈ U₁ ⊔ U₂ := hbT₁₂ u₂
        (fun x hx => by rw [T.fix₂ x (Submodule.mem_sup_left hx)]; exact hx)
        (fun x hx => by rw [T.neg₂ x hx]; exact neg_mem hx)
      refine ⟨hcomm_of g a₁ ?_, hcomm_of g a₂ ?_⟩
      · exact commute_of_scalar_on_T (S := W) (T := U₁ ⊔ U₂) hdec
          (fun x hx => (hgT x).mp hx) hc (fun x hx => T.fix₁ x (Submodule.mem_sup_right hx)) hu₁
      · exact commute_of_scalar_on_T (S := W) (T := U₁ ⊔ U₂) hdec
          (fun x hx => (hgT x).mp hx) hc (fun x hx => T.fix₂ x (Submodule.mem_sup_right hx)) hu₂
  ·
    set P : Subgroup X := ⨆ Pf ∈ ({P₁, P₂, P₃} : Set (Subgroup X)), Pf with hP
    have hP₁le : P₁ ≤ P := le_iSup₂_of_le P₁ (by simp) le_rfl
    have hP₂le : P₂ ≤ P := le_iSup₂_of_le P₂ (by simp) le_rfl
    have hP₃le : P₃ ≤ P := le_iSup₂_of_le P₃ (by simp) le_rfl
    have i₁ : img e (elemOn Q (U₂ ⊔ W)) ≤ P :=
      (img_mono e (le_sup_right : elemOn Q (U₂ ⊔ W) ≤ elemOn Q U₁ ⊔ elemOn Q (U₂ ⊔ W))).trans
        hP₁le
    have i₂ : img e (elemOn Q (U₁ ⊔ W)) ≤ P :=
      (img_mono e (le_sup_right : elemOn Q (U₁ ⊔ W) ≤ elemOn Q U₂ ⊔ elemOn Q (U₁ ⊔ W))).trans
        hP₂le
    have i₃ : img e (elemOn Q (U₁ ⊔ U₂)) ≤ P :=
      (img_mono e (le_sup_left : elemOn Q (U₁ ⊔ U₂) ≤ elemOn Q (U₁ ⊔ U₂) ⊔ elemOn Q W)).trans
        hP₃le
    rcases T.gen with h3 | h3 | h3
    ·
      have hgen := elementaryGroup_le_join_of_decomp hodd hQ (U₁ := U₂) (U₂ := W) (W := U₁)
        T.nd₁ h3 (fun x hx y hy => by rw [polar_comm]; exact T.o₁₂ y hy x hx)
        (fun x hx y hy => by rw [polar_comm]; exact T.o₁W y hy x hx)
        (by rw [sup_comm, ← sup_assoc]; exact T.top)
      exact range_le_of_img_le e elemOn_le_elementaryGroup elemOn_le_elementaryGroup hgen
        ((img_mono e (elemOn_mono (sup_comm W U₁).le)).trans i₂)
        ((img_mono e (elemOn_mono (sup_comm U₂ U₁).le)).trans i₃)
    ·
      have hgen := elementaryGroup_le_join_of_decomp hodd hQ (U₁ := U₁) (U₂ := W) (W := U₂)
        T.nd₂ h3 T.o₁₂ (fun x hx y hy => by rw [polar_comm]; exact T.o₂W y hy x hx)
        (by rw [sup_right_comm]; exact T.top)
      exact range_le_of_img_le e elemOn_le_elementaryGroup elemOn_le_elementaryGroup hgen
        ((img_mono e (elemOn_mono (sup_comm W U₂).le)).trans i₁) i₃
    ·
      have hgen := elementaryGroup_le_join_of_decomp hodd hQ T.ndW h3 T.o₁W T.o₂W T.top
      exact range_le_of_img_le e elemOn_le_elementaryGroup elemOn_le_elementaryGroup hgen i₁ i₂

theorem alphaOf_twin_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) {U₁ U₂ W : Submodule F V} {u₁ u₂ : V ≃ₗ[F] V}
    (T : TwinDatum Q U₁ U₂ W u₁ u₂) {X : Type} [Group X] [Finite X]
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    (hcent : ∀ x : X, (∀ y ∈ e.range, x * y = y * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨u₁, T.mem₁⟩, e ⟨u₂, T.mem₂⟩} : Set X)) = ⊥ :=
  alphaOf_klein_eq_bot hodd h5 hQ T.toKlein e hker hcent

end Main

end CFSG.ClassicalInvolution.ModelFacts.Orth15
