module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankA

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Count

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

@[expose] def IsSelfAdj (σ : F ≃+* F) (f : Module.End F (Fin 4 → F)) : Prop :=
  ∀ x y, herm σ (f x) y = herm σ x (f y)

theorem IsSelfAdj.add {f g : Module.End F (Fin 4 → F)} (hf : IsSelfAdj σ f) (hg : IsSelfAdj σ g) :
    IsSelfAdj σ (f + g) := fun x y => by
  simp only [LinearMap.add_apply, herm_add_left, herm_add_right, hf x y, hg x y]

theorem IsSelfAdj.neg {f : Module.End F (Fin 4 → F)} (hf : IsSelfAdj σ f) :
    IsSelfAdj σ (-f) := fun x y => by
  simp only [LinearMap.neg_apply, herm_neg_left, herm_neg_right, hf x y]

theorem isSelfAdj_zero : IsSelfAdj σ (0 : Module.End F (Fin 4 → F)) := fun x y => by
  simp

theorem selfAdj_split {ω : F} (hω : σ ω ≠ ω) (hσ : ∀ c, σ (σ c) = c)
    {f₁ f₂ : Module.End F (Fin 4 → F)} (h₁ : IsSelfAdj σ f₁) (h₂ : IsSelfAdj σ f₂)
    (h : f₁ + ω • f₂ = 0) : f₁ = 0 ∧ f₂ = 0 := by
  have hf₁ : ∀ x, f₁ x = -(ω • f₂ x) := fun x => by
    have := LinearMap.congr_fun h x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  have hA : ∀ x y, herm σ x (f₂ y) = 0 := by
    intro x y
    have key := h₁ x y
    rw [hf₁ x, hf₁ y, herm_neg_left, herm_neg_right, herm_smul_left, herm_smul_right,
      h₂ x y] at key
    have h3 : (σ ω - ω) * herm σ x (f₂ y) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hω
    · exact h0
  have hf₂ : f₂ = 0 := LinearMap.ext fun y => by
    show f₂ y = 0
    apply eq_zero_of_herm σ
    intro z
    rw [herm_conj σ hσ z (f₂ y), hA z y, map_zero]
  refine ⟨LinearMap.ext fun x => ?_, hf₂⟩
  rw [hf₁, hf₂]
  simp

theorem card_sq_le_of_separating {ω : F} (hω : σ ω ≠ ω) (hσ : ∀ c, σ (σ c) = c) {r : ℕ}
    (t : Fin r → (Fin 4 → F)) (U' : Submodule F (Fin 4 → F))
    (S : AddSubgroup (Module.End F (Fin 4 → F))) (hS : ∀ f ∈ S, IsSelfAdj σ f)
    (hmaps : ∀ f ∈ S, ∀ i, f (t i) ∈ U')
    (hsep : ∀ f₁ ∈ S, ∀ f₂ ∈ S, (∀ i, (f₁ + ω • f₂) (t i) = 0) → f₁ + ω • f₂ = 0) :
    Nat.card ↥S * Nat.card ↥S ≤ Nat.card ↥U' ^ r := by
  let Φ : ↥S × ↥S → (Fin r → ↥U') := fun p i =>
    ⟨(p.1.1 + ω • p.2.1) (t i), by
      rw [LinearMap.add_apply, LinearMap.smul_apply]
      exact U'.add_mem (hmaps _ p.1.2 i) (U'.smul_mem _ (hmaps _ p.2.2 i))⟩
  have hΦ : Function.Injective Φ := by
    intro p q hpq
    have hi : ∀ i, (p.1.1 + ω • p.2.1) (t i) = (q.1.1 + ω • q.2.1) (t i) := fun i =>
      congrArg Subtype.val (congrFun hpq i)
    have hd : ((p.1.1 - q.1.1) + ω • (p.2.1 - q.2.1)) = 0 := by
      apply hsep (p.1.1 - q.1.1) (S.sub_mem p.1.2 q.1.2) (p.2.1 - q.2.1) (S.sub_mem p.2.2 q.2.2)
      intro i
      have := hi i
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_sub] at this ⊢
      rw [← sub_eq_zero] at this
      rw [← this]
      abel
    have hsp := selfAdj_split hω hσ
      (f₁ := p.1.1 - q.1.1) (f₂ := p.2.1 - q.2.1)
      (by
        intro x y
        simp only [LinearMap.sub_apply, herm_sub_left, herm_sub_right,
          hS _ p.1.2 x y, hS _ q.1.2 x y])
      (by
        intro x y
        simp only [LinearMap.sub_apply, herm_sub_left, herm_sub_right,
          hS _ p.2.2 x y, hS _ q.2.2 x y]) hd
    exact Prod.ext (Subtype.ext (sub_eq_zero.mp hsp.1)) (Subtype.ext (sub_eq_zero.mp hsp.2))
  have := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this

@[expose] def nilEnd (a : SUid σ 4) : Module.End F (Fin 4 → F) where
  toFun x := a • x - x
  map_add' x y := by simp only [smul_add]; abel
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_comm a c x, smul_sub]

@[simp] theorem nilEnd_apply (a : SUid σ 4) (x : Fin 4 → F) : nilEnd a x = a • x - x := rfl

@[expose] def JJ (E : Subgroup (SUid σ 4)) : Submodule F (Module.End F (Fin 4 → F)) where
  carrier := {f | (∀ x, f x ∈ commSp E) ∧ (∀ x ∈ fixSp E, f x = 0) ∧
    ∀ a ∈ E, ∀ x, f (a • x) = a • f x}
  add_mem' := fun {f g} hf hg =>
    ⟨fun x => (commSp E).add_mem (hf.1 x) (hg.1 x),
     fun x hx => by simp [hf.2.1 x hx, hg.2.1 x hx],
     fun a ha x => by simp [hf.2.2 a ha x, hg.2.2 a ha x, smul_add]⟩
  zero_mem' := ⟨fun x => (commSp E).zero_mem, fun x _ => rfl, fun a _ x => by simp⟩
  smul_mem' := fun c f hf =>
    ⟨fun x => (commSp E).smul_mem c (hf.1 x),
     fun x hx => by simp [hf.2.1 x hx],
     fun a ha x => by simp [hf.2.2 a ha x, smul_comm a c]⟩

@[expose] def SS (E : Subgroup (SUid σ 4)) : AddSubgroup (Module.End F (Fin 4 → F)) where
  carrier := {f | f ∈ JJ E ∧ IsSelfAdj σ f}
  add_mem' := fun {f g} hf hg => ⟨add_mem hf.1 hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨zero_mem _, isSelfAdj_zero⟩
  neg_mem' := fun {f} hf => ⟨neg_mem hf.1, hf.2.neg⟩

theorem nilEnd_mem_SS {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {a : SUid σ 4} (ha : a ∈ E) :
    nilEnd a ∈ SS E := by
  refine ⟨⟨fun x => sub_mem_commSp ha x, fun x hx => ?_, fun b hb x => ?_⟩, fun x y => ?_⟩
  · simp [mem_fixSp.mp hx a ha]
  · simp only [nilEnd_apply, smul_sub]
    rw [← mul_smul, ← mul_smul, hEc a ha b hb]
  · exact herm_nil (hE2 a ha) x y

theorem card_le_card_SS {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : Nat.card ↥E ≤ Nat.card ↥(SS E) := by
  haveI : Finite (Module.End F (Fin 4 → F)) :=
    Finite.of_injective (fun f : Module.End F (Fin 4 → F) => (f : (Fin 4 → F) → (Fin 4 → F)))
      DFunLike.coe_injective
  refine Nat.card_le_card_of_injective (fun a => ⟨nilEnd (a : SUid σ 4), nilEnd_mem_SS hE2 hEc a.2⟩) ?_
  intro a b hab
  have h : nilEnd (a : SUid σ 4) = nilEnd (b : SUid σ 4) := congrArg Subtype.val hab
  refine Subtype.ext (ext_smul σ fun x => ?_)
  have := LinearMap.congr_fun h x
  simp only [nilEnd_apply] at this
  exact sub_left_injective this

theorem JJ_eq_zero_of_family {E : Subgroup (SUid σ 4)} {r : ℕ} (t : Fin r → (Fin 4 → F))
    (ht : Submodule.span F (Set.range t) ⊔ fixSp E = ⊤) {g : Module.End F (Fin 4 → F)}
    (hg : g ∈ JJ E) (h0 : ∀ i, g (t i) = 0) : g = 0 := by
  have h1 : ∀ s ∈ Submodule.span F (Set.range t), g s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact h0 i
    | zero => exact map_zero g
    | add y y' _ _ h1 h2 => rw [map_add, h1, h2, add_zero]
    | smul c y _ h1 => rw [map_smul, h1, smul_zero]
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span F (Set.range t) ⊔ fixSp E := by rw [ht]; trivial
  obtain ⟨s, hs, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, h1 s hs, hg.2.1 k hk, add_zero]
  rfl

theorem exists_family (K : Submodule F (Fin 4 → F)) :
    ∃ t : Fin (Module.finrank F ((Fin 4 → F) ⧸ K)) → (Fin 4 → F),
      Submodule.span F (Set.range t) ⊔ K = ⊤ := by
  let b := Module.finBasis F ((Fin 4 → F) ⧸ K)
  choose t ht using fun i => Submodule.Quotient.mk_surjective K (b i)
  refine ⟨t, eq_top_iff.mpr fun x _ => ?_⟩
  set s : Fin 4 → F := ∑ i, (b.repr (K.mkQ x) i) • t i with hs
  have hmk : K.mkQ s = K.mkQ x := by
    rw [hs, map_sum]
    simp only [map_smul]
    have : ∀ i, K.mkQ (t i) = b i := fun i => ht i
    simp only [this]
    exact b.sum_repr _
  have hxs : x - s ∈ K := (Submodule.Quotient.eq K).mp hmk.symm
  have hx : x = s + (x - s) := by abel
  rw [hx]
  exact Submodule.add_mem_sup
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hxs

end Count

end CFSG.LocalAnalysis.RankThreeUC
