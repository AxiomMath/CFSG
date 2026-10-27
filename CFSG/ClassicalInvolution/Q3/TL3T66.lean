module

public import CFSG.ClassicalInvolution.Q3.TL3T65

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg

open Equiv Equiv.Perm CFSG.ComponentClassification.PresentationLocal

variable {m N k : ℕ}

theorem perm_apply_inv {α : Type*} (π : Perm α) (x : α) : π (π⁻¹ x) = x := π.apply_symm_apply x

theorem perm_inv_apply {α : Type*} (π : Perm α) (x : α) : π⁻¹ (π x) = x := π.symm_apply_apply x

theorem exists_perm_two {α : Type*} [DecidableEq α] {a b x y : α} (hab : a ≠ b) (hxy : x ≠ y) :
    ∃ π : Perm α, π a = x ∧ π b = y := by
  have hy' : swap a x y ≠ a := by
    intro h
    have := congrArg (swap a x) h
    rw [swap_apply_self, swap_apply_left] at this
    exact hxy this.symm
  refine ⟨swap a x * swap b (swap a x y), ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab hy'.symm, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_self]

theorem extPerm_trans (c : Fin k ↪ Fin N) (ε : Fin N ↪ Fin m) (τ : Perm (Fin k)) :
    extPerm ε (extPerm c τ) = extPerm (c.trans ε) τ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range (c.trans ε)
  · obtain ⟨i, rfl⟩ := hx
    rw [extPerm_apply_mem (c.trans ε) τ i]
    show extPerm ε (extPerm c τ) (ε (c i)) = ε (c (τ i))
    rw [extPerm_apply_mem ε, extPerm_apply_mem c]
  · rw [extPerm_apply_not_mem (c.trans ε) τ hx]
    by_cases hy : x ∈ Set.range ε
    · obtain ⟨y, rfl⟩ := hy
      have hyc : y ∉ Set.range c := by
        rintro ⟨i, rfl⟩
        exact hx ⟨i, rfl⟩
      rw [extPerm_apply_mem ε, extPerm_apply_not_mem c τ hyc]
    · rw [extPerm_apply_not_mem ε _ hy]

theorem extPerm_conj (ε : Fin N ↪ Fin m) (ρ : Perm (Fin N)) (π : Perm (Fin m))
    (σ : Perm (Fin N)) :
    extPerm (ρ.toEmbedding.trans (ε.trans π.toEmbedding)) σ = π * extPerm ε (ρ * σ * ρ⁻¹) * π⁻¹ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range (ρ.toEmbedding.trans (ε.trans π.toEmbedding))
  · obtain ⟨i, rfl⟩ := hx
    rw [extPerm_apply_mem]
    show π (ε (ρ (σ i))) = (π * extPerm ε (ρ * σ * ρ⁻¹) * π⁻¹) (π (ε (ρ i)))
    rw [Perm.mul_apply, Perm.mul_apply, perm_inv_apply, extPerm_apply_mem]
    simp
  · rw [extPerm_apply_not_mem _ _ hx, Perm.mul_apply, Perm.mul_apply]
    have hy : π⁻¹ x ∉ Set.range ε := by
      rintro ⟨y, hy⟩
      apply hx
      refine ⟨ρ⁻¹ y, ?_⟩
      show π (ε (ρ (ρ⁻¹ y))) = x
      rw [perm_apply_inv, hy, perm_apply_inv]
    rw [extPerm_apply_not_mem ε _ hy, perm_apply_inv]

theorem exists_hom_of_two_charts_gen {A : Type*} [Group A] (hm : 3 ≤ m) (hN : 3 ≤ N)
    (ε₁ ε₂ : Fin N ↪ Fin m) {o e q₁ q₂ a' c p₁ p₂ : Fin m}
    (ho₁ : o ∈ Set.range ε₁) (ho₂ : o ∈ Set.range ε₂) (he₁ : e ∈ Set.range ε₁)
    (he₂ : e ∈ Set.range ε₂)
    (hr₁ : ∀ x, x ∈ Set.range ε₁ ↔ x ≠ p₁ ∧ x ≠ p₂)
    (hr₂ : ∀ x, x ∈ Set.range ε₂ ↔ x ≠ q₁ ∧ x ≠ q₂)
    {T₁ T₂ : Set (Fin m)} (hT : Disjoint T₁ T₂)
    (hq₁ : q₁ ∈ T₁) (hq₂ : q₂ ∈ T₁) (hoT : o ∈ T₁) (ha' : a' ∈ T₁)
    (heT : e ∈ T₂) (hc : c ∈ T₂) (hp₁ : p₁ ∈ T₂) (hp₂ : p₂ ∈ T₂)
    (ha'o : a' ≠ o) (ha'q₁ : a' ≠ q₁) (ha'q₂ : a' ≠ q₂)
    (hce : c ≠ e) (hcp₁ : c ≠ p₁) (hcp₂ : c ≠ p₂)
    (f₁ f₂ : alternatingGroup (Fin N) →* A)
    (hagree : ∀ σ σ', altExt ε₁ σ = altExt ε₂ σ' → f₁ σ = f₂ σ')
    (hcross : ∀ σ σ' : alternatingGroup (Fin N), (∀ x ∉ T₁, extPerm ε₁ (σ : Perm (Fin N)) x = x) →
      (∀ x ∉ T₂, extPerm ε₂ (σ' : Perm (Fin N)) x = x) → f₁ σ * f₂ σ' = f₂ σ' * f₁ σ) :
    ∃ f : alternatingGroup (Fin m) →* A, f.comp (altExt ε₁) = f₁ ∧ f.comp (altExt ε₂) = f₂ := by
  classical
  have hoe : o ≠ e := fun h => Set.disjoint_left.mp hT hoT (h ▸ heT)
  have h01m : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  have h01N : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp)
  obtain ⟨π', hπ'0, hπ'1⟩ := exists_perm_two h01m hoe
  obtain ⟨i₁, hi₁⟩ := ho₁
  obtain ⟨j₁, hj₁⟩ := he₁
  obtain ⟨i₂, hi₂⟩ := ho₂
  obtain ⟨j₂, hj₂⟩ := he₂
  have hij₁ : i₁ ≠ j₁ := fun h => hoe (by rw [← hi₁, ← hj₁, h])
  have hij₂ : i₂ ≠ j₂ := fun h => hoe (by rw [← hi₂, ← hj₂, h])
  obtain ⟨ρ₁, hρ₁0, hρ₁1⟩ := exists_perm_two h01N hij₁
  obtain ⟨ρ₂, hρ₂0, hρ₂1⟩ := exists_perm_two h01N hij₂
  set π := π'⁻¹ with hπ
  have hπo : π o = ⟨0, by omega⟩ := by rw [hπ, ← hπ'0, perm_inv_apply]
  have hπe : π e = ⟨1, by omega⟩ := by rw [hπ, ← hπ'1, perm_inv_apply]
  set ε₁' := ρ₁.toEmbedding.trans (ε₁.trans π.toEmbedding) with hε₁'
  set ε₂' := ρ₂.toEmbedding.trans (ε₂.trans π.toEmbedding) with hε₂'
  have hε₁'a : ∀ i, ε₁' i = π (ε₁ (ρ₁ i)) := fun i => rfl
  have hε₂'a : ∀ i, ε₂' i = π (ε₂ (ρ₂ i)) := fun i => rfl
  have h₁0 : ε₁' ⟨0, by omega⟩ = ⟨0, by omega⟩ := by rw [hε₁'a, hρ₁0, hi₁, hπo]
  have h₁1 : ε₁' ⟨1, by omega⟩ = ⟨1, by omega⟩ := by rw [hε₁'a, hρ₁1, hj₁, hπe]
  have h₂0 : ε₂' ⟨0, by omega⟩ = ⟨0, by omega⟩ := by rw [hε₂'a, hρ₂0, hi₂, hπo]
  have h₂1 : ε₂' ⟨1, by omega⟩ = ⟨1, by omega⟩ := by rw [hε₂'a, hρ₂1, hj₂, hπe]
  have hrange : ∀ (ε : Fin N ↪ Fin m) (ρ : Perm (Fin N)) (x : Fin m),
      x ∈ Set.range (ρ.toEmbedding.trans (ε.trans π.toEmbedding)) ↔ π⁻¹ x ∈ Set.range ε := by
    intro ε ρ x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ρ i, by
        show ε (ρ i) = π⁻¹ (π (ε (ρ i)))
        rw [perm_inv_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨ρ⁻¹ y, ?_⟩
      show π (ε (ρ (ρ⁻¹ y))) = x
      rw [perm_apply_inv, hy, perm_apply_inv]
  have hr₁' : ∀ x, x ∈ Set.range ε₁' ↔ x ≠ π p₁ ∧ x ≠ π p₂ := by
    intro x
    rw [hrange, hr₁]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, perm_inv_apply]),
        fun h => h2 (by rw [h, perm_inv_apply])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [← h, perm_apply_inv]),
        fun h => h2 (by rw [← h, perm_apply_inv])⟩
  have hr₂' : ∀ x, x ∈ Set.range ε₂' ↔ x ≠ π q₁ ∧ x ≠ π q₂ := by
    intro x
    rw [hrange, hr₂]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, perm_inv_apply]),
        fun h => h2 (by rw [h, perm_inv_apply])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [← h, perm_apply_inv]),
        fun h => h2 (by rw [← h, perm_apply_inv])⟩
  have hT' : Disjoint (π '' T₁) (π '' T₂) :=
    (Set.disjoint_image_iff π.injective).mpr hT
  have hmem : ∀ {x : Fin m} {T : Set (Fin m)}, x ∈ T → π x ∈ π '' T := fun hx => ⟨_, hx, rfl⟩
  set κ₁ : alternatingGroup (Fin N) →* alternatingGroup (Fin N) :=
    (MulAut.conjNormal ρ₁).toMonoidHom with hκ₁
  set κ₂ : alternatingGroup (Fin N) →* alternatingGroup (Fin N) :=
    (MulAut.conjNormal ρ₂).toMonoidHom with hκ₂
  have hκ₁a : ∀ σ : alternatingGroup (Fin N),
      ((κ₁ σ : alternatingGroup (Fin N)) : Perm (Fin N)) = ρ₁ * σ * ρ₁⁻¹ := fun σ =>
    MulAut.conjNormal_apply ρ₁ σ
  have hκ₂a : ∀ σ : alternatingGroup (Fin N),
      ((κ₂ σ : alternatingGroup (Fin N)) : Perm (Fin N)) = ρ₂ * σ * ρ₂⁻¹ := fun σ =>
    MulAut.conjNormal_apply ρ₂ σ
  have key₁ : ∀ σ : alternatingGroup (Fin N),
      extPerm ε₁' σ = π * extPerm ε₁ (κ₁ σ : Perm (Fin N)) * π⁻¹ := fun σ => by
    rw [hκ₁a]
    exact extPerm_conj ε₁ ρ₁ π σ
  have key₂ : ∀ σ : alternatingGroup (Fin N),
      extPerm ε₂' σ = π * extPerm ε₂ (κ₂ σ : Perm (Fin N)) * π⁻¹ := fun σ => by
    rw [hκ₂a]
    exact extPerm_conj ε₂ ρ₂ π σ
  have hfix : ∀ {ε : Fin N ↪ Fin m} {τ : Perm (Fin N)} {T : Set (Fin m)},
      (∀ x ∉ π '' T, (π * extPerm ε τ * π⁻¹) x = x) → ∀ y ∉ T, extPerm ε τ y = y := by
    intro ε τ T h y hy
    have hy' : π y ∉ π '' T := by
      rintro ⟨z, hz, hzy⟩
      exact hy (π.injective hzy ▸ hz)
    have := h (π y) hy'
    rw [Perm.mul_apply, Perm.mul_apply, perm_inv_apply] at this
    exact π.injective this
  obtain ⟨f', hf'₁, hf'₂⟩ := exists_hom_of_two_charts hm hN ε₁' ε₂' h₁0 h₁1 h₂0 h₂1
    (q₁ := π q₁) (q₂ := π q₂) (a' := π a') (c := π c) (p₁ := π p₁) (p₂ := π p₂) hr₁' hr₂' hT'
    (hmem hq₁) (hmem hq₂) (hπo ▸ hmem hoT) (hmem ha') (hπe ▸ hmem heT) (hmem hc) (hmem hp₁)
    (hmem hp₂) (fun h => ha'o (π.injective (h.trans hπo.symm)))
    (fun h => ha'q₁ (π.injective h)) (fun h => ha'q₂ (π.injective h))
    (fun h => hce (π.injective (h.trans hπe.symm)))
    (fun h => hcp₁ (π.injective h)) (fun h => hcp₂ (π.injective h))
    (f₁.comp κ₁) (f₂.comp κ₂)
    (by
      intro σ σ' h
      apply hagree
      apply Subtype.ext
      rw [altExt_coe, altExt_coe]
      have e := congrArg Subtype.val h
      rw [altExt_coe, altExt_coe, key₁, key₂] at e
      exact mul_left_cancel (mul_right_cancel e))
    (by
      intro σ σ' h1 h2
      refine hcross _ _ (hfix ?_) (hfix ?_)
      · intro x hx
        rw [← key₁]
        exact h1 x hx
      · intro x hx
        rw [← key₂]
        exact h2 x hx)
  set κ : alternatingGroup (Fin m) →* alternatingGroup (Fin m) :=
    (MulAut.conjNormal π).toMonoidHom with hκ
  refine ⟨f'.comp κ, ?_, ?_⟩
  · ext σ
    have h1 : (((MulAut.conjNormal ρ₁⁻¹).toMonoidHom σ : alternatingGroup (Fin N)) :
        Perm (Fin N)) = ρ₁⁻¹ * σ * ρ₁⁻¹⁻¹ := MulAut.conjNormal_apply _ _
    have h3 : ρ₁ * (ρ₁⁻¹ * (σ : Perm (Fin N)) * ρ₁⁻¹⁻¹) * ρ₁⁻¹ = σ := by group
    have e : κ (altExt ε₁ σ) = altExt ε₁' ((MulAut.conjNormal ρ₁⁻¹).toMonoidHom σ) := by
      apply Subtype.ext
      have h2 : ((κ (altExt ε₁ σ) : alternatingGroup (Fin m)) : Perm (Fin m)) =
          π * extPerm ε₁ σ * π⁻¹ := MulAut.conjNormal_apply _ _
      rw [h2, altExt_coe, key₁, hκ₁a, h1, h3]
    show f' (κ (altExt ε₁ σ)) = f₁ σ
    rw [e]
    have := DFunLike.congr_fun hf'₁ ((MulAut.conjNormal ρ₁⁻¹).toMonoidHom σ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at this
    rw [this]
    congr 1
    apply Subtype.ext
    rw [hκ₁a, h1, h3]
  · ext σ
    have h1 : (((MulAut.conjNormal ρ₂⁻¹).toMonoidHom σ : alternatingGroup (Fin N)) :
        Perm (Fin N)) = ρ₂⁻¹ * σ * ρ₂⁻¹⁻¹ := MulAut.conjNormal_apply _ _
    have h3 : ρ₂ * (ρ₂⁻¹ * (σ : Perm (Fin N)) * ρ₂⁻¹⁻¹) * ρ₂⁻¹ = σ := by group
    have e : κ (altExt ε₂ σ) = altExt ε₂' ((MulAut.conjNormal ρ₂⁻¹).toMonoidHom σ) := by
      apply Subtype.ext
      have h2 : ((κ (altExt ε₂ σ) : alternatingGroup (Fin m)) : Perm (Fin m)) =
          π * extPerm ε₂ σ * π⁻¹ := MulAut.conjNormal_apply _ _
      rw [h2, altExt_coe, key₂, hκ₂a, h1, h3]
    show f' (κ (altExt ε₂ σ)) = f₂ σ
    rw [e]
    have := DFunLike.congr_fun hf'₂ ((MulAut.conjNormal ρ₂⁻¹).toMonoidHom σ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at this
    rw [this]
    congr 1
    apply Subtype.ext
    rw [hκ₂a, h1, h3]

theorem altExt_trans (c : Fin k ↪ Fin N) (ε : Fin N ↪ Fin m) (τ : alternatingGroup (Fin k)) :
    altExt ε (altExt c τ) = altExt (c.trans ε) τ :=
  Subtype.ext (extPerm_trans c ε τ)

end CFSG.ClassicalInvolution.Q3.TC.Thin.Amalg

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {n : ℕ} {I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n} {D : PairChart Ω K J I}

@[expose] def globEmb₁ (n : ℕ) : Fin (n + 2) ↪ Fin (n + 4) := Fin.castLEEmb (by omega)

theorem globEmb₁_val (x : Fin (n + 2)) : ((globEmb₁ n x : Fin (n + 4)) : ℕ) = x := rfl

namespace GlueData

variable (E : GlueData D)

open Classical in
@[expose] noncomputable def emb₂Fun : Fin (n + 2) → Fin (n + 4) := fun y =>
  if h : y ∈ Set.range E.c₂ then (globEmb₁ n) (E.c₁ h.choose)
  else if y = D.ι D.a' then ⟨n + 2, by omega⟩ else ⟨n + 3, by omega⟩

theorem emb₂Fun_c₂ (i : Fin n) : E.emb₂Fun (E.c₂ i) = (globEmb₁ n) (E.c₁ i) := by
  have h : E.c₂ i ∈ Set.range E.c₂ := ⟨i, rfl⟩
  have hs := h.choose_spec
  simp only [emb₂Fun, h, ↓reduceDIte]
  congr 2
  exact E.c₂.injective hs

theorem emb₂Fun_a' : E.emb₂Fun (D.ι D.a') = ⟨n + 2, by omega⟩ := by
  have h : D.ι D.a' ∉ Set.range E.c₂ := fun h' => ((E.hc₂ _).mp h').1 rfl
  simp only [emb₂Fun, h, ↓reduceDIte, ↓reduceIte]

theorem emb₂Fun_c' : E.emb₂Fun (D.ι D.c') = ⟨n + 3, by omega⟩ := by
  have h : D.ι D.c' ∉ Set.range E.c₂ := fun h' => ((E.hc₂ _).mp h').2 rfl
  have h' : D.ι D.c' ≠ D.ι D.a' := D.ι.injective.ne D.hac'.symm
  simp only [emb₂Fun, h, h', ↓reduceDIte, ↓reduceIte]

theorem cases₂ (y : Fin (n + 2)) : (∃ i, y = E.c₂ i) ∨ y = D.ι D.a' ∨ y = D.ι D.c' := by
  by_cases h : y ∈ Set.range E.c₂
  · obtain ⟨i, rfl⟩ := h
    exact Or.inl ⟨i, rfl⟩
  · rcases em (y = D.ι D.a') with h1 | h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      by_contra h2
      exact h ((E.hc₂ y).mpr ⟨h1, h2⟩)

theorem cases₁ (x : Fin (n + 2)) : (∃ i, x = E.c₁ i) ∨ x = D.ι D.a ∨ x = D.ι D.c := by
  by_cases h : x ∈ Set.range E.c₁
  · obtain ⟨i, rfl⟩ := h
    exact Or.inl ⟨i, rfl⟩
  · rcases em (x = D.ι D.a) with h1 | h1
    · exact Or.inr (Or.inl h1)
    · refine Or.inr (Or.inr ?_)
      by_contra h2
      exact h ((E.hc₁ x).mpr ⟨h1, h2⟩)

theorem emb₂Fun_injective : Function.Injective E.emb₂Fun := by
  have hval : ∀ i, (((globEmb₁ n) (E.c₁ i) : Fin (n + 4)) : ℕ) < n + 2 := fun i => (E.c₁ i).2
  intro y y' hyy
  rcases E.cases₂ y with ⟨i, rfl⟩ | rfl | rfl <;> rcases E.cases₂ y' with ⟨i', rfl⟩ | rfl | rfl
  · rw [E.emb₂Fun_c₂, E.emb₂Fun_c₂] at hyy
    rw [E.c₁.injective ((globEmb₁ n).injective hyy)]
  · rw [E.emb₂Fun_c₂, E.emb₂Fun_a'] at hyy
    exact absurd (congrArg Fin.val hyy) (by have := hval i; simp at this ⊢; omega)
  · rw [E.emb₂Fun_c₂, E.emb₂Fun_c'] at hyy
    exact absurd (congrArg Fin.val hyy) (by have := hval i; simp at this ⊢; omega)
  · rw [E.emb₂Fun_c₂, E.emb₂Fun_a'] at hyy
    exact absurd (congrArg Fin.val hyy).symm (by have := hval i'; simp at this ⊢; omega)
  · rfl
  · rw [E.emb₂Fun_a', E.emb₂Fun_c'] at hyy
    exact absurd (congrArg Fin.val hyy) (by simp)
  · rw [E.emb₂Fun_c₂, E.emb₂Fun_c'] at hyy
    exact absurd (congrArg Fin.val hyy).symm (by have := hval i'; simp at this ⊢; omega)
  · rw [E.emb₂Fun_c', E.emb₂Fun_a'] at hyy
    exact absurd (congrArg Fin.val hyy) (by simp)
  · rfl

@[expose] noncomputable def emb₂ : Fin (n + 2) ↪ Fin (n + 4) := ⟨E.emb₂Fun, E.emb₂Fun_injective⟩

theorem emb₂_apply (y : Fin (n + 2)) : E.emb₂ y = E.emb₂Fun y := rfl

theorem range_emb₁ (x : Fin (n + 4)) :
    x ∈ Set.range (globEmb₁ n) ↔ x ≠ ⟨n + 2, by omega⟩ ∧ x ≠ ⟨n + 3, by omega⟩ := by
  constructor
  · rintro ⟨y, rfl⟩
    have := y.2
    refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    · have := congrArg Fin.val h
      simp only [globEmb₁_val] at this
      omega
  · rintro ⟨h1, h2⟩
    have h1' : (x : ℕ) ≠ n + 2 := fun h => h1 (Fin.ext h)
    have h2' : (x : ℕ) ≠ n + 3 := fun h => h2 (Fin.ext h)
    have hx := x.2
    exact ⟨⟨x, by omega⟩, Fin.ext rfl⟩

theorem range_emb₂ (x : Fin (n + 4)) :
    x ∈ Set.range E.emb₂ ↔ x ≠ (globEmb₁ n) (D.ι D.a) ∧ x ≠ (globEmb₁ n) (D.ι D.c) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [emb₂_apply]
    rcases E.cases₂ y with ⟨i, rfl⟩ | rfl | rfl
    · rw [E.emb₂Fun_c₂]
      have := (E.hc₁ (E.c₁ i)).mp ⟨i, rfl⟩
      exact ⟨fun h => this.1 ((globEmb₁ n).injective h), fun h => this.2 ((globEmb₁ n).injective h)⟩
    · rw [E.emb₂Fun_a']
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · have := congrArg Fin.val h
        rw [globEmb₁_val] at this
        have := (D.ι D.a).2
        have := (D.ι D.c).2
        simp at *
        omega
    · rw [E.emb₂Fun_c']
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · have := congrArg Fin.val h
        rw [globEmb₁_val] at this
        have := (D.ι D.a).2
        have := (D.ι D.c).2
        simp at *
        omega
  · rintro ⟨h1, h2⟩
    by_cases hx : x ∈ Set.range (globEmb₁ n)
    · obtain ⟨x', rfl⟩ := hx
      have h1' : x' ≠ D.ι D.a := fun h => h1 (by rw [h])
      have h2' : x' ≠ D.ι D.c := fun h => h2 (by rw [h])
      obtain ⟨i, rfl⟩ := (E.hc₁ x').mpr ⟨h1', h2'⟩
      exact ⟨E.c₂ i, by rw [emb₂_apply, E.emb₂Fun_c₂]⟩
    · rw [range_emb₁] at hx
      by_cases h3 : x = ⟨n + 2, by omega⟩
      · exact ⟨D.ι D.a', by rw [emb₂_apply, E.emb₂Fun_a', h3]⟩
      · have h4 : x = ⟨n + 3, by omega⟩ := by
          by_contra h4
          exact hx ⟨h3, h4⟩
        exact ⟨D.ι D.c', by rw [emb₂_apply, E.emb₂Fun_c', h4]⟩

theorem emb₂_c₂ (i : Fin n) : E.emb₂ (E.c₂ i) = (globEmb₁ n) (E.c₁ i) := E.emb₂Fun_c₂ i

theorem trans_eq : E.c₁.trans (globEmb₁ n) = E.c₂.trans E.emb₂ := by
  ext i
  exact congrArg Fin.val (E.emb₂_c₂ i).symm

theorem eq_of_altExt_eq {σ σ' : alternatingGroup (Fin (n + 2))}
    (h : altExt (globEmb₁ n) σ = altExt E.emb₂ σ') :
    ∃ τ : alternatingGroup (Fin n), altExt E.c₁ τ = σ ∧ altExt E.c₂ τ = σ' := by
  have hv := congrArg Subtype.val h
  rw [altExt_coe, altExt_coe] at hv
  have hσ : ∀ x, x ∉ Set.range E.c₁ → (σ : Equiv.Perm (Fin (n + 2))) x = x := by
    intro x hx
    have hx' : x = D.ι D.a ∨ x = D.ι D.c := by
      rcases E.cases₁ x with ⟨i, rfl⟩ | h' | h'
      · exact absurd ⟨i, rfl⟩ hx
      · exact Or.inl h'
      · exact Or.inr h'
    have hq : (globEmb₁ n) x ∉ Set.range E.emb₂ := by
      rw [E.range_emb₂]
      rintro ⟨h1, h2⟩
      rcases hx' with rfl | rfl
      · exact h1 rfl
      · exact h2 rfl
    have e1 := congrArg (fun π : Equiv.Perm (Fin (n + 4)) => π ((globEmb₁ n) x)) hv
    rw [extPerm_apply_mem, extPerm_apply_not_mem _ _ hq] at e1
    exact (globEmb₁ n).injective e1
  have hσ' : ∀ x, x ∉ Set.range E.c₂ → (σ' : Equiv.Perm (Fin (n + 2))) x = x := by
    intro x hx
    have hx' : x = D.ι D.a' ∨ x = D.ι D.c' := by
      rcases E.cases₂ x with ⟨i, rfl⟩ | h' | h'
      · exact absurd ⟨i, rfl⟩ hx
      · exact Or.inl h'
      · exact Or.inr h'
    have hq : E.emb₂ x ∉ Set.range (globEmb₁ n) := by
      rw [range_emb₁]
      rintro ⟨h1, h2⟩
      rcases hx' with rfl | rfl
      · exact h1 (E.emb₂Fun_a')
      · exact h2 (E.emb₂Fun_c')
    have e1 := congrArg (fun π : Equiv.Perm (Fin (n + 4)) => π (E.emb₂ x)) hv
    rw [extPerm_apply_mem, extPerm_apply_not_mem _ _ hq] at e1
    exact E.emb₂.injective e1.symm
  obtain ⟨τ, rfl⟩ := exists_altExt_eq E.c₁ σ hσ
  obtain ⟨τ', rfl⟩ := exists_altExt_eq E.c₂ σ' hσ'
  refine ⟨τ, rfl, ?_⟩
  rw [altExt_trans, altExt_trans, trans_eq] at h
  rw [altExt_injective _ h]

theorem exists_glue (hn : 5 ≤ n)
    (hcross : ∀ σ σ' : alternatingGroup (Fin (n + 2)),
      (∀ x ∉ D.γ.map D.ι, (σ : Equiv.Perm (Fin (n + 2))) x = x) →
      (∀ x ∉ D.γ.map D.ι, (σ' : Equiv.Perm (Fin (n + 2))) x = x) →
      (E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹) *
          (D.t * ((E.s₁ σ' : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) =
        (D.t * ((E.s₁ σ' : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹) *
          (E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹)) :
    ∃ f : alternatingGroup (Fin (n + 4)) →* G,
      (∀ σ, f (altExt (globEmb₁ n) σ) = E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹) ∧
      ∀ σ, f (altExt E.emb₂ σ) = D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹ := by
  classical
  set β₁ := D.γ.map D.ι with hβ₁
  have hβ₁c : β₁.card = 4 := by rw [hβ₁, Finset.card_map]; exact D.hγ
  have hmem : ∀ {x : Fin n}, x ∈ D.γ → D.ι x ∈ β₁ := fun hx => Finset.mem_map_of_mem _ hx
  have hsub₁ : ({D.ι D.a, D.ι D.c} : Finset (Fin (n + 2))) ⊆ β₁ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmem D.ha
    · rw [Finset.mem_singleton.mp hx]
      exact hmem D.hc
  have hsub₂ : ({D.ι D.a', D.ι D.c'} : Finset (Fin (n + 2))) ⊆ β₁ := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmem D.ha'
    · rw [Finset.mem_singleton.mp hx]
      exact hmem D.hc'
  obtain ⟨x₁, x₂, hx₁₂, hx⟩ := Finset.card_eq_two.mp (show (β₁ \ {D.ι D.a, D.ι D.c}).card = 2 by
    rw [Finset.card_sdiff_of_subset hsub₁, hβ₁c, Finset.card_pair (D.ι.injective.ne D.hac)])
  obtain ⟨y₁, y₂, hy₁₂, hy⟩ := Finset.card_eq_two.mp (show (β₁ \ {D.ι D.a', D.ι D.c'}).card = 2 by
    rw [Finset.card_sdiff_of_subset hsub₂, hβ₁c, Finset.card_pair (D.ι.injective.ne D.hac')])
  have hx₁ : x₁ ∈ β₁ \ {D.ι D.a, D.ι D.c} := by rw [hx]; exact Finset.mem_insert_self _ _
  have hx₂ : x₂ ∈ β₁ \ {D.ι D.a, D.ι D.c} := by
    rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hy₁ : y₁ ∈ β₁ \ {D.ι D.a', D.ι D.c'} := by rw [hy]; exact Finset.mem_insert_self _ _
  have hy₂ : y₂ ∈ β₁ \ {D.ι D.a', D.ι D.c'} := by
    rw [hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx₁ hx₂ hy₁ hy₂
  have hcom₁ : ∀ {x : Fin (n + 2)}, x ≠ D.ι D.a → x ≠ D.ι D.c → (globEmb₁ n) x ∈ Set.range E.emb₂ :=
    fun h1 h2 => (E.range_emb₂ _).mpr ⟨fun h => h1 ((globEmb₁ n).injective h),
      fun h => h2 ((globEmb₁ n).injective h)⟩
  have hcom₂ : ∀ {y : Fin (n + 2)}, y ≠ D.ι D.a' → y ≠ D.ι D.c' → E.emb₂ y ∈ Set.range (globEmb₁ n) := by
    intro y h1 h2
    obtain ⟨i, rfl⟩ := (E.hc₂ y).mpr ⟨h1, h2⟩
    exact ⟨E.c₁ i, (E.emb₂_c₂ i).symm⟩
  have hT : Disjoint ((globEmb₁ n) '' (β₁ : Set (Fin (n + 2)))) (E.emb₂ '' (β₁ : Set (Fin (n + 2)))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    rcases E.cases₂ y with ⟨i, rfl⟩ | rfl | rfl
    · rw [E.emb₂_c₂] at hxy
      have := (globEmb₁ n).injective hxy
      subst this
      exact E.hdisj i hx hy
    · rw [emb₂_apply, E.emb₂Fun_a'] at hxy
      exact ((range_emb₁ _).mp ⟨x, rfl⟩).1 hxy.symm
    · rw [emb₂_apply, E.emb₂Fun_c'] at hxy
      exact ((range_emb₁ _).mp ⟨x, rfl⟩).2 hxy.symm
  set f₁ : alternatingGroup (Fin (n + 2)) →* G :=
    (MulAut.conj E.g).toMonoidHom.comp ((pSpan (centMembers Ω D.u)).subtype.comp E.s₁) with hf₁
  set f₂ : alternatingGroup (Fin (n + 2)) →* G :=
    (MulAut.conj D.t).toMonoidHom.comp ((pSpan (centMembers Ω D.u)).subtype.comp E.s₁) with hf₂
  have hf₁a : ∀ σ, f₁ σ = E.g * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * E.g⁻¹ :=
    fun σ => rfl
  have hf₂a : ∀ σ, f₂ σ = D.t * ((E.s₁ σ : ↥(pSpan (centMembers Ω D.u))) : G) * D.t⁻¹ :=
    fun σ => rfl
  have hsupp₁ : ∀ σ : alternatingGroup (Fin (n + 2)),
      (∀ x ∉ (globEmb₁ n) '' (β₁ : Set (Fin (n + 2))), extPerm (globEmb₁ n) (σ : Equiv.Perm _) x = x) →
      ∀ x ∉ β₁, (σ : Equiv.Perm (Fin (n + 2))) x = x := by
    intro σ h x hx
    have hx' : (globEmb₁ n) x ∉ (globEmb₁ n) '' (β₁ : Set (Fin (n + 2))) := by
      rintro ⟨y, hy, hyx⟩
      exact hx ((globEmb₁ n).injective hyx ▸ hy)
    have := h _ hx'
    rw [extPerm_apply_mem] at this
    exact (globEmb₁ n).injective this
  have hsupp₂ : ∀ σ : alternatingGroup (Fin (n + 2)),
      (∀ x ∉ E.emb₂ '' (β₁ : Set (Fin (n + 2))), extPerm E.emb₂ (σ : Equiv.Perm _) x = x) →
      ∀ x ∉ β₁, (σ : Equiv.Perm (Fin (n + 2))) x = x := by
    intro σ h x hx
    have hx' : E.emb₂ x ∉ E.emb₂ '' (β₁ : Set (Fin (n + 2))) := by
      rintro ⟨y, hy, hyx⟩
      exact hx (E.emb₂.injective hyx ▸ hy)
    have := h _ hx'
    rw [extPerm_apply_mem] at this
    exact E.emb₂.injective this
  obtain ⟨f, hf1, hf2⟩ := exists_hom_of_two_charts_gen (A := G) (by omega) (by omega)
    (globEmb₁ n) E.emb₂ (o := (globEmb₁ n) x₁) (e := E.emb₂ y₁) (q₁ := (globEmb₁ n) (D.ι D.a))
    (q₂ := (globEmb₁ n) (D.ι D.c)) (a' := (globEmb₁ n) x₂) (c := E.emb₂ y₂) (p₁ := ⟨n + 2, by omega⟩)
    (p₂ := ⟨n + 3, by omega⟩) ⟨x₁, rfl⟩ (hcom₁ hx₁.2.1 hx₁.2.2) (hcom₂ hy₁.2.1 hy₁.2.2)
    ⟨y₁, rfl⟩ range_emb₁ E.range_emb₂ hT
    ⟨_, hmem D.ha, rfl⟩ ⟨_, hmem D.hc, rfl⟩ ⟨x₁, hx₁.1, rfl⟩ ⟨x₂, hx₂.1, rfl⟩
    ⟨y₁, hy₁.1, rfl⟩ ⟨y₂, hy₂.1, rfl⟩ ⟨_, hmem D.ha', E.emb₂Fun_a'⟩
    ⟨_, hmem D.hc', E.emb₂Fun_c'⟩
    (fun h => hx₁₂ ((globEmb₁ n).injective h).symm) (fun h => hx₂.2.1 ((globEmb₁ n).injective h))
    (fun h => hx₂.2.2 ((globEmb₁ n).injective h)) (fun h => hy₁₂ (E.emb₂.injective h).symm)
    (fun h => hy₂.2.1 (E.emb₂.injective (h.trans E.emb₂Fun_a'.symm)))
    (fun h => hy₂.2.2 (E.emb₂.injective (h.trans E.emb₂Fun_c'.symm)))
    f₁ f₂
    (by
      intro σ σ' h
      obtain ⟨τ, rfl, rfl⟩ := E.eq_of_altExt_eq h
      rw [hf₁a, hf₂a]
      exact (E.halign τ).symm)
    (by
      intro σ σ' h1 h2
      rw [hf₁a, hf₂a]
      exact hcross σ σ' (hsupp₁ σ h1) (hsupp₂ σ' h2))
  exact ⟨f, fun σ => DFunLike.congr_fun hf1 σ, fun σ => DFunLike.congr_fun hf2 σ⟩

end GlueData

end CFSG.ClassicalInvolution.Q3.TC.Thin
