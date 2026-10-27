module

public import CFSG.LieType.Chevalley.FixedCollection
public import CFSG.LieType.Chevalley.TwistUnipotent
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

@[expose] noncomputable def wordRoots : List (Fin τ.rank) → List (Root τ)
  | [] => []
  | i :: ω => ((coxeterSystem τ).wordProd ω)⁻¹ • simpleRoot τ i :: wordRoots ω

@[expose] def wordRootVecs : List (Fin τ.rank) → List (Fin τ.rank → ℤ)
  | [] => []
  | i :: ω => ω.reverse.foldr (reflect τ) (Pi.single i 1) :: wordRootVecs ω

theorem wordRoots_val : ∀ ω : List (Fin τ.rank),
    (wordRoots ω).map Subtype.val = wordRootVecs (τ := τ) ω
  | [] => rfl
  | i :: ω => by
    rw [wordRoots, List.map_cons, wordRootVecs, wordRoots_val ω, coe_smul_root,
      ← CoxeterSystem.wordProd_reverse, wordProd_smul]
    rfl

theorem wordRoots_spec : ∀ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω →
    ∀ β ∈ wordRoots ω, 0 < height β.1 ∧ height ((coxeterSystem τ).wordProd ω • β).1 < 0
  | [], _, β, hβ => by simp [wordRoots] at hβ
  | i :: ω, hred, β, hβ => by
    have hred' : (coxeterSystem τ).IsReduced ([i] ++ ω) := hred
    obtain ⟨-, hω⟩ := isReduced_left_right_of_append hred'
    have hlen := length_mul_of_isReduced_append hred'
    rw [CoxeterSystem.wordProd_singleton, (coxeterSystem τ).length_simple] at hlen
    have hlen' : (coxeterSystem τ).length (simple τ i * (coxeterSystem τ).wordProd ω) =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) + 1 := by
      rw [hlen, add_comm]
    rcases List.mem_cons.1 hβ with rfl | hβ
    · refine ⟨(length_simple_mul_eq_add_one_iff _ i).1 hlen', ?_⟩
      rw [CoxeterSystem.wordProd_cons, mul_smul, smul_inv_smul, coe_smul_root]
      change height (simple τ i • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0
      rw [simple_smul]
      simp [reflect, height, Pi.single_apply, Tag.cartan_self]
    · obtain ⟨hpos, hneg⟩ := wordRoots_spec ω hω β hβ
      refine ⟨hpos, ?_⟩
      rw [CoxeterSystem.wordProd_cons]
      exact height_simple_mul_smul_neg hlen' hpos hneg

theorem exists_mem_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | _, _, .nil, _, ha => absurd ha List.not_mem_nil
  | _, _, .cons hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, h'⟩ := exists_mem_of_forall₂ h a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

variable {K : Type} [Field K] [Finite K]

theorem eq_of_reverse_prod_eq : ∀ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω →
    ∀ y y' : List (adjointGroup τ K),
      List.Forall₂ (fun g (β : Root τ) => g ∈ (nativeRootSubgroups τ K).X β) y (wordRoots ω) →
      List.Forall₂ (fun g (β : Root τ) => g ∈ (nativeRootSubgroups τ K).X β) y' (wordRoots ω) →
      y.reverse.prod = y'.reverse.prod → y = y'
  | [], _, y, y', hy, hy', _ => by
    rw [wordRoots, List.forall₂_nil_right_iff] at hy hy'
    rw [hy, hy']
  | i :: ω, hred, y, y', hy, hy', h => by
    have hred' : (coxeterSystem τ).IsReduced ([i] ++ ω) := hred
    obtain ⟨-, hω⟩ := isReduced_left_right_of_append hred'
    rw [wordRoots] at hy hy'
    obtain ⟨y₀, ys, hy₀, hys, rfl⟩ := List.forall₂_cons_right_iff.1 hy
    obtain ⟨y₀', ys', hy₀', hys', rfl⟩ := List.forall₂_cons_right_iff.1 hy'
    rw [List.reverse_cons, List.prod_append, List.prod_singleton, List.reverse_cons,
      List.prod_append, List.prod_singleton] at h
    have htail : ∀ zs : List (adjointGroup τ K),
        List.Forall₂ (fun g (β : Root τ) => g ∈ (nativeRootSubgroups τ K).X β) zs
          (wordRoots ω) → zs.reverse.prod ∈ Uminus τ K ((coxeterSystem τ).wordProd ω) := by
      intro zs hzs
      refine list_prod_mem fun g hg => ?_
      rw [List.mem_reverse] at hg
      obtain ⟨β, hβ, hgβ⟩ := exists_mem_of_forall₂ hzs g hg
      obtain ⟨hpos, hneg⟩ := wordRoots_spec ω hω β hβ
      exact mem_Uminus_of_mem_X hpos hneg hgβ
    set m : monomialGroup τ K :=
      ⟨nrep τ K ((coxeterSystem τ).wordProd ω), nrep_mem_monomialGroup τ K _⟩
    have hhead : ∀ g ∈ (nativeRootSubgroups τ K).X
        (((coxeterSystem τ).wordProd ω)⁻¹ • simpleRoot τ i),
        nrep τ K ((coxeterSystem τ).wordProd ω) * g *
          (nrep τ K ((coxeterSystem τ).wordProd ω))⁻¹ ∈ (nativeData τ K).U := by
      intro g hg
      have h1 := RootGroupData.conj_mem (D := nativeData τ K) m hg
      change nrep τ K _ * g * (nrep τ K _)⁻¹ ∈
        (nativeRootSubgroups τ K).X (weylHom τ K m • _) at h1
      rw [weylHom_nrep, smul_inv_smul] at h1
      exact RootGroupData.X_le_U (D := nativeData τ K) (height_simpleRoot_pos i) h1
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_mem_Uminus (htail ys hys) (htail ys' hys')
      (hhead y₀ hy₀) (hhead y₀' hy₀') h
    rw [eq_of_reverse_prod_eq ω hω ys ys' hys hys' h1, h2]

end CFSG.LieType.Chevalley
