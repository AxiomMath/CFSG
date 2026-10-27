module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.Certificates.Kernel.ThDemp.ChainEx

public section

namespace CFSG.StandardType.LieCore.A3E6K

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm iform_add_left iform_add_right
  iform_smul_left iform_smul_right iform_sub_left iform_sub_right iform_self_pos
  iform_self_of_isRoot iform_sq_lt)
open Matrix

abbrev E6V : Type := Fin Tag.E6.rank → ℤ


theorem iform_neg_right (x y : E6V) : iform x (-y) = -iform x y := by
  simp [iform, Finset.sum_neg_distrib]

theorem iform_neg_left (x y : E6V) : iform (-x) y = -iform x y := by
  simp [iform, Finset.sum_neg_distrib]

theorem iform_root_self {γ : E6V} (hγ : IsRoot Tag.E6 γ) : iform γ γ = 2 := by
  obtain ⟨j, h⟩ := iform_self_of_isRoot hγ
  have hs : Tag.E6.symmetrizer j j = 1 := by fin_cases j <;> decide
  rw [h, hs]
  rfl

theorem iform_roots_cases {α β : E6V} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    iform α β = 0 ∨ iform α β = 1 ∨ iform α β = -1 := by
  have h := iform_sq_lt hα hβ hne hne'
  rw [iform_root_self hα, iform_root_self hβ] at h
  have h1 : -2 < iform α β := by nlinarith
  have h2 : iform α β < 2 := by nlinarith
  omega

theorem corootPair_e6 {β : E6V} (hβ : IsRoot Tag.E6 β) (v : E6V) :
    corootPair β v = iform β v := by
  have h := corootPair_mul hβ v
  rw [iform_root_self hβ] at h
  linarith

theorem rootReflection_smul_e6 {β : E6V} (hβ : IsRoot Tag.E6 β) (v : E6V) :
    rootReflection β • v = v - iform β v • β := by
  rw [rootReflection_smul hβ, corootPair_e6 hβ]

theorem isRoot_add {α β : E6V} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β)
    (h : iform α β = -1) : IsRoot Tag.E6 (α + β) := by
  have h' := IsRoot.smul hβ (rootReflection α)
  rw [rootReflection_smul_e6 hα, h, neg_one_smul, sub_neg_eq_add, add_comm] at h'
  exact h'

theorem pair_add (x y : E6V) (c : Fin Tag.E6.rank → ZMod 3) :
    ggLiePair (x + y) c = ggLiePair x c + ggLiePair y c := by
  simp [ggLiePair, add_mul, Finset.sum_add_distrib]

theorem pair_neg (x : E6V) (c : Fin Tag.E6.rank → ZMod 3) :
    ggLiePair (-x) c = -ggLiePair x c := by
  have h := pair_add (-x) x c
  rw [neg_add_cancel] at h
  have h0 : ggLiePair (0 : E6V) c = 0 := by simp [ggLiePair]
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem pair_zsmul (k : ℤ) (x : E6V) (c : Fin Tag.E6.rank → ZMod 3) :
    ggLiePair (k • x) c = k * ggLiePair x c := by
  simp [ggLiePair, Finset.mul_sum, mul_assoc]

theorem pair_sub (x y : E6V) (c : Fin Tag.E6.rank → ZMod 3) :
    ggLiePair (x - y) c = ggLiePair x c - ggLiePair y c := by
  rw [sub_eq_add_neg, pair_add, pair_neg]
  exact (sub_eq_add_neg _ _).symm

@[expose] def pairL (c : Fin Tag.E6.rank → ZMod 3) : E6V →ₗ[ℤ] ZMod 3 where
  toFun x := ggLiePair x c
  map_add' x y := pair_add x y c
  map_smul' k x := by
    rw [pair_zsmul, RingHom.id_apply, zsmul_eq_mul]

section Comp

variable {c₁ c₂ : Fin Tag.E6.rank → ZMod 3} {m : E6V}

theorem mem_comp_of_adj {x δ : E6V} (hx : x ∈ a3Comp Tag.E6 c₁ c₂ m) (hδ : IsRoot Tag.E6 δ)
    (h₁ : ggLiePair δ c₁ = 0) (h₂ : ggLiePair δ c₂ = 0) (hne : iform x δ ≠ 0) :
    δ ∈ a3Comp Tag.E6 c₁ c₂ m := by
  refine ⟨⟨hδ, h₁, h₂⟩, Relation.EqvGen.trans _ _ _ hx.2 (Relation.EqvGen.rel _ _ ?_)⟩
  refine ⟨hx.1, ⟨hδ, h₁, h₂⟩, ?_⟩
  rw [dotProduct_mulVec_eq_iform]
  exact hne

theorem neg_mem_comp {x : E6V} (hx : x ∈ a3Comp Tag.E6 c₁ c₂ m) :
    -x ∈ a3Comp Tag.E6 c₁ c₂ m := by
  obtain ⟨⟨hr, h₁, h₂⟩, -⟩ := id hx
  refine mem_comp_of_adj hx (IsRoot.neg hr) (by rw [pair_neg, h₁]; decide)
    (by rw [pair_neg, h₂]; decide) ?_
  rw [iform_neg_right, iform_root_self hr]
  decide

theorem add_mem_comp {x y : E6V} (hx : x ∈ a3Comp Tag.E6 c₁ c₂ m)
    (hy : y ∈ a3Comp Tag.E6 c₁ c₂ m) (h : iform x y = -1) :
    x + y ∈ a3Comp Tag.E6 c₁ c₂ m := by
  obtain ⟨⟨hxr, hx₁, hx₂⟩, -⟩ := id hx
  obtain ⟨⟨hyr, hy₁, hy₂⟩, -⟩ := id hy
  refine mem_comp_of_adj hx (isRoot_add hxr hyr h) (by simp [pair_add, hx₁, hy₁])
    (by simp [pair_add, hx₂, hy₂]) ?_
  rw [iform_add_right, iform_root_self hxr, h]
  decide

theorem comp_subset {S : Set E6V} (hm : m ∈ S)
    (hS : ∀ x ∈ S, ∀ δ ∈ a3Ker Tag.E6 c₁ c₂, iform x δ ≠ 0 → δ ∈ S) :
    a3Comp Tag.E6 c₁ c₂ m ⊆ S := by
  rintro δ ⟨-, hδ⟩
  have key : ∀ a b, Relation.EqvGen (fun α β : E6V => α ∈ a3Ker Tag.E6 c₁ c₂ ∧
      β ∈ a3Ker Tag.E6 c₁ c₂ ∧ α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) ≠ 0) a b →
      (a ∈ S ↔ b ∈ S) := by
    intro a b h
    induction h with
    | rel a b hab =>
      obtain ⟨ha, hb, hne⟩ := hab
      rw [dotProduct_mulVec_eq_iform] at hne
      exact ⟨fun h => hS a h b hb hne, fun h => hS b h a ha (by rwa [iform_comm])⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (key m δ hδ).mp hm

theorem exists_adj_out {S : Set E6V} (hm : m ∈ S) (hfin : S.Finite) (hlt : S.ncard < 12)
    (hn : (a3Comp Tag.E6 c₁ c₂ m).ncard = 12) :
    ∃ x ∈ S, ∃ δ ∈ a3Ker Tag.E6 c₁ c₂, iform x δ ≠ 0 ∧ δ ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub := comp_subset hm hcon
  have := Set.ncard_le_ncard hsub hfin
  omega

theorem ncard_le_two (a b : E6V) : ({a, b} : Set E6V).ncard ≤ 2 :=
  (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])

theorem ncard_le_six (a b c d e g : E6V) : ({a, b, c, d, e, g} : Set E6V).ncard ≤ 6 := by
  refine (Set.ncard_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
  rw [Set.ncard_singleton]

@[expose] def IsChain (i j k : E6V) : Prop :=
  iform i j = -1 ∧ iform j k = -1 ∧ iform i k = 0

theorem chain_of_third {a b y : E6V} (ha : a ∈ a3Comp Tag.E6 c₁ c₂ m)
    (hb : b ∈ a3Comp Tag.E6 c₁ c₂ m) (hy : y ∈ a3Comp Tag.E6 c₁ c₂ m) (hab : iform a b = -1)
    (hya : iform y a = 0 ∨ iform y a = 1 ∨ iform y a = -1)
    (hyb : iform y b = 0 ∨ iform y b = 1 ∨ iform y b = -1)
    (hyab : iform y a + iform y b = 0 ∨ iform y a + iform y b = 1 ∨
      iform y a + iform y b = -1)
    (hnz : ¬(iform y a = 0 ∧ iform y b = 0)) :
    ∃ i ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ j ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ k ∈ a3Comp Tag.E6 c₁ c₂ m,
      IsChain i j k := by
  have haa := iform_root_self ha.1.1
  have hbb := iform_root_self hb.1.1
  have hba : iform b a = -1 := by rw [iform_comm]; exact hab
  have hab' := add_mem_comp ha hb hab
  rcases hya with h1 | h1 | h1 <;> rcases hyb with h2 | h2 | h2
  · exact absurd ⟨h1, h2⟩ hnz
  · refine ⟨a, ha, b, hb, -y, neg_mem_comp hy, hab, ?_, ?_⟩
    · rw [iform_neg_right, iform_comm, h2]
    · rw [iform_neg_right, iform_comm, h1, neg_zero]
  · refine ⟨a, ha, b, hb, y, hy, hab, ?_, ?_⟩
    · rw [iform_comm, h2]
    · rw [iform_comm, h1]
  · refine ⟨-y, neg_mem_comp hy, a, ha, b, hb, ?_, hab, ?_⟩
    · rw [iform_neg_left, h1]
    · rw [iform_neg_left, h2, neg_zero]
  · omega
  · refine ⟨y, hy, b, hb, -(a + b), neg_mem_comp hab', h2, ?_, ?_⟩
    · rw [iform_neg_right, iform_add_right, hba, hbb]
      decide
    · rw [iform_neg_right, iform_add_right, h1, h2]
      decide
  · refine ⟨y, hy, a, ha, b, hb, h1, hab, h2⟩
  · refine ⟨y, hy, a, ha, -(a + b), neg_mem_comp hab', h1, ?_, ?_⟩
    · rw [iform_neg_right, iform_add_right, haa, hab]
      decide
    · rw [iform_neg_right, iform_add_right, h1, h2]
      decide
  · omega

theorem exists_chain (hm : m ∈ a3Ker Tag.E6 c₁ c₂) (hn : (a3Comp Tag.E6 c₁ c₂ m).ncard = 12) :
    ∃ i ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ j ∈ a3Comp Tag.E6 c₁ c₂ m, ∃ k ∈ a3Comp Tag.E6 c₁ c₂ m,
      IsChain i j k := by
  have hmC : m ∈ a3Comp Tag.E6 c₁ c₂ m := ⟨hm, Relation.EqvGen.refl _⟩
  obtain ⟨x, hxS, δ, hδ, hxδ, hδS⟩ := exists_adj_out (S := {m, -m}) (by simp) (Set.toFinite _)
    (by have := ncard_le_two m (-m); omega) hn
  have hxC : x ∈ a3Comp Tag.E6 c₁ c₂ m := by
    rcases hxS with rfl | h
    · exact hmC
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact neg_mem_comp hmC
  have hδC := mem_comp_of_adj hxC hδ.1 hδ.2.1 hδ.2.2 hxδ
  have hδx : δ ≠ x ∧ δ ≠ -x := by
    rcases hxS with rfl | h
    · exact ⟨fun h => hδS (by simp [h]), fun h => hδS (by simp [h])⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact ⟨fun h => hδS (by simp [h]), fun h => hδS (by simp [h])⟩
  obtain ⟨b, hbC, hxb⟩ : ∃ b ∈ a3Comp Tag.E6 c₁ c₂ m, iform x b = -1 := by
    rcases iform_roots_cases hxC.1.1 hδ.1 (Ne.symm hδx.1) (fun h => hδx.2 (by rw [h, neg_neg]))
      with h | h | h
    · exact absurd h hxδ
    · exact ⟨-δ, neg_mem_comp hδC, by rw [iform_neg_right, h]⟩
    · exact ⟨δ, hδC, h⟩
  have hxx := iform_root_self hxC.1.1
  have hbb := iform_root_self hbC.1.1
  have hbx : iform b x = -1 := by rw [iform_comm]; exact hxb
  have hxbC := add_mem_comp hxC hbC hxb
  have hmS : m ∈ ({x, -x, b, -b, x + b, -(x + b)} : Set E6V) := by
    rcases hxS with rfl | h
    · simp
    · rw [Set.mem_singleton_iff] at h
      rw [h, neg_neg]
      simp
  obtain ⟨x', hx'S, y, hy, hx'y, hyS⟩ := exists_adj_out hmS (Set.toFinite _)
    (by have := ncard_le_six x (-x) b (-b) (x + b) (-(x + b)); omega) hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hyS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hyS
  have hyC : y ∈ a3Comp Tag.E6 c₁ c₂ m := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'S
    rcases hx'S with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_comp_of_adj hxC hy.1 hy.2.1 hy.2.2 hx'y
    · exact mem_comp_of_adj (neg_mem_comp hxC) hy.1 hy.2.1 hy.2.2 hx'y
    · exact mem_comp_of_adj hbC hy.1 hy.2.1 hy.2.2 hx'y
    · exact mem_comp_of_adj (neg_mem_comp hbC) hy.1 hy.2.1 hy.2.2 hx'y
    · exact mem_comp_of_adj hxbC hy.1 hy.2.1 hy.2.2 hx'y
    · exact mem_comp_of_adj (neg_mem_comp hxbC) hy.1 hy.2.1 hy.2.2 hx'y
  have hneg : ∀ u : E6V, y ≠ -u ↔ ¬y = -u := fun _ => Iff.rfl
  have hya := iform_roots_cases hy.1 hxC.1.1 h1 h2
  have hyb := iform_roots_cases hy.1 hbC.1.1 h3 h4
  have hyab := iform_roots_cases hy.1 hxbC.1.1 h5 h6
  rw [iform_add_right] at hyab
  refine chain_of_third hxC hbC hyC hxb hya hyb hyab ?_
  rintro ⟨ha0, hb0⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'S
  rcases hx'S with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hx'y (by rw [iform_comm, ha0])
  · exact hx'y (by rw [iform_neg_left, iform_comm, ha0, neg_zero])
  · exact hx'y (by rw [iform_comm, hb0])
  · exact hx'y (by rw [iform_neg_left, iform_comm, hb0, neg_zero])
  · exact hx'y (by rw [iform_comm, iform_add_right, ha0, hb0, add_zero])
  · exact hx'y (by rw [iform_neg_left, iform_comm, iform_add_right, ha0, hb0, add_zero,
      neg_zero])

end Comp

end CFSG.StandardType.LieCore.A3E6K
