module

public import CFSG.LargeExtraspecial.A2ModBasic
public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem linearIndependent_of_finrank_span_pair {x y : V}
    (h : finrank (ZMod 2) (Submodule.span (ZMod 2) {x, y}) = 2) :
    LinearIndependent (ZMod 2) ![x, y] := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank,
    Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, h]

theorem eq_of_pair_mem [FiniteDimensional (ZMod 2) V] {U W : Submodule (ZMod 2) V}
    (hU : finrank (ZMod 2) U = 2) (hW : finrank (ZMod 2) W = 2) {x y : V}
    (hli : LinearIndependent (ZMod 2) ![x, y]) (hxU : x ∈ U) (hyU : y ∈ U) (hxW : x ∈ W)
    (hyW : y ∈ W) : U = W := by
  have hle : ∀ T : Submodule (ZMod 2) V, x ∈ T → y ∈ T →
      Submodule.span (ZMod 2) {x, y} ≤ T := fun T hx hy => by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  have h2 := finrank_span_pair hli
  have eU := Submodule.eq_of_le_of_finrank_eq (hle U hxU hyU) (by rw [h2, hU])
  have eW := Submodule.eq_of_le_of_finrank_eq (hle W hxW hyW) (by rw [h2, hW])
  rw [← eU, eW]

theorem left_mem_span_pair (x y : V) : x ∈ Submodule.span (ZMod 2) {x, y} :=
  Submodule.subset_span (by simp)

theorem right_mem_span_pair (x y : V) : y ∈ Submodule.span (ZMod 2) {x, y} :=
  Submodule.subset_span (by simp)

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem commSpace_mul_eq_span_add (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA Q α 2) (hβ : IsTypeA Q β 2) (hne : commSpace α ≠ commSpace β) {p x y : V}
    (hx : commSpace α = Submodule.span (ZMod 2) {p, x})
    (hy : commSpace β = Submodule.span (ZMod 2) {p, y}) :
    commSpace (α * β) = Submodule.span (ZMod 2) {p, x + y} ∧ x + y ∉ (ZMod 2) ∙ p := by
  have hlix : LinearIndependent (ZMod 2) ![p, x] :=
    linearIndependent_of_finrank_span_pair (by rw [← hx]; exact hα.2.2.2.1)
  have hliy : LinearIndependent (ZMod 2) ![p, y] :=
    linearIndependent_of_finrank_span_pair (by rw [← hy]; exact hβ.2.2.2.1)
  obtain ⟨hqp, -, hpx, rfl⟩ := eq_eichler_of_isTypeA hQ hα hlix hx
  obtain ⟨-, -, hpy, rfl⟩ := eq_eichler_of_isTypeA hQ hβ hliy hy
  have hp0 : p ≠ 0 := (linearIndependent_pair_iff.mp hlix).1
  have hxy : x + y ∉ (ZMod 2) ∙ p := by
    intro hmem
    apply hne
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hyα : y ∈ commSpace (eichler Q p x) := by
      have e : y = c • p + x := by
        rw [hc, add_comm x y, add_assoc, vec_add_self, add_zero]
      rw [hx, e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ c (left_mem_span_pair p x))
        (right_mem_span_pair p x)
    exact eq_of_pair_mem hα.2.2.2.1 hβ.2.2.2.1 hliy (hx ▸ left_mem_span_pair p x) hyα
      (hy ▸ left_mem_span_pair p y) (hy ▸ right_mem_span_pair p y)
  have hpxy : polar Q p (x + y) = 0 := by rw [polar_add_right, hpx, hpy, add_zero]
  refine ⟨?_, hxy⟩
  rw [eichler_mul hpx hpy]
  exact (eichler_type_of_not_mem_span hQ hp0 hqp hpxy hxy).1

theorem third_line_of_meet (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA Q α 2) (hβ : IsTypeA Q β 2) (hne : commSpace α ≠ commSpace β)
    (hmeet : commSpace α ⊓ commSpace β ≠ ⊥) :
    finrank (ZMod 2) (commSpace (α * β)) = 2 ∧
      commSpace α ⊓ commSpace β ≤ commSpace (α * β) ∧
      commSpace (α * β) ≤ commSpace α ⊔ commSpace β ∧
      commSpace (α * β) ≠ commSpace α ∧ commSpace (α * β) ≠ commSpace β ∧
      commSpace α ⊓ commSpace (α * β) = commSpace α ⊓ commSpace β ∧
      commSpace β ⊓ commSpace (α * β) = commSpace α ⊓ commSpace β ∧
      ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → commSpace α ⊓ commSpace β ≤ U →
        U ≤ commSpace α ⊔ commSpace β →
          U = commSpace α ∨ U = commSpace β ∨ U = commSpace (α * β) := by
  obtain ⟨p, hpI, hp0⟩ := (Submodule.ne_bot_iff _).mp hmeet
  have hpα : p ∈ commSpace α := (Submodule.mem_inf.mp hpI).1
  have hpβ : p ∈ commSpace β := (Submodule.mem_inf.mp hpI).2
  obtain ⟨x, hlix, hspx⟩ := exists_pair_of_mem_of_finrank_eq_two hα.2.2.2.1 hpα hp0
  obtain ⟨y, hliy, hspy⟩ := exists_pair_of_mem_of_finrank_eq_two hβ.2.2.2.1 hpβ hp0
  obtain ⟨hc, hxy⟩ := commSpace_mul_eq_span_add hQ hα hβ hne hspx.symm hspy.symm
  have hlixy : LinearIndependent (ZMod 2) ![p, x + y] :=
    linearIndependent_pair_iff.mpr ⟨hp0, fun h => hxy (h ▸ Submodule.zero_mem _),
      fun h => hxy (h ▸ Submodule.mem_span_singleton_self p)⟩
  have h2 : finrank (ZMod 2) (commSpace (α * β)) = 2 := by rw [hc, finrank_span_pair hlixy]
  have hinf1 := (finrank_fixSpace_inf_of_meet hQ hα hβ hne hmeet).1
  have hpt : commSpace α ⊓ commSpace β = (ZMod 2) ∙ p := by
    refine (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem p _).mpr hpI)
      (by rw [finrank_span_singleton hp0, hinf1])).symm
  have hxα : x ∈ commSpace α := hspx ▸ right_mem_span_pair p x
  have hyβ : y ∈ commSpace β := hspy ▸ right_mem_span_pair p y
  have hpαβ : p ∈ commSpace (α * β) := hc ▸ left_mem_span_pair p (x + y)
  have hxyαβ : x + y ∈ commSpace (α * β) := hc ▸ right_mem_span_pair p (x + y)
  have hle : commSpace (α * β) ≤ commSpace α ⊔ commSpace β := by
    rw [hc, Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.mem_sup_left hpα
    · exact Submodule.add_mem_sup hxα hyβ
  have hneα : commSpace (α * β) ≠ commSpace α := by
    intro h
    apply hxy
    have hy' : y ∈ commSpace α := by
      have := Submodule.sub_mem _ (h ▸ hxyαβ) hxα
      rwa [add_sub_cancel_left] at this
    have hyI : y ∈ commSpace α ⊓ commSpace β := Submodule.mem_inf.mpr ⟨hy', hyβ⟩
    rw [hpt] at hyI
    exact absurd ((mem_span_singleton_iff.mp hyI).resolve_left
      (linearIndependent_pair_iff.mp hliy).2.1) (linearIndependent_pair_iff.mp hliy).2.2.symm
  have hneβ : commSpace (α * β) ≠ commSpace β := by
    intro h
    have hx' : x ∈ commSpace β := by
      have := Submodule.sub_mem _ (h ▸ hxyαβ) hyβ
      rwa [add_sub_cancel_right] at this
    have hxI : x ∈ commSpace α ⊓ commSpace β := Submodule.mem_inf.mpr ⟨hxα, hx'⟩
    rw [hpt] at hxI
    exact absurd ((mem_span_singleton_iff.mp hxI).resolve_left
      (linearIndependent_pair_iff.mp hlix).2.1) (linearIndependent_pair_iff.mp hlix).2.2.symm
  have hmeetpt : ∀ U W : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 →
      finrank (ZMod 2) W = 2 → U ≠ W → p ∈ U → p ∈ W → U ⊓ W = (ZMod 2) ∙ p := by
    intro U W hU hW hUW hpU hpW
    have hle1 : (ZMod 2) ∙ p ≤ U ⊓ W :=
      (Submodule.span_singleton_le_iff_mem p _).mpr (Submodule.mem_inf.mpr ⟨hpU, hpW⟩)
    refine (Submodule.eq_of_le_of_finrank_le hle1 ?_).symm
    rw [finrank_span_singleton hp0]
    by_contra hlt
    push Not at hlt
    have hU2 := Submodule.finrank_mono (inf_le_left : U ⊓ W ≤ U)
    have hW2 := Submodule.finrank_mono (inf_le_right : U ⊓ W ≤ W)
    apply hUW
    have e1 := Submodule.eq_of_le_of_finrank_eq (inf_le_left : U ⊓ W ≤ U) (by omega)
    have e2 := Submodule.eq_of_le_of_finrank_eq (inf_le_right : U ⊓ W ≤ W) (by omega)
    rw [← e1, e2]
  refine ⟨h2, hpt ▸ (Submodule.span_singleton_le_iff_mem p _).mpr hpαβ, hle, hneα, hneβ,
    ?_, ?_, ?_⟩
  · rw [hpt]
    exact hmeetpt _ _ hα.2.2.2.1 h2 hneα.symm hpα hpαβ
  · rw [hpt]
    exact hmeetpt _ _ hβ.2.2.2.1 h2 hneβ.symm hpβ hpαβ
  · intro U hU hpU hUle
    rw [hpt, Submodule.span_singleton_le_iff_mem] at hpU
    obtain ⟨u, hliu, hspu⟩ := exists_pair_of_mem_of_finrank_eq_two hU hpU hp0
    have huU : u ∈ U := hspu ▸ right_mem_span_pair p u
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hUle huU)
    rw [← hspx] at ha
    rw [← hspy] at hb
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp ha
    obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hb
    have hU' : ∀ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 → p ∈ W → u ∈ W → U = W :=
      fun W hW hpW huW => eq_of_pair_mem hU hW hliu hpU huU hpW huW
    have hu0 : u ∉ (ZMod 2) ∙ p := not_mem_span_singleton_of_pair hliu
    rcases zmod2_eq_zero_or_eq_one t with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one t' with rfl | rfl
    · exfalso
      apply hu0
      rw [← hab]
      simp only [zero_smul, add_zero, ← add_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)
    · refine Or.inr (Or.inl (hU' _ hβ.2.2.2.1 hpβ ?_))
      rw [← hab, ← hspy]
      simp only [zero_smul, add_zero, one_smul, ← add_assoc, ← add_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (left_mem_span_pair p y))
        (right_mem_span_pair p y)
    · refine Or.inl (hU' _ hα.2.2.2.1 hpα ?_)
      rw [← hab, ← hspx]
      simp only [zero_smul, add_zero, one_smul]
      rw [add_right_comm, ← add_smul]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (left_mem_span_pair p x))
        (right_mem_span_pair p x)
    · refine Or.inr (Or.inr (hU' _ h2 hpαβ ?_))
      rw [← hab, hc]
      simp only [one_smul]
      have e : s • p + x + (s' • p + y) = (s + s') • p + (x + y) := by
        rw [add_smul]
        abel
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (left_mem_span_pair p (x + y)))
        (right_mem_span_pair p (x + y))

theorem third_line (hQ : Q.polarBilin.Nondegenerate) {α β : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA Q α 2) (hβ : IsTypeA Q β 2) (hαβ : IsTypeA Q (α * β) 2) :
    commSpace α ≠ commSpace β ∧ finrank (ZMod 2) ↥(commSpace α ⊓ commSpace β) = 1 ∧
      commSpace α ⊓ commSpace β ≤ commSpace (α * β) ∧
      commSpace (α * β) ≤ commSpace α ⊔ commSpace β ∧
      commSpace (α * β) ≠ commSpace α ∧ commSpace (α * β) ≠ commSpace β ∧
      commSpace α ⊓ commSpace (α * β) = commSpace α ⊓ commSpace β ∧
      commSpace β ⊓ commSpace (α * β) = commSpace α ⊓ commSpace β ∧
      ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 → commSpace α ⊓ commSpace β ≤ U →
        U ≤ commSpace α ⊔ commSpace β →
          U = commSpace α ∨ U = commSpace β ∨ U = commSpace (α * β) := by
  obtain ⟨hne, hmeet, h1, -, -⟩ := timmesfeld_12_1 hQ hα hβ hαβ
  obtain ⟨-, h⟩ := third_line_of_meet hQ hα hβ hne hmeet
  exact ⟨hne, h1, h⟩

theorem mem_or_mem_or_mem_of_isTypeA_mul (hQ : Q.polarBilin.Nondegenerate)
    {α β : V ≃ₗ[ZMod 2] V} (hα : IsTypeA Q α 2) (hβ : IsTypeA Q β 2)
    (hαβ : IsTypeA Q (α * β) 2) {v : V} (hv : v ∈ commSpace α ⊔ commSpace β) :
    v ∈ commSpace α ∨ v ∈ commSpace β ∨ v ∈ commSpace (α * β) := by
  obtain ⟨-, h1, -, -, -, -, -, -, h3⟩ := third_line hQ hα hβ hαβ
  have hmeet : commSpace α ⊓ commSpace β ≠ ⊥ := Submodule.one_le_finrank_iff.mp h1.ge
  obtain ⟨p, hpI, hp0⟩ := (Submodule.ne_bot_iff _).mp hmeet
  have hpt : commSpace α ⊓ commSpace β = (ZMod 2) ∙ p :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem p _).mpr hpI)
      (by rw [finrank_span_singleton hp0, h1])).symm
  by_cases hvp : v ∈ (ZMod 2) ∙ p
  · rw [← hpt] at hvp
    exact Or.inl (Submodule.mem_inf.mp hvp).1
  have hli : LinearIndependent (ZMod 2) ![p, v] :=
    linearIndependent_pair_iff.mpr ⟨hp0, fun h => hvp (h ▸ Submodule.zero_mem _),
      fun h => hvp (h ▸ Submodule.mem_span_singleton_self p)⟩
  have hle : Submodule.span (ZMod 2) {p, v} ≤ commSpace α ⊔ commSpace β := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact Submodule.mem_sup_left (Submodule.mem_inf.mp hpI).1
    · exact hv
  have hp : commSpace α ⊓ commSpace β ≤ Submodule.span (ZMod 2) {p, v} := by
    rw [hpt, Submodule.span_singleton_le_iff_mem]
    exact left_mem_span_pair p v
  rcases h3 _ (finrank_span_pair hli) hp hle with h | h | h
  · exact Or.inl (h ▸ right_mem_span_pair p v)
  · exact Or.inr (Or.inl (h ▸ right_mem_span_pair p v))
  · exact Or.inr (Or.inr (h ▸ right_mem_span_pair p v))

end Linear

namespace A2Action

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem eq_of_commSpace_eq (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (h : commSpace (ρ d) = commSpace (ρ e)) : d = e :=
  hA.injective (OrthoF2.eq_of_commSpace_eq hA.nondegenerate (hA.isTypeA hd) (hA.isTypeA he) h)

theorem commSpace_ne (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) :
    commSpace (ρ d) ≠ commSpace (ρ e) := fun h => hde (hA.eq_of_commSpace_eq hd he h)

theorem commSpace_mul_eq_span_add (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d ≠ e) {p x y : V} (hx : commSpace (ρ d) = Submodule.span (ZMod 2) {p, x})
    (hy : commSpace (ρ e) = Submodule.span (ZMod 2) {p, y}) :
    commSpace (ρ (d * e)) = Submodule.span (ZMod 2) {p, x + y} ∧ x + y ∉ (ZMod 2) ∙ p := by
  rw [map_mul]
  exact A2Mod.commSpace_mul_eq_span_add hA.nondegenerate (hA.isTypeA hd) (hA.isTypeA he)
    (hA.commSpace_ne hd he hde) hx hy

theorem third_line (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e ∈ D) :
    commSpace (ρ d) ≠ commSpace (ρ e) ∧ finrank (ZMod 2) ↥(commSpace (ρ d) ⊓ commSpace (ρ e)) = 1 ∧
      commSpace (ρ d) ⊓ commSpace (ρ e) ≤ commSpace (ρ (d * e)) ∧
      commSpace (ρ (d * e)) ≤ commSpace (ρ d) ⊔ commSpace (ρ e) ∧
      commSpace (ρ (d * e)) ≠ commSpace (ρ d) ∧ commSpace (ρ (d * e)) ≠ commSpace (ρ e) ∧
      commSpace (ρ d) ⊓ commSpace (ρ (d * e)) = commSpace (ρ d) ⊓ commSpace (ρ e) ∧
      commSpace (ρ e) ⊓ commSpace (ρ (d * e)) = commSpace (ρ d) ⊓ commSpace (ρ e) ∧
      ∀ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 2 →
        commSpace (ρ d) ⊓ commSpace (ρ e) ≤ U → U ≤ commSpace (ρ d) ⊔ commSpace (ρ e) →
          U = commSpace (ρ d) ∨ U = commSpace (ρ e) ∨ U = commSpace (ρ (d * e)) := by
  have hde' := hA.isTypeA hde
  rw [map_mul] at hde' ⊢
  exact A2Mod.third_line hA.nondegenerate (hA.isTypeA hd) (hA.isTypeA he) hde'

theorem mem_or_mem_or_mem (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e ∈ D) {v : V} (hv : v ∈ commSpace (ρ d) ⊔ commSpace (ρ e)) :
    v ∈ commSpace (ρ d) ∨ v ∈ commSpace (ρ e) ∨ v ∈ commSpace (ρ (d * e)) := by
  have hde' := hA.isTypeA hde
  rw [map_mul] at hde' ⊢
  exact mem_or_mem_or_mem_of_isTypeA_mul hA.nondegenerate (hA.isTypeA hd) (hA.isTypeA he) hde'
    hv

theorem finrank_commSpaceOf_sup_zpowers_le_of_collinear (hA : A2Action D Q ρ)
    {H : Subgroup X} {d e : X} (hd : d ∈ D) (he : e ∈ D) (heH : e ∈ H) (hde : d * e ∈ D) :
    finrank (ZMod 2) (commSpaceOf ρ (H ⊔ Subgroup.zpowers d)) ≤
      finrank (ZMod 2) (commSpaceOf ρ H) + 1 := by
  obtain ⟨-, h1, -⟩ := hA.third_line hd he hde
  have hmeet : commSpace (ρ d) ⊓ commSpace (ρ e) ≠ ⊥ := Submodule.one_le_finrank_iff.mp h1.ge
  refine finrank_commSpaceOf_sup_zpowers_le ρ H (hA.isTypeA hd).2.2.2.1.le fun h => hmeet ?_
  exact eq_bot_iff.mpr (h ▸ inf_le_inf_left _ (commSpace_le_commSpaceOf ρ heH))

end A2Action

end CFSG.LargeExtraspecial.A2Mod
