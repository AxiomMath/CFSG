module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapGenerated

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding

variable {r s : ℕ}

@[expose] def blockFlip (r : ℕ) : Perm (Fin r × Bool) :=
  Equiv.prodCongr (Equiv.refl _) Equiv.boolNot

@[expose] def pairSig (r s : ℕ) : Perm (OmegaE r s) := Perm.sumCongr (blockFlip r) 1

theorem pairSig_inl (i : Fin r) (b : Bool) :
    pairSig r s (Sum.inl (i, b)) = Sum.inl (i, !b) := rfl

theorem pairSig_inr (j : Fin s) : pairSig r s (Sum.inr j) = Sum.inr j := rfl

theorem pairSig_invol (x : OmegaE r s) : pairSig r s (pairSig r s x) = x := by
  rcases x with ⟨i, b⟩ | j
  · rw [pairSig_inl, pairSig_inl]; simp
  · rw [pairSig_inr, pairSig_inr]

variable (i₀ : Fin r) (f₀ : Fin s)

@[expose] def In3 (x : OmegaE r s) : Prop :=
  x = Sum.inl (i₀, false) ∨ x = Sum.inl (i₀, true) ∨ x = Sum.inr f₀

theorem In3_pairSig (x : OmegaE r s) : In3 i₀ f₀ (pairSig r s x) ↔ In3 i₀ f₀ x := by
  rcases x with ⟨i, b⟩ | j
  · rw [pairSig_inl]
    unfold In3
    simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, or_false]
    cases b <;> simp
  · rw [pairSig_inr]

@[expose] def YStar : Subgroup (Perm (OmegaE r s)) where
  carrier := {g | (∀ x, In3 i₀ f₀ x → In3 i₀ f₀ (g x)) ∧
    ∀ x, ¬ In3 i₀ f₀ x → g x = x ∨ g x = pairSig r s x}
  mul_mem' := by
    intro g h hg hh
    refine ⟨fun x hx => hg.1 _ (hh.1 x hx), fun x hx => ?_⟩
    simp only [Perm.mul_apply]
    have hsx : ¬ In3 i₀ f₀ (pairSig r s x) := fun h' => hx ((In3_pairSig i₀ f₀ x).1 h')
    rcases hh.2 x hx with e | e
    · rw [e]; exact hg.2 x hx
    · rw [e]
      rcases hg.2 _ hsx with e' | e'
      · right; exact e'
      · left; rw [e', pairSig_invol]
  one_mem' := ⟨fun x hx => hx, fun x _ => Or.inl rfl⟩
  inv_mem' := by
    intro g hg
    have h1 : ∀ x, In3 i₀ f₀ x → In3 i₀ f₀ (g⁻¹ x) := by
      intro x hx
      by_contra h
      rcases hg.2 _ h with e | e
      · apply h
        have : g (g⁻¹ x) = x := by simp
        rw [this] at e
        rw [← e]; exact hx
      · apply h
        have : g (g⁻¹ x) = x := by simp
        rw [this] at e
        have hx' : In3 i₀ f₀ (pairSig r s (g⁻¹ x)) := by rw [← e]; exact hx
        exact (In3_pairSig i₀ f₀ _).1 hx'
    refine ⟨h1, fun x hx => ?_⟩
    have hy : ¬ In3 i₀ f₀ (g⁻¹ x) := fun h => hx (by simpa using hg.1 _ h)
    have hgx : g (g⁻¹ x) = x := by simp
    rcases hg.2 _ hy with e | e
    · left; rw [hgx] at e; exact e.symm
    · right
      rw [hgx] at e
      calc g⁻¹ x = pairSig r s (pairSig r s (g⁻¹ x)) := (pairSig_invol _).symm
        _ = pairSig r s x := by rw [← e]

theorem mem_Wr_iff' {g : Perm (OmegaE r s)} :
    g ∈ Wr r s ↔ (∀ j, g (Sum.inr j) = Sum.inr j) ∧
      ∀ p : Fin r × Bool, ∃ q : Fin r × Bool, g (Sum.inl p) = Sum.inl q ∧ q.1 = p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun j => rfl, fun p => ⟨x p, rfl, hx p⟩⟩
  · rintro ⟨hinr, hinl⟩
    have hmaps : Set.MapsTo g (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨q, hq, -⟩ := hinl p
      exact ⟨q, hq.symm⟩
    obtain ⟨⟨σ₁, σ₂⟩, hσ⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    have hgeq : g = Perm.sumCongr σ₁ σ₂ := hσ.symm
    have h2 : σ₂ = 1 := by
      refine Equiv.ext fun j => ?_
      have := hinr j
      rw [hgeq] at this
      simpa using this
    have h1 : σ₁ ∈ blockFix (Fin r) := by
      intro p
      obtain ⟨q, hq, hq1⟩ := hinl p
      rw [hgeq] at hq
      simp only [Perm.sumCongr_apply, Sum.map_inl, Sum.inl.injEq] at hq
      rw [hq]; exact hq1
    refine ⟨σ₁, h1, ?_⟩
    rw [hgeq, h2]
    rfl

theorem Wr_le_YStar : Wr r s ≤ YStar i₀ f₀ := by
  rintro w hw
  rw [mem_Wr_iff'] at hw
  obtain ⟨hinr, hinl⟩ := hw
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rcases hx with rfl | rfl | rfl
    · obtain ⟨q, hq, hq1⟩ := hinl (i₀, false)
      rw [hq]
      obtain ⟨k, c⟩ := q
      simp only at hq1
      subst hq1
      cases c
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · obtain ⟨q, hq, hq1⟩ := hinl (i₀, true)
      rw [hq]
      obtain ⟨k, c⟩ := q
      simp only at hq1
      subst hq1
      cases c
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rw [hinr]; exact Or.inr (Or.inr rfl)
  · rcases x with p | j
    · obtain ⟨q, hq, hq1⟩ := hinl p
      rw [hq, pairSig_inl]
      obtain ⟨i, b⟩ := p
      obtain ⟨k, c⟩ := q
      simp only at hq1
      subst hq1
      cases b <;> cases c <;> simp
    · left; exact hinr j

theorem mem_Wr_of_mem_YStar {g : Perm (OmegaE r s)} (hg : g ∈ YStar i₀ f₀)
    (hf : g (Sum.inr f₀) = Sum.inr f₀) : g ∈ Wr r s := by
  rw [mem_Wr_iff']
  refine ⟨fun j => ?_, fun p => ?_⟩
  · by_cases hj : j = f₀
    · subst hj; exact hf
    · have hn : ¬ In3 i₀ f₀ (Sum.inr j : OmegaE r s) := by
        simp [In3, hj]
      rcases hg.2 _ hn with e | e
      · exact e
      · rw [e]; rfl
  · by_cases hp : p.1 = i₀
    · obtain ⟨i, b⟩ := p
      simp only at hp
      subst hp
      have hin : In3 i f₀ (Sum.inl (i, b) : OmegaE r s) := by
        cases b
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      have := hg.1 _ hin
      rcases this with e | e | e
      · exact ⟨(i, false), e, rfl⟩
      · exact ⟨(i, true), e, rfl⟩
      · exfalso
        have : g (Sum.inl (i, b)) = g (Sum.inr f₀) := by rw [e, hf]
        exact Sum.inl_ne_inr (g.injective this)
    · have hn : ¬ In3 i₀ f₀ (Sum.inl p : OmegaE r s) := by
        simp [In3]
        refine ⟨?_, ?_⟩ <;> intro h <;> exact hp (by rw [h])
      rcases hg.2 _ hn with e | e
      · exact ⟨p, e, rfl⟩
      · obtain ⟨i, b⟩ := p
        exact ⟨(i, !b), by rw [e, pairSig_inl], rfl⟩

abbrev X3 (i₀ : Fin r) (f₀ : Fin s) := {x : OmegaE r s // In3 i₀ f₀ x}

theorem In3_iff_of_mem_YStar {g : Perm (OmegaE r s)} (hg : g ∈ YStar i₀ f₀) (x : OmegaE r s) :
    In3 i₀ f₀ x ↔ In3 i₀ f₀ (g x) := by
  refine ⟨hg.1 x, fun h => ?_⟩
  by_contra hx
  rcases hg.2 x hx with e | e
  · exact hx (e ▸ h)
  · exact hx ((In3_pairSig i₀ f₀ x).1 (e ▸ h))

@[expose] noncomputable def rhoStar : ↥(YStar i₀ f₀) →* Perm (X3 i₀ f₀) where
  toFun g := (g.1).subtypePerm fun x => (In3_iff_of_mem_YStar i₀ f₀ g.2 x).symm
  map_one' := Equiv.ext fun x => Subtype.ext rfl
  map_mul' g h := Equiv.ext fun x => Subtype.ext rfl

theorem rhoStar_apply (g : ↥(YStar i₀ f₀)) (x : X3 i₀ f₀) :
    ((rhoStar i₀ f₀ g x : X3 i₀ f₀) : OmegaE r s) = g.1 x := rfl

theorem rhoStar_surjective : Function.Surjective (rhoStar i₀ f₀) := by
  classical
  intro π
  have hmem : (Perm.ofSubtype π : Perm (OmegaE r s)) ∈ YStar i₀ f₀ := by
    refine ⟨fun x hx => ?_, fun x hx => Or.inl ?_⟩
    · rw [Perm.ofSubtype_apply_of_mem π hx]
      exact (π ⟨x, hx⟩).2
    · exact Perm.ofSubtype_apply_of_not_mem π hx
  refine ⟨⟨_, hmem⟩, Equiv.ext fun x => Subtype.ext ?_⟩
  rw [rhoStar_apply]
  exact Perm.ofSubtype_apply_of_mem π x.2

theorem YStar_le {H : Subgroup (Perm (OmegaE r s))} (hW : Wr r s ≤ H)
    (hA : alternatingGroup (OmegaE r s) ≤ H) : YStar i₀ f₀ ≤ H := by
  classical
  have ha : (Sum.inl (i₀, false) : OmegaE r s) ≠ Sum.inl (i₀, true) := by simp
  have ha' : (Sum.inl (i₀, true) : OmegaE r s) ≠ Sum.inr f₀ := Sum.inl_ne_inr
  have ha'' : (Sum.inl (i₀, false) : OmegaE r s) ≠ Sum.inr f₀ := Sum.inl_ne_inr
  have ht : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) ∈ H := by
    apply hW
    have h := embL_blockTransp r s i₀ false
    simp only [Bool.not_false] at h
    rw [h]
    exact ⟨blockTransp i₀, swap_mem_blockFix rfl, rfl⟩
  have hc : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) *
      swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) ∈ H := by
    apply hA
    rw [mem_alternatingGroup, map_mul, sign_swap ha, sign_swap ha']
    rfl
  have ht2 : swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) ∈ H := by
    have := H.mul_mem ht hc
    simpa [← mul_assoc] using this
  have ht3 : swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inr f₀) ∈ H := by
    have h := H.mul_mem (H.mul_mem ht2 ht) ht2
    have e : swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) *
        swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inl (i₀, true)) *
        swap (Sum.inl (i₀, true) : OmegaE r s) (Sum.inr f₀) =
        swap (Sum.inl (i₀, false) : OmegaE r s) (Sum.inr f₀) := by
      ext z
      simp only [Perm.mul_apply, swap_apply_def]
      split_ifs <;> simp_all
    rwa [e] at h
  have hsub : ∀ π : Perm (X3 i₀ f₀), (Perm.ofSubtype π : Perm (OmegaE r s)) ∈ H := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one => simp [one_mem]
    | swap_mul f x y hxy ih =>
      rw [map_mul, Perm.ofSubtype_swap_eq]
      refine H.mul_mem ?_ ih
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      have hne : x ≠ y := fun h => hxy (Subtype.ext h)
      simp only
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hne
        | assumption
        | (rw [swap_comm]; assumption)
  intro g hg
  set π := rhoStar i₀ f₀ ⟨g, hg⟩ with hπ
  have hπH := hsub π
  have hyst : (Perm.ofSubtype π : Perm (OmegaE r s)) ∈ YStar i₀ f₀ := by
    refine ⟨fun x hx => ?_, fun x hx => Or.inl ?_⟩
    · rw [Perm.ofSubtype_apply_of_mem π hx]
      exact (π ⟨x, hx⟩).2
    · exact Perm.ofSubtype_apply_of_not_mem π hx
  have hq : g * (Perm.ofSubtype π)⁻¹ ∈ Wr r s := by
    have hqY : g * (Perm.ofSubtype π)⁻¹ ∈ YStar i₀ f₀ := (YStar i₀ f₀).mul_mem hg ((YStar i₀ f₀).inv_mem hyst)
    refine mem_Wr_of_mem_YStar i₀ f₀ hqY ?_
    have hf : In3 i₀ f₀ (Sum.inr f₀ : OmegaE r s) := Or.inr (Or.inr rfl)
    have h2 : ((Perm.ofSubtype π : Perm (OmegaE r s)))⁻¹ = Perm.ofSubtype π⁻¹ :=
      (map_inv _ _).symm
    simp only [Perm.mul_apply]
    rw [h2, Perm.ofSubtype_apply_of_mem π⁻¹ hf]
    have h3 := rhoStar_apply i₀ f₀ ⟨g, hg⟩ (π⁻¹ ⟨Sum.inr f₀, hf⟩)
    rw [← hπ] at h3
    have h4 : π (π⁻¹ ⟨Sum.inr f₀, hf⟩) = ⟨Sum.inr f₀, hf⟩ := by simp
    rw [h4] at h3
    exact h3.symm
  have : g = (g * (Perm.ofSubtype π)⁻¹) * Perm.ofSubtype π := by group
  rw [this]
  exact H.mul_mem (hW hq) hπH

theorem card_X3 : Nat.card (X3 i₀ f₀) = 3 := by
  classical
  have : Nat.card (X3 i₀ f₀) = Nat.card ↥({Sum.inl (i₀, false), Sum.inl (i₀, true), Sum.inr f₀} :
      Finset (OmegaE r s)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp [In3]
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.card_insert_of_notMem, Finset.card_pair]
  · exact Sum.inl_ne_inr
  · simp

theorem YStar_relIndex_Wr : (Wr r s).relIndex (YStar i₀ f₀) = 3 := by
  classical
  have hf : In3 i₀ f₀ (Sum.inr f₀ : OmegaE r s) := Or.inr (Or.inr rfl)
  have hsub : (Wr r s).subgroupOf (YStar i₀ f₀) =
      (MulAction.stabilizer (Perm (X3 i₀ f₀)) (⟨Sum.inr f₀, hf⟩ : X3 i₀ f₀)).comap
        (rhoStar i₀ f₀) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact Subtype.ext (Wr_apply_inr h f₀)
    · intro h
      exact mem_Wr_of_mem_YStar i₀ f₀ g.2 (congrArg Subtype.val h)
  unfold Subgroup.relIndex
  rw [hsub, Subgroup.index_comap_of_surjective _ (rhoStar_surjective i₀ f₀),
    MulAction.index_stabilizer_of_transitive, card_X3]

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
