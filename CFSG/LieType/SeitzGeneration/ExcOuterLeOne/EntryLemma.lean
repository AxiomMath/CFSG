module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Entry
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.IrrationalRoot

open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section EntryLemma

variable {τ : Tag} {K : Type} [Field K]

noncomputable def vanishSub (R : Subgroup ↥(adjointGroup τ K)) (a : Label τ) : Submodule K (RootModule τ K) where
  carrier := {z | ∀ r ∈ R, (endHom K r z) a = 0}
  zero_mem' := fun r _ => by simp
  add_mem' := fun {z w} hz hw r hr => by
    rw [map_add, Finsupp.add_apply, hz r hr, hw r hr, add_zero]
  smul_mem' := fun c z hz r hr => by
    rw [map_smul, Finsupp.smul_apply, hz r hr, smul_zero]

theorem mem_vanishSub {R : Subgroup ↥(adjointGroup τ K)} {a : Label τ} {z : RootModule τ K} :
    z ∈ vanishSub R a ↔ ∀ r ∈ R, (endHom K r z) a = 0 := Iff.rfl

theorem isSimpleGroup_adjointGroup_of_type (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K] :
    IsSimpleGroup ↥(adjointGroup τ K) := by
  have hq : CFSG.IsQuasisimple ↥(adjointGroup τ K) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 K
    · exact CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K
    · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K
    · exact CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 K
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem rootNorm_neg (v : Fin τ.rank → ℤ) : rootNorm τ (-v) = rootNorm τ v := by
  unfold rootNorm
  rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]

theorem weyl_step_explicit (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      endHom K (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ))
          (rootVec τ K α) = (ε : K) • rootVec τ K (reflect τ i α) ∧
      ∀ z : RootModule τ K,
        (endHom K (CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ)) z)
          (rootLabel (IsRoot.reflect i hα)) = (ε : K) * z (rootLabel hα) := by
  classical
  have hwe : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) =
      CFSG.LieType.Chevalley.weylElement τ K i := by
    rw [CFSG.LieType.Steinberg.Adjoint.weylElement_xPar, torusElement_one_eq, one_mul]
  have hend : endHom K (CFSG.LieType.Chevalley.weylElement τ K i) =
      (weylElt τ K i 1 : Module.End K (RootModule τ K)) := rfl
  refine ⟨(-1) ^ stringDown τ i α, neg_one_pow_eq_or ℤ _, ?_, ?_⟩
  · rw [hwe, hend, weylElt_rootVec i 1 hα]
    simp
  · intro z
    rw [hwe, hend]
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h1 h2 => simp only [map_add, Finsupp.add_apply, h1, h2, mul_add]
    | single b c =>
      rcases b with j | ⟨β, hβ⟩
      · have h := weylElt_hVec (R := K) i j 1
        have e : Finsupp.single (Sum.inl j) c = c • hVec τ K j := by simp [hVec]
        rw [e, map_smul, h]
        simp [hVec, Finsupp.single_apply]
      · have e : Finsupp.single (Sum.inr ⟨β, hβ⟩) c = c • rootVec τ K β := by
          simp [rootVec_eq_single hβ]
        rw [e, map_smul, weylElt_rootVec i 1 hβ]
        by_cases hβα : β = α
        · subst hβα
          simp [rootVec_eq_single hβ, rootVec_eq_single (IsRoot.reflect i hβ), mul_comm]
        · have hne : reflect τ i β ≠ reflect τ i α := fun h' => hβα (by
            have := congrArg (reflect τ i) h'
            rwa [reflect_reflect, reflect_reflect] at this)
          simp [rootVec_eq_single hβ, rootVec_eq_single (IsRoot.reflect i hβ),
            rootVec_eq_single (IsRoot.reflect i hα), Finsupp.single_apply, hne, hβα]

theorem weyl_step {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ r ∈ R, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      endHom K r (rootVec τ K α) = (ε : K) • rootVec τ K (reflect τ i α) ∧
      ∀ z : RootModule τ K,
        (endHom K r z) (rootLabel (IsRoot.reflect i hα)) = (ε : K) * z (rootLabel hα) := by
  obtain ⟨ε, hε, h1, h2⟩ := weyl_step_explicit (K := K) i hα
  exact ⟨_, hw i, ε, hε, h1, h2⟩

@[expose] def WeylMove (R : Subgroup ↥(adjointGroup τ K)) (β γ : Fin τ.rank → ℤ) : Prop :=
  ∀ (hβ : IsRoot τ β) (hγ : IsRoot τ γ), ∃ r ∈ R, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    endHom K r (rootVec τ K β) = (ε : K) • rootVec τ K γ ∧
    ∀ z : RootModule τ K, (endHom K r z) (rootLabel hγ) = (ε : K) * z (rootLabel hβ)

theorem WeylMove.exists {R : Subgroup ↥(adjointGroup τ K)} {β γ : Fin τ.rank → ℤ}
    (h : WeylMove R β γ) (hβ : IsRoot τ β) (hγ : IsRoot τ γ) :
    ∃ r ∈ R, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      endHom K r (rootVec τ K β) = (ε : K) • rootVec τ K γ ∧
      ∀ z : RootModule τ K, (endHom K r z) (rootLabel hγ) = (ε : K) * z (rootLabel hβ) :=
  h hβ hγ

theorem WeylMove.refl (R : Subgroup ↥(adjointGroup τ K)) (β : Fin τ.rank → ℤ) : WeylMove R β β :=
  fun hβ hγ => ⟨1, R.one_mem, 1, Or.inl rfl, by simp, fun z => by simp⟩

theorem WeylMove.trans {R : Subgroup ↥(adjointGroup τ K)} {β γ δ : Fin τ.rank → ℤ}
    (h₁ : WeylMove R β γ) (h₂ : WeylMove R γ δ) (hγ : IsRoot τ γ) : WeylMove R β δ := by
  intro hβ hδ
  obtain ⟨r₁, hr₁, ε₁, hε₁, hv₁, hz₁⟩ := h₁ hβ hγ
  obtain ⟨r₂, hr₂, ε₂, hε₂, hv₂, hz₂⟩ := h₂ hγ hδ
  refine ⟨r₂ * r₁, R.mul_mem hr₂ hr₁, ε₂ * ε₁, ?_, ?_, ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> simp
  · rw [map_mul, Module.End.mul_apply, hv₁, map_smul, hv₂, smul_smul]
    congr 1
    push_cast
    ring
  · intro z
    rw [map_mul, Module.End.mul_apply, hz₂, hz₁]
    push_cast
    ring

theorem WeylMove.symm {R : Subgroup ↥(adjointGroup τ K)} {β γ : Fin τ.rank → ℤ}
    (h : WeylMove R β γ) : WeylMove R γ β := by
  intro hγ hβ
  obtain ⟨r, hr, ε, hε, hv, hz⟩ := h hβ hγ
  have hεε : (ε : K) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  refine ⟨r⁻¹, R.inv_mem hr, ε, hε, ?_, ?_⟩
  · have h1 : endHom K r⁻¹ (endHom K r (rootVec τ K β)) = rootVec τ K β := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hv, map_smul] at h1
    calc endHom K r⁻¹ (rootVec τ K γ) = ((ε : K) * ε) • endHom K r⁻¹ (rootVec τ K γ) := by
          rw [hεε, one_smul]
      _ = (ε : K) • ((ε : K) • endHom K r⁻¹ (rootVec τ K γ)) := by rw [smul_smul]
      _ = (ε : K) • rootVec τ K β := by rw [h1]
  · intro z
    have h2 := hz (endHom K r⁻¹ z)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h2
    calc (endHom K r⁻¹ z) (rootLabel hβ) = ((ε : K) * ε) * (endHom K r⁻¹ z) (rootLabel hβ) := by
          rw [hεε, one_mul]
      _ = (ε : K) * ((ε : K) * (endHom K r⁻¹ z) (rootLabel hβ)) := by ring
      _ = (ε : K) * z (rootLabel hγ) := by rw [← h2]

theorem WeylMove.step {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    (i : Fin τ.rank) (β : Fin τ.rank → ℤ) : WeylMove R β (reflect τ i β) := by
  intro hβ hγ
  exact weyl_step hw i hβ

theorem exists_simple_move {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ j : Fin τ.rank, rootNorm τ γ = rootNorm τ (Pi.single j 1) ∧ WeylMove R γ (Pi.single j 1) := by
  induction hγ with
  | basis j => exact ⟨j, rfl, WeylMove.refl R _⟩
  | reflect i hv ih =>
    obtain ⟨j, hn, hm⟩ := ih
    exact ⟨j, by rw [rootNorm_reflect, hn], ((WeylMove.step hw i _).symm.trans hm hv)⟩

theorem weylMove_neighbour {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    {i l : Fin τ.rank} (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) :
    WeylMove R (Pi.single l 1) (Pi.single i 1) := by
  have hr1 : reflect τ i (Pi.single l 1) = Pi.single l 1 + Pi.single i 1 := by
    have hsum : ∑ j, τ.cartan i j * (Pi.single l 1 : Fin τ.rank → ℤ) j = τ.cartan i l := by
      simp [Pi.single_apply]
    simp only [reflect, hsum, hil]
    simp
  have hr2 : reflect τ l (Pi.single l 1 + Pi.single i 1) = Pi.single i 1 := by
    have hsum : ∑ j, τ.cartan l j * (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) j = 1 := by
      simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, hli, τ.cartan_self]
    simp only [reflect, hsum]
    simp
  have h1 := WeylMove.step hw i (Pi.single l 1)
  have h2 := WeylMove.step hw l (Pi.single l 1 + Pi.single i 1)
  rw [hr1] at h1
  rw [hr2] at h2
  exact h1.trans h2 (isRoot_single_add_single hil)

theorem weylMove_of_connected {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    (hconn : ∀ i j : Fin τ.rank,
      Relation.ReflTransGen (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j)
    (j j' : Fin τ.rank) : WeylMove R (Pi.single j 1) (Pi.single j' 1) := by
  have h := hconn j j'
  induction h with
  | refl => exact WeylMove.refl R _
  | tail _ hbc ih => exact ih.trans (weylMove_neighbour hw hbc.2 hbc.1) (isRoot_single τ _)

theorem exists_weyl_move (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    {R : Subgroup ↥(adjointGroup τ K)}
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hn : rootNorm τ β = rootNorm τ γ) :
    ∃ r ∈ R, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ endHom K r (rootVec τ K β) = (ε : K) • rootVec τ K γ ∧
      ∀ z : RootModule τ K, (endHom K r z) (rootLabel hγ) = (ε : K) * z (rootLabel hβ) := by
  obtain ⟨j, hj, mj⟩ := exists_simple_move hw hβ
  obtain ⟨j', hj', mj'⟩ := exists_simple_move hw hγ
  have hjj' : rootNorm τ (Pi.single j 1) = rootNorm τ (Pi.single j' 1) := by
    rw [← hj, ← hj', hn]
  have hm : WeylMove R (Pi.single j 1) (Pi.single j' 1) := by
    rcases hτ with hE | hE | hE | hF
    · exact weylMove_of_connected hw (cartanE_connected (Or.inl hE)) j j'
    · exact weylMove_of_connected hw (cartanE_connected (Or.inr (Or.inl hE))) j j'
    · exact weylMove_of_connected hw (cartanE_connected (Or.inr (Or.inr hE))) j j'
    · subst hF
      fin_cases j <;> fin_cases j'
      all_goals first
        | exact WeylMove.refl R _
        | exact weylMove_neighbour hw (by decide) (by decide)
        | (exfalso; revert hjj'; decide)
  exact ((mj.trans hm (isRoot_single τ j)).trans mj'.symm (isRoot_single τ j')) hβ hγ

private theorem rootNorm_E_two (hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootNorm τ γ = 2 := by
  induction hγ with
  | basis j =>
    rcases hE with rfl | rfl | rfl <;> revert j <;> decide +kernel
  | reflect i hv ih => rw [rootNorm_reflect, ih]

private theorem rootNorm_F4_mem_two {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    rootNorm Tag.F4 γ = 2 ∨ rootNorm Tag.F4 γ = 4 := by
  induction hγ with
  | basis j => revert j; decide +kernel
  | reflect i hv ih => rw [rootNorm_reflect]; exact ih

private abbrev F4idxLong : Fin Tag.F4.rank := ⟨1, by decide⟩

private abbrev F4idxShort : Fin Tag.F4.rank := ⟨2, by decide⟩

private theorem rootNorm_add_smul (v w : Fin τ.rank → ℤ) (m : ℤ) :
    rootNorm τ (v + m • w) =
      rootNorm τ v + 2 * m * dotProduct v (τ.symmetrizedCartan.mulVec w) + m ^ 2 * rootNorm τ w := by
  have hT : Matrix.transpose τ.symmetrizedCartan = τ.symmetrizedCartan :=
    symmetrizedCartan_isSymm τ
  have hvm : Matrix.vecMul v τ.symmetrizedCartan = τ.symmetrizedCartan.mulVec v := by
    rw [← Matrix.vecMul_transpose, hT]
  have hc : dotProduct v (τ.symmetrizedCartan.mulVec w) =
      dotProduct w (τ.symmetrizedCartan.mulVec v) := by
    rw [Matrix.dotProduct_mulVec, hvm, dotProduct_comm]
  unfold rootNorm
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hc]
  ring

private theorem rootNorm_F4_e1 : rootNorm Tag.F4 (Pi.single F4idxLong 1) = 4 := by
  decide +kernel

private theorem rootNorm_F4_e2 : rootNorm Tag.F4 (Pi.single F4idxShort 1) = 2 := by
  decide +kernel

private theorem dotProduct_F4_e1_e2 :
    dotProduct (Pi.single F4idxLong 1 : Fin Tag.F4.rank → ℤ)
      (Matrix.mulVec (Tag.symmetrizedCartan Tag.F4) (Pi.single F4idxShort 1)) = -2 := by
  decide +kernel

private theorem rootNorm_F4_formula (m : ℤ) :
    rootNorm Tag.F4 (Pi.single F4idxLong 1 + m • Pi.single F4idxShort 1) =
      4 - 4 * m + 2 * m ^ 2 := by
  rw [rootNorm_add_smul, rootNorm_F4_e1, rootNorm_F4_e2, dotProduct_F4_e1_e2]
  ring

private theorem isRoot_F4_e1_e2 :
    IsRoot Tag.F4 (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) := by
  have e : reflect Tag.F4 F4idxLong (Pi.single F4idxShort 1) =
      Pi.single F4idxLong 1 + Pi.single F4idxShort 1 := by
    decide +kernel
  rw [← e]
  exact IsRoot.reflect _ (isRoot_single Tag.F4 F4idxShort)

private theorem isRoot_F4_e1_2e2 :
    IsRoot Tag.F4 (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) := by
  have e : reflect Tag.F4 F4idxShort (Pi.single F4idxLong 1) =
      Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1 := by
    decide +kernel
  rw [← e]
  exact IsRoot.reflect _ (isRoot_single Tag.F4 F4idxLong)

private theorem F4_stringUp_eq :
    stringUp Tag.F4 F4idxShort (Pi.single F4idxLong 1) = 2 := by
  have hbd : ∀ k : ℕ,
      IsRoot Tag.F4 (Pi.single F4idxLong 1 + (k : ℤ) • Pi.single F4idxShort 1) → k ≤ 2 := by
    intro k hk
    have h := rootNorm_F4_mem_two hk
    rw [rootNorm_F4_formula] at h
    have hk2 : (k : ℤ) ≤ 2 := by
      by_contra hcon
      push Not at hcon
      rcases h with h | h <;> nlinarith
    omega
  apply le_antisymm
  · exact csSup_le ⟨0, by simpa using isRoot_single Tag.F4 F4idxLong⟩ (fun k hk => hbd k hk)
  · refine le_csSup ⟨2, by intro k hk; exact hbd k hk⟩ ?_
    show IsRoot Tag.F4 (Pi.single F4idxLong 1 + ((2 : ℕ) : ℤ) • Pi.single F4idxShort 1)
    have e : ((2 : ℕ) : ℤ) • (Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) =
        (2 : ℤ) • (Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) := by norm_num
    rw [e]
    exact isRoot_F4_e1_2e2

private theorem F4_stringDown_eq :
    stringDown Tag.F4 F4idxShort (Pi.single F4idxLong 1) = 0 := by
  have hbd : ∀ k : ℕ,
      IsRoot Tag.F4 (Pi.single F4idxLong 1 - (k : ℤ) • Pi.single F4idxShort 1) → k = 0 := by
    intro k hk
    have h := rootNorm_F4_mem_two hk
    have e : (Pi.single F4idxLong 1 : Fin Tag.F4.rank → ℤ) -
        (k : ℤ) • (Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) =
        (Pi.single F4idxLong 1 : Fin Tag.F4.rank → ℤ) +
          (-(k : ℤ)) • (Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) := by
      rw [neg_smul, sub_eq_add_neg]
    have hnn : (0 : ℤ) ≤ (k : ℤ) := by positivity
    rw [e, rootNorm_F4_formula] at h
    have hk0 : (k : ℤ) ≤ 0 := by
      rcases h with h | h <;> nlinarith
    omega
  apply le_antisymm
  · exact csSup_le ⟨0, by simpa using isRoot_single Tag.F4 F4idxLong⟩
      (fun k hk => (hbd k hk).le)
  · exact Nat.zero_le _

private theorem F4_string_formula (c : K) :
    endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) c)
        (rootVec Tag.F4 K (Pi.single F4idxLong 1)) =
      rootVec Tag.F4 K (Pi.single F4idxLong 1) +
        c • rootVec Tag.F4 K (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) +
        c ^ 2 • rootVec Tag.F4 K (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) := by
  have e : endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) c) =
      xOp Tag.F4 K F4idxShort c := by
    rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.F4).elt_simple]
  have hne1 : Pi.single F4idxLong 1 ≠ (Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) := by
    decide +kernel
  have hne2 : Pi.single F4idxLong 1 ≠ -(Pi.single F4idxShort 1 : Fin Tag.F4.rank → ℤ) := by
    decide +kernel
  rw [e, (simple_root_operators (τ := Tag.F4) (R := K) F4idxShort c).2.2.2.2.2.2.1 _
    (isRoot_single Tag.F4 F4idxLong) hne1 hne2, F4_stringUp_eq, F4_stringDown_eq]
  simp [Finset.sum_range_succ]

private theorem exists_omega_of_three_le {k : Subfield K} (h3 : 3 ≤ Nat.card k) :
    ∃ c₂ ∈ k, c₂ ≠ 0 ∧ c₂ ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : Nat.card k ≤ 2 := by
    have hinj : Function.Injective (fun x : k => decide ((x : K) = 0)) := by
      intro x y hxy
      have hx := hcon x x.2
      have hy := hcon y y.2
      simp only [decide_eq_decide] at hxy
      apply Subtype.ext
      by_cases h0 : (x : K) = 0
      · rw [h0, (hxy.1 h0)]
      · have hx1 := hx h0
        have hy0 : (y : K) ≠ 0 := fun h' => h0 (hxy.2 h')
        rw [hx1, hy hy0]
    simpa using Nat.card_le_card_of_injective _ hinj
  omega

theorem rootVec_mem_span_orbit (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β ∈ Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} := by
  classical
  set S := Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} with hS
  have hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R :=
    weylElement_one_mem_of_rat k R hrat
  have hRinv : ∀ r ∈ R, ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact S.smul_mem a hx
  have transfer : ∀ {γ δ : Fin τ.rank → ℤ}, IsRoot τ γ → IsRoot τ δ →
      rootNorm τ γ = rootNorm τ δ → rootVec τ K γ ∈ S → rootVec τ K δ ∈ S := by
    intro γ δ hγ hδ hn hγS
    obtain ⟨r, hr, ε, hε, hv, -⟩ := exists_weyl_move hτ hw hγ hδ hn
    have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rcases hε with rfl | rfl <;> simp
    have e : rootVec τ K δ = ((ε : ℤ) : K) • endHom K r (rootVec τ K γ) := by
      rw [hv, smul_smul, hεε, one_smul]
    rw [e]
    exact S.smul_mem _ (hRinv r hr _ hγS)
  have hθS : rootVec τ K θ ∈ S := Submodule.subset_span ⟨1, R.one_mem, by simp⟩
  have hsame : ∀ γ, IsRoot τ γ → rootNorm τ γ = rootNorm τ θ → rootVec τ K γ ∈ S :=
    fun γ hγ hn => transfer hθ.1 hγ hn.symm hθS
  by_cases hF : τ = .F4
  · subst hF
    have hθ4 : rootNorm Tag.F4 θ = 4 := hθ.rootNorm_F4
    have hα1 : rootVec Tag.F4 K (Pi.single F4idxLong 1) ∈ S :=
      hsame _ (isRoot_single Tag.F4 F4idxLong) (by rw [hθ4]; decide +kernel)
    obtain ⟨ω, hωk, hω0, hω1⟩ := exists_omega_of_three_le h3
    have hωne : ω - ω ^ 2 ≠ 0 := by
      have h := mul_ne_zero hω0 (sub_ne_zero.2 (Ne.symm hω1))
      intro h'
      apply h
      linear_combination h'
    have hx1 : endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) 1)
        (rootVec Tag.F4 K (Pi.single F4idxLong 1)) ∈ S :=
      hRinv _ (hrat _ (isRoot_single Tag.F4 F4idxShort) 1 k.one_mem) _ hα1
    have hxω : endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) ω)
        (rootVec Tag.F4 K (Pi.single F4idxLong 1)) ∈ S :=
      hRinv _ (hrat _ (isRoot_single Tag.F4 F4idxShort) ω hωk) _ hα1
    have hkey : (ω - ω ^ 2) • rootVec Tag.F4 K
        (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) =
        ω • (endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) 1)
              (rootVec Tag.F4 K (Pi.single F4idxLong 1)) -
            rootVec Tag.F4 K (Pi.single F4idxLong 1)) -
          (endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) ω)
              (rootVec Tag.F4 K (Pi.single F4idxLong 1)) -
            rootVec Tag.F4 K (Pi.single F4idxLong 1)) := by
      rw [F4_string_formula (K := K) 1, F4_string_formula (K := K) ω]
      module
    have hγS : rootVec Tag.F4 K (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) ∈ S := by
      have h1 : (ω - ω ^ 2) • rootVec Tag.F4 K
          (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) ∈ S := by
        rw [hkey]
        exact S.sub_mem (S.smul_mem _ (S.sub_mem hx1 hα1)) (S.sub_mem hxω hα1)
      have h2 := S.smul_mem (ω - ω ^ 2)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hωne, one_smul] at h2
    have hβ₀root : IsRoot Tag.F4 (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) :=
      isRoot_F4_e1_e2
    have hβ₀S : rootVec Tag.F4 K (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) ∈ S := by
      have h1 : rootVec Tag.F4 K (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) =
          (endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single F4idxShort 1) 1)
              (rootVec Tag.F4 K (Pi.single F4idxLong 1)) -
            rootVec Tag.F4 K (Pi.single F4idxLong 1)) -
          rootVec Tag.F4 K (Pi.single F4idxLong 1 + (2 : ℤ) • Pi.single F4idxShort 1) := by
        rw [F4_string_formula (K := K) 1]
        module
      rw [h1]
      exact S.sub_mem (S.sub_mem hx1 hα1) hγS
    have hβ₀norm : rootNorm Tag.F4 (Pi.single F4idxLong 1 + Pi.single F4idxShort 1) = 2 := by
      have h := rootNorm_F4_formula 1
      simp only [one_smul] at h
      linarith
    rcases rootNorm_F4_mem_two hβ with h | h
    · exact transfer hβ₀root hβ (by rw [hβ₀norm, h]) hβ₀S
    · exact hsame β hβ (by rw [h, hθ4])
  · have hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h hF
    exact hsame β hβ (by rw [rootNorm_E_two hE hβ, rootNorm_E_two hE hθ.1])

theorem hVec_mem_span_orbit (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (i : Fin τ.rank) :
    hVec τ K i ∈ Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} := by
  classical
  set S := Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} with hS
  have hRinv : ∀ r ∈ R, ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact S.smul_mem a hx
  have h1 : rootVec τ K (-Pi.single i 1) ∈ S :=
    rootVec_mem_span_orbit hτ h3 hrat hθ (isRoot_neg_single τ i)
  have h2 : rootVec τ K (Pi.single i 1) ∈ S :=
    rootVec_mem_span_orbit hτ h3 hrat hθ (isRoot_single τ i)
  have hxr : xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K) ∈ R :=
    hrat _ (isRoot_single τ i) 1 k.one_mem
  have h4 := hRinv _ hxr _ h1
  have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K)) = xOp τ K i 1 := by
    rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
  rw [e, CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single] at h4
  have h5 := S.sub_mem (S.sub_mem h4 h1) h2
  convert h5 using 1
  module

theorem span_orbit_eq_top (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) :
    Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} = ⊤ := by
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Label τ)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  rw [Finsupp.coe_basisSingleOne]
  rcases b with i | ⟨β, hβ⟩
  · exact hVec_mem_span_orbit hτ h3 hrat hθ i
  · have := rootVec_mem_span_orbit hτ h3 hrat hθ hβ
    rwa [rootVec_of_isRoot' hβ] at this

theorem endHom_xPar_simple_poly (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (i : Fin τ.rank) :
    (∃ X₁ X₂ : Module.End K (RootModule τ K), ∀ c : K,
        endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) c) = 1 + c • X₁ + c ^ 2 • X₂) ∧
      (∃ X₁ X₂ : Module.End K (RootModule τ K), ∀ c : K,
        endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) c) = 1 + c • X₁ + c ^ 2 • X₂) := by
  have hG2 : τ ≠ .G2 := by rcases hτ with rfl | rfl | rfl | rfl <;> decide
  have hb : entryDegreeBound τ = 2 := by simp [entryDegreeBound, hG2]
  constructor
  · refine ⟨xCoeff τ K i 1, xCoeff τ K i 2, fun c => ?_⟩
    have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) c) = xOp τ K i c := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    rw [e, xOp_eq_sum_xCoeff_entryDegreeBound, hb]
    simp [Finset.sum_range_succ, xCoeff_zero, add_assoc]
  · refine ⟨yCoeff τ K i 1, yCoeff τ K i 2, fun c => ?_⟩
    have e : endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) c) = yOp τ K i c := by
      rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
    rw [e, yOp_eq_sum_yCoeff_entryDegreeBound, hb]
    simp [Finset.sum_range_succ, yCoeff_zero, add_assoc]

theorem poly_invariant {V : Type*} [AddCommGroup V] [Module K V] (Z : Submodule K V)
    (X₁ X₂ : Module.End K V) {k : Subfield K} (h3 : 3 ≤ Nat.card k)
    (h : ∀ c ∈ k, ∀ z ∈ Z, z + c • X₁ z + c ^ 2 • X₂ z ∈ Z) (c : K) {z : V} (hz : z ∈ Z) :
    z + c • X₁ z + c ^ 2 • X₂ z ∈ Z := by
  classical
  obtain ⟨c₂, hc₂k, hc₂0, hc₂1⟩ : ∃ c₂ ∈ k, c₂ ≠ 0 ∧ c₂ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card k ≤ 2 := by
      have hinj : Function.Injective (fun x : k => decide ((x : K) = 0)) := by
        intro x y hxy
        have hx := hcon x x.2
        have hy := hcon y y.2
        simp only [decide_eq_decide] at hxy
        apply Subtype.ext
        by_cases h0 : (x : K) = 0
        · rw [h0, (hxy.1 h0)]
        · have hx1 := hx h0
          have hy0 : (y : K) ≠ 0 := fun h' => h0 (hxy.2 h')
          rw [hx1, hy hy0]
      simpa using Nat.card_le_card_of_injective _ hinj
    omega
  have hc₁ : (1 : K) ∈ k := k.one_mem
  have u1 := Z.sub_mem (h 1 hc₁ z hz) hz
  have u2 := Z.sub_mem (h c₂ hc₂k z hz) hz
  have v1 : (1 : K) • X₁ z + (1 : K) ^ 2 • X₂ z ∈ Z := by
    convert u1 using 1
    module
  have v2 : c₂ • X₁ z + c₂ ^ 2 • X₂ z ∈ Z := by
    convert u2 using 1
    module
  have hne : c₂ * (1 - c₂) ≠ 0 := mul_ne_zero hc₂0 (sub_ne_zero.2 (Ne.symm hc₂1))
  have hX₂ : X₂ z ∈ Z := by
    have e : (c₂ * (1 - c₂))⁻¹ • (c₂ • ((1 : K) • X₁ z + (1 : K) ^ 2 • X₂ z) -
        (1 : K) • (c₂ • X₁ z + c₂ ^ 2 • X₂ z)) = X₂ z := by
      have h' : c₂ • ((1 : K) • X₁ z + (1 : K) ^ 2 • X₂ z) - (1 : K) • (c₂ • X₁ z + c₂ ^ 2 • X₂ z) =
          (c₂ * (1 - c₂)) • X₂ z := by module
      rw [h', smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [← e]
    exact Z.smul_mem _ (Z.sub_mem (Z.smul_mem _ v1) (Z.smul_mem _ v2))
  have hX₁ : X₁ z ∈ Z := by
    have e : X₁ z = ((1 : K) • X₁ z + (1 : K) ^ 2 • X₂ z) - (1 : K) ^ 2 • X₂ z := by module
    rw [e]
    exact Z.sub_mem v1 (Z.smul_mem _ hX₂)
  exact Z.add_mem (Z.add_mem hz (Z.smul_mem _ hX₁)) (Z.smul_mem _ hX₂)

theorem vanishSub_invariant (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    (a : Label τ) (x : ↥(adjointGroup τ K)) {z : RootModule τ K} (hz : z ∈ vanishSub R a) :
    endHom K x z ∈ vanishSub R a := by
  classical
  set Z := vanishSub R a with hZ
  let Stab : Subgroup ↥(adjointGroup τ K) :=
    { carrier := {g | (∀ z ∈ Z, endHom K g z ∈ Z) ∧ (∀ z ∈ Z, endHom K g⁻¹ z ∈ Z)}
      one_mem' := ⟨fun z hz => by simpa using hz, fun z hz => by simpa using hz⟩
      mul_mem' := fun {g₁ g₂} h1 h2 => ⟨fun z hz => by
          rw [map_mul, Module.End.mul_apply]
          exact h1.1 _ (h2.1 z hz), fun z hz => by
          rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact h2.2 _ (h1.2 z hz)⟩
      inv_mem' := fun {g} h => ⟨h.2, fun z hz => by simpa using h.1 z hz⟩ }
  have hinvgen : ∀ (i : Fin τ.rank) (c : K), xPar (rootOperatorFamily τ) (Pi.single i 1) c ∈ Stab ∧
      xPar (rootOperatorFamily τ) (-Pi.single i 1) c ∈ Stab := by
    intro i c
    obtain ⟨⟨X₁, X₂, hX⟩, ⟨Y₁, Y₂, hY⟩⟩ := endHom_xPar_simple_poly (K := K) hτ i
    have key : ∀ (γ : Fin τ.rank → ℤ) (hγ : IsRoot τ γ) (X₁ X₂ : Module.End K (RootModule τ K)),
        (∀ c : K, endHom K (xPar (rootOperatorFamily τ) γ c) = 1 + c • X₁ + c ^ 2 • X₂) →
        ∀ c : K, ∀ z ∈ Z, endHom K (xPar (rootOperatorFamily τ) γ c) z ∈ Z := by
      intro γ hγ X₁ X₂ hX c z hz
      have h0 : ∀ c ∈ k, ∀ z ∈ Z, z + c • X₁ z + c ^ 2 • X₂ z ∈ Z := by
        intro c₀ hc₀ z hz
        have := hz
        have hr := hz
        have := (mem_vanishSub.1 hz)
        have hxR : xPar (rootOperatorFamily τ) γ c₀ ∈ R := hrat γ hγ c₀ hc₀
        have hRinv : endHom K (xPar (rootOperatorFamily τ) γ c₀) z ∈ Z := by
          intro r hr
          rw [← Module.End.mul_apply, ← map_mul]
          exact mem_vanishSub.1 hz (r * xPar (rootOperatorFamily τ) γ c₀) (R.mul_mem hr hxR)
        rw [hX c₀] at hRinv
        simpa [add_assoc] using hRinv
      have := poly_invariant Z X₁ X₂ h3 h0 c hz
      rw [hX c]
      simpa [add_assoc] using this
    have hneg : ∀ (γ : Fin τ.rank → ℤ) (c : K), (xPar (rootOperatorFamily τ) γ c)⁻¹ =
        xPar (rootOperatorFamily τ) γ (-c) := fun γ c => xPar_neg γ c
    refine ⟨⟨key _ (isRoot_single τ i) X₁ X₂ hX c, ?_⟩, ⟨key _ (isRoot_neg_single τ i) Y₁ Y₂ hY c, ?_⟩⟩
    · rw [hneg]
      exact key _ (isRoot_single τ i) X₁ X₂ hX (-c)
    · rw [hneg]
      exact key _ (isRoot_neg_single τ i) Y₁ Y₂ hY (-c)
  have htop : Stab = ⊤ := by
    set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
      (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c} with hS
    have hcl : Subgroup.closure (((↑) : ↥(adjointGroup τ K) → ModGL τ K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have e : g = xPar (rootOperatorFamily τ) (Pi.single i 1) c := endHom_injective (by
        rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).1
    · have e : g = xPar (rootOperatorFamily τ) (-Pi.single i 1) c := endHom_injective (by
        rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).2
  have hxS : x ∈ Stab := by rw [htop]; trivial
  exact hxS.1 z hz

theorem vanishSub_rootCoord (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {z : RootModule τ K}
    (hz : z ∈ vanishSub R (negLabel hθ.1)) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hn : rootNorm τ β = rootNorm τ θ) : z (rootLabel hβ) = 0 := by
  have hw := weylElement_one_mem_of_rat k R hrat
  obtain ⟨r, hr, ε, hε, -, hcoord⟩ := exists_weyl_move hτ hw hβ (isRoot_neg_iff.2 hθ.1)
    (hn.trans (rootNorm_neg θ).symm)
  have h0 := hz r hr
  rw [hcoord z] at h0
  rcases hε with rfl | rfl <;> simpa using h0

theorem xPar_neg_coord_formula {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    ∃ u : ℤ, (u = 1 ∨ u = -1) ∧ ∀ c : K,
      (endHom K (xPar (rootOperatorFamily τ) θ c) (rootVec τ K (-θ))) (rootLabel hθ) = (u : K) * c ^ 2 := by
  classical
  induction hθ with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun c => ?_⟩
    have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single j 1) c) = xOp τ K j c := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    rw [e, CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
    have hne : (Sum.inr ⟨-(Pi.single j 1 : Fin τ.rank → ℤ), isRoot_neg_single τ j⟩ : Label τ) ≠
        Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩ := by
      intro h
      have h' : (-(Pi.single j 1 : Fin τ.rank → ℤ)) = Pi.single j 1 := by simpa using h
      have := congrFun h' j
      simp at this
    simp [rootVec_eq_single (isRoot_single τ j), rootVec_eq_single (isRoot_neg_single τ j), hVec,
      Finsupp.single_apply, hne]
  | @reflect i v hv ih =>
    obtain ⟨u, hu, hform⟩ := ih
    obtain ⟨ε, hε, hconj⟩ := weylElement_xPar_conj (F := rootOperatorFamily τ) (K := K) i hv
    obtain ⟨ε₁, hε₁, -, hz₁⟩ := weyl_step_explicit (K := K) i hv
    obtain ⟨ε₂, hε₂, hv₂, -⟩ := weyl_step_explicit (K := K) i (isRoot_neg_iff.2 hv)
    set w := CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) with hw
    have hεε : (ε : K) * ε = 1 := by rcases hε with rfl | rfl <;> simp
    have hε₂₂ : (ε₂ : K) * ε₂ = 1 := by rcases hε₂ with rfl | rfl <;> simp
    have hrefl : CFSG.LieType.RootSystem.reflection τ.cartan i v = reflect τ i v := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    refine ⟨ε₂ * ε₁ * u, ?_, fun c => ?_⟩
    · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;> rcases hu with rfl | rfl <;> simp
    · have hx : w * xPar (rootOperatorFamily τ) v ((ε : K) * c) * w⁻¹ =
          xPar (rootOperatorFamily τ) (reflect τ i v) c := by
        have h1 := hconj 1 ((ε : K) * c)
        rw [hrefl] at h1
        simp only [Units.val_one, one_zpow, mul_one] at h1
        rw [h1]
        congr 1
        calc (ε : K) * ((ε : K) * c) = ((ε : K) * ε) * c := by ring
          _ = c := by rw [hεε, one_mul]
      have hinv : endHom K w⁻¹ (rootVec τ K (-(reflect τ i v))) = (ε₂ : K) • rootVec τ K (-v) := by
        have h1 : endHom K w⁻¹ (endHom K w (rootVec τ K (-v))) = rootVec τ K (-v) := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [hv₂, map_smul, CFSG.LieType.Steinberg.Adjoint.reflect_neg] at h1
        calc endHom K w⁻¹ (rootVec τ K (-(reflect τ i v)))
            = ((ε₂ : K) * ε₂) • endHom K w⁻¹ (rootVec τ K (-(reflect τ i v))) := by
              rw [hε₂₂, one_smul]
          _ = (ε₂ : K) • ((ε₂ : K) • endHom K w⁻¹ (rootVec τ K (-(reflect τ i v)))) := by
              rw [smul_smul]
          _ = (ε₂ : K) • rootVec τ K (-v) := by rw [h1]
      have hmain : endHom K (w * xPar (rootOperatorFamily τ) v ((ε : K) * c) * w⁻¹)
          (rootVec τ K (-(reflect τ i v))) = (ε₂ : K) • endHom K w
            (endHom K (xPar (rootOperatorFamily τ) v ((ε : K) * c)) (rootVec τ K (-v))) := by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, map_smul, map_smul]
      rw [← hx, hmain, Finsupp.smul_apply, hz₁, hform ((ε : K) * c), smul_eq_mul]
      push_cast
      linear_combination ((ε₂ : K) * ε₁ * u * c ^ 2) * hεε

theorem xPar_apply_neg_root_coord {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    (endHom K (xPar (rootOperatorFamily τ) θ (1 : K) : ↥(adjointGroup τ K)) (rootVec τ K (-θ)))
      (rootLabel hθ) ≠ 0 := by
  obtain ⟨u, hu, h⟩ := xPar_neg_coord_formula (K := K) hθ
  rw [h]
  rcases hu with rfl | rfl <;> simp

theorem eq_one_of_sub_mem_vanishSub (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K]
    {k : Subfield K} (h3 : 3 ≤ Nat.card k) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (x : ↥(adjointGroup τ K))
    (hx : ∀ v : RootModule τ K, endHom K x v - v ∈ vanishSub R (negLabel hθ.1)) : x = 1 := by
  classical
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hinv : ∀ y : ↥(adjointGroup τ K), ∀ z ∈ Z, endHom K y z ∈ Z := fun y z hz =>
    vanishSub_invariant hτ h3 hrat _ y hz
  let N : Subgroup ↥(adjointGroup τ K) :=
    { carrier := {y | ∀ v : RootModule τ K, endHom K y v - v ∈ Z}
      one_mem' := fun v => by simp
      mul_mem' := fun {y₁ y₂} h1 h2 v => by
        have e : endHom K (y₁ * y₂) v - v =
            endHom K y₁ (endHom K y₂ v - v) + (endHom K y₁ v - v) := by
          rw [map_mul, Module.End.mul_apply, map_sub]
          abel
        rw [e]
        exact Z.add_mem (hinv y₁ _ (h2 v)) (h1 v)
      inv_mem' := fun {y} h v => by
        have e : endHom K y⁻¹ v - v = -(endHom K y (endHom K y⁻¹ v) - endHom K y⁻¹ v) := by
          have : endHom K y (endHom K y⁻¹ v) = v := by
            rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          rw [this]
          abel
        rw [e]
        exact Z.neg_mem (h _) }
  have hNn : N.Normal := ⟨fun y hy h v => by
    have e : endHom K (h * y * h⁻¹) v - v = endHom K h (endHom K y (endHom K h⁻¹ v) - endHom K h⁻¹ v) := by
      have : endHom K h (endHom K h⁻¹ v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, map_sub, this]
    rw [e]
    exact hinv h _ (hy _)⟩
  haveI := isSimpleGroup_adjointGroup_of_type (K := K) hτ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have hxN : x ∈ N := hx
    rw [h] at hxN
    exact (Subgroup.mem_bot.1 hxN)
  · exfalso
    have hmem : xPar (rootOperatorFamily τ) θ (1 : K) ∈ N := by rw [h]; trivial
    have h1 := hmem (rootVec τ K (-θ))
    have h2 := vanishSub_rootCoord hτ h3 hrat hθ h1 hθ.1 rfl
    apply xPar_apply_neg_root_coord hθ.1 (K := K)
    have hv : (rootVec τ K (-θ)) (rootLabel hθ.1) = 0 := by
      rw [rootVec_of_isRoot' (isRoot_neg_iff.2 hθ.1)]
      have hne : (rootLabel hθ.1 : Label τ) ≠ negLabel hθ.1 := by
        intro hh
        have hh' : θ = -θ := by simpa using hh
        have := hθ.height_pos
        have h3' := congrArg height hh'
        simp only [height, Pi.neg_apply, Finset.sum_neg_distrib] at h3'
        simp only [height] at this
        omega
      simp [Finsupp.single_apply, hne]
    simpa [hv] using h2

theorem three_le_card_fixSubfield [Finite K] (σ : K ≃+* K)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) : 3 ≤ Nat.card (fixSubfield σ) := by
  classical
  rcases hD with h | h
  · have h2 : 2 ≤ Nat.card (fixSubfield σ) := Finite.one_lt_card
    by_contra hlt
    have hc : Nat.card (fixSubfield σ) = 2 := by omega
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype (fixSubfield σ) := Fintype.ofFinite _
    obtain ⟨n, hℓ, -⟩ := FiniteField.card K (ringChar K)
    haveI : CharP K (ringChar K) := ringChar.charP K
    haveI : CharP (fixSubfield σ) (ringChar K) :=
      ((fixSubfield σ).subtype.charP_iff Subtype.val_injective _).2 inferInstance
    obtain ⟨m, -, hm⟩ := FiniteField.card (fixSubfield σ) (ringChar K)
    rw [Nat.card_eq_fintype_card] at hc
    rw [hc] at hm
    have hdvd : ringChar K ∣ 2 := by
      rw [hm]
      exact dvd_pow_self _ m.ne_zero
    exact h ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd)
  · have := Nat.le_of_dvd Nat.card_pos h
    omega

theorem mem_subfieldGroup_of_entries (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K]
    (σ : K ≃+* K) (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ))
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hall : ∀ r ∈ subfieldGroup τ σ, ∀ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ subfieldGroup τ σ := by
  classical
  set k := fixSubfield σ with hk
  set R := subfieldGroup τ σ with hR
  have h3 : 3 ≤ Nat.card k := three_le_card_fixSubfield σ hD
  have hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R :=
    fun γ _ c hc => xPar_mem_subfieldGroup τ σ γ hc
  set g₂ : ↥(adjointGroup τ K) := entrywiseAdjointAut τ σ g with hg₂
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut τ σ r = r := fun r hr => mem_fixedSubgroup.1 hr
  have hent : ∀ r ∈ R, ∀ r' ∈ R, entry (r * g₂ * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : r * g₂ * r' = entrywiseAdjointAut τ σ (r * g * r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hDmem : ∀ r' ∈ R, (endHom K g₂ - endHom K g) (endHom K r' (rootVec τ K θ)) ∈ Z := by
    intro r' hr' r hr
    have hv : rootVec τ K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply, ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := span_orbit_eq_top hτ h3 hrat hθ
  have hle : Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} ≤
      Z.comap (endHom K g₂ - endHom K g) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    exact hDmem r' hr'
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K g) v ∈ Z := fun v => hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule τ K, endHom K (g₂ * g⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K g⁻¹ v)
    have e1 : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have h1 := eq_one_of_sub_mem_vanishSub hτ h3 hrat hθ (g₂ * g⁻¹) hx
  have h2 : g₂ = g := mul_inv_eq_one.1 h1
  rw [hR, subfieldGroup, mem_fixedSubgroup]
  exact h2

theorem exists_bad_entry (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K] (σ : K ≃+* K)
    (hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ)) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K)) (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ subfieldGroup τ σ, ∃ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
  by_contra h
  push Not at h
  exact hg (mem_subfieldGroup_of_entries hτ σ hD hθ g h)

end EntryLemma

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
