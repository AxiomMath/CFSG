module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open Matrix
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Asm

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
  {a : Fin Tag.E6.rank → Lˣ}

@[expose] def ClassPeel (i : KernelComponent (rootCharHom a)) : Prop :=
  CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    ∀ Q' : Subgroup (ModGL Tag.E6 L), (∀ q ∈ Q', S.D.step q ∈ Q') →
      torusGroup Tag.E6 L ≤ Subgroup.normalizer (Q' : Set (ModGL Tag.E6 L)) →
      (∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i), ∀ b ∈ Q', u * b = b * u) →
      ∀ x ∈ torusGroup Tag.E6 L ⊔ (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊔ Q'),
        S.D.step x = x → ∃ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
          ∃ x' ∈ torusGroup Tag.E6 L ⊔ Q', S.D.step x' = x' ∧ x = r * x'

theorem conj_mem_rationalComponent (i : KernelComponent (rootCharHom a))
    (hstab : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    {t : ModGL Tag.E6 L} (ht : t ∈ torusGroup Tag.E6 L) (hFt : S.D.step t = t)
    {r : ModGL Tag.E6 L} (hr : r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    t * r * t⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  let φ : ModGL Tag.E6 L →* ModGL Tag.E6 L := (MulAut.conj t).toMonoidHom
  have hφ : ∀ g, φ g = t * g * t⁻¹ := fun g => rfl
  have htM : t ∈ S.D.model :=
    ⟨torusGroup_le_adjointGroup' ht, hFt⟩
  have hM : S.D.model.map φ ≤ S.D.model := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    exact mul_mem (mul_mem htM hg) (inv_mem htM)
  have hΓ : S.Γ.map φ ≤ S.Γ := by
    have h1 : (⁅S.D.model, S.D.model⁆).map φ ≤ ⁅S.D.model, S.D.model⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hM hM
    exact h1
  have hS : (rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i)).map φ ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hφ]
    have hN := torusGroup_le_normalizer_rootSpan (L := L) (τ := Tag.E6)
      (S := rationalRoots S.ρ (rootCharHom a) i) (by
        rw [rationalRoots_eq_componentRoots S i hstab]
        exact fun γ hγ => isRoot_of_mem_componentRoots hγ)
    exact (Subgroup.mem_normalizer_iff.1 (hN ht) g).1 hg
  have hrs : (rationalSpan S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf hS hΓ)
  have : (rationalComponent S.ρ S.Γ (rootCharHom a) i).map φ ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalComponent
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hrs hrs
  exact this ⟨r, hr, rfl⟩

@[expose] def classRoots (a : Fin Tag.E6.rank → Lˣ) (s : Finset (KernelComponent (rootCharHom a))) :
    Set (Fin Tag.E6.rank → ℤ) :=
  ⋃ j ∈ s, componentRoots (rootCharHom a) j

theorem classRoots_empty : classRoots a ∅ = ∅ := by
  simp [classRoots]

theorem classRoots_insert [DecidableEq (KernelComponent (rootCharHom a))]
    (i : KernelComponent (rootCharHom a)) (s : Finset (KernelComponent (rootCharHom a))) :
    classRoots a (insert i s) = componentRoots (rootCharHom a) i ∪ classRoots a s := by
  simp [classRoots, Finset.set_biUnion_insert]

theorem rootSpan_union (S₁ S₂ : Set (Fin Tag.E6.rank → ℤ)) :
    rootSpan Tag.E6 L (S₁ ∪ S₂) = rootSpan Tag.E6 L S₁ ⊔ rootSpan Tag.E6 L S₂ := by
  unfold rootSpan
  exact iSup_union

theorem isRoot_of_mem_classRoots {s : Finset (KernelComponent (rootCharHom a))}
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ classRoots a s) : IsRoot Tag.E6 γ := by
  obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hγ
  exact isRoot_of_mem_componentRoots hj

theorem step_rootSpan_le {Θ : Set (Fin Tag.E6.rank → ℤ)} (hroot : ∀ γ ∈ Θ, IsRoot Tag.E6 γ)
    (hΘ : ∀ γ ∈ Θ, S.ρ γ ∈ Θ) :
    (rootSpan Tag.E6 L Θ).map S.D.step ≤ rootSpan Tag.E6 L Θ := by
  refine map_rootSpan_le_of_forall fun γ hγ c => ?_
  obtain ⟨μ, -, hμ⟩ := step_pinnedX S (hroot γ hγ)
  rw [hμ]
  exact pinnedX_mem_rootSpan (hΘ γ hγ) _

theorem rootSpan_comm_classRoots (i : KernelComponent (rootCharHom a))
    {s : Finset (KernelComponent (rootCharHom a))} (hi : i ∉ s) :
    ∀ u ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom a) i),
      ∀ b ∈ rootSpan Tag.E6 L (classRoots a s), u * b = b * u := by
  refine rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
    (fun γ hγ => isRoot_of_mem_componentRoots hγ) (fun γ hγ => isRoot_of_mem_classRoots hγ) ?_
  intro α hα β hβ
  obtain ⟨j, hj, hβj⟩ := Set.mem_iUnion₂.1 hβ
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβj
  rw [dotProduct_mulVec_eq_iform]
  refine iform_eq_zero_of_mk_ne (α := ⟨α, hα1⟩) (β := ⟨β, hβ1⟩) ?_
  rw [hα2, hβ2]
  rintro rfl
  exact hi hj

theorem peel_classes (hall : ∀ i : KernelComponent (rootCharHom a), ClassPeel S i)
    (hstab : ∀ i : KernelComponent (rootCharHom a), ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    ∀ s : Finset (KernelComponent (rootCharHom a)),
      ∀ x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (classRoots a s), S.D.step x = x →
        ∃ r ∈ ⨆ j ∈ s, rationalComponent S.ρ S.Γ (rootCharHom a) j,
          ∃ t ∈ torusGroup Tag.E6 L, S.D.step t = t ∧ x = r * t := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x hx hFx
    refine ⟨1, one_mem _, x, ?_, hFx, (one_mul x).symm⟩
    have h0 : rootSpan Tag.E6 L (classRoots a ∅) = ⊥ := by
      rw [classRoots_empty]
      simp [rootSpan]
    rwa [h0, sup_bot_eq] at hx
  | insert i s hi ih =>
    intro x hx hFx
    rw [classRoots_insert, rootSpan_union] at hx
    have hQF : ∀ q ∈ rootSpan Tag.E6 L (classRoots a s),
        S.D.step q ∈ rootSpan Tag.E6 L (classRoots a s) := by
      intro q hq
      refine step_rootSpan_le S (fun γ hγ => isRoot_of_mem_classRoots hγ) ?_ ⟨q, hq, rfl⟩
      intro γ hγ
      obtain ⟨j, hj, hγj⟩ := Set.mem_iUnion₂.1 hγ
      exact Set.mem_iUnion₂.2 ⟨j, hj, hstab j γ hγj⟩
    obtain ⟨r, hr, x', hx'mem, hFx', rfl⟩ := (hall i).2 _ hQF
      (CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan
        (fun γ hγ => isRoot_of_mem_classRoots hγ))
      (rootSpan_comm_classRoots i hi) x hx hFx
    obtain ⟨r', hr', t, ht, hFt, rfl⟩ := ih x' hx'mem hFx'
    have h1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
        ⨆ j ∈ insert i s, rationalComponent S.ρ S.Γ (rootCharHom a) j :=
      le_iSup₂_of_le (f := fun j (_ : j ∈ insert i s) =>
        rationalComponent S.ρ S.Γ (rootCharHom a) j) i (Finset.mem_insert_self i s) le_rfl
    have h2 : (⨆ j ∈ s, rationalComponent S.ρ S.Γ (rootCharHom a) j) ≤
        ⨆ j ∈ insert i s, rationalComponent S.ρ S.Γ (rootCharHom a) j :=
      iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ∈ insert i s) =>
        rationalComponent S.ρ S.Γ (rootCharHom a) j) j (Finset.mem_insert_of_mem hj) le_rfl
    exact ⟨r * r', mul_mem (h1 hr) (h2 hr'), t, ht, hFt, by rw [mul_assoc]⟩

theorem fixed_of_classPeel (hall : ∀ i : KernelComponent (rootCharHom a), ClassPeel S i)
    (hstab : ∀ i : KernelComponent (rootCharHom a), ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    ∀ x ∈ torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
      S.D.step x = x → ∃ t, S.D.step t = t ∧ (∀ s ∈ torusGroup Tag.E6 L, s * t = t * s) ∧
        ∃ r ∈ ⨆ (i : KernelComponent (rootCharHom a))
          (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
            rationalComponent S.ρ S.Γ (rootCharHom a) i, x = t * r := by
  classical
  intro x hx hFx
  haveI : Finite (KernelComponent (rootCharHom a)) :=
    (root_character_kernel_orthogonal_central_product Tag.E6 L (rootCharHom a)).2.1
  haveI := Fintype.ofFinite (KernelComponent (rootCharHom a))
  have hker : classRoots a Finset.univ = kernelRoots (rootCharHom a) := by
    ext γ
    constructor
    · intro hγ
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hγ
      obtain ⟨h1, -⟩ := hj
      exact h1
    · intro hγ
      exact Set.mem_iUnion₂.2 ⟨⟦⟨γ, hγ⟩⟧, Finset.mem_univ _, hγ, rfl⟩
  rw [← hker] at hx
  obtain ⟨r, hr, t, ht, hFt, rfl⟩ := peel_classes S hall hstab Finset.univ x hx hFx
  refine ⟨t, hFt, fun s hs => torusGroup_comm hs ht, t⁻¹ * r * t, ?_, by group⟩
  have hle : (⨆ j ∈ (Finset.univ : Finset (KernelComponent (rootCharHom a))),
      rationalComponent S.ρ S.Γ (rootCharHom a) j) ≤
      (⨆ (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
          rationalComponent S.ρ S.Γ (rootCharHom a) i).comap (MulAut.conj t⁻¹).toMonoidHom := by
    refine iSup₂_le fun j _ g hg => ?_
    have h1 := conj_mem_rationalComponent S j (hstab j) (inv_mem ht)
      (by rw [map_inv, hFt]) hg
    rw [inv_inv] at h1
    have h3 : rationalComponent S.ρ S.Γ (rootCharHom a) j ≤
        ⨆ (i : KernelComponent (rootCharHom a))
          (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)),
            rationalComponent S.ρ S.Γ (rootCharHom a) i :=
      le_iSup₂_of_le (f := fun (i : KernelComponent (rootCharHom a))
        (_ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) =>
          rationalComponent S.ρ S.Γ (rootCharHom a) i) j (hall j).1 le_rfl
    exact h3 (by simpa [mul_assoc] using h1)
  have := hle hr
  simpa [MulAut.conj_apply, mul_assoc] using this

end Asm

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
