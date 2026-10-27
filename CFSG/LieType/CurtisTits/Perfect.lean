module

public import CFSG.LieType.CurtisTits.Reduction
public import CFSG.LieType.Universal.RootData

public section

namespace CFSG.LieType.CurtisTits

open CFSG.LieType.RootSystem CFSG.LieType.Universal

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {nw : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem weylAction_mem_roots {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (w : (coxeterMatrix D.isFiniteType).Group) : weylAction D.isFiniteType w γ ∈ D.roots := by
  rcases hγ with ⟨w', i, rfl⟩ | ⟨w', i, hi, rfl⟩
  · exact Or.inl ⟨w * w', i, by rw [weylAction_mul_apply]⟩
  · refine Or.inr ⟨w * w', i, hi, ?_⟩
    rw [map_nsmul, weylAction_mul_apply]

theorem rootGroup_weylAction_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    {N : Subgroup K} [N.Normal] {v : Fin D.rank → ℤ} (hv : v ∈ D.roots)
    (hN : D.rootGroup v ≤ N) (w : (coxeterMatrix D.isFiniteType).Group) :
    D.rootGroup (weylAction D.isFiniteType w v) ≤ N := by
  induction w using (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_induction_left with
  | one => simpa using hN
  | mul_simple_left w i ih =>
    intro x hx
    set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
    have hγ := weylAction_mem_roots hv (cs.simple i * w)
    have hconj := hct.conj_mem i _ hγ x hx
    have heq : weylAction D.isFiniteType (cs.simple i)
        (weylAction D.isFiniteType (cs.simple i * w) v) = weylAction D.isFiniteType w v := by
      rw [← weylAction_mul_apply, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
    rw [heq] at hconj
    have hmem := ‹N.Normal›.conj_mem _ (ih hconj) (nw i)⁻¹
    simpa [mul_assoc] using hmem

theorem isPerfect_of_rootGroup_single_le_commutator
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    (h2 : ∀ γ ∈ D.roots, 2 • γ ∈ D.roots → D.rootGroup (2 • γ) ≤ D.rootGroup γ)
    (hfund : ∀ i, D.rootGroup (Pi.single i 1) ≤ commutator K) : Group.IsPerfect K := by
  rw [Group.isPerfect_def, eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  have hsingle : ∀ i, Pi.single i 1 ∈ D.roots := fun i => Or.inl ⟨1, i, by simp⟩
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact rootGroup_weylAction_le hct (hsingle i) (hfund i) w
  · have h2i : 2 • Pi.single i (1 : ℤ) ∈ D.roots := Or.inr ⟨1, i, hi, by simp⟩
    rw [← map_nsmul]
    exact rootGroup_weylAction_le hct h2i ((h2 _ (hsingle i) h2i).trans (hfund i)) w

theorem isPerfect_of_exists_weylAction_eq
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw H)
    (h2 : ∀ γ ∈ D.roots, 2 • γ ∈ D.roots → D.rootGroup (2 • γ) ≤ D.rootGroup γ)
    (hfund : ∀ i, ∃ v ∈ D.roots, D.rootGroup v ≤ commutator K ∧
      ∃ w : (coxeterMatrix D.isFiniteType).Group, weylAction D.isFiniteType w v = Pi.single i 1) :
    Group.IsPerfect K :=
  isPerfect_of_rootGroup_single_le_commutator hct h2 fun i => by
    obtain ⟨v, hv, hle, w, hw⟩ := hfund i
    rw [← hw]
    exact rootGroup_weylAction_le hct hv hle w

end CFSG.LieType.CurtisTits
