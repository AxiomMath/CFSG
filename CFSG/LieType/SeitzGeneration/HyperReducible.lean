module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

variable {F : Type*} [Field F] [Finite F] {n : ℕ}

theorem isCyclic_of_commutative_irreducible [NeZero n]
    {H : Subgroup (SpecialLinearGroup (Fin n) F)} (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hirr : ∀ W : Submodule F (Fin n → F),
      (∀ x ∈ H, ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W) → W = ⊥ ∨ W = ⊤) :
    IsCyclic H := by
  classical
  let s : Set (Matrix (Fin n) (Fin n) F) :=
    {M | ∃ x ∈ H, (x : Matrix (Fin n) (Fin n) F) = M}
  have hsc : s.Pairwise Commute := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _
    exact congrArg Subtype.val (hcomm x hx y hy)
  let R : Subalgebra F (Matrix (Fin n) (Fin n) F) := Algebra.adjoin F s
  have hRc : IsMulCommutative R := Algebra.isMulCommutative_adjoin F hsc
  have hRs : ∀ a ∈ R, ∀ M ∈ s, M * a = a * M := by
    intro a ha M hM
    have hle : R ≤ Subalgebra.centralizer F s := Algebra.adjoin_le (fun M' hM' =>
      (Subalgebra.mem_centralizer_iff F).2 (fun g hg => by
        by_cases h : g = M'
        · rw [h]
        · exact (hsc hg hM' h).eq))
    exact (Subalgebra.mem_centralizer_iff F).1 (hle ha) M hM
  have hinj : ∀ a ∈ R, a ≠ 0 → ∀ v : Fin n → F, a.mulVec v = 0 → v = 0 := by
    intro a ha ha0 v hv
    have hK : ∀ x ∈ H, ∀ w ∈ LinearMap.ker (Matrix.toLin' a),
        (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ LinearMap.ker (Matrix.toLin' a) := by
      intro x hx w hw
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw ⊢
      rw [Matrix.mulVec_mulVec, ← hRs a ha x ⟨x, hx, rfl⟩, ← Matrix.mulVec_mulVec, hw,
        Matrix.mulVec_zero]
    rcases hirr _ hK with h | h
    · have : v ∈ LinearMap.ker (Matrix.toLin' a) := by
        rw [LinearMap.mem_ker, Matrix.toLin'_apply]
        exact hv
      rw [h] at this
      exact (Submodule.mem_bot F).1 this
    · exfalso
      apply ha0
      rw [Matrix.ext_iff_mulVec]
      intro w
      have hw : w ∈ LinearMap.ker (Matrix.toLin' a) := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hw
      rw [hw, Matrix.zero_mulVec]
  let _ : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun a b => hRc.is_comm.comm a b }
  have hnzd : NoZeroDivisors R := ⟨fun {a b} hab => by
    by_contra hne
    push Not at hne
    obtain ⟨ha0, hb0⟩ := hne
    have hab' : (a : Matrix (Fin n) (Fin n) F) * (b : Matrix (Fin n) (Fin n) F) = 0 :=
      congrArg Subtype.val hab
    let v : Fin n → F := Pi.single ⟨0, Nat.pos_of_neZero n⟩ 1
    have hv : v ≠ 0 := fun h => by
      have := congrFun h ⟨0, Nat.pos_of_neZero n⟩
      simp [v] at this
    have ha0' : (a : Matrix (Fin n) (Fin n) F) ≠ 0 := fun h => ha0 (Subtype.ext h)
    have hb0' : (b : Matrix (Fin n) (Fin n) F) ≠ 0 := fun h => hb0 (Subtype.ext h)
    have hbv : (b : Matrix (Fin n) (Fin n) F).mulVec v ≠ 0 := fun h =>
      hv (hinj b b.2 hb0' v h)
    apply hbv
    apply hinj a a.2 ha0'
    rw [Matrix.mulVec_mulVec, hab', Matrix.zero_mulVec]⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let f : H →* R :=
    { toFun := fun x => ⟨((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F),
        Algebra.subset_adjoin ⟨x, x.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hf : Function.Injective f := fun x y hxy => by
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h1)
  exact isCyclic_of_injective_ringHom f hf

theorem exists_stable_of_commutative [NeZero n]
    {E : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)} (hnc : ¬ IsCyclic E)
    (hcomm : ∀ x y : SpecialLinearGroup (Fin n) F,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) y ∈ E → x * y = y * x) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x : SpecialLinearGroup (Fin n) F,
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) x ∈ E →
          ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W := by
  by_contra hne
  push Not at hne
  set π : SpecialLinearGroup (Fin n) F →* ProjectiveSpecialLinearGroup (Fin n) F :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) with hπ
  set H : Subgroup (SpecialLinearGroup (Fin n) F) := E.comap π with hH
  have hHc : IsCyclic H := isCyclic_of_commutative_irreducible
    (fun x hx y hy => hcomm x y hx hy) (fun W hW => by
      by_contra h
      push Not at h
      obtain ⟨x, hx, w, hw, hnot⟩ := hne W h.1 h.2
      exact hnot (hW x hx w hw))
  let πH : H →* E := (π.comp H.subtype).codRestrict E (fun h => h.2)
  have hπH : Function.Surjective πH := by
    intro e
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F))
      (e : ProjectiveSpecialLinearGroup (Fin n) F)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    show π g ∈ E
    rw [show π g = (e : ProjectiveSpecialLinearGroup (Fin n) F) from hg]
    exact e.2
  exact hnc (isCyclic_of_surjective πH hπH)

end CFSG.LieType.SeitzGeneration
