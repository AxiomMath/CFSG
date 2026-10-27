module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

@[expose] def diagEig (a : Fin τ.rank → Kˣ) : Label τ → K
  | .inl _ => 1
  | .inr α => ((∏ i, a i ^ α.1 i : Kˣ) : K)

theorem rootDiag_single_eq (a : Fin τ.rank → Kˣ) (b : Label τ) :
    rootDiag a (Finsupp.single b 1) = diagEig a b • Finsupp.single b (1 : K) := by
  rcases b with i | α
  · rw [rootDiag_single_inl, diagEig, one_smul]
  · rw [rootDiag_single_inr]
    rfl

theorem rootDiag_apply (a : Fin τ.rank → Kˣ) (w : RootModule τ K) (c : Label τ) :
    rootDiag a w c = diagEig a c * w c := by
  classical
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
  | single b r =>
    have hs : Finsupp.single b r = r • Finsupp.single b (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, rootDiag_single_eq, smul_smul, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with h
    · subst h
      ring
    · ring

theorem apply_single_eq_smul_of_commute {D : Set (Fin τ.rank → Kˣ)}
    {u : Module.End K (RootModule τ K)} (hu : ∀ a ∈ D, rootDiag a * u = u * rootDiag a)
    {β : Label τ} (hsep : ∀ c : Label τ, c ≠ β → ∃ a ∈ D, diagEig a c ≠ diagEig a β) :
    u (Finsupp.single β 1) = u (Finsupp.single β 1) β • Finsupp.single β (1 : K) := by
  classical
  ext c
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  by_cases hc : β = c
  · subst hc
    simp
  · rw [if_neg hc, mul_zero]
    obtain ⟨a, ha, hne⟩ := hsep c (Ne.symm hc)
    have h1 : rootDiag a (u (Finsupp.single β 1)) =
        diagEig a β • u (Finsupp.single β (1 : K)) := by
      have h2 := congrArg (fun f : Module.End K (RootModule τ K) => f (Finsupp.single β 1))
        (hu a ha)
      simp only [Module.End.mul_apply] at h2
      rw [h2, rootDiag_single_eq, map_smul]
    have h3 := congrArg (fun w : RootModule τ K => w c) h1
    simp only [Finsupp.smul_apply, smul_eq_mul] at h3
    rw [rootDiag_apply] at h3
    have h4 : (diagEig a c - diagEig a β) * u (Finsupp.single β 1) c = 0 := by
      rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (sub_eq_zero.1 h5) hne
    · exact h5

theorem exists_unit_smul_of_commute {D : Set (Fin τ.rank → Kˣ)} {u : ModGL τ K}
    (hu : ∀ a ∈ D, rootDiagUnit τ a * u = u * rootDiagUnit τ a)
    {β : Label τ} (hsep : ∀ c : Label τ, c ≠ β → ∃ a ∈ D, diagEig a c ≠ diagEig a β) :
    ∃ s : Kˣ, (u : Module.End K (RootModule τ K)) (Finsupp.single β 1) =
        (s : K) • Finsupp.single β (1 : K) ∧
      ((u⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single β 1) =
        ((s⁻¹ : Kˣ) : K) • Finsupp.single β (1 : K) := by
  classical
  have hu' : ∀ a ∈ D, rootDiag a * (u : Module.End K (RootModule τ K)) =
      (u : Module.End K (RootModule τ K)) * rootDiag a := fun a ha =>
    congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))) (hu a ha)
  have h := apply_single_eq_smul_of_commute hu' hsep
  set s : K := (u : Module.End K (RootModule τ K)) (Finsupp.single β 1) β with hsdef
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h
    have hinj : Function.Injective (u : Module.End K (RootModule τ K)) := by
      intro w w' hww'
      have := congrArg (fun z => ((u⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) z) hww'
      simpa [← Module.End.mul_apply, ← Units.val_mul] using this
    have h1 := hinj (h.trans (map_zero _).symm)
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrArg (fun w : RootModule τ K => w β) h1)
  refine ⟨Units.mk0 s hs0, h, ?_⟩
  have h2 : (u : Module.End K (RootModule τ K))
      (((Units.mk0 s hs0)⁻¹ : Kˣ) • Finsupp.single β (1 : K)) = Finsupp.single β 1 := by
    rw [Units.smul_def, map_smul, h, smul_smul, Units.val_inv_eq_inv_val, Units.val_mk0,
      inv_mul_cancel₀ hs0, one_smul]
  have h3 := congrArg (fun z => ((u⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) z) h2
  simp only [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply] at h3
  rw [← h3, Units.smul_def]

theorem commutator_apply_single_of_commute {D : Set (Fin τ.rank → Kˣ)} {u v : ModGL τ K}
    (hu : ∀ a ∈ D, rootDiagUnit τ a * u = u * rootDiagUnit τ a)
    (hv : ∀ a ∈ D, rootDiagUnit τ a * v = v * rootDiagUnit τ a)
    {β : Label τ} (hsep : ∀ c : Label τ, c ≠ β → ∃ a ∈ D, diagEig a c ≠ diagEig a β) :
    ((u * v * u⁻¹ * v⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (Finsupp.single β 1) =
      Finsupp.single β 1 := by
  obtain ⟨s, hs, hs'⟩ := exists_unit_smul_of_commute hu hsep
  obtain ⟨t, ht, ht'⟩ := exists_unit_smul_of_commute hv hsep
  simp only [Units.val_mul, Module.End.mul_apply, map_smul, hs, hs', ht, ht', smul_smul]
  have h0 : (((t⁻¹ : Kˣ) : K) * (((s⁻¹ : Kˣ) : K) * ((t : K) * (s : K)))) = 1 := by
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have h1 : ∀ x : K, x = 1 → x • Finsupp.single β (1 : K) = Finsupp.single β 1 := by
    rintro x rfl
    exact one_smul _ _
  apply h1
  simp only [Units.val_inv_eq_inv_val]
  field_simp

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
