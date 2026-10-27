module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

public section

namespace CFSG.CGT.PushingUpLit.CGT6.WeilJoint

open Module

section Joint

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem exists_joint_eigenvector [IsAlgClosed K] [FiniteDimensional K W] {ι : Type}
    (f : ι → Module.End K W) (hcomm : ∀ i j, f i * f j = f j * f i) (s : Finset ι) :
    ∀ I : Submodule K W, I ≠ ⊥ → (∀ i, ∀ u ∈ I, f i u ∈ I) →
      ∃ φ ∈ I, φ ≠ 0 ∧ ∀ i ∈ s, ∃ μ : K, f i φ = μ • φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro I hI _
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨b, hb, hb0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert i s hi ih =>
    intro I hI hinv
    have : Nontrivial ↥I := Submodule.nontrivial_iff_ne_bot.mpr hI
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f i).restrict (hinv i))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hwμ : f i (w : W) = μ • (w : W) := by
      have := hw.apply_eq_smul
      exact congrArg Subtype.val this
    let I' : Submodule K W := I ⊓ Module.End.eigenspace (f i) μ
    have hwI' : (w : W) ∈ I' := ⟨w.2, Module.End.mem_eigenspace_iff.mpr hwμ⟩
    have hI' : I' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hwI'
      exact hw.2 (Subtype.ext hwI')
    have hinv' : ∀ j, ∀ u ∈ I', f j u ∈ I' := by
      intro j u hu
      refine ⟨hinv j u hu.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
      have h1 : f i u = μ • u := Module.End.mem_eigenspace_iff.mp hu.2
      have h2 : f i (f j u) = f j (f i u) := by
        have := congrArg (fun g => g u) (hcomm i j)
        exact this
      rw [h2, h1, map_smul]
    obtain ⟨φ, hφ, hφ0, hφs⟩ := ih I' hI' hinv'
    refine ⟨φ, hφ.1, hφ0, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact ⟨μ, Module.End.mem_eigenspace_iff.mp hφ.2⟩
    · exact hφs j hj'

theorem sub_one_apply_eq_zero_of_sq (c : Module.End K W) {N : ℕ} (hc : c ^ N = 1)
    (hN : (N : K) = 1) (u : W) (h : c ((c - 1) u) = (c - 1) u) : (c - 1) u = 0 := by
  set w : W := (c - 1) u with hw
  have hu : c u = u + w := by
    rw [hw, LinearMap.sub_apply, Module.End.one_apply]
    abel
  have hpow : ∀ n : ℕ, (c ^ n) u = u + (n : K) • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, h, hu]
      simp only [Nat.cast_succ, add_smul, one_smul]
      abel
  have h1 := hpow N
  rw [hc, hN, one_smul, Module.End.one_apply] at h1
  have h2 : w = 0 := by
    have := congrArg (fun y => y - u) h1
    simpa using this.symm
  exact h2

end Joint

section Independent

variable {K : Type} [Field K] {M : Type} [AddCommGroup M] [Module K M] [FiniteDimensional K M]

theorem finrank_biSup_eq_sum {ι : Type} [DecidableEq ι] (W : ι → Submodule K M)
    (hW : iSupIndep W) (s : Finset ι) :
    finrank K (⨆ i ∈ s, W i : Submodule K M) = ∑ i ∈ s, finrank K (W i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (W a) (⨆ i ∈ s, W i) := by
      have := hW.disjoint_biSup (y := (s : Set ι)) (x := a) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (⨆ i ∈ s, W i)
    rw [hd.eq_bot, finrank_bot, add_zero] at h
    exact h

theorem sum_finrank_map_le {ℓ : ℕ} (c N : Module.End K M) (U : Fin ℓ → Submodule K M)
    (μ : Fin ℓ → K) (hμ : Function.Injective μ)
    (hU : ∀ j, Submodule.map N (U j) ≤ Module.End.eigenspace c (μ j)) :
    ∑ j : Fin ℓ, finrank K (Submodule.map N (U j)) ≤ finrank K (LinearMap.range N) := by
  have hind : iSupIndep (fun j : Fin ℓ => Submodule.map N (U j)) :=
    ((Module.End.eigenspaces_iSupIndep c).comp hμ).mono (fun j => hU j)
  have h1 := finrank_biSup_eq_sum (fun j : Fin ℓ => Submodule.map N (U j)) hind Finset.univ
  rw [← h1]
  refine Submodule.finrank_mono (iSup₂_le fun j _ => ?_)
  rintro _ ⟨u, _, rfl⟩
  exact ⟨u, rfl⟩

end Independent

end CFSG.CGT.PushingUpLit.CGT6.WeilJoint
