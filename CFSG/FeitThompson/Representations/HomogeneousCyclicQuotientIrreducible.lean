module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import CFSG.FeitThompson.Representations.SchurLemmaAlgebraicallyClosed
import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField
import CFSG.FeitThompson.OddOrder.CliffordConjugateDirectSumBasis
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.CategoryTheory.Category.Init

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module DirectSum

section Generalities

variable {k H V W : Type*} [Field k] [Group H] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem Representation.isIrreducible_comp {H' : Type*} [Group H'] {ρ : Representation k H V}
    (hρ : ρ.IsIrreducible) (f : H' →* H) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) := by
  have := hρ
  have : Nontrivial V := nontrivial_of_isIrreducible ρ
  refine isIrreducible_of_forall_map_le (fun U hU => ?_)
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr (eq_top_of_isIrreducible_of_map_le hρ (fun g => ?_) h)
    obtain ⟨g', rfl⟩ := hf g
    exact hU g'

def stabSubmodule (ρ : Representation k H V) (U : Submodule k V) : Subgroup H where
  carrier := {g | U.map (ρ g) = U}
  one_mem' := by simpa using map_rho_one ρ U
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [← map_rho_map_rho, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha, map_rho_map_rho, inv_mul_cancel, map_rho_one]

theorem mem_stabSubmodule_iff (ρ : Representation k H V) (U : Submodule k V) (g : H) :
    g ∈ stabSubmodule ρ U ↔ U.map (ρ g) = U := Iff.rfl

theorem mem_stabSubmodule_of_map_le [FiniteDimensional k V] (ρ : Representation k H V)
    {U : Submodule k V} {g : H} (h : ∀ v ∈ U, ρ g v ∈ U) : g ∈ stabSubmodule ρ U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
    (finrank_map_rho ρ g U)

theorem Representation.exists_smul_eq_of_intertwiner [IsAlgClosed k] [FiniteDimensional k V]
    {ρ : Representation k H V} {σ : Representation k H W} (hρ : ρ.IsIrreducible)
    (hσ : σ.IsIrreducible) (f g : V →ₗ[k] W)
    (hf : ∀ (h : H) (v : V), f (ρ h v) = σ h (f v))
    (hg : ∀ (h : H) (v : V), g (ρ h v) = σ h (g v)) (hg0 : g ≠ 0) :
    ∃ c : k, ∀ v : V, f v = c • g v := by
  have := hρ; have := hσ
  set G : ρ.IntertwiningMap σ := ⟨g, fun h => by ext v; exact hg h v⟩ with hG
  have hGne : G ≠ 0 := fun hc => hg0 (by
    have h := congrArg _root_.Representation.IntertwiningMap.toLinearMap hc
    simpa [hG] using h)
  have hgb : Function.Bijective g := by
    rcases _root_.Representation.IsIrreducible.bijective_or_eq_zero G with h | h
    · exact h
    · exact absurd h hGne
  set gE : V ≃ₗ[k] W := LinearEquiv.ofBijective g hgb with hgE
  have hgEapp : ∀ v, gE v = g v := fun v => rfl
  set T : Module.End k V := gE.symm.toLinearMap ∘ₗ f with hT
  have hcomm : ∀ h : H, Commute T (ρ h) := by
    intro h
    ext v
    change gE.symm (f (ρ h v)) = ρ h (gE.symm (f v))
    have h2 : gE (ρ h (gE.symm (f v))) = σ h (f v) := by
      rw [hgEapp, hg h, ← hgEapp, gE.apply_symm_apply]
    rw [hf h, ← h2, gE.symm_apply_apply]
  obtain ⟨c, hc⟩ :=
    Representation.IsIrreducible.exists_forall_apply_eq_smul_of_commute ρ T hcomm
  refine ⟨c, fun v => ?_⟩
  have h3 : gE.symm (f v) = c • v := hc v
  calc f v = gE (gE.symm (f v)) := (gE.apply_symm_apply _).symm
    _ = gE (c • v) := by rw [h3]
    _ = c • g v := by rw [map_smul, hgEapp]

end Generalities

section ConjRep

variable {k G M : Type*} [Field k] [Group G] [AddCommGroup M] [Module k M] {N : Subgroup G}
  [N.Normal]

noncomputable def conjRep (σ : Representation k N M) (x : G) : Representation k N M :=
  σ.comp (MulAut.conjNormal (H := N) x).toMonoidHom

@[simp]
theorem conjRep_apply (σ : Representation k N M) (x : G) (n : N) :
    conjRep σ x n = σ (MulAut.conjNormal (H := N) x n) := (rfl)

theorem coe_conjNormal (x : G) (n : N) :
    ((MulAut.conjNormal (H := N) x n : N) : G) = x * (n : G) * x⁻¹ :=
  MulAut.conjNormal_apply x n

@[simp]
theorem conjRep_one (σ : Representation k N M) : conjRep σ (1 : G) = σ := by
  ext n u
  rw [conjRep_apply]
  congr 2
  ext
  rw [coe_conjNormal]
  group

theorem isIrreducible_conjRep {σ : Representation k N M} (hσ : σ.IsIrreducible) (x : G) :
    Representation.IsIrreducible (conjRep σ x) :=
  Representation.isIrreducible_comp hσ _ (MulAut.conjNormal (H := N) x).surjective

end ConjRep

section DirectSumAux

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] {m : ℕ}

theorem ds_apply_eq_component (z : ⨁ _ : Fin m, M) (i : Fin m) :
    DirectSum.component k (Fin m) (fun _ => M) i z = z i :=
  (DirectSum.apply_eq_component (R := k) (M := fun _ : Fin m => M) z i).symm

theorem ds_ext {z y : ⨁ _ : Fin m, M} (h : ∀ i, z i = y i) : z = y := DFunLike.ext _ _ h

noncomputable def tensorLine (w : Fin m → k) : M →ₗ[k] (⨁ _ : Fin m, M) :=
  ∑ j, w j • DirectSum.lof k (Fin m) (fun _ => M) j

@[simp]
theorem tensorLine_apply_apply (w : Fin m → k) (u : M) (i : Fin m) :
    tensorLine w u i = w i • u := by
  classical
  rw [← ds_apply_eq_component (k := k) (tensorLine w u) i, tensorLine, LinearMap.sum_apply,
    map_sum, Finset.sum_eq_single i]
  · rw [LinearMap.smul_apply, map_smul, DirectSum.component.lof_self]
  · intro j _ hj
    rw [LinearMap.smul_apply, map_smul, DirectSum.component.of, dif_neg hj, smul_zero]
  · simp

theorem tensorLine_eq_sum (w : Fin m → k) (u : M) :
    tensorLine (M := M) w u = ∑ j, DirectSum.lof k (Fin m) (fun _ => M) j (w j • u) := by
  classical
  refine ds_ext fun i => ?_
  rw [tensorLine_apply_apply, ← ds_apply_eq_component (k := k) _ i, map_sum,
    Finset.sum_eq_single i]
  · rw [DirectSum.component.lof_self]
  · intro j _ hj
    rw [DirectSum.component.of, dif_neg hj]
  · simp

noncomputable def dsFinOneEquiv : (⨁ _ : Fin 1, M) ≃ₗ[k] M :=
  LinearEquiv.ofBijective (DirectSum.component k (Fin 1) (fun _ => M) 0)
    ⟨fun a b hab => ds_ext fun i => by
      rw [Subsingleton.elim i 0, ← ds_apply_eq_component (k := k) a,
        ← ds_apply_eq_component (k := k) b]
      exact hab,
     fun u => ⟨DirectSum.lof k (Fin 1) (fun _ => M) 0 u, DirectSum.component.lof_self _ _ _⟩⟩

@[simp]
theorem dsFinOneEquiv_apply (z : ⨁ _ : Fin 1, M) : dsFinOneEquiv (k := k) z = z 0 :=
  ds_apply_eq_component z 0

theorem tensorLine_injective {w : Fin m → k} (hw : w ≠ 0) :
    Function.Injective (tensorLine (M := M) w) := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc
    exact hw (funext fun j => not_not.1 (fun h => hc ⟨j, h⟩))
  intro a b hab
  have h := congrArg (fun z : ⨁ _ : Fin m, M => z i) hab
  simp only [tensorLine_apply_apply] at h
  exact smul_right_injective M hi h

end DirectSumAux

section Main

variable {k G M V : Type*} [Field k] [Group G] [AddCommGroup M] [Module k M]
  [AddCommGroup V] [Module k V] {N : Subgroup G} [N.Normal] {m : ℕ}
  {ρ : Representation k G V} {σ : Representation k N M}

omit [N.Normal] in
theorem directSum_apply_apply (n : N) (z : ⨁ _ : Fin m, M) (i : Fin m) :
    ((Representation.directSum fun _ : Fin m => σ) n z) i = σ n (z i) := by
  rw [Representation.directSum_apply, DirectSum.lmap_apply]

omit [N.Normal] in
theorem directSum_apply_lof (n : N) (j : Fin m) (u : M) :
    (Representation.directSum fun _ : Fin m => σ) n (DirectSum.lof k (Fin m) (fun _ => M) j u)
      = DirectSum.lof k (Fin m) (fun _ => M) j (σ n u) := by
  rw [Representation.directSum_apply, DirectSum.lmap_lof]

theorem equiv_rho_conj (e : Representation.Equiv (ρ.comp N.subtype)
    (Representation.directSum fun _ : Fin m => σ)) (x : G) (n : N) (z : ⨁ _ : Fin m, M) :
    e.toLinearEquiv (ρ x (e.toLinearEquiv.symm
        ((Representation.directSum fun _ : Fin m => σ) n z)))
      = (Representation.directSum fun _ : Fin m => σ) (MulAut.conjNormal (H := N) x n)
          (e.toLinearEquiv (ρ x (e.toLinearEquiv.symm z))) := by
  have he : ∀ (n : N) (v : V), e.toLinearEquiv (ρ (n : G) v)
      = (Representation.directSum fun _ : Fin m => σ) n (e.toLinearEquiv v) := fun n v => by
    simpa using Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap n v
  have hsym : ∀ (n : N) (w : ⨁ _ : Fin m, M),
      e.toLinearEquiv.symm ((Representation.directSum fun _ : Fin m => σ) n w)
        = ρ (n : G) (e.toLinearEquiv.symm w) := by
    intro n w
    apply e.toLinearEquiv.injective
    rw [e.toLinearEquiv.apply_symm_apply, he n, e.toLinearEquiv.apply_symm_apply]
  rw [hsym]
  have hx : x * (n : G) = ((MulAut.conjNormal (H := N) x n : N) : G) * x := by
    rw [coe_conjNormal]; group
  rw [← Module.End.mul_apply, ← map_mul, hx, map_mul, Module.End.mul_apply, he]

theorem exists_matrix_of_twist [IsAlgClosed k] [FiniteDimensional k M] (hσ : σ.IsIrreducible)
    (e : Representation.Equiv (ρ.comp N.subtype)
      (Representation.directSum fun _ : Fin m => σ)) (x : G) :
    ∃ (S : M →ₗ[k] M) (t : Matrix (Fin m) (Fin m) k),
      (∀ (n : N) (u : M), S (conjRep σ x⁻¹ n u) = σ n (S u)) ∧
      ∀ (u : M) (j i : Fin m),
        (e.toLinearEquiv (ρ x (e.toLinearEquiv.symm
          (DirectSum.lof k (Fin m) (fun _ => M) j u)))) i = t i j • S u := by
  classical
  set R : (⨁ _ : Fin m, M) →ₗ[k] (⨁ _ : Fin m, M) :=
    e.toLinearEquiv.toLinearMap ∘ₗ (ρ x : V →ₗ[k] V) ∘ₗ e.toLinearEquiv.symm.toLinearMap with hR
  have hRapp : ∀ z, R z = e.toLinearEquiv (ρ x (e.toLinearEquiv.symm z)) := fun z => rfl
  set B : Fin m → Fin m → M →ₗ[k] M := fun i j =>
    DirectSum.component k (Fin m) (fun _ => M) i ∘ₗ R ∘ₗ
      DirectSum.lof k (Fin m) (fun _ => M) j with hB
  have hBapp : ∀ (i j : Fin m) (u : M),
      B i j u = (R (DirectSum.lof k (Fin m) (fun _ => M) j u)) i := fun i j u => by
    rw [hB]
    simp only [LinearMap.comp_apply]
    exact ds_apply_eq_component _ i
  have hBint : ∀ (i j : Fin m) (n : N) (u : M), B i j (conjRep σ x⁻¹ n u) = σ n (B i j u) := by
    intro i j n u
    have hnn : MulAut.conjNormal (H := N) x (MulAut.conjNormal (H := N) x⁻¹ n) = n := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [hBapp, hBapp, conjRep_apply, ← directSum_apply_lof, hRapp, hRapp, equiv_rho_conj,
      directSum_apply_apply, hnn]
  have hconj : Representation.IsIrreducible (conjRep σ x⁻¹) := isIrreducible_conjRep hσ x⁻¹
  by_cases hall : ∀ (i j : Fin m), B i j = 0
  ·
    refine ⟨0, 0, fun n u => by simp, fun u j i => ?_⟩
    rw [← hRapp, ← hBapp, hall i j]
    simp
  ·
    obtain ⟨p, q, hpq⟩ : ∃ p q, B p q ≠ 0 := by
      by_contra hc
      exact hall fun i j => not_not.1 fun h => hc ⟨i, j, h⟩
    refine ⟨B p q, Matrix.of fun i j =>
      (Representation.exists_smul_eq_of_intertwiner hconj hσ (B i j) (B p q) (hBint i j)
        (hBint p q) hpq).choose, hBint p q, fun u j i => ?_⟩
    have h := (Representation.exists_smul_eq_of_intertwiner hconj hσ (B i j) (B p q) (hBint i j)
      (hBint p q) hpq).choose_spec u
    rw [← hRapp, ← hBapp]
    simpa using h

theorem eq_one_of_homogeneous_restriction_of_isCyclic_quotient [IsAlgClosed k]
    [FiniteDimensional k V] [IsCyclic (G ⧸ N)] (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (e : Representation.Equiv (ρ.comp N.subtype)
      (Representation.directSum fun _ : Fin m => σ)) : m = 1 := by
  classical
  have := hρ
  have := hσ
  have hVnt : Nontrivial V := nontrivial_of_isIrreducible ρ
  have hMnt : Nontrivial M := nontrivial_of_isIrreducible σ
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      subst h
      have hs : Subsingleton (⨁ _ : Fin 0, M) :=
        ⟨fun a b => ds_ext fun i => absurd i.2 (by omega)⟩
      have hnt := e.toLinearEquiv.toEquiv.nontrivial_congr.1 hVnt
      rw [← not_subsingleton_iff_nontrivial] at hnt
      exact hnt hs
    · exact h
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hMfd : FiniteDimensional k M := by
    have hds : FiniteDimensional k (⨁ _ : Fin m, M) :=
      FiniteDimensional.of_injective e.toLinearEquiv.symm.toLinearMap
        e.toLinearEquiv.symm.injective
    exact FiniteDimensional.of_injective (DirectSum.lof k (Fin m) (fun _ => M) ⟨0, hm⟩)
      (fun a b hab => by
        have h := congrArg (DirectSum.component k (Fin m) (fun _ => M) ⟨0, hm⟩) hab
        rwa [DirectSum.component.lof_self, DirectSum.component.lof_self] at h)
  obtain ⟨y, hy⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hgen : ∀ g : G, ∃ (j : ℤ) (n : N), g = x ^ j * (n : G) := by
    intro g
    obtain ⟨j, hj⟩ := hy (QuotientGroup.mk g)
    have hq : ((x ^ j : G) : G ⧸ N) = (g : G ⧸ N) := by rw [← hj]; simp
    exact ⟨j, ⟨(x ^ j)⁻¹ * g, QuotientGroup.eq.1 hq⟩, by group⟩
  obtain ⟨S, t, hSint, hblock⟩ := exists_matrix_of_twist hσ e x
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.mulVecLin t)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : w ≠ 0 := (Module.End.hasEigenvector_iff.1 hw).2
  have hteig : ∀ i, ∑ j, t i j * w j = c * w i := fun i => by
    simpa [Matrix.mulVec_apply, dotProduct] using congrFun hw.apply_eq_smul i
  set U : Submodule k V := (LinearMap.range (tensorLine (M := M) w)).comap
    e.toLinearEquiv.toLinearMap with hU
  have hUmem : ∀ v : V, v ∈ U ↔ ∃ u : M, e.toLinearEquiv v = tensorLine w u := by
    intro v
    simp only [hU, Submodule.mem_comap, LinearMap.mem_range]
    exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
  have hU0 : U ≠ ⊥ := by
    obtain ⟨u, hu⟩ := exists_ne (0 : M)
    refine (Submodule.ne_bot_iff U).2 ⟨e.toLinearEquiv.symm (tensorLine w u), ?_, ?_⟩
    · exact (hUmem _).2 ⟨u, e.toLinearEquiv.apply_symm_apply _⟩
    · intro hc0
      have h := congrArg e.toLinearEquiv hc0
      rw [e.toLinearEquiv.apply_symm_apply, map_zero] at h
      exact hu (tensorLine_injective hw0 (h.trans (map_zero _).symm))
  have hUN : ∀ n : N, ∀ v ∈ U, ρ (n : G) v ∈ U := by
    intro n v hv
    obtain ⟨u, hu⟩ := (hUmem v).1 hv
    refine (hUmem _).2 ⟨σ n u, ds_ext fun i => ?_⟩
    have he : e.toLinearEquiv (ρ (n : G) v)
        = (Representation.directSum fun _ : Fin m => σ) n (e.toLinearEquiv v) := by
      simpa using Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap n v
    rw [he, hu, directSum_apply_apply, tensorLine_apply_apply, tensorLine_apply_apply, map_smul]
  have hUx : ∀ v ∈ U, ρ x v ∈ U := by
    intro v hv
    obtain ⟨u, hu⟩ := (hUmem v).1 hv
    refine (hUmem _).2 ⟨c • S u, ds_ext fun i => ?_⟩
    have hv' : v = e.toLinearEquiv.symm (tensorLine w u) := by
      rw [← hu, e.toLinearEquiv.symm_apply_apply]
    rw [hv', tensorLine_eq_sum, map_sum, map_sum, map_sum, DirectSum.sum_apply]
    calc ∑ j, (e.toLinearEquiv (ρ x (e.toLinearEquiv.symm
            (DirectSum.lof k (Fin m) (fun _ => M) j (w j • u))))) i
        = ∑ j, (t i j * w j) • S u := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hblock (w j • u) j i, map_smul, smul_smul]
      _ = (∑ j, t i j * w j) • S u := by rw [Finset.sum_smul]
      _ = tensorLine w (c • S u) i := by
          rw [tensorLine_apply_apply, hteig i, smul_smul, mul_comm]
  have hUG : ∀ g : G, U.map (ρ g) ≤ U := by
    have hxst : x ∈ stabSubmodule ρ U := mem_stabSubmodule_of_map_le ρ hUx
    have hNst : ∀ n : N, (n : G) ∈ stabSubmodule ρ U := fun n =>
      mem_stabSubmodule_of_map_le ρ (hUN n)
    intro g
    obtain ⟨j, n, rfl⟩ := hgen g
    exact le_of_eq ((mem_stabSubmodule_iff ρ U _).1
      (mul_mem (zpow_mem hxst j) (hNst n)))
  have hUtop : U = ⊤ := eq_top_of_isIrreducible_of_map_le hρ hUG hU0
  have hdimV : finrank k V = m * finrank k M := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_directSum k (fun _ : Fin m => M)]
    simp
  have hdimU : finrank k V = finrank k M := by
    have hsurj : Function.Surjective (tensorLine (M := M) w) := by
      intro z
      have hz : e.toLinearEquiv.symm z ∈ U := by simp [hUtop]
      obtain ⟨u, hu⟩ := (hUmem _).1 hz
      exact ⟨u, by rw [← hu, e.toLinearEquiv.apply_symm_apply]⟩
    calc finrank k V = finrank k (⨁ _ : Fin m, M) := e.toLinearEquiv.finrank_eq
      _ = finrank k M := (LinearEquiv.ofBijective (tensorLine (M := M) w)
          ⟨tensorLine_injective hw0, hsurj⟩).finrank_eq.symm
  have hMpos : 0 < finrank k M := finrank_pos
  rw [hdimV] at hdimU
  have : m * finrank k M = 1 * finrank k M := by rw [hdimU, one_mul]
  exact Nat.eq_of_mul_eq_mul_right hMpos this

theorem isIrreducible_comp_subtype_of_homogeneous_of_isCyclic_quotient [IsAlgClosed k]
    [FiniteDimensional k V] [IsCyclic (G ⧸ N)] (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (e : Representation.Equiv (ρ.comp N.subtype)
      (Representation.directSum fun _ : Fin m => σ)) :
    Representation.IsIrreducible (ρ.comp N.subtype) := by
  have := hρ
  have := hσ
  have hMnt : Nontrivial M := nontrivial_of_isIrreducible σ
  have hVnt : Nontrivial V := nontrivial_of_isIrreducible ρ
  refine isIrreducible_of_forall_map_le (fun U hU => ?_)
  have hm : m = 1 := eq_one_of_homogeneous_restriction_of_isCyclic_quotient hρ hσ e
  subst hm
  set fE : V ≃ₗ[k] M := e.toLinearEquiv.trans (dsFinOneEquiv (k := k) (M := M)) with hfE
  set f : V →ₗ[k] M := fE.toLinearMap with hf
  have hfbij : Function.Bijective f := fE.bijective
  have hfint : ∀ (n : N) (v : V), f (ρ (n : G) v) = σ n (f v) := by
    intro n v
    have he : e.toLinearEquiv (ρ (n : G) v)
        = (Representation.directSum fun _ : Fin 1 => σ) n (e.toLinearEquiv v) := by
      simpa using Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap n v
    change dsFinOneEquiv (k := k) (M := M) (e.toLinearEquiv (ρ (n : G) v))
      = σ n (dsFinOneEquiv (k := k) (M := M) (e.toLinearEquiv v))
    rw [he, dsFinOneEquiv_apply, dsFinOneEquiv_apply, directSum_apply_apply]
  have hmap : ∀ n : N, (U.map f).map (σ n) ≤ U.map f := by
    rintro n _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ (n : G) v, hU n ⟨v, hv, rfl⟩, hfint n v⟩
  rcases eq_or_ne (U.map f) ⊥ with h | h
  · left
    refine le_antisymm (fun v hv => ?_) bot_le
    have hfv : f v = 0 := by
      have hmem := Submodule.mem_map_of_mem (f := f) hv
      rw [h] at hmem
      simpa using hmem
    simpa using hfbij.1 (hfv.trans (map_zero f).symm)
  · right
    have htop : U.map f = ⊤ := eq_top_of_isIrreducible_of_map_le hσ hmap h
    refine le_antisymm le_top (fun v _ => ?_)
    have hmem : f v ∈ U.map f := htop ▸ Submodule.mem_top
    obtain ⟨u, hu, huv⟩ := hmem
    exact hfbij.1 huv ▸ hu

end Main

end CFSG.FeitThompson
