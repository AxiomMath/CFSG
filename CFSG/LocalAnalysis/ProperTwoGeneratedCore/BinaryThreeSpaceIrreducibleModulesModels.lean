module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFlagKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceTraceZeroIrreducible

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

variable (V) in
@[expose] def natRep : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem natRep_apply (g : V ≃ₗ[ZMod 2] V) (v : V) : natRep V g v = g v :=
  rfl

variable (V) in
@[expose] def dualRep : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) (Module.Dual (ZMod 2) V) :=
  (natRep V).dual

theorem dualRep_apply (g : V ≃ₗ[ZMod 2] V) (f : Module.Dual (ZMod 2) V) (v : V) :
    dualRep V g f v = f (g.symm v) :=
  rfl

variable (V) in
@[expose] def trivRep : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) (ZMod 2) :=
  Representation.trivial (ZMod 2) (V ≃ₗ[ZMod 2] V) (ZMod 2)

theorem trivRep_apply (g : V ≃ₗ[ZMod 2] V) (c : ZMod 2) : trivRep V g c = c :=
  rfl

variable (V) in
abbrev endRep : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) (Module.End (ZMod 2) V) :=
  (natRep V).linHom (natRep V)

theorem endRep_apply (g : V ≃ₗ[ZMod 2] V) (X : Module.End (ZMod 2) V) :
    endRep V g X = (g : V →ₗ[ZMod 2] V) ∘ₗ X ∘ₗ (g.symm : V →ₗ[ZMod 2] V) :=
  rfl

theorem endRep_mem_traceZeroEnd (g : V ≃ₗ[ZMod 2] V) {X : Module.End (ZMod 2) V}
    (hX : X ∈ traceZeroEnd V) : endRep V g X ∈ traceZeroEnd V := by
  rw [traceZeroEnd, LinearMap.mem_ker] at hX ⊢
  have h := LinearMap.trace_conj' X g
  rw [LinearEquiv.conj_apply, LinearMap.comp_assoc] at h
  rw [endRep_apply, h, hX]

variable (V) in
@[expose] def traceZeroSubrep : Subrepresentation (endRep V) :=
  ⟨traceZeroEnd V, fun g _ hX => endRep_mem_traceZeroEnd g hX⟩

variable (V) in
@[expose] def adjRep : Representation (ZMod 2) (V ≃ₗ[ZMod 2] V) (traceZeroEnd V) :=
  (traceZeroSubrep V).toRepresentation

theorem adjRep_apply (g : V ≃ₗ[ZMod 2] V) (X : traceZeroEnd V) :
    ((adjRep V g X : traceZeroEnd V) : Module.End (ZMod 2) V) =
      (g : V →ₗ[ZMod 2] V) ∘ₗ (X : Module.End (ZMod 2) V) ∘ₗ (g.symm : V →ₗ[ZMod 2] V) :=
  rfl

theorem zmod_two_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

theorem linearIndependent_three {u w v : V} (hv : v ≠ 0) (hw : ∀ a : ZMod 2, a • v ≠ w)
    (hu : u ∉ Submodule.span (ZMod 2) {w, v}) : LinearIndependent (ZMod 2) ![u, w, v] := by
  refine linearIndependent_finCons.2 ⟨linearIndependent_fin2.2 ⟨hv, hw⟩, ?_⟩
  rwa [Matrix.range_cons_cons_empty]

@[expose] def basisThree (hV : finrank (ZMod 2) V = 3) {u w v : V} (hv : v ≠ 0)
    (hw : ∀ a : ZMod 2, a • v ≠ w) (hu : u ∉ Submodule.span (ZMod 2) {w, v}) :
    Basis (Fin 3) (ZMod 2) V :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_three hv hw hu) (by rw [hV]; rfl)

theorem basisThree_apply (hV : finrank (ZMod 2) V = 3) {u w v : V} (hv : v ≠ 0)
    (hw : ∀ a : ZMod 2, a • v ≠ w) (hu : u ∉ Submodule.span (ZMod 2) {w, v}) :
    basisThree hV hv hw hu 0 = u ∧ basisThree hV hv hw hu 1 = w ∧
      basisThree hV hv hw hu 2 = v := by
  simp [basisThree]

theorem exists_linearEquiv_three (hV : finrank (ZMod 2) V = 3) {u w v u' w' v' : V}
    (hv : v ≠ 0) (hw : ∀ a : ZMod 2, a • v ≠ w) (hu : u ∉ Submodule.span (ZMod 2) {w, v})
    (hv' : v' ≠ 0) (hw' : ∀ a : ZMod 2, a • v' ≠ w')
    (hu' : u' ∉ Submodule.span (ZMod 2) {w', v'}) :
    ∃ g : V ≃ₗ[ZMod 2] V, g u = u' ∧ g w = w' ∧ g v = v' := by
  set b := basisThree hV hv hw hu
  set b' := basisThree hV hv' hw' hu'
  obtain ⟨h0, h1, h2⟩ := basisThree_apply hV hv hw hu
  obtain ⟨h0', h1', h2'⟩ := basisThree_apply hV hv' hw' hu'
  refine ⟨b.equiv b' (Equiv.refl _), ?_, ?_, ?_⟩
  · rw [← h0, ← h0', Basis.equiv_apply, Equiv.refl_apply]
  · rw [← h1, ← h1', Basis.equiv_apply, Equiv.refl_apply]
  · rw [← h2, ← h2', Basis.equiv_apply, Equiv.refl_apply]

theorem exists_not_mem_span_pair (hV : finrank (ZMod 2) V = 3) (w v : V) :
    ∃ u : V, u ∉ Submodule.span (ZMod 2) {w, v} := by
  classical
  by_contra h
  push Not at h
  have htop : Submodule.span (ZMod 2) {w, v} = ⊤ := eq_top_iff.2 fun u _ => h u
  have hle := finrank_span_finset_le_card (R := ZMod 2) ({w, v} : Finset V)
  unfold Set.finrank at hle
  rw [Finset.coe_pair, htop, finrank_top, hV] at hle
  have := Finset.card_le_two (a := w) (b := v)
  omega

theorem smul_ne_of_not_mem_span {v w : V} (hw : w ∉ Submodule.span (ZMod 2) {v}) :
    ∀ a : ZMod 2, a • v ≠ w := fun a h =>
  hw (h ▸ Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v))

theorem smul_ne_of_ne {v w : V} (hw : w ≠ 0) (hvw : v ≠ w) : ∀ a : ZMod 2, a • v ≠ w := by
  intro a
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · rw [zero_smul]
    exact hw.symm
  · rw [one_smul]
    exact hvw

theorem exists_not_mem_span_singleton (hV : finrank (ZMod 2) V = 3) (v : V) :
    ∃ w : V, w ∉ Submodule.span (ZMod 2) {v} := by
  obtain ⟨w, hw⟩ := exists_not_mem_span_pair hV v v
  exact ⟨w, by rwa [Set.pair_eq_singleton] at hw⟩

theorem exists_linearEquiv_apply_eq_pair (hV : finrank (ZMod 2) V = 3) {v w v' w' : V}
    (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w) (hv' : v' ≠ 0) (hw' : w' ≠ 0) (hvw' : v' ≠ w') :
    ∃ g : V ≃ₗ[ZMod 2] V, g v = v' ∧ g w = w' := by
  obtain ⟨u, hu⟩ := exists_not_mem_span_pair hV w v
  obtain ⟨u', hu'⟩ := exists_not_mem_span_pair hV w' v'
  obtain ⟨g, -, h1, h2⟩ := exists_linearEquiv_three hV hv (smul_ne_of_ne hw hvw) hu hv'
    (smul_ne_of_ne hw' hvw') hu'
  exact ⟨g, h2, h1⟩

theorem exists_linearEquiv_apply_eq (hV : finrank (ZMod 2) V = 3) {v v' : V} (hv : v ≠ 0)
    (hv' : v' ≠ 0) : ∃ g : V ≃ₗ[ZMod 2] V, g v = v' := by
  obtain ⟨w, hw⟩ := exists_not_mem_span_singleton hV v
  obtain ⟨w', hw'⟩ := exists_not_mem_span_singleton hV v'
  obtain ⟨u, hu⟩ := exists_not_mem_span_pair hV w v
  obtain ⟨u', hu'⟩ := exists_not_mem_span_pair hV w' v'
  obtain ⟨g, -, -, h⟩ := exists_linearEquiv_three hV hv (smul_ne_of_not_mem_span hw) hu hv'
    (smul_ne_of_not_mem_span hw') hu'
  exact ⟨g, h⟩

section Flag

variable [Fintype V]

theorem exists_adapted (hV : finrank (ZMod 2) V = 3) {p : V} (hp : p ≠ 0)
    {f : Module.Dual (ZMod 2) V} (hf : f ≠ 0) (hfp : f p = 0) :
    ∃ u w : V, (∀ a : ZMod 2, a • p ≠ w) ∧ u ∉ Submodule.span (ZMod 2) {w, p} ∧ f u = 1 ∧
      f w = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_dual_eq_one hp
  obtain ⟨w, hw0, hfw, hψw⟩ := exists_ne_zero_ker (card_eq_eight hV) f ψ
  obtain ⟨u, hu⟩ := exists_eq_one_of_ne_zero hf
  refine ⟨u, w, smul_ne_of_ne hw0 fun h => ?_, fun hmem => ?_, hu, hfw⟩
  · rw [h, hψw] at hψ
    exact zero_ne_one hψ
  · have hle : Submodule.span (ZMod 2) {w, p} ≤ LinearMap.ker f := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨hfw, hfp⟩
    have h := hle hmem
    rw [LinearMap.mem_ker, hu] at h
    exact one_ne_zero h

theorem exists_flag_eq (hV : finrank (ZMod 2) V = 3) {p p' : V}
    {f f' : Module.Dual (ZMod 2) V} (hp : p ≠ 0) (hp' : p' ≠ 0) (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hfp : f p = 0) (hfp' : f' p' = 0) :
    ∃ g : V ≃ₗ[ZMod 2] V, g p = p' ∧ f' ∘ₗ (g : V →ₗ[ZMod 2] V) = f := by
  obtain ⟨u, w, hw, hu, hfu, hfw⟩ := exists_adapted hV hp hf hfp
  obtain ⟨u', w', hw', hu', hfu', hfw'⟩ := exists_adapted hV hp' hf' hfp'
  obtain ⟨g, h0, h1, h2⟩ := exists_linearEquiv_three hV hp hw hu hp' hw' hu'
  obtain ⟨b0, b1, b2⟩ := basisThree_apply hV hp hw hu
  refine ⟨g, h2, (basisThree hV hp hw hu).ext fun i => ?_⟩
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  fin_cases i
  · change f' (g (basisThree hV hp hw hu 0)) = f (basisThree hV hp hw hu 0)
    rw [b0, h0, hfu, hfu']
  · change f' (g (basisThree hV hp hw hu 1)) = f (basisThree hV hp hw hu 1)
    rw [b1, h1, hfw, hfw']
  · change f' (g (basisThree hV hp hw hu 2)) = f (basisThree hV hp hw hu 2)
    rw [b2, h2, hfp, hfp']

theorem exists_dualRep_eq (hV : finrank (ZMod 2) V = 3) {f f' : Module.Dual (ZMod 2) V}
    (hf : f ≠ 0) (hf' : f' ≠ 0) : ∃ g : V ≃ₗ[ZMod 2] V, dualRep V g f = f' := by
  obtain ⟨p, hp, hfp, -⟩ := exists_ne_zero_ker (card_eq_eight hV) f f
  obtain ⟨p', hp', hfp', -⟩ := exists_ne_zero_ker (card_eq_eight hV) f' f'
  obtain ⟨g, -, hg⟩ := exists_flag_eq hV hp hp' hf hf' hfp hfp'
  refine ⟨g, LinearMap.ext fun v => ?_⟩
  rw [dualRep_apply, ← hg, LinearMap.comp_apply, LinearEquiv.coe_coe, g.apply_symm_apply]

end Flag

section Schur

variable {k G M E : Type*} [Field k] [Monoid G] [AddCommGroup M] [Module k M] [AddCommGroup E]
  [Module k E]

theorem bot_ne_top_of_ne_zero (ρ : Representation k G M) {m : M} (hm : m ≠ 0) :
    (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h => by
  have hmem : m ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
  rw [← h] at hmem
  exact hm ((Submodule.mem_bot k).mp hmem)

theorem isIrreducible_of_transitive (ρ : Representation k G M) {m₀ : M} (hm₀ : m₀ ≠ 0)
    (htrans : ∀ m m' : M, m ≠ 0 → m' ≠ 0 → ∃ g, ρ g m = m') : ρ.IsIrreducible where
  exists_pair_ne := ⟨⊥, ⊤, bot_ne_top_of_ne_zero ρ hm₀⟩
  eq_bot_or_eq_top W := by
    by_cases h : ∃ m ∈ W, m ≠ 0
    · right
      obtain ⟨m, hmW, hm⟩ := h
      rw [eq_top_iff]
      intro m' _
      by_cases hm' : m' = 0
      · rw [hm']
        exact W.toSubmodule.zero_mem
      · obtain ⟨g, rfl⟩ := htrans m m' hm hm'
        exact W.apply_mem_toSubmodule g hmW
    · left
      push Not at h
      rw [eq_bot_iff]
      intro m hm
      rw [h m hm]
      exact (⊥ : Subrepresentation ρ).toSubmodule.zero_mem

theorem nonempty_equiv_of_ne_zero {ρ : Representation k G E} {σ : Representation k G M}
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (f : M →ₗ[k] E)
    (hf : ∀ g m, f (σ g m) = ρ g (f m)) (hne : f ≠ 0) : Nonempty (ρ.Equiv σ) := by
  let F : Representation.IntertwiningMap σ ρ := f.intertwiningMap_of_isIntertwiningMap σ ρ hf
  rcases Representation.IsIrreducible.bijective_or_eq_zero F with h | h
  · exact ⟨(Representation.IntertwiningMap.ofBijective F h).symm⟩
  · exact absurd (congrArg Representation.IntertwiningMap.toLinearMap h) hne

theorem finrank_eq_of_equiv {ρ : Representation k G E} {σ : Representation k G M}
    (φ : ρ.Equiv σ) : finrank k E = finrank k M :=
  φ.toLinearEquiv.finrank_eq

end Schur

theorem trivRep_isIrreducible : (trivRep V).IsIrreducible :=
  isIrreducible_of_transitive _ one_ne_zero fun m m' hm hm' => ⟨1, by
    rcases zmod_two_eq_zero_or_one m with rfl | rfl
    · exact absurd rfl hm
    rcases zmod_two_eq_zero_or_one m' with rfl | rfl
    · exact absurd rfl hm'
    rfl⟩

theorem exists_ne_zero (hV : finrank (ZMod 2) V = 3) : ∃ v : V, v ≠ 0 := by
  have := Module.nontrivial_of_finrank_eq_succ hV
  exact exists_ne 0

theorem natRep_isIrreducible (hV : finrank (ZMod 2) V = 3) : (natRep V).IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne_zero hV
  exact isIrreducible_of_transitive _ hv fun _ _ hm hm' => exists_linearEquiv_apply_eq hV hm hm'

theorem dualRep_isIrreducible [Fintype V] (hV : finrank (ZMod 2) V = 3) :
    (dualRep V).IsIrreducible := by
  obtain ⟨v, hv⟩ := exists_ne_zero hV
  obtain ⟨f, hf⟩ := exists_dual_eq_one hv
  have hf0 : f ≠ 0 := fun h => by
    rw [h, LinearMap.zero_apply] at hf
    exact zero_ne_one hf
  exact isIrreducible_of_transitive _ hf0 fun m m' hm hm' => exists_dualRep_eq hV hm hm'

@[expose] def glEquiv (b : Basis (Fin 3) (ZMod 2) V) (g : GL (Fin 3) (ZMod 2)) :
    V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofLinearMap (Matrix.toLin b b (g : Mat3))
    (Matrix.toLin b b ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3))
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin_one])

theorem toMatrix_mem_traceZero (b : Basis (Fin 3) (ZMod 2) V) (X : Module.End (ZMod 2) V) :
    LinearMap.toMatrix b b X ∈ traceZero ↔ X ∈ traceZeroEnd V := by
  rw [traceZero, traceZeroEnd, LinearMap.mem_ker, LinearMap.mem_ker, Matrix.traceLinearMap_apply,
    LinearMap.trace_eq_matrix_trace (ZMod 2) b]

theorem toMatrix_conj (b : Basis (Fin 3) (ZMod 2) V) (g : GL (Fin 3) (ZMod 2))
    (X : Module.End (ZMod 2) V) :
    LinearMap.toMatrix b b ((glEquiv b g : V →ₗ[ZMod 2] V) ∘ₗ X ∘ₗ
        ((glEquiv b g).symm : V →ₗ[ZMod 2] V)) =
      (g : Mat3) * LinearMap.toMatrix b b X * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) := by
  rw [LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b]
  change LinearMap.toMatrix b b (Matrix.toLin b b (g : Mat3)) * (LinearMap.toMatrix b b X *
      LinearMap.toMatrix b b (Matrix.toLin b b ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3))) = _
  rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin, Matrix.mul_assoc]

theorem adjRep_isIrreducible [Fintype V] (hV : finrank (ZMod 2) V = 3) :
    (adjRep V).IsIrreducible := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
  let τ : Module.End (ZMod 2) V →ₗ[ZMod 2] Mat3 := (LinearMap.toMatrix b b).toLinearMap
  have hτ : Function.Injective τ := (LinearMap.toMatrix b b).injective
  refine { exists_pair_ne := ?_, eq_bot_or_eq_top := fun W => ?_ }
  · have := Module.nontrivial_of_finrank_eq_succ (finrank_traceZeroEnd hV)
    obtain ⟨X, hX⟩ := exists_ne (0 : traceZeroEnd V)
    exact ⟨⊥, ⊤, bot_ne_top_of_ne_zero _ hX⟩
  set W' : Submodule (ZMod 2) Mat3 := (W.toSubmodule.map (traceZeroEnd V).subtype).map τ
  have hW'A : W' ≤ traceZero := by
    rintro _ ⟨_, ⟨X, -, rfl⟩, rfl⟩
    exact (toMatrix_mem_traceZero b X).mpr X.2
  have hinv : ∀ g : GL (Fin 3) (ZMod 2), ∀ Y ∈ W',
      (g : Mat3) * Y * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Mat3) ∈ W' := by
    rintro g _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    exact ⟨_, ⟨adjRep V (glEquiv b g) X, W.apply_mem_toSubmodule _ hX, rfl⟩, toMatrix_conj b g X⟩
  rcases trace_zero_irreducibility.2.2 W' hW'A hinv with h | h
  · left
    rw [eq_bot_iff]
    intro X hX
    have hmem : τ X ∈ W' := ⟨X, ⟨X, hX, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact (Submodule.mem_bot (ZMod 2)).mpr (Subtype.ext (hτ (hmem.trans (map_zero τ).symm)))
  · right
    rw [eq_top_iff]
    intro X _
    have hmem : τ X ∈ W' := h ▸ (toMatrix_mem_traceZero b X).mpr X.2
    obtain ⟨_, ⟨Y, hY, rfl⟩, hYX⟩ := hmem
    exact (Subtype.ext (hτ hYX) : Y = X) ▸ hY

section Schur

variable {k G M E : Type*} [Field k] [Monoid G] [AddCommGroup M] [Module k M] [AddCommGroup E]
  [Module k E]

theorem isEmpty_equiv_of_finrank_ne {ρ : Representation k G E} {σ : Representation k G M}
    (h : finrank k E ≠ finrank k M) : IsEmpty (ρ.Equiv σ) :=
  ⟨fun φ => h (finrank_eq_of_equiv φ)⟩

end Schur

theorem isEmpty_equiv_natRep_dualRep (hV : finrank (ZMod 2) V = 3) :
    IsEmpty ((natRep V).Equiv (dualRep V)) := by
  refine ⟨fun φ => ?_⟩
  have hB : ∀ (g : V ≃ₗ[ZMod 2] V) (v w : V), φ (g v) (g w) = φ v w := fun g v w => by
    have h := congrArg (fun F : Module.Dual (ZMod 2) V => F (g w))
      (Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v)
    simp only [Representation.Equiv.coe_toIntertwiningMap] at h
    rw [natRep_apply, dualRep_apply, g.symm_apply_apply] at h
    exact h
  obtain ⟨e1, he1⟩ := exists_ne_zero hV
  obtain ⟨e2, he2⟩ := exists_not_mem_span_singleton hV e1
  obtain ⟨e3, he3⟩ := exists_not_mem_span_pair hV e2 e1
  have hmem1 : e1 ∈ Submodule.span (ZMod 2) {e2, e1} := Submodule.subset_span (by simp)
  have hmem2 : e2 ∈ Submodule.span (ZMod 2) {e2, e1} := Submodule.subset_span (by simp)
  have h2 : e2 ≠ 0 := fun h => he2 (h ▸ Submodule.zero_mem _)
  have h12 : e1 ≠ e2 := fun h => he2 (h ▸ Submodule.mem_span_singleton_self e1)
  have h3 : e3 ≠ 0 := fun h => he3 (h ▸ Submodule.zero_mem _)
  have h13 : e1 ≠ e3 := fun h => he3 (h ▸ hmem1)
  have h23 : e2 + e3 ≠ 0 := fun h => he3 (by
    have he : e3 = (e2 + e3) - e2 := by abel
    rw [he, h, zero_sub]
    exact Submodule.neg_mem _ hmem2)
  have h123 : e1 ≠ e2 + e3 := fun h => he3 (by
    have he : e3 = (e2 + e3) - e2 := by abel
    rw [he, ← h]
    exact Submodule.sub_mem _ hmem1 hmem2)
  have h112 : e1 + e2 ≠ 0 := fun h => he2 (by
    have he : e2 = (e1 + e2) - e1 := by abel
    rw [he, h, zero_sub]
    exact Submodule.neg_mem _ (Submodule.mem_span_singleton_self e1))
  have h1112 : e1 ≠ e1 + e2 := fun h => h2 (by
    have he : e2 = (e1 + e2) - e1 := by abel
    rw [he, ← h, sub_self])
  have hdiag : ∀ v : V, v ≠ 0 → φ v v = φ e1 e1 := fun v hv => by
    obtain ⟨g, rfl⟩ := exists_linearEquiv_apply_eq hV he1 hv
    exact hB g e1 e1
  have hoff : ∀ v w : V, v ≠ 0 → w ≠ 0 → v ≠ w → φ v w = φ e1 e2 := fun v w hv hw hvw => by
    obtain ⟨g, rfl, rfl⟩ := exists_linearEquiv_apply_eq_pair hV he1 h2 h12 hv hw hvw
    exact hB g e1 e2
  have hc : φ e1 e2 = 0 := by
    have h := hoff e1 (e2 + e3) he1 h23 h123
    rw [map_add, hoff e1 e3 he1 h3 h13] at h
    exact (by decide : ∀ a : ZMod 2, a + a = a → a = 0) _ h
  have ha : φ e1 e1 = 0 := by
    have h := hoff e1 (e1 + e2) he1 h112 h1112
    rw [map_add, hc, add_zero] at h
    exact h
  have hzero : ∀ v w : V, φ v w = 0 := fun v w => by
    by_cases hv : v = 0
    · rw [hv, map_zero, LinearMap.zero_apply]
    by_cases hw : w = 0
    · rw [hw, map_zero]
    by_cases hvw : v = w
    · rw [← hvw, hdiag v hv, ha]
    · rw [hoff v w hv hw hvw, hc]
  have hφ : φ e1 = 0 := LinearMap.ext fun w => hzero e1 w
  exact he1 ((map_eq_zero_iff φ (EquivLike.injective φ)).mp hφ)

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
