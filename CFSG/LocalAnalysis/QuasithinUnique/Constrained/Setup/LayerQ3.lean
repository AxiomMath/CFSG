module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTransitive

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open TensorProduct Module

universe u

theorem no_transitive_perfect_orbit {F : Type u} [Field F] [Finite F] [CharP F 2] {W : Type u}
    [AddCommGroup W] [Module F W] [Nontrivial W] [Finite W] {s : ℕ} (hs : 2 ≤ s)
    (L : Fin s → Subgroup (W ≃ₗ[F] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hperf : ∀ i, Group.IsPerfect ↥(L i)) (hnt : ∀ i, Nontrivial ↥(L i))
    (hirr : IsIrrAct (⨆ i, L i))
    (hend : ∀ f : Module.End F W, (∀ h ∈ ⨆ i, L i, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w)
    (A : Subgroup (W ≃ₗ[F] W)) [CFSG.IsElementaryAbelian 2 A]
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card (fixGL A))
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (L i) = L j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (L i) = L j) : False := by
  classical
  have hGLfin : Finite (W ≃ₗ[F] W) :=
    Finite.of_injective (fun f : W ≃ₗ[F] W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨V, hV1, hV2, ρ, e, hVnt, hVfin, hρinj, hact, hspan, -, hdim2, hRiff⟩ :=
    commuting_factors_absolutely_irreducible_tensor_decomposition.{u, 0} L hcomm hirr hend
  set R : Fin s → Submodule F (Module.End F W) := fun i =>
    Submodule.span F (Set.range fun l : L i => ((l : W ≃ₗ[F] W) : Module.End F W)) with hR
  have hRfin : ∀ i, Module.finrank F (R i) = Module.finrank F (V i) ^ 2 := fun i =>
    finrank_span_of_tensor e (R i) i (hRiff i)
  have hdim : ∀ i j, Module.finrank F (V i) = Module.finrank F (V j) := by
    intro i j
    obtain ⟨a, ha, hij⟩ := htrans i j
    have h1 : (R i).map (a.conjAlgEquiv F).toLinearMap = R j := conj_map_span a (L i) (L j) hij
    have h2 : Module.finrank F (R i) = Module.finrank F (R j) := by
      rw [← h1]
      exact (LinearEquiv.finrank_map_eq (a.conjAlgEquiv F).toLinearEquiv (R i)).symm
    rw [hRfin, hRfin] at h2
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  let i0 : Fin s := ⟨0, by omega⟩
  let τ : ∀ i, V i ≃ₗ[F] V i0 := fun i => LinearEquiv.ofFinrankEq (V i) (V i0) (hdim i i0)
  let e' : W ≃ₗ[F] ⨂[F] _ : Fin s, V i0 := e.trans (PiTensorProduct.congr τ)
  let A' : Subgroup ((⨂[F] _ : Fin s, V i0) ≃ₗ[F] ⨂[F] _ : Fin s, V i0) :=
    A.map (autConj e').toMonoidHom
  have hel' : CFSG.IsElementaryAbelian 2 ↥A' := isElementaryAbelian_map (autConj e').toMonoidHom A
  have hΨ : ∀ i (X : Module.End F (⨂[F] _ : Fin s, V i0)),
      X ∈ factorAlg (F := F) (V := fun _ : Fin s => V i0) i ↔
        ((e'.conjAlgEquiv F).symm X) ∈ R i := by
    intro i X
    rw [mem_factorAlg_const_iff e τ (R i) i (hRiff i) X]
    rfl
  have hmapeq : ∀ a ∈ A, ∀ i j, conjSub a (L i) = L j →
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map
        ((autConj e' a).conjAlgEquiv F).toAlgHom = factorAlg j := by
    intro a ha i j hj
    have hRj : (R i).map (a.conjAlgEquiv F).toLinearMap = R j := conj_map_span a (L i) (L j) hj
    have hkey : ∀ Y, (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) Y) =
        a.conjAlgEquiv F ((e'.conjAlgEquiv F).symm Y) := by
      intro Y
      have := conjAlgEquiv_autConj e' a ((e'.conjAlgEquiv F).symm Y)
      rw [AlgEquiv.apply_symm_apply] at this
      rw [this]
      exact AlgEquiv.symm_apply_apply _ _
    apply Subalgebra.ext
    intro X
    rw [Subalgebra.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [hΨ] at hY ⊢
      have h1 : a.conjAlgEquiv F ((e'.conjAlgEquiv F).symm Y) ∈
          (R i).map (a.conjAlgEquiv F).toLinearMap := Submodule.mem_map_of_mem hY
      rw [hRj] at h1
      show (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) Y) ∈ R j
      rw [hkey]
      exact h1
    · intro hX
      rw [hΨ] at hX
      rw [← hRj] at hX
      obtain ⟨T, hT, hTX⟩ := hX
      refine ⟨e'.conjAlgEquiv F T, ?_, ?_⟩
      · rw [hΨ]
        simpa using hT
      · apply (e'.conjAlgEquiv F).symm.injective
        show (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) (e'.conjAlgEquiv F T)) =
          (e'.conjAlgEquiv F).symm X
        rw [hkey]
        have : (e'.conjAlgEquiv F).symm (e'.conjAlgEquiv F T) = T := AlgEquiv.symm_apply_apply _ _
        rw [this]
        exact hTX
  have hperm' : ∀ a' ∈ A', ∀ i, ∃ j,
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map (a'.conjAlgEquiv F).toAlgHom =
        factorAlg j := by
    rintro _ ⟨a, ha, rfl⟩ i
    obtain ⟨j, hj⟩ := hperm a ha i
    exact ⟨j, hmapeq a ha i j hj⟩
  have htrans' : ∀ i j, ∃ a' ∈ A',
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map (a'.conjAlgEquiv F).toAlgHom =
        factorAlg j := by
    intro i j
    obtain ⟨a, ha, hj⟩ := htrans i j
    exact ⟨autConj e' a, ⟨a, ha, rfl⟩, hmapeq a ha i j hj⟩
  have hquad' : ∀ a' ∈ A', ∀ b' ∈ A', ∀ w, b' (a' w - w) = a' w - w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
    have h1 := hquad a ha b hb (e'.symm w)
    rw [map_sub] at h1
    show (autConj e' b) ((autConj e' a) w - w) = (autConj e' a) w - w
    simp only [autConj_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [← map_sub e', h1, map_sub, LinearEquiv.apply_symm_apply]
  have hoff' : Nat.card (⨂[F] _ : Fin s, V i0) ≤ Nat.card ↥A' * Nat.card ↥(fixGL A') :=
    natCard_le_weight_map_autConj e' A hoff
  have hd : 2 ≤ Module.finrank F (V i0) := hdim2 i0 (hperf i0) (hnt i0)
  obtain ⟨-, hU2, hF2⟩ := transitive_tensor_quadratic_offender_small_exception (F := F)
    (U := V i0) hd hs A' hperm' htrans' hquad' hoff'
  have : Nontrivial ↥(L i0) := hnt i0
  have : Finite ↥(L i0) := inferInstance
  exact not_perfect_of_finrank_two hF2 hU2 (ρ i0) (hρinj i0) (hperf i0)

end CFSG.QuasithinUnique.Setup.Layer
