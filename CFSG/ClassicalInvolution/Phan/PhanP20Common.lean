module

public import CFSG.ClassicalInvolution.Phan.PhanP14Minus
public import CFSG.ClassicalInvolution.Phan.PhanP17Ell
public import CFSG.ClassicalInvolution.Phan.PhanP18Swap

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.GroupTheory.WeirSylow
open scoped MatrixGroups

theorem exists_le_finrank_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Submodule K V) [FiniteDimensional K T] {n : ℕ} (hn : n ≤ Module.finrank K T) :
    ∃ T' ≤ T, Module.finrank K T' = n := by
  classical
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := T) hn
  refine ⟨(Submodule.span K (s : Set T)).map T.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_finset_eq_card hli, hs]

section PerpTS

variable {F : Type} [Field F] [Finite F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem finrank_le_two_of_ts (h2 : (2 : F) ≠ 0) (hε' : ¬IsSquare (-ε))
    {T : Submodule F (Fin 4 ⊕ Fin 4 → F)}
    (hTN : T ≤ LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin (planeA ε hε h4))
    (hTts : ∀ x ∈ T, quadPlus 4 F x = 0) : Module.finrank F T ≤ 2 := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨T', hT'T, hT'⟩ := exists_le_finrank_eq T (n := 3) hlt
  set N := LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin (planeA ε hε h4) with hN
  have hT'N : T' ≤ N := hT'T.trans hTN
  refine not_isPlusType_planeA_perp h2 hε h4 hε' ⟨T'.comap N.subtype, ?_, ?_⟩
  · have hfr : Module.finrank F (T'.comap N.subtype) = 3 := by
      rw [(Submodule.comapSubtypeEquivOfLe hT'N).finrank_eq, hT']
    rw [hfr, finrank_planeA_perp h2 hε h4]
  · intro x hx
    exact hTts _ (hT'T hx)

end PerpTS

section Incl

variable {F : Type} [Field F] [Finite F] [Invertible (2 : F)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Nontrivial V] {Q : QuadraticForm F V}

@[expose] def inclIsometry (A : Submodule F V) : (Q.restrict A) →qᵢ Q where
  toLinearMap := A.subtype
  map_app' _ := rfl

theorem exists_spin_extend_incl (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    {A : Submodule F V} (hA : (Q.restrict A).Nondegenerate)
    (hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal Q.polarBilin A))
    (β : (Q.restrict A) →qᵢ Q) (hβ : Function.Injective β) :
    ∃ y : spinGroup Q, ∀ a : A, spinAction Q y a = β a := by
  have hα : Function.Injective (inclIsometry (Q := Q) A) := Subtype.val_injective
  have hrange : LinearMap.range (inclIsometry (Q := Q) A).toLinearMap = A := by
    simp [inclIsometry]
  obtain ⟨y, hy⟩ := exists_spin_extend hodd hQ (inclIsometry A) β hα hβ
    (nondegenerate_range (inclIsometry A) hα hA) (by rw [hrange]; exact hdim)
  exact ⟨y, fun a => hy a⟩

end Incl

section PlaneEmb

variable {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

@[expose] noncomputable def planeEmb (h2 : (2 : F) ≠ 0) (u v : Fin 4 ⊕ Fin 4 → F)
    (hu : quadPlus 4 F u = 1) (hv : quadPlus 4 F v = ε) (huv : polar (quadPlus 4 F) u v = 0) :
    ((quadPlus 4 F).restrict (planeA ε hε h4)) →qᵢ quadPlus 4 F where
  toLinearMap := (LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
    (LinearMap.toSpanSingleton F _ v)) ∘ₗ (planeAIsometry h2 ε hε h4).toLinearEquiv.symm.toLinearMap
  map_app' x := by
    obtain ⟨c, rfl⟩ := (planeAIsometry h2 ε hε h4).toLinearEquiv.surjective x
    have h1 := (planeAIsometry h2 ε hε h4).map_app' c
    have e1 : ((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
        (LinearMap.toSpanSingleton F _ v)) ∘ₗ
          (planeAIsometry h2 ε hε h4).toLinearEquiv.symm.toLinearMap)
        ((planeAIsometry h2 ε hε h4).toLinearEquiv c) = c.1 • u + c.2 • v := by
      simp
    change quadPlus 4 F (((LinearMap.coprod (LinearMap.toSpanSingleton F _ u)
        (LinearMap.toSpanSingleton F _ v)) ∘ₗ
          (planeAIsometry h2 ε hε h4).toLinearEquiv.symm.toLinearMap)
        ((planeAIsometry h2 ε hε h4).toLinearEquiv c)) = _
    rw [e1]
    rw [QuadraticMap.map_add (quadPlus 4 F), QuadraticMap.map_smul, QuadraticMap.map_smul, hu, hv,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, huv]
    have h3 : (restrict (quadPlus 4 F) (planeA ε hε h4))
        ((planeAIsometry h2 ε hε h4).toLinearEquiv c) = binForm (0 : F) ε c := h1
    rw [h3, binForm_apply]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    ring

theorem exists_spin_map_A [Finite F] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    {S : Submodule F (Fin 4 ⊕ Fin 4 → F)} {u v : Fin 4 ⊕ Fin 4 → F} (hu : quadPlus 4 F u = 1)
    (hv : quadPlus 4 F v = ε) (huv : polar (quadPlus 4 F) u v = 0) (huS : u ∈ S) (hvS : v ∈ S) :
    ∃ y : spinGroup (quadPlus 4 F), ∀ a ∈ planeA ε hε h4, spinAction (quadPlus 4 F) y a ∈ S := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin
      (planeA ε hε h4)) := by
    rw [finrank_planeA_perp h2 hε h4]
    norm_num
  obtain ⟨y, hy⟩ := exists_spin_extend_incl hodd (nondegenerate_polarBilin_quadPlus 4 F) hA hdim
    (planeEmb (hε := hε) (h4 := h4) h2 u v hu hv huv)
    (isometry_injective_of_nondegenerate hA _)
  refine ⟨y, fun a ha => ?_⟩
  rw [hy ⟨a, ha⟩]
  change ((LinearMap.coprod (LinearMap.toSpanSingleton F _ u) (LinearMap.toSpanSingleton F _ v)) ∘ₗ
    (planeAIsometry h2 ε hε h4).toLinearEquiv.symm.toLinearMap) ⟨a, ha⟩ ∈ S
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coprod_apply,
    LinearMap.toSpanSingleton_apply]
  exact S.add_mem (S.smul_mem _ huS) (S.smul_mem _ hvS)

end PlaneEmb

section CommonPerp

variable {F : Type} [Field F] [Finite F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

theorem exists_common_perp (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) (hε' : ¬IsSquare (-ε))
    (g : spinGroup (quadPlus 4 F)) :
    ∃ h : spinGroup (quadPlus 4 F),
      (∀ a ∈ planeA ε hε h4, ∀ a' ∈ planeA ε hε h4,
        polar (quadPlus 4 F) (spinAction (quadPlus 4 F) h a) a' = 0) ∧
      (∀ a ∈ planeA ε hε h4, ∀ a' ∈ planeA ε hε h4,
        polar (quadPlus 4 F) (spinAction (quadPlus 4 F) h a)
          (spinAction (quadPlus 4 F) g a') = 0) := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set A := planeA ε hε h4 with hA
  set A' : Submodule F (Fin 4 ⊕ Fin 4 → F) := A.map (spinAction (quadPlus 4 F) g).toLinearMap
    with hA'
  set S : Submodule F (Fin 4 ⊕ Fin 4 → F) :=
    LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin (A ⊔ A') with hS
  have hSN : S ≤ LinearMap.BilinForm.orthogonal (quadPlus 4 F).polarBilin A :=
    LinearMap.BilinForm.orthogonal_le le_sup_left
  have hA2 : Module.finrank F A = 2 := finrank_planeA h2 hε h4
  have hA'2 : Module.finrank F A' = 2 := by
    rw [hA', LinearEquiv.finrank_map_eq (spinAction (quadPlus 4 F) g), hA2]
  have hsup : Module.finrank F ↥(A ⊔ A') ≤ 4 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (K := F) A A'
    omega
  have hS4 : 4 ≤ Module.finrank F S := by
    rw [hS, LinearMap.BilinForm.finrank_orthogonal (nondegenerate_polarBilin_quadPlus 4 F)]
    have h8 : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨u, huS, v, hvS, hu, hv, huv⟩ := exists_elliptic_pair hodd hε' hS4
    (fun T hTS hTts => finrank_le_two_of_ts h2 hε' (hTS.trans hSN) hTts)
  obtain ⟨h, hh⟩ := exists_spin_map_A (ε := ε) (hε := hε) (h4 := h4) h2 hodd hu hv huv huS hvS
  refine ⟨h, fun a ha a' ha' => ?_, fun a ha a' ha' => ?_⟩
  · have h1 : (quadPlus 4 F).polarBilin a' (spinAction (quadPlus 4 F) h a) = 0 :=
      hh a ha a' (Submodule.mem_sup_left ha')
    rw [QuadraticMap.polarBilin_apply_apply] at h1
    rw [QuadraticMap.polar_comm]
    exact h1
  · have h1 : (quadPlus 4 F).polarBilin (spinAction (quadPlus 4 F) g a')
        (spinAction (quadPlus 4 F) h a) = 0 :=
      hh a ha _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem ha'))
    rw [QuadraticMap.polarBilin_apply_apply] at h1
    rw [QuadraticMap.polar_comm]
    exact h1

end CommonPerp

end CFSG.ClassicalInvolution.PhanP
