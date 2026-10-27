module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankNonsplit
public import CFSG.HardMathSupport.Solomon.Coordinator.LBID4RankRed
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap Module CFSG.Open

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Steps

variable {g : V ≃ₗ[K] V} (h3 : (3 : K) ≠ 0) (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
  (hg3 : ∀ v, g (g (g v)) = v)
include h3 hg hg3

theorem exists_adapted_frame [Finite K] [FiniteDimensional K V] {M : Submodule K V}
    (hM : NDeg Q M) (hMg : ∀ v ∈ M, g v ∈ M) (h4 : 4 ≤ finrank K M) :
    ∃ F : EFrame Q, F.b ∈ M ∧ F.b' ∈ M ∧ Adapted g F := by
  by_cases hmov : M ⊓ movSp g = ⊥
  · have hfix := le_fixSp_of_inf_movSp h3 hg3 hMg hmov
    obtain ⟨F, hb, hb'⟩ := exists_frame_of_nDeg hM h4
    exact ⟨F, hb, hb', adapted_of_mem_fixSp (hfix hb) (hfix hb')⟩
  · obtain ⟨v, hv, hQv⟩ := (nDeg_inf_movSp h3 hg3 hg hM hMg).exists_ne_zero hmov
    obtain ⟨F, hFb, hFb', hFa⟩ := exists_rotFrame hg hv.2 hQv
    exact ⟨F, hFb ▸ hv.1, hFb' ▸ hMg v hv.1, hFa⟩

theorem exists_adapted_frame_last [Finite K] [FiniteDimensional K V]
    (hB : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4) (F0 F1 F2 : EFrame Q) (h01 : F0.Perp F1)
    (h02 : F0.Perp F2) (h12 : F1.Perp F2) (hR : NDeg Q (lastPlane F0 F1 F2))
    (hRg : ∀ v ∈ lastPlane F0 F1 F2, g v ∈ lastPlane F0 F1 F2)
    (hM'dim : finrank K ↥(F0.orthSub ⊓ F1.orthSub) = 4)
    (hRdim : finrank K ↥(lastPlane F0 F1 F2) = 2) :
    ∃ F : EFrame Q, F.b ∈ lastPlane F0 F1 F2 ∧ F.b' ∈ lastPlane F0 F1 F2 ∧ Adapted g F := by
  by_cases hmov : lastPlane F0 F1 F2 ⊓ movSp g = ⊥
  · have hfix := le_fixSp_of_inf_movSp h3 hg3 hRg hmov
    obtain ⟨F, hb, hb'⟩ :=
      exists_frame_last h3 hB hdim hW hWdim F0 F1 F2 h01 h02 h12 hR hM'dim hRdim
    exact ⟨F, hb, hb', adapted_of_mem_fixSp (hfix hb) (hfix hb')⟩
  · obtain ⟨v, hv, hQv⟩ := (nDeg_inf_movSp h3 hg3 hg hR hRg).exists_ne_zero hmov
    obtain ⟨F, hFb, hFb', hFa⟩ := exists_rotFrame hg hv.2 hQv
    exact ⟨F, hFb ▸ hv.1, hFb' ▸ hRg v hv.1, hFa⟩

theorem exists_E81_of_cube [Finite K] [FiniteDimensional K V]
    (hB : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8) {W : Submodule K V}
    (hW : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = 4) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧ g ∈ E := by
  have hTop : NDeg Q (⊤ : Submodule K V) := fun v _ hv =>
    hB.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w trivial
  have hTopg : ∀ v ∈ (⊤ : Submodule K V), g v ∈ (⊤ : Submodule K V) := fun _ _ => trivial
  have hTopdim : finrank K (⊤ : Submodule K V) = 8 := by rw [finrank_top, hdim]
  obtain ⟨F0, -, -, hF0⟩ := exists_adapted_frame h3 hg hg3 hTop hTopg (by omega)
  obtain ⟨hM1, hM1dim⟩ := F0.split h3 (Submodule.mem_top) (Submodule.mem_top) hTop
  have hM1g := F0.inf_orthSub_invariant hg hF0 hTopg
  rw [top_inf_eq] at hM1 hM1dim hM1g
  obtain ⟨F1, h1b, h1b', hF1⟩ := exists_adapted_frame h3 hg hg3 hM1 hM1g (by omega)
  obtain ⟨hM2, hM2dim⟩ := F1.split h3 h1b h1b' hM1
  have hM2g := F1.inf_orthSub_invariant hg hF1 hM1g
  obtain ⟨F2, h2b, h2b', hF2⟩ := exists_adapted_frame h3 hg hg3 hM2 hM2g (by omega)
  obtain ⟨hM3, hM3dim⟩ := F2.split h3 h2b h2b' hM2
  have hM3g := F2.inf_orthSub_invariant hg hF2 hM2g
  have h01 : F0.Perp F1 := ⟨(F0.mem_orthSub).mp h1b, (F0.mem_orthSub).mp h1b'⟩
  have h02 : F0.Perp F2 :=
    ⟨(F0.mem_orthSub).mp (Submodule.mem_inf.mp h2b).1,
      (F0.mem_orthSub).mp (Submodule.mem_inf.mp h2b').1⟩
  have h12 : F1.Perp F2 :=
    ⟨(F1.mem_orthSub).mp (Submodule.mem_inf.mp h2b).2,
      (F1.mem_orthSub).mp (Submodule.mem_inf.mp h2b').2⟩
  have hlast : F0.orthSub ⊓ F1.orthSub ⊓ F2.orthSub = lastPlane F0 F1 F2 := rfl
  rw [hlast] at hM3 hM3dim hM3g
  obtain ⟨F3, h3b, h3b', hF3⟩ := exists_adapted_frame_last h3 hg hg3 hB hdim hW hWdim F0 F1 F2
    h01 h02 h12 hM3 hM3g (by omega) (by omega)
  obtain ⟨ho0, ho1, ho2⟩ := (mem_lastPlane F0 F1 F2).mp h3b
  obtain ⟨ho0', ho1', ho2'⟩ := (mem_lastPlane F0 F1 F2).mp h3b'
  have h03 : F0.Perp F3 := ⟨ho0, ho0'⟩
  have h13 : F1.Perp F3 := ⟨ho1, ho1'⟩
  have h23 : F2.Perp F3 := ⟨ho2, ho2'⟩
  let F : Fin 4 → EFrame Q := ![F0, F1, F2, F3]
  have hperp : ∀ i j, i ≠ j → (F i).Perp (F j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
      | exact h01.symm | exact h02.symm | exact h03.symm | exact h12.symm | exact h13.symm
      | exact h23.symm
  have hadapt : ∀ i, Adapted g (F i) := by
    intro i
    fin_cases i
    · exact hF0
    · exact hF1
    · exact hF2
    · exact hF3
  exact exists_E81_of_frames hperp h3 hdim g hadapt

end Steps

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4

namespace CFSG.HardMathSupport.Solomon.Coordinator

open QuadraticMap Module CFSG.Open Matrix CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap)

theorem lbid4_totallySingular (K : Type) [Field K] :
    (∀ w ∈ Submodule.span K (Set.range fun i : Fin 4 => Pi.single (Sum.inl i) (1 : K)),
        quadPlus 4 K w = 0) ∧
      finrank K ↥(Submodule.span K (Set.range fun i : Fin 4 =>
        (Pi.single (Sum.inl i) (1 : K) : Fin 4 ⊕ Fin 4 → K))) = 4 := by
  classical
  constructor
  · refine LBID4.q_eq_zero_of_mem_span ?_ ?_
    · rintro _ ⟨i, rfl⟩
      rw [quadPlus_apply]
      simp
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [polar_quadPlus]
      simp
  · have hli : LinearIndependent K fun i : Fin 4 =>
        (Pi.single (Sum.inl i) (1 : K) : Fin 4 ⊕ Fin 4 → K) := by
      have := (Pi.basisFun K (Fin 4 ⊕ Fin 4)).linearIndependent.comp Sum.inl Sum.inl_injective
      simpa [Function.comp_def] using this
    rw [finrank_span_eq_card hli, Fintype.card_fin]

theorem lbid4Core_holds : LBID4Core := by
  intro K _ _ h3 g hg hg3
  have hQ : ⇑(quadPlus 4 K) = StatedQuadPlus 4 K := by
    funext v
    rw [quadPlus_apply]
    rfl
  have hΩ : StatedOmega (StatedQuadPlus 4 K) =
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆.comap
          (toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom :=
    statedOmega_eq_comap hQ
  have hg' : toLinEquiv (Fin 4 ⊕ Fin 4) K g ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ := by
    rw [hΩ] at hg
    exact hg
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hgO : toLinEquiv (Fin 4 ⊕ Fin 4) K g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    hle hg'
  have hg3' : ∀ v, toLinEquiv (Fin 4 ⊕ Fin 4) K g (toLinEquiv (Fin 4 ⊕ Fin 4) K g
      (toLinEquiv (Fin 4 ⊕ Fin 4) K g v)) = v := by
    intro v
    have h := congrArg (fun f : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => f v)
      (show toLinEquiv (Fin 4 ⊕ Fin 4) K g ^ 3 = 1 by rw [← map_pow, hg3, map_one])
    simpa [pow_three] using h
  have hdim : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    rfl
  obtain ⟨hW, hWdim⟩ := lbid4_totallySingular K
  obtain ⟨E, hEO, hE, hcard, hgE⟩ := LBID4.exists_E81_of_cube h3 hgO hg3'
    (nondegenerate_polarBilin_quadPlus 4 K) hdim hW hWdim
  refine ⟨E.map (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hΩ]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_comap]
    simpa using hEO hx
  · refine ⟨?_, ?_⟩
    · have := hE.1
      infer_instance
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hE.2 y hy, map_one]
  · rw [Subgroup.card_map_of_injective (toLinEquiv (Fin 4 ⊕ Fin 4) K).symm.injective, hcard]
  · exact ⟨_, hgE, by simp⟩

end CFSG.HardMathSupport.Solomon.Coordinator
