module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentPaired

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

open Module Matrix CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open TauCeti.QuadraticMap (orthogonalGroup)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

section Frame

variable {B : LinearMap.BilinForm K V} {m : ℕ} {b d : Fin m → V}

theorem bilin_left_sum_symm (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (c : Fin m ⊕ Fin m → K) (i : Fin m) :
    B (b i) (∑ a, c a • Sum.elim b d a) = c (Sum.inr i) := by
  simp [map_sum, Fintype.sum_sum_type, hbb, hbd]

theorem bilin_right_sum_symm (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (c : Fin m ⊕ Fin m → K) (i : Fin m) :
    B (d i) (∑ a, c a • Sum.elim b d a) = c (Sum.inl i) := by
  simp [map_sum, Fintype.sum_sum_type, hdd, hdb]

theorem linearIndependent_sumElim_symm (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) :
    LinearIndependent K (Sum.elim b d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  rcases a with i | i
  · rw [← bilin_right_sum_symm hdd hdb c i, hc, map_zero]
  · rw [← bilin_left_sum_symm hbb hbd c i, hc, map_zero]

variable {bV : Basis (Fin m ⊕ Fin m) K V}

theorem repr_inl_symm (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inl i) = B (d i) v := by
  have h1 := bilin_right_sum_symm hdd hdb (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  exact h1.symm

theorem repr_inr_symm (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inr i) = B (b i) v := by
  have h1 := bilin_left_sum_symm hbb hbd (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  exact h1.symm

theorem pairedHermForm_id_eq_bilin (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d)
    (u v : Fin m ⊕ Fin m → K) :
    pairedHermForm (RingHom.id K) m u v = B (bV.equivFun.symm u) (bV.equivFun.symm v) := by
  have key : ∀ (x : Fin m ⊕ Fin m → K) (w : V), B (∑ a, x a • Sum.elim b d a) w =
      ∑ i, (x (Sum.inl i) * B (b i) w + x (Sum.inr i) * B (d i) w) := by
    intro x w
    rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Sum.elim_inl,
      Sum.elim_inr, smul_eq_mul, smul_eq_mul]
  rw [pairedHermForm_eq, Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, hbV, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilin_left_sum_symm hbb hbd, bilin_right_sum_symm hdd hdb]
  rfl

end Frame

theorem mem_positiveSquareKernel_of_commute {A g : V ≃ₗ[K] V} (hg : ∀ x, g (A x) = A (g x))
    {b : K} {v : V} (hv : v ∈ positiveSquareKernel A b) : g v ∈ positiveSquareKernel A b := by
  have hv' : b⁻¹ • A v - v = 0 := hv
  change b⁻¹ • A (g v) - g v = 0
  rw [← hg, ← map_smul, ← map_sub, hv', map_zero]

theorem mem_negativeSquareKernel_of_commute {A g : V ≃ₗ[K] V} (hg : ∀ x, g (A x) = A (g x))
    {b : K} {v : V} (hv : v ∈ negativeSquareKernel A b) : g v ∈ negativeSquareKernel A b := by
  have hv' : b⁻¹ • A v + v = 0 := hv
  change b⁻¹ • A (g v) + g v = 0
  rw [← hg, ← map_smul, ← map_add, hv', map_zero]

theorem paired_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] (hd : 5 ≤ finrank K V)
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {T : orthogonalGroup Q}
    (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hTT : ∀ x, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) x) = -x) (b : Kˣ) (hb : (b : K) ^ 2 = -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (orthogonalGroup Q)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (orthogonalGroup Q)) : Set (orthogonalGroup Q)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f hℓ hℓ2 hf
      hK (by omega) Q hQ (T : V ≃ₗ[K] V) (-1) 1
      (fun x => by rw [Units.val_neg, Units.val_one, neg_one_smul]; exact hTT x)
      (fun x y => by rw [Units.val_one, one_mul]; exact polarBilin_map_of_mem T.2 x y) hTns
  obtain ⟨hc, -, -, -, hneg⟩ := hsq b (by rw [Units.val_neg, Units.val_one, hb])
  obtain ⟨hQP, hQN, -, hdimeq, -, -, e, -, -, he1, -, -⟩ :=
    hneg (by rw [Units.val_one, Units.val_neg, Units.val_one, div_neg, div_one])
  obtain ⟨m, hm⟩ : ∃ m, finrank K (positiveSquareKernel (T : V ≃ₗ[K] V) b) = m := ⟨_, rfl⟩
  have hdimV : m + m = finrank K V := by
    rw [← Submodule.finrank_add_eq_of_isCompl hc, ← hdimeq, hm]
  have hm3 : 3 ≤ m := by omega
  obtain ⟨bP⟩ : Nonempty (Basis (Fin m) K (positiveSquareKernel (T : V ≃ₗ[K] V) b)) :=
    ⟨Module.finBasisOfFinrankEq K _ hm⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup.centralizer {T} ≃* GL (Fin m) K,
      F = (MulEquiv.subgroupCongr (centralizer_eq_orthogonalOperatorCentralizer T)).trans
        (e.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.trans
          (Units.mapEquiv (LinearMap.toMatrixAlgEquiv bP).toMulEquiv))) := ⟨_, rfl⟩
  have hFapp : ∀ (x : Subgroup.centralizer {T}) (i j : Fin m),
      ((F x : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) i j =
        bP.repr (((e (MulEquiv.subgroupCongr
          (centralizer_eq_orthogonalOperatorCentralizer T) x)) :
            positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
              positiveSquareKernel (T : V ≃ₗ[K] V) b) (bP j)) i := by
    intro x i j
    rw [hF]
    exact LinearMap.toMatrixAlgEquiv_apply bP _ i j
  have hL' : CFSG.IsComponent (L.map F.toMonoidHom) := isComponent_map_of_isComponent F hL
  have : Group.IsPerfect (L.map F.toMonoidHom) := hL'.1.1
  have : Nontrivial (L.map F.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  have hSL : L.map F.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange m K := by
    obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters m K (by omega)
      (by omega)
    exact CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m K hm2 h22 h23 _ hL'.2
  have hBP : ∀ x ∈ positiveSquareKernel (T : V ≃ₗ[K] V) b,
      ∀ y ∈ positiveSquareKernel (T : V ≃ₗ[K] V) b, Q.polarBilin x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQP _ (add_mem hx hy),
      hQP x hx, hQP y hy, sub_zero, sub_zero]
  have hBN : ∀ x ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b,
      ∀ y ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b, Q.polarBilin x y = 0 := fun x hx y hy => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQN _ (add_mem hx hy),
      hQN x hx, hQN y hy, sub_zero, sub_zero]
  have hpair : ∀ w ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b,
      (∀ v ∈ positiveSquareKernel (T : V ≃ₗ[K] V) b, Q.polarBilin w v = 0) → w = 0 := by
    intro w hw h0
    refine hQ.1 w fun z => ?_
    obtain ⟨p, hp, n, hn, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
      z ∈ positiveSquareKernel (T : V ≃ₗ[K] V) b ⊔ negativeSquareKernel (T : V ≃ₗ[K] V) b)
    rw [map_add, h0 p hp, hBN w hw n hn, add_zero]
  have hex : ∀ j : Fin m, ∃ w ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b,
      ∀ v : positiveSquareKernel (T : V ≃ₗ[K] V) b, Q.polarBilin w v = bP.coord j v := fun j =>
    exists_bilin_eq_of_pairing hpair hdimeq.symm (bP.coord j)
  choose d hdN hdB using hex
  have hbb : ∀ i j, Q.polarBilin (bP i : V) (bP j : V) = 0 := fun i j =>
    hBP _ (bP i).2 _ (bP j).2
  have hdd : ∀ i j, Q.polarBilin (d i) (d j) = 0 := fun i j => hBN _ (hdN i) _ (hdN j)
  have hdb : ∀ i j, Q.polarBilin (d i) (bP j : V) = if i = j then 1 else 0 := fun i j => by
    rw [hdB i (bP j), Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  have hbd : ∀ i j, Q.polarBilin (bP i : V) (d j) = if i = j then 1 else 0 := fun i j => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
      ← QuadraticMap.polarBilin_apply_apply, hdb j i]
    exact if_congr eq_comm rfl rfl
  obtain ⟨bV, hbV⟩ : ∃ bV : Basis (Fin m ⊕ Fin m) K V,
      ⇑bV = Sum.elim (fun i => (bP i : V)) d :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _
      (linearIndependent_sumElim_symm (b := fun i => (bP i : V)) hbb hdd hbd hdb)
      (by rw [Fintype.card_sum, Fintype.card_fin, hdimV]),
      coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (V ≃ₗ[K] V) ≃* GL (Fin m ⊕ Fin m) K,
      ψ = (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm.trans (frameMatrix bV) :=
    ⟨_, rfl⟩
  have hψe : ∀ (g : V ≃ₗ[K] V) (a c : Fin m ⊕ Fin m),
      ((ψ g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) a c =
        bV.repr (g (bV c)) a := fun g a c => by
    rw [hψ]
    exact LinearMap.toMatrix_apply bV bV g.toLinearMap a c
  have hψU : ∀ g : orthogonalGroup Q, ∀ u v, pairedHermForm (RingHom.id K) m
      (((ψ (g : V ≃ₗ[K] V) : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ u)
      (((ψ (g : V ≃ₗ[K] V) : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v) =
        pairedHermForm (RingHom.id K) m u v := by
    intro g u v
    rw [hψ]
    change pairedHermForm (RingHom.id K) m (LinearMap.toMatrix bV bV (g : V ≃ₗ[K] V).toLinearMap
      *ᵥ u) (LinearMap.toMatrix bV bV (g : V ≃ₗ[K] V).toLinearMap *ᵥ v) = _
    rw [toMatrix_mulVec_eq, toMatrix_mulVec_eq,
      pairedHermForm_id_eq_bilin (b := fun i => (bP i : V)) hbb hdd hbd hdb hbV,
      pairedHermForm_id_eq_bilin (b := fun i => (bP i : V)) hbb hdd hbd hdb hbV,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact polarBilin_map_of_mem g.2 _ _
  have hcover : ∀ M : SpecialLinearGroup (Fin m) K, ∃ x ∈ L,
      ψ ((x : orthogonalGroup Q) : V ≃ₗ[K] V) = pairedSLHom (RingHom.id K) m M := by
    intro M
    have hM : SpecialLinearGroup.toGL M ∈ L.map F.toMonoidHom := by
      rw [hSL]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := hM
    have hxM' : F x = SpecialLinearGroup.toGL M := hxM
    refine ⟨x, hx, ?_⟩
    have hxT : ∀ v, ((x : orthogonalGroup Q) : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) v) =
        (T : V ≃ₗ[K] V) (((x : orthogonalGroup Q) : V ≃ₗ[K] V) v) := fun v =>
      LinearEquiv.congr_fun (congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp x.2)) v
    obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K,
        P = ((ψ ((x : orthogonalGroup Q) : V ≃ₗ[K] V) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := ⟨_, rfl⟩
    have hPe : ∀ a c, P a c = bV.repr (((x : orthogonalGroup Q) : V ≃ₗ[K] V) (bV c)) a :=
      fun a c => by rw [hP, hψe]
    have h11 : P.toBlocks₁₁ = (M : Matrix (Fin m) (Fin m) K) := by
      ext i j
      change P (Sum.inl i) (Sum.inl j) = _
      rw [hPe, hbV, Sum.elim_inl, repr_inl_symm (b := fun i => (bP i : V)) hdd hdb hbV]
      have h2 : (((e (MulEquiv.subgroupCongr (centralizer_eq_orthogonalOperatorCentralizer T) x)
          : positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
            positiveSquareKernel (T : V ≃ₗ[K] V) b) (bP j) :
              positiveSquareKernel (T : V ≃ₗ[K] V) b) : V) =
          ((x : orthogonalGroup Q) : V ≃ₗ[K] V) (bP j) := he1 _ (bP j)
      rw [← h2, hdB, Basis.coord_apply, ← hFapp, hxM']
      rfl
    have h12 : P.toBlocks₁₂ = 0 := by
      ext i j
      change P (Sum.inl i) (Sum.inr j) = 0
      rw [hPe, hbV, Sum.elim_inr, repr_inl_symm (b := fun i => (bP i : V)) hdd hdb hbV]
      exact hBN _ (hdN i) _ (mem_negativeSquareKernel_of_commute hxT (hdN j))
    have h21 : P.toBlocks₂₁ = 0 := by
      ext i j
      change P (Sum.inr i) (Sum.inl j) = 0
      rw [hPe, hbV, Sum.elim_inl, repr_inr_symm (b := fun i => (bP i : V)) hbb hbd hbV]
      exact hBP _ (bP i).2 _ (mem_positiveSquareKernel_of_commute hxT (bP j).2)
    have hblocks : fromBlocks (M : Matrix (Fin m) (Fin m) K) 0 0 P.toBlocks₂₂ = P := by
      calc fromBlocks (M : Matrix (Fin m) (Fin m) K) 0 0 P.toBlocks₂₂ =
          fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ := by
            rw [h11, h12, h21]
        _ = P := fromBlocks_toBlocks P
    have hPU : ∀ u v, pairedHermForm (RingHom.id K) m
        (fromBlocks (M : Matrix (Fin m) (Fin m) K) 0 0 P.toBlocks₂₂ *ᵥ u)
        (fromBlocks (M : Matrix (Fin m) (Fin m) K) 0 0 P.toBlocks₂₂ *ᵥ v) =
          pairedHermForm (RingHom.id K) m u v := by
      rw [hblocks, hP]
      exact hψU _
    have hSLU := pairedSLHom_range_le_pairedUnitaryGroup (σ := RingHom.id K) (m := m)
      (fun _ => rfl) ⟨M, rfl⟩
    rw [mem_pairedUnitaryGroup, pairedSLHom_coe] at hSLU
    have h22 : P.toBlocks₂₂ =
        (((SpecialLinearGroup.map (RingHom.id K) M)⁻¹ : SpecialLinearGroup (Fin m) K) :
          Matrix (Fin m) (Fin m) K)ᵀ :=
      (Matrix.inv_eq_right_inv (map_transpose_mul_eq_one_of_fromBlocks hPU)).symm.trans
        (Matrix.inv_eq_right_inv (map_transpose_mul_eq_one_of_fromBlocks hSLU))
    apply Units.ext
    rw [← hP, ← hblocks, h22, pairedSLHom_coe]
  obtain ⟨-, hab⟩ := paired_special_linear_geq_three_linear_centralizer (k := K) hm3
  have hRcent : ∀ r ∈ R, ψ (r : V ≃ₗ[K] V) ∈ Subgroup.centralizer
      ((pairedSLHom (RingHom.id K) m).range : Set (GL (Fin m ⊕ Fin m) K)) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := hcover M
    have hxr := Subgroup.mem_centralizer_iff.mp (hR hr) _ (Subgroup.mem_map_of_mem _ hx)
    rw [← hxM, ← map_mul, ← map_mul]
    exact congrArg (fun z : orthogonalGroup Q => ψ (z : V ≃ₗ[K] V)) hxr
  have hRcomm : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ h₁ r₂ h₂
    have h3 := hab.is_comm.comm ⟨_, hRcent r₁ h₁⟩ ⟨_, hRcent r₂ h₂⟩
    have h4 : ψ ((r₁ * r₂ : orthogonalGroup Q) : V ≃ₗ[K] V) =
        ψ ((r₂ * r₁ : orthogonalGroup Q) : V ≃ₗ[K] V) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val h3
    exact Subtype.ext (ψ.injective h4)
  have hRle : R ≤ Subgroup.centralizer (R : Set (orthogonalGroup Q)) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => hRcomm s hs r hr
  rw [← hRp, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRle]

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal
