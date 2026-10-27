module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainNormalizer
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorShape
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorChainStab
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorAnalysis

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

@[expose] noncomputable def glToLin (n : ℕ) (K : Type) [Field K] :
    GL (Fin n) K →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).toMonoidHom

theorem glToLin_apply {K : Type} [Field K] {n : ℕ} (u : GL (Fin n) K) (v : Fin n → K) :
    ((glToLin n K u : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
      (u : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem glToLin_injective {K : Type} [Field K] {n : ℕ} : Function.Injective (glToLin n K) :=
  fun _ _ hxy => Matrix.GeneralLinearGroup.toLin.injective hxy

theorem suToGL_eq_glToLin {K : Type} [Field K] {n q : ℕ} (y : StatedSU n q K) :
    suToGL n q K y = glToLin n K (y : GL (Fin n) K) := rfl

theorem glToLin_scalar {K : Type} [Field K] {n : ℕ} (c : Kˣ) :
    ((glToLin n K (Matrix.GeneralLinearGroup.scalar (Fin n) c) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) = (c : K) • 1 := by
  refine LinearMap.ext fun v => ?_
  rw [glToLin_apply]
  ext i
  simp [Matrix.GeneralLinearGroup.coe_scalar]

theorem chainStabData_of_normalizer {K : Type} [Field K] [Finite K] [CharP K 2] {r ε f : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) (hDtJ : Dt ≤ J) (hDt : ⁅Dt, Dt⁆ = Dt)
    (d : StatedSU (2 * r + ε) (2 ^ f) K) (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K)
    (hd3 : (d : GL (Fin (2 * r + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r + ε)) K)
    (hfree : ∀ H : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), ⁅H, H⁆ = H →
      (∀ w ∈ H, Commute w d) → H = ⊥)
    (hcyc : ∀ V : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), V ≤ J → ⁅V, V⁆ = V →
      ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center (StatedSU (2 * r + ε) (2 ^ f) K)))))
    (Ũ : Subgroup (GL (Fin (2 * r + ε)) K))
    (hUiso : ∀ u ∈ Ũ, ∀ x y : Fin (2 * r + ε) → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ x)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y)
    (hUthree : ∀ u ∈ Ũ, ∃ k : ℕ, u ^ 3 ^ k = 1)
    (hUnorm : ∀ u ∈ Ũ, ∀ y y' : StatedSU (2 * r + ε) (2 ^ f) K,
      (y' : GL (Fin (2 * r + ε)) K) = u * y * u⁻¹ → (y ∈ J ↔ y' ∈ J))
    (hUcomm : ∀ u ∈ Ũ, ∀ x ∈ Dt,
      u * (x : GL (Fin (2 * r + ε)) K) * u⁻¹ * (x : GL (Fin (2 * r + ε)) K)⁻¹ ∈
        StatedScalars (Fin (2 * r + ε)) K) :
    f = 1 ∧
    ∃ (I : Set ℕ) (ψ : hypSU (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε ≃*
        StatedSU (2 * r + ε) (2 ^ f) K),
      I.Nonempty ∧ I ⊆ Set.Icc 1 r ∧
      J = (flagStabilizer (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε I).map
        ψ.toMonoidHom ∧
      (hypScalars (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) r ε).map ψ.toMonoidHom =
        (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) ∧
      ∃ (s m k₀ : ℕ) (W' : ℕ → Submodule K (Fin (2 * r + ε) → K)),
        W' 0 = ⊥ ∧ 1 ≤ s ∧ (∀ j, 1 ≤ j → j ≤ s → W' (j - 1) < W' j) ∧
        (∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W' j, ∀ w ∈ W' j,
          stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) v w = 0) ∧
        (∀ y : StatedSU (2 * r + ε) (2 ^ f) K, y ∈ J ↔ ∀ j, 1 ≤ j → j ≤ s → ∀ w ∈ W' j,
          ((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w ∈
            W' j) ∧
        1 ≤ k₀ ∧ k₀ ≤ s ∧ finrank K (PieceQ (W' (k₀ - 1)) (W' k₀)) = 2 ∧
        (∀ k, 1 ≤ k → k ≤ s → k ≠ k₀ → finrank K (PieceQ (W' (k - 1)) (W' k)) = 1) ∧
        finrank K (perpQuot (stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf)
          (2 * r + ε)) (W' s)) = m ∧
        SurvivorShapeTable r ε I s k₀ m ∧
        ChainStabData (stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε))
          s W' (Ũ.map (glToLin (2 * r + ε) K)) := by
  classical
  have hf1 : f = 1 := by
    by_contra hne
    obtain ⟨H, hH0, hHp, hHc⟩ := exists_perfect_centralizer_of_cube_scalar hK (by omega) hn d hd3 hds
    exact hH0 (hfree H hHp hHc)
  refine ⟨hf1, ?_⟩
  subst hf1
  set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
  obtain ⟨I, ψ, hIne, hIsub, hJI, hZψ, W, hWd, hWm, hWJ, hWnorm⟩ :=
    exists_chain_iso_normalizer hr hε hK hf J S₀ hNJ hJ
  refine ⟨I, ψ, hIne, hIsub, hJI, hZψ, ?_⟩
  have hcyc' := cyclic_hypProj_of_cyclic_centralQuot h ψ hZψ
    (center_statedSU_eq_scalars hK (by omega)) I hJI hcyc
  obtain ⟨hshort, htail⟩ := census_open_nodes h hε hn I hIsub hcyc'
  have hDtW : ∀ y ∈ Dt, ∀ i ∈ I, ∀ w ∈ W i,
      ((y : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w ∈ W i :=
    fun y hy i hi w hw => (hWJ y).mp (hDtJ hy) i hi w hw
  obtain ⟨S, a, k₀, hSI, hc, hk1, hk2, hplane, hother, htailb⟩ :=
    survivor_chain_data h hε hn hIne hIsub hshort htail hWd hWm Dt hDtW hDt hd hds
  have hsurv := survivor_core h hε hn hIne hIsub hshort htail hWd hWm Dt hDtW hDt hd hds hd3 hfree
  have hshape := survivor_shape hSI hc.enum hk1 hk2 hplane hsurv
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have hnt : ∃ y ∈ Dt, y ≠ 1 := ⟨d, hd, fun e => hds (by
    rw [e, Subgroup.coe_one]; exact Subgroup.one_mem _)⟩
  have hstab : ∀ u ∈ Ũ, ∀ j, 1 ≤ j → j ≤ S.card → ∀ v ∈ reindexChain a S.card W j,
      (u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈ reindexChain a S.card W j := by
    intro u hu j hj1 hj2 v hv
    rw [reindexChain_of_le a W hj1 hj2] at hv ⊢
    exact hWnorm u (hUiso u hu) (hUnorm u hu) (a j) ((hSI _).mp (hc.enum.mem j hj1 hj2)) v hv
  have hcsd : ChainStabData (stdHermForm h (2 * r + ε)) S.card (reindexChain a S.card W)
      (Ũ.map (glToLin (2 * r + ε) K)) := by
    refine hc.chainStabData hk1 hk2 hplane hother htailb hnt ?_ ?_ ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩ v w
      exact hUiso u hu v w
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨k, hk⟩ := hUthree u hu
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · rintro _ ⟨u, hu, rfl⟩ j hj1 hj2 v hv
      exact hstab u hu j hj1 hj2 v hv
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨c, hcc⟩ := hUcomm u hu y hy
      refine ⟨(c : K), ?_⟩
      have : glToLin (2 * r + ε) K (u * (y : GL (Fin (2 * r + ε)) K) * u⁻¹ *
          (y : GL (Fin (2 * r + ε)) K)⁻¹) =
          glToLin (2 * r + ε) K u * suToGL (2 * r + ε) (2 ^ 1) K y * (glToLin (2 * r + ε) K u)⁻¹ *
            (suToGL (2 * r + ε) (2 ^ 1) K y)⁻¹ := by
        rw [suToGL_eq_glToLin]; simp only [map_mul, map_inv]
      rw [← this, ← hcc]
      exact glToLin_scalar c
  have hW'lt : ∀ j, 1 ≤ j → j ≤ S.card →
      reindexChain a S.card W (j - 1) < reindexChain a S.card W j := by
    intro j hj1 hj2
    refine lt_of_le_of_ne ?_ ?_
    · have := reindexChain_mono hc.enum hc.mono (j - 1)
      rwa [Nat.sub_add_cancel hj1] at this
    · intro he
      have h1 := finrank_reindexChain (K := K) hc.enum hc.dim (k := j - 1) (by omega)
      have h2 := finrank_reindexChain (K := K) hc.enum hc.dim (k := j) hj2
      have h3 := hc.enum.strictMonoOn (show j - 1 < j by omega) hj2
      rw [he] at h1
      omega
  refine ⟨S.card, 2 * r + ε - 2 * a S.card, k₀, reindexChain a S.card W,
    reindexChain_zero a S.card W, hs, hW'lt, fun j hj1 hj2 => hc.iso_reindex j hj1 hj2, ?_, hk1, hk2,
    ?_, ?_, hc.finrank_tail_eq, hshape, hcsd⟩
  · intro y
    rw [hWJ y]
    constructor
    · intro hy j hj1 hj2 w hw
      rw [reindexChain_of_le a W hj1 hj2] at hw ⊢
      exact hy _ ((hSI _).mp (hc.enum.mem j hj1 hj2)) w hw
    · intro hy i hi w hw
      obtain ⟨k, hk1', hk2', rfl⟩ := hc.enum.surj i ((hSI i).mpr hi)
      have := hy k hk1' hk2' w (by rwa [reindexChain_of_le a W hk1' hk2'])
      rwa [reindexChain_of_le a W hk1' hk2'] at this
  · rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hk1 hk2]
    omega
  · intro k hk1' hk2' hne
    rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hk1' hk2']
    have := hother k hk1' hk2' hne
    omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
