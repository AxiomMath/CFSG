module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorGlue
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainPieceScalar
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ScalarOnBlock

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}
variable {h : UnitaryFieldData 2 1 K} {Dt : Subgroup (StatedSU n (2 ^ 1) K)} {S : Finset ℕ}
  {a : ℕ → ℕ} {W : ℕ → Submodule K (Fin n → K)}

namespace SUChain

theorem delta_le_stabPair (hc : SUChain h n Dt S a W) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ S.card) :
    delta Dt ≤ stabPair (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j) :=
  fun d hd => ⟨fun v hv => hc.delta_stab' d hd (j - 1) (by omega) v hv,
    fun v hv => hc.delta_stab' d hd j hj2 v hv,
    fun v hv => hc.delta_stab' d⁻¹ ((delta Dt).inv_mem hd) (j - 1) (by omega) v hv,
    fun v hv => hc.delta_stab' d⁻¹ ((delta Dt).inv_mem hd) j hj2 v hv⟩

theorem eq_one_of_trivial_on_plane [Finite K] (hc : SUChain h n Dt S a W) {k₀ : ℕ}
    (hother : ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1)
    (htail : n - 2 * a S.card ≤ 3)
    (htriv : ∀ d ∈ delta Dt, ∀ v ∈ reindexChain a S.card W k₀,
      (d : Module.End K (Fin n → K)) v - v ∈ reindexChain a S.card W (k₀ - 1)) :
    ∀ y ∈ Dt, y = 1 := by
  have := h.charP
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have h2 : ∀ d ∈ delta Dt, ∃ k, d ^ 2 ^ k = 1 := by
    intro d hd
    refine exists_pow_two_pow_eq_one_of_trivial_on_pieces (B := stdHermForm h n)
      (reindexChain_zero a S.card W) hs d (delta_iso d hd)
      (fun j hj1 hjs v hv => hc.delta_stab d⁻¹ ((delta Dt).inv_mem hd) j hj1 hjs v hv) ?_ ?_
    · intro j hj1 hjs v hv
      by_cases hjk : j = k₀
      · subst hjk
        exact htriv d hd v hv
      · exact hc.delta_trivial_on_line hj1 hjs (hother j hj1 hjs hjk) d hd v hv
    · intro v hv
      exact hc.delta_trivial_on_tail htail d hd v (Submodule.mem_orthogonalBilin.mpr hv)
  have hp : IsPGroup 2 Dt := by
    intro y
    obtain ⟨k, hk⟩ := h2 (suToGL n (2 ^ 1) K y) ⟨y, y.2, rfl⟩
    refine ⟨k, Subtype.ext (suToGL_injective ?_)⟩
    rw [← map_pow] at hk
    simpa using hk
  have : Finite Dt := inferInstance
  have hnil : Group.IsNilpotent Dt := hp.isNilpotent
  have hperf : Group.IsPerfect Dt := Subgroup.isPerfect_iff.mpr hc.perf
  intro y hy
  by_contra hne
  have : Nontrivial Dt := ⟨⟨⟨y, hy⟩, 1, fun e => hne (congrArg Subtype.val e)⟩⟩
  exact Group.IsPerfect.not_isSolvable (G := Dt) inferInstance

theorem exists_nonscalar_on_plane [Finite K] (hc : SUChain h n Dt S a W) {k₀ : ℕ} (hk1 : 1 ≤ k₀)
    (hk2 : k₀ ≤ S.card) (hother : ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1)
    (htail : n - 2 * a S.card ≤ 3) (hnt : ∃ y ∈ Dt, y ≠ 1) :
    ∃ (x : LinearMap.GeneralLinearGroup K (Fin n → K)) (hx : x ∈ delta Dt),
      ∀ c : K, ((quotGL (reindexChain a S.card W (k₀ - 1)) (reindexChain a S.card W k₀)
        ⟨x, hc.delta_le_stabPair hk1 hk2 hx⟩ :
          LinearMap.GeneralLinearGroup K (PieceQ (reindexChain a S.card W (k₀ - 1))
            (reindexChain a S.card W k₀))) :
        Module.End K (PieceQ (reindexChain a S.card W (k₀ - 1)) (reindexChain a S.card W k₀))) ≠
        c • 1 := by
  by_contra hcon
  push Not at hcon
  have htriv := trivial_on_piece_of_scalar (hc.delta_le_stabPair hk1 hk2) hc.perf_delta
    (fun d hd => hcon d hd)
  obtain ⟨y, hy, hy1⟩ := hnt
  exact hy1 (hc.eq_one_of_trivial_on_plane hother htail htriv y hy)

theorem chainStabData [Finite K] (hc : SUChain h n Dt S a W) {k₀ : ℕ} (hk1 : 1 ≤ k₀)
    (hk2 : k₀ ≤ S.card) (hplane : a k₀ = a (k₀ - 1) + 2)
    (hother : ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1)
    (htail : n - 2 * a S.card ≤ 3) (hnt : ∃ y ∈ Dt, y ≠ 1)
    {U : Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K))}
    (hUiso : ∀ u ∈ U, ∀ v w, stdHermForm h n ((u : Module.End K (Fin n → K)) v)
      ((u : Module.End K (Fin n → K)) w) = stdHermForm h n v w)
    (hUthree : ∀ u ∈ U, ∃ k : ℕ, u ^ 3 ^ k = 1)
    (hUstab : ∀ u ∈ U, ∀ j, 1 ≤ j → j ≤ S.card → ∀ v ∈ reindexChain a S.card W j,
      (u : Module.End K (Fin n → K)) v ∈ reindexChain a S.card W j)
    (hUcomm : ∀ u ∈ U, ∀ x ∈ delta Dt, ∃ c : K,
      ((u * x * u⁻¹ * x⁻¹ : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) = c • 1) :
    ChainStabData (stdHermForm h n) S.card (reindexChain a S.card W) U := by
  classical
  have := h.charP
  have hUst0 : ∀ u ∈ U, ∀ j, j ≤ S.card → ∀ v ∈ reindexChain a S.card W j,
      (u : Module.End K (Fin n → K)) v ∈ reindexChain a S.card W j := by
    intro u hu j hj v hv
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [reindexChain_zero, Submodule.mem_bot] at hv ⊢
      simp [hv]
    · exact hUstab u hu j hj0 hj v hv
  refine ⟨hUiso, hUthree, hUstab, fun u hu j hj1 hj2 => ?_⟩
  have he : u ∈ stabPair (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j) :=
    ⟨fun v hv => hUst0 u hu (j - 1) (by omega) v hv, fun v hv => hUst0 u hu j hj2 v hv,
      fun v hv => hUst0 u⁻¹ (U.inv_mem hu) (j - 1) (by omega) v hv,
      fun v hv => hUst0 u⁻¹ (U.inv_mem hu) j hj2 v hv⟩
  by_cases hjk : j = k₀
  · subst hjk
    obtain ⟨x, hx, hxs⟩ := hc.exists_nonscalar_on_plane hk1 hk2 hother htail hnt
    have hdim : finrank K (PieceQ (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j)) =
        2 := by
      rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hk1 hk2]
      omega
    obtain ⟨c, hcc⟩ := quotGL_scalar_of_commutators_scalar (V := Fin n → K) hdim
      (hc.delta_le_stabPair hk1 hk2) hc.perf_delta hx hxs he (fun d hd => hUcomm u hu d hd)
    exact ⟨c, sub_smul_mem_of_quotGL_eq (e := ⟨u, he⟩) hcc⟩
  · have hdim : finrank K (PieceQ (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j)) =
        1 := by
      rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hj1 hj2]
      have := hother j hj1 hj2 hjk
      omega
    exact exists_scalar_of_finrank_pieceQ_one hdim ⟨u, he⟩

end SUChain

end CFSG.HardMathSupport.Curtis.UnitaryLevi
