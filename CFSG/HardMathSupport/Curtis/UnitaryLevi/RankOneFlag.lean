module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainIso
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorGlue

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

section Core

variable {K : Type*} [Field K] [CharP K 2] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_pow_two_pow_eq_one_of_rank_one_flag [FiniteDimensional K V]
    (hσ : Function.Surjective σ) (hV : finrank K V = 3) {B : V →ₛₗ[σ] V →ₗ[K] K}
    (hBs : B.SeparatingLeft) {L : Submodule K V} (hL : finrank K L = 1)
    (hLiso : ∀ v ∈ L, ∀ w ∈ L, B v w = 0) (Δ : Subgroup (LinearMap.GeneralLinearGroup K V))
    (hperf : ⁅Δ, Δ⁆ = Δ)
    (hΔiso : ∀ d ∈ Δ, ∀ v w, B ((d : Module.End K V) v) ((d : Module.End K V) w) = B v w)
    (hΔst : ∀ d ∈ Δ, ∀ v ∈ L, (d : Module.End K V) v ∈ L) :
    ∀ d ∈ Δ, ∃ k, d ^ 2 ^ k = 1 := by
  classical
  have hle : L ≤ L.orthogonalBilin B := fun v hv => by
    rw [Submodule.mem_orthogonalBilin]
    exact fun w hw => hLiso w hw v hv
  have hΔperp : ∀ d ∈ Δ, ∀ v ∈ L.orthogonalBilin B, (d : Module.End K V) v ∈ L.orthogonalBilin B := by
    intro d hd v hv
    rw [Submodule.mem_orthogonalBilin] at hv ⊢
    intro w hw
    have hw' := hΔst d⁻¹ (Δ.inv_mem hd) w hw
    have e : (d : Module.End K V) (((d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) = w := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rfl
    have := hΔiso d hd (((d⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) v
    rw [e] at this
    rw [this]
    exact hv _ hw'
  have hline1 : finrank K (PieceQ (⊥ : Submodule K V) L) = 1 := by
    have := finrank_pieceQ_add (K := K) (V := V) (bot_le : (⊥ : Submodule K V) ≤ L)
    rw [finrank_bot] at this
    omega
  have hline2 : finrank K (PieceQ L (L.orthogonalBilin B)) = 1 := by
    have := finrank_perpQuot_eq hσ hBs L hle
    rw [hV, hL] at this
    exact this
  let W : ℕ → Submodule K V := fun i => if i = 0 then ⊥ else L
  have hW0 : W 0 = ⊥ := by simp [W]
  have hW1 : W 1 = L := by simp [W]
  intro d hd
  refine exists_pow_two_pow_eq_one_of_trivial_on_pieces (B := B) (s := 1) (W := W) hW0 le_rfl d
    (hΔiso d hd) ?_ ?_ ?_
  · intro j hj1 hj2 v hv
    obtain rfl : j = 1 := by omega
    rw [hW1] at hv ⊢
    exact hΔst d⁻¹ (Δ.inv_mem hd) v hv
  · intro j hj1 hj2 v hv
    obtain rfl : j = 1 := by omega
    rw [hW1] at hv
    have h := perfect_trivial_on_line_piece hline1 Δ hperf
      (fun d hd v hv => by
        rw [Submodule.mem_bot] at hv ⊢
        simp [hv])
      (fun d hd v hv => hΔst d hd v hv) d hd v hv
    simpa [hW0, hW1] using h
  · intro v hv
    rw [hW1] at hv ⊢
    have hv' : v ∈ L.orthogonalBilin B := Submodule.mem_orthogonalBilin.mpr hv
    exact perfect_trivial_on_line_piece hline2 Δ hperf
      (fun d hd v hv => hΔst d hd v hv) hΔperp d hd v hv'

end Core

section SU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem no_perfect_in_rank_one_flag {r ε : ℕ} (hr : r = 1) (hε : ε = 1)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) (hDtJ : Dt ≤ J) (hDt : ⁅Dt, Dt⁆ = Dt) :
    Dt = ⊥ := by
  classical
  subst hr hε
  obtain ⟨I, ψ, hIne, hIsub, -, -, W, hWd, -, hWJ⟩ :=
    exists_chain_iso (r := 1) (ε := 1) le_rfl le_rfl hK hf J S₀ hNJ hJ
  have h1 : 1 ∈ I := by
    obtain ⟨i, hi⟩ := hIne
    have := hIsub hi
    rw [Set.mem_Icc] at this
    obtain rfl : i = 1 := by omega
    exact hi
  set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
  have := h.charP
  obtain ⟨hdim, hiso⟩ := hWd 1 h1
  have hiso' := (ToralCensus.isTotallyIsotropicSU_iff h (W 1)).mp hiso
  have h2 : ∀ d ∈ Dt.map (suToGL (2 * 1 + 1) (2 ^ f) K), ∃ k, d ^ 2 ^ k = 1 :=
    exists_pow_two_pow_eq_one_of_rank_one_flag (σ := h.bar)
      (fun c => ⟨h.bar c, h.bar_bar c⟩) (by rw [Module.finrank_fin_fun])
      (stdHermForm_separatingLeft h (2 * 1 + 1)) hdim hiso' (Dt.map (suToGL (2 * 1 + 1) (2 ^ f) K))
      (by rw [← Subgroup.map_commutator, hDt])
      (by
        rintro d ⟨y, -, rfl⟩ v w
        exact suToGL_isometry h y v w)
      (by
        rintro d ⟨y, hy, rfl⟩ v hv
        exact (hWJ y).mp (hDtJ hy) 1 h1 v hv)
  have hp : IsPGroup 2 Dt := by
    intro y
    obtain ⟨k, hk⟩ := h2 (suToGL (2 * 1 + 1) (2 ^ f) K y) ⟨y, y.2, rfl⟩
    refine ⟨k, Subtype.ext (suToGL_injective ?_)⟩
    rw [← map_pow] at hk
    simpa using hk
  have : Finite Dt := inferInstance
  have hnil : Group.IsNilpotent Dt := hp.isNilpotent
  have hperf : Group.IsPerfect Dt := Subgroup.isPerfect_iff.mpr hDt
  by_contra hne
  have : Nontrivial Dt := (Subgroup.nontrivial_iff_ne_bot Dt).mpr hne
  exact Group.IsPerfect.not_isSolvable (G := Dt) inferInstance

end SU

end CFSG.HardMathSupport.Curtis.UnitaryLevi
