module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidM

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ABGLocalTools
open CFSG.Quasithin (perfectCore)
open scoped Pointwise

variable {K : Type} [Field K] {ε f : ℕ} (h : UnitaryFieldData 2 f K)

theorem conj_vecMulVec {n : ℕ} {u : Fin n → K} {g : GL (Fin n) K} (hg : g ∈ StatedSU n (2 ^ f) K)
    {ν : K} (hgu : (g : Matrix (Fin n) (Fin n) K) *ᵥ u = ν • u) :
    (g : Matrix (Fin n) (Fin n) K) * vecMulVec u (h.bar ∘ u) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (ν * h.bar ν) • vecMulVec u (h.bar ∘ u) := by
  have hgu' := adjM_mul_self_of_mem_statedSU h.bar_bar h.bar_apply hg
  have hinv : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      adjM h.bar (g : Matrix (Fin n) (Fin n) K) :=
    Units.inv_eq_of_mul_eq_one_left hgu'
  rw [hinv, mul_vecMulVec, hgu, vecMulVec_mul]
  have : (h.bar ∘ u) ᵥ* adjM h.bar (g : Matrix (Fin n) (Fin n) K) = h.bar ν • (h.bar ∘ u) := by
    funext j
    have := congrFun hgu j
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [vecMul, dotProduct, adjM, transpose_apply, map_apply, Function.comp,
      Pi.smul_apply, smul_eq_mul]
    rw [← map_mul, ← this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, mul_comm]
  rw [this, vecMulVec_smul, smul_vecMulVec, smul_smul, mul_comm]

include h in
theorem unitary_m123 [Finite K] [CharP K 2] (hf : 2 ≤ f) (hε : 2 ≤ ε)
    {M : GL (Fin (2 * 1 + ε)) K} (hMH : M ∈ StatedSU (2 * 1 + ε) (2 ^ f) K)
    (hM2 : orderOf M = 2)
    (hr : ((M : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) - 1).rank = 1) :
    (∃ S : Subgroup (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)), IsSylowOf 2 S ⊤ ∧
      S ≤ perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))} :
          Set (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))))) ∧
    (∀ z : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K), orderOf z = 2 →
      (∃ S : Subgroup (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)), IsSylowOf 2 S ⊤ ∧
        S ≤ centralizer ({z} : Set _)) →
        ∃ a : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K), a * z * a⁻¹ =
          QuotientGroup.mk ⟨M, hMH⟩) ∧
    (∀ z : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K), orderOf z = 2 →
      z ∈ centralizer (perfectCore (centralizer ({(QuotientGroup.mk ⟨M, hMH⟩ :
        StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))} :
          Set (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)))) :
            Set (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))) →
        ∃ (N : GL (Fin (2 * 1 + ε)) K) (hN : N ∈ StatedSU (2 * 1 + ε) (2 ^ f) K),
          (QuotientGroup.mk ⟨N, hN⟩ : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)) = z ∧
          ∃ a : K, (N : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) - 1 =
            a • ((M : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) - 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, c, hu0, hc0, hcσ, huu, hMuc⟩ := exists_transvection_eq h hMH hM2 hr
  obtain ⟨R, hR, hRu⟩ := exists_isHypTransport_col h (by omega) hu0 huu
  obtain ⟨S, hES, hSst⟩ := exists_sylow_le_stabU h hR
  set π : StatedSU (2 * 1 + ε) (2 ^ f) K →* StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K) :=
    QuotientGroup.mk' _ with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set W := vecMulVec u (h.bar ∘ u) with hW
  have hM : (M : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) = 1 + c • W := by
    rw [← hMuc, add_sub_cancel]
  have hK1 : ∀ g ∈ stabU h hR, g * ⟨M, hMH⟩ = ⟨M, hMH⟩ * g := by
    intro g hg
    have hgu := mulVec_of_mem_stabU h hR hg
    rw [hRu] at hgu
    have hgW := commute_vecMulVec_of_mulVec h g.2 hgu
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    change ((g : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) *
      (M : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) =
        (M : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K) *
          ((g : GL (Fin (2 * 1 + ε)) K) : Matrix (Fin (2 * 1 + ε)) (Fin (2 * 1 + ε)) K)
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, hgW]
  set Mbar : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K) := QuotientGroup.mk ⟨M, hMH⟩ with hMbar
  have hπM : π ⟨M, hMH⟩ = Mbar := rfl
  set Xbar := (stabU h hR).map π with hXbar
  have hK2 : ⁅Xbar, Xbar⁆ = Xbar := by rw [hXbar, ← map_commutator, commutator_stabU h hR hf hε]
  have hK3 : Xbar ≤ centralizer ({Mbar} : Set (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hπM, ← map_mul, ← map_mul, hK1 g hg]
  have hK4 := CFSG.Quasithin.le_perfectCore_of_perfect hK3 hK2
  set Sbar := (S : Subgroup (StatedSU (2 * 1 + ε) (2 ^ f) K)).map π with hSbar
  have hK5 : Sbar ≤ perfectCore (centralizer ({Mbar} :
      Set (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K)))) := (map_mono hSst).trans hK4
  have hSbarSyl : IsSylowOf 2 Sbar ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, S.isPGroup'.map π, ?_⟩
    rw [relIndex_top_right]
    exact (S.mapSurjective hπ).not_dvd_index
  have hlift : ∀ zbar : StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K),
      (∀ s ∈ Sbar, s * zbar = zbar * s) → ∃ b : K, h.bar b = b ∧
        ∃ N : StatedSU (2 * 1 + ε) (2 ^ f) K, (N : GL (Fin (2 * 1 + ε)) K).val = 1 + b • W ∧
          π N = zbar := by
    intro zbar hz
    obtain ⟨z, rfl⟩ := hπ zbar
    obtain ⟨b, hb, N, hN, hNz⟩ := exists_one_add_of_mk_commute h hR hES S.isPGroup' (z := z)
      fun s hs => by
        have := hz (π s) ⟨s, hs, rfl⟩
        rwa [← map_mul, ← map_mul] at this
    exact ⟨b, hb, N, by rw [hN, hRu], hNz⟩
  refine ⟨⟨Sbar, hSbarSyl, hK5⟩, ?_, ?_⟩
  · rintro z hz2 ⟨S', hS'syl, hS'z⟩
    obtain ⟨-, hS'p, hS'ind⟩ := isSylowOf_iff.mp hS'syl
    rw [relIndex_top_right] at hS'ind
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (StatedProj (StatedSU (2 * 1 + ε) (2 ^ f) K))
      (S.mapSurjective hπ) (hS'p.toSylow hS'ind)
    have hz' : ∀ s ∈ Sbar, s * (a⁻¹ * z * a) = (a⁻¹ * z * a) * s := by
      intro s hs
      have hmem : a * s * a⁻¹ ∈ S' := by
        have h1 : MulAut.conj a • s ∈ MulAut.conj a •
            ((S.mapSurjective hπ : Sylow 2 _) : Subgroup (StatedProj
              (StatedSU (2 * 1 + ε) (2 ^ f) K))) :=
          Subgroup.smul_mem_pointwise_smul _ _ _ hs
        rw [← Sylow.coe_subgroup_smul, ha, IsPGroup.toSylow_coe] at h1
        simpa [MulAut.smul_def, MulAut.conj_apply] using h1
      have h2 := mem_centralizer_singleton_iff.mp (hS'z hmem)
      calc s * (a⁻¹ * z * a) = a⁻¹ * ((a * s * a⁻¹) * z) * a := by group
        _ = a⁻¹ * (z * (a * s * a⁻¹)) * a := by rw [h2]
        _ = (a⁻¹ * z * a) * s := by group
    obtain ⟨b, hb, N, hN, hNz⟩ := hlift _ hz'
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at hN
      have hN1 : N = 1 := Subtype.ext (Units.ext hN)
      rw [hN1, map_one] at hNz
      have hz1 : z = 1 := by
        have := congrArg (fun x => a * x * a⁻¹) hNz
        simpa [mul_assoc] using this.symm
      rw [hz1, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    obtain ⟨ν, hν⟩ := h.normHom_surjective ⟨c / b, (h.mem_fixedField).mpr (by
      rw [map_div₀, hcσ, hb])⟩
    have hν' : ν * h.bar ν = c / b := congrArg Subtype.val hν
    have hν0 : ν ≠ 0 := by
      rintro rfl
      rw [zero_mul, eq_comm, div_eq_zero_iff] at hν'
      rcases hν' with h1 | h1
      · exact hc0 h1
      · exact hb0 h1
    obtain ⟨g, hg⟩ := exists_statedSU_mulVec_eq h (n := 2 * 1 + ε) (by omega) hu0 huu
      (smul_ne_zero hν0 hu0) (by rw [hform_smul_left, hform_smul_right, huu, mul_zero, mul_zero])
    have hgN : g * N * g⁻¹ = ⟨M, hMH⟩ := by
      refine Subtype.ext (Units.ext ?_)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
      rw [hN, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
        conj_vecMulVec h g.2 hg, ← Units.val_mul, mul_inv_cancel, Units.val_one, smul_smul, hν',
        mul_div_cancel₀ _ hb0, hM]
    refine ⟨π g * a⁻¹, ?_⟩
    calc π g * a⁻¹ * z * (π g * a⁻¹)⁻¹ = π g * (a⁻¹ * z * a) * (π g)⁻¹ := by group
      _ = π g * π N * (π g)⁻¹ := by rw [hNz]
      _ = π (g * N * g⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = Mbar := by rw [hgN, hπM]
  · intro z _ hzC
    obtain ⟨b, hb, N, hN, hNz⟩ := hlift z fun s hs => (mem_centralizer_iff.mp hzC s (hK5 hs))
    refine ⟨N, N.2, hNz, b / c, ?_⟩
    rw [hN, add_sub_cancel_left, hMuc, smul_smul, div_mul_cancel₀ _ hc0]

end CFSG.ComponentClassification.RankTwoClassical.URigid
