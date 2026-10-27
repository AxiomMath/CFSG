module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem span_singleton_mem_isotropicLines (h : UnitaryFieldData p f K) {n : ℕ} {v : Fin n → K}
    (hv0 : v ≠ 0) (hv : stdHermForm h n v v = 0) :
    Submodule.span K {v} ∈ isotropicLines h n := by
  refine ⟨finrank_span_singleton hv0, fun a ha => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  simp [hv]

theorem eq_smul_of_forall_isotropic (h : UnitaryFieldData p f K) {n : ℕ} (hn : 2 ≤ n)
    {M : Matrix (Fin n) (Fin n) K} (hM : ∀ x y, stdHermForm h n (M *ᵥ x) (M *ᵥ y) =
      stdHermForm h n x y)
    (hfix : ∀ v : Fin n → K, v ≠ 0 → stdHermForm h n v v = 0 → ∃ κ : K, M *ᵥ v = κ • v) :
    ∃ lam : K, ∀ x, M *ᵥ x = lam • x := by
  set B := stdHermForm h n with hBdef
  have hB : B.IsSymm := stdHermForm_isSymm h n
  have hBl : B.SeparatingLeft := stdHermForm_separatingLeft h n
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨e, he0, he⟩ := (hermitian_witt_basis h hB hBl (Module.finrank_fin_fun K)).2.1 hn
  obtain ⟨⟨f', hef, hf⟩, -⟩ := hermitian_hyperbolic_splitting h hB hBl he0 he
  have hfe : B f' e = 1 := by rw [hsymm, hef, map_one]
  have hf0 : f' ≠ 0 := by
    rintro rfl
    simp at hef
  obtain ⟨lam, hl⟩ := hfix e he0 he
  obtain ⟨μ, hμ⟩ := hfix f' hf0 hf
  have hne : ∀ v, B f' v = 1 → v ≠ 0 := by
    rintro v hv rfl
    simp at hv
  obtain ⟨τ, hτE, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  have hτ : τ + h.bar τ = 0 := (h.mem_traceZero).mp hτE
  have hlμ : μ = lam := by
    have hv : B (e + τ • f') (e + τ • f') = 0 := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he,
        hf, hef, hfe]
      linear_combination hτ
    obtain ⟨κ, hκ⟩ := hfix _ (hne _ (by simp [hfe, hf])) hv
    rw [mulVec_add, mulVec_smul, hl, hμ] at hκ
    have h1 := congrArg (B f') hκ
    have h2 := congrArg (B e) hκ
    simp only [map_add, map_smul, smul_eq_mul, hfe, hf, he, hef] at h1 h2
    have hκl : κ = lam := by linear_combination -h1
    rw [hκl] at h2
    exact mul_left_cancel₀ hτ0 (by linear_combination h2)
  have hl0 : lam ≠ 0 := by
    rintro rfl
    have := hM e f'
    rw [hl, zero_smul, map_zero, LinearMap.zero_apply, hef] at this
    exact zero_ne_one this
  have hW : ∀ w, B e w = 0 → B f' w = 0 → M *ᵥ w = lam • w := by
    intro w hew hfw
    have hwe : B w e = 0 := by rw [hsymm, hew, map_zero]
    have hwf : B w f' = 0 := by rw [hsymm, hfw, map_zero]
    have hwwF : h.bar (B w w) = B w w := hB.eq w w
    obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
    set c' := c * B w w with hc'
    have hc'' : c' + h.bar c' = -B w w := by
      rw [hc', map_mul, hwwF]
      linear_combination B w w * hc
    have hv : B (e + w + c' • f') (e + w + c' • f') = 0 := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, he,
        hf, hef, hfe, hew, hwe, hfw, hwf, RingHom.id_apply]
      linear_combination hc''
    obtain ⟨κ, hκ⟩ := hfix _ (hne _ (by simp [hfe, hf, hfw])) hv
    rw [mulVec_add, mulVec_add, mulVec_smul, hl, hμ, hlμ] at hκ
    have hfMw : B f' (M *ᵥ w) = 0 := by
      have h1 := hM f' w
      rw [hμ, hlμ, map_smulₛₗ, LinearMap.smul_apply, hfw, smul_eq_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left ((map_ne_zero h.bar).mpr hl0)
    have h1 := congrArg (B f') hκ
    simp only [map_add, map_smul, smul_eq_mul, hfe, hf, hfMw, hfw] at h1
    have hκl : κ = lam := by linear_combination -h1
    rw [hκl] at hκ
    linear_combination (norm := module) hκ
  refine ⟨lam, fun x => ?_⟩
  have hx : x = B f' x • e + B e x • f' + (x - B f' x • e - B e x • f') := by abel
  have hw1 : B e (x - B f' x • e - B e x • f') = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, he, hef]
    ring
  have hw2 : B f' (x - B f' x • e - B e x • f') = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hfe, hf]
    ring
  rw [hx, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hl, hμ, hlμ, hW _ hw1 hw2]
  module

theorem eq_scalar_of_mulVec_eq_smul {n : ℕ} {M : Matrix (Fin n) (Fin n) K} {lam : K}
    (hM : ∀ x, M *ᵥ x = lam • x) : M = Matrix.scalar (Fin n) lam := by
  ext i j
  have := congrFun (hM (Pi.single j 1)) i
  rw [mulVec_single_one, col_apply] at this
  rw [this, scalar_apply, diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem unitary_isotropic_kernel (h : UnitaryFieldData p f K) {n : ℕ} (hn : 2 ≤ n) :
    (MulAction.toPermHom (unitarySU p f K n) (isotropicLines h n)).ker = unitaryScalars h n := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hfix : ∀ L ∈ isotropicLines h n, g • L = L := fun L hL => by
      have := congrArg (fun σ : Equiv.Perm (isotropicLines h n) => ((σ ⟨L, hL⟩ :
        isotropicLines h n) : Submodule K (Fin n → K))) hg
      simpa using this
    obtain ⟨lam, hlam⟩ := eq_smul_of_forall_isotropic h hn ((mem_unitarySU_iff_isometry h).mp g.2).2
      fun v hv0 hv => by
        have hL := hfix _ (span_singleton_mem_isotropicLines h hv0 hv)
        have hgv : g • v ∈ Submodule.span K {v} := by
          rw [← hL]
          exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_span_singleton_self v)
        obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp hgv
        exact ⟨κ, hκ.symm⟩
    have hM := eq_scalar_of_mulVec_eq_smul hlam
    have hdet := ((mem_unitarySU_iff h).mp g.2).1
    rw [hM, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hdet
      exact zero_ne_one hdet
    have hgc : (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (Units.mk0 lam hlam0) :=
      Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hM)
    have hmem := (scalar_mem_statedSU_iff h.prime h.card_eq_sq (by omega) _).mp (hgc ▸ g.2)
    refine ⟨Units.mk0 lam hlam0, ?_, hmem.1, hgc⟩
    rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, hmem.2, Units.val_one]
  · rintro ⟨c, -, -, hg⟩
    refine Equiv.ext fun L => Subtype.ext ?_
    change g • (L : Submodule K (Fin n → K)) = L
    rw [Subgroup.smul_def, hg, scalar_smul_submodule]

end CFSG.ClassicalGroups.UnitaryFlag
