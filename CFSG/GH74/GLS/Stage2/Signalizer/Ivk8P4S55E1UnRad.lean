module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1FlRad
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} (h : UnitaryFieldData p f K)

theorem posFlag_mono' {i j : ℕ} (hij : i ≤ j) : posFlag r ε K i ≤ posFlag r ε K j :=
  fun _ hv a ha => hv a (hij.trans ha)

theorem hypFlag_le_compl (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) :
    hypFlag h r ε d ≤ hypFlag h r ε (2 * r + ε - d) := by
  rw [hypFlag_eq_posFlag h hε (by omega), hypFlag_eq_posFlag h hε (by omega)]
  exact posFlag_mono' (by omega)

@[expose] noncomputable def unRad (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) : Subgroup (hypSU h r ε) :=
  radFl (hypSU h r ε) (hypFlag h r ε d) (hypFlag h r ε (2 * r + ε - d))
    (hypFlag_le_compl h hε hd)

theorem mulVec_mem_of_mem_isoStabilizer {W : Submodule K (HypIndex r ε → K)} {s : hypSU h r ε}
    (hs : s ∈ isoStabilizer h r ε W) {w : HypIndex r ε → K} (hw : w ∈ W) :
    ((s : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W := by
  have h1 := mem_isoStabilizer.mp hs
  have h2 : s • w ∈ s • W := Submodule.smul_mem_pointwise_smul w s W hw
  rw [h1] at h2
  exact h2

theorem hypFlag_compl_eq (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) :
    hypFlag h r ε (2 * r + ε - d) = (hypFlag h r ε d).orthogonalBilin (hypForm h r ε) := by
  rw [hypFlag_eq_posFlag h hε (by omega), hypFlag_eq_posFlag h hε (by omega : d ≤ 2 * r + ε),
    ← isoFlag_eq_posFlag hd, orthogonal_isoFlag h hε hd]

theorem mulVec_mem_hypFlag_compl (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) {s : hypSU h r ε}
    (hs : s ∈ isoStabilizer h r ε (hypFlag h r ε d)) {x : HypIndex r ε → K}
    (hx : x ∈ hypFlag h r ε (2 * r + ε - d)) :
    ((s : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x ∈
      hypFlag h r ε (2 * r + ε - d) := by
  rw [hypFlag_compl_eq h hε hd] at hx ⊢
  rw [Submodule.mem_orthogonalBilin] at hx ⊢
  intro n hn
  have hn' := mulVec_mem_of_mem_isoStabilizer h (inv_mem hs) hn
  have key := hypForm_smul_smul h s
    (((s⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) *ᵥ n) x
  have hss : ((s : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (((s⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      = 1 := by
    rw [Subgroup.coe_inv, Units.mul_inv]
  have e1 : s • (((s⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) *ᵥ n) = n := by
    change ((s : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      ((((s⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
        *ᵥ n) = n
    rw [Matrix.mulVec_mulVec, hss, Matrix.one_mulVec]
  rw [e1] at key
  change (hypForm h r ε) n (s • x) = 0
  rw [key]
  exact hx _ hn'

theorem conj_mem_unRad (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) {s : hypSU h r ε}
    (hs : s ∈ isoStabilizer h r ε (hypFlag h r ε d)) {g : hypSU h r ε}
    (hg : g ∈ unRad h hε hd) : s * g * s⁻¹ ∈ unRad h hε hd :=
  conj_mem_radFl (fun _ hw => mulVec_mem_of_mem_isoStabilizer h hs hw)
    (fun _ hw => mulVec_mem_hypFlag_compl h hε hd hs hw)
    (fun _ hw => mulVec_mem_of_mem_isoStabilizer h (inv_mem hs) hw)
    (fun _ hw => mulVec_mem_hypFlag_compl h hε hd (inv_mem hs) hw) hg

theorem unRad_le_isoStabilizer (hε : ε ≤ 1) {d : ℕ} (hd : d ≤ r) :
    unRad h hε hd ≤ isoStabilizer h r ε (hypFlag h r ε d) := by
  rintro g ⟨hg1, hg2, hg3⟩
  rw [mem_isoStabilizer]
  apply le_antisymm
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a g _).mp ha
    have : g • b = b := hg1 b hb
    rw [this]
    exact hb
  · intro w hw
    exact (Submodule.mem_smul_pointwise_iff_exists w g _).mpr ⟨w, hw, hg1 w hw⟩

theorem exists_smul_of_hypProj_eq {g g' : hypSU h r ε}
    (e : hypProj h r ε g' = hypProj h r ε g) :
    ∃ c : K, c ≠ 0 ∧ c ^ (2 * r + ε) = 1 ∧
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        c • ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  have h1 : g'⁻¹ * g ∈ hypScalars h r ε := QuotientGroup.eq.mp e
  obtain ⟨c, -, hcn, hc⟩ := h1
  refine ⟨(c : K), c.ne_zero, ?_, ?_⟩
  · have := congrArg (fun u : Kˣ => (u : K)) hcn
    simpa using this
  · have h2 : (g : GL (HypIndex r ε) K) = (g' : GL (HypIndex r ε) K) *
        ((g'⁻¹ * g : hypSU h r ε) : GL (HypIndex r ε) K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h2, Units.val_mul, hc, GeneralLinearGroup.coe_scalar, scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem fix_matrix (hr : 1 ≤ r) (hε : ε ≤ 1) (x : semilinearSimilitudes h r ε)
    (g : hypSU h r ε)
    (hfix : semilinearAutHom h hr hε x (hypProj h r ε g) = hypProj h r ε g) :
    ∃ c : K, c ≠ 0 ∧ c ^ (2 * r + ε) = 1 ∧
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        c • ((((x : SemiGL (HypIndex r ε) K).left : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map
            (x : SemiGL (HypIndex r ε) K).right *
          (((x : SemiGL (HypIndex r ε) K).left⁻¹ : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K)) := by
  rw [semilinearAutHom_apply] at hfix
  obtain ⟨c, hc0, hcn, hc⟩ := exists_smul_of_hypProj_eq h hfix
  refine ⟨c, hc0, hcn, hc.trans (congrArg (c • ·) ?_)⟩
  simp only [Units.val_mul, coe_glAut]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
