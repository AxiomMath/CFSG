module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrR2UniDiag

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

section Conj

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K}
  {y : semilinearSimilitudes h r ε}

@[expose] def conjSU (y : semilinearSimilitudes h r ε) (g : hypSU h r ε) : hypSU h r ε :=
  ⟨_, conj_mem_hypSU y.2 g⟩

theorem coe_conjSU (y : semilinearSimilitudes h r ε) (g : hypSU h r ε) :
    ((conjSU y g : hypSU h r ε) : GL (HypIndex r ε) K) =
      (y : SemiGL (HypIndex r ε) K).left * glAut (y : SemiGL (HypIndex r ε) K).right
        (g : GL (HypIndex r ε) K) * (y : SemiGL (HypIndex r ε) K).left⁻¹ :=
  rfl

theorem coe_conjSU_apply {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) (g : hypSU h r ε) (a b : HypIndex r ε) :
    (((conjSU y g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a b =
      (d a : K) * (y : SemiGL (HypIndex r ε) K).right
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a b) *
          ((d b)⁻¹ : Kˣ) := by
  rw [coe_conjSU, hy]
  exact coe_diagGL_conj d _ _ a b

theorem coe_conjSU_diag {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) (g : hypSU h r ε) (a : HypIndex r ε) :
    (((conjSU y g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a a =
      (y : SemiGL (HypIndex r ε) K).right
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a) := by
  rw [coe_conjSU_apply hy]
  have : (d a : K) * ((d a)⁻¹ : Kˣ) = 1 := Units.mul_inv _
  calc _ = ((d a : K) * ((d a)⁻¹ : Kˣ)) * (y : SemiGL (HypIndex r ε) K).right
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) a a) := by ring
    _ = _ := by rw [this, one_mul]

theorem blockTriangular_conjSU {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {g : hypSU h r ε}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
      fullPos) :
    (((conjSU y g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos := by
  intro a b hab
  rw [coe_conjSU_apply hy, hg hab, map_zero, mul_zero, zero_mul]

theorem conjSU_mem_hypBorel {d : HypIndex r ε → Kˣ} (hε : ε ≤ 1)
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {g : hypSU h r ε}
    (hg : g ∈ hypBorel h r ε) : conjSU y g ∈ hypBorel h r ε :=
  mem_hypBorel_of_blockTriangular h
    (blockTriangular_conjSU hy (blockTriangular_of_mem_hypBorel h hε hg))

theorem conjSU_mem_hypUnitriangular {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {g : hypSU h r ε}
    (hg : g ∈ hypUnitriangular h r ε) : conjSU y g ∈ hypUnitriangular h r ε := by
  rw [mem_hypUnitriangular] at hg ⊢
  exact ⟨blockTriangular_conjSU hy hg.1, fun a => by rw [coe_conjSU_diag hy, hg.2 a, map_one]⟩

theorem conjSU_mul_pow_inv_mem {d : HypIndex r ε → Kˣ} (hε : ε ≤ 1)
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {k : ℕ}
    (hk : ∀ x : K, (y : SemiGL (HypIndex r ε) K).right x = x ^ k) {g : hypSU h r ε}
    (hg : g ∈ hypBorel h r ε) : conjSU y g * (g ^ k)⁻¹ ∈ hypUnitriangular h r ε := by
  set g' : hypBorel h r ε := ⟨g, hg⟩ with hg'
  set c' : hypBorel h r ε := ⟨conjSU y g, conjSU_mem_hypBorel hε hy hg⟩ with hc'
  have hdiag : hypDiagHom h r ε hε c' = (hypDiagHom h r ε hε g') ^ k := by
    funext i
    apply Units.ext
    simp only [Pi.pow_apply, Units.val_pow_eq_pow_val, coe_hypDiagHom]
    exact (coe_conjSU_diag hy g (.inl i)).trans (hk _)
  have hmem : c' * (g' ^ k)⁻¹ ∈ (hypDiagHom h r ε hε).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hdiag, mul_inv_cancel]
  rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hmem
  simpa [g', c'] using hmem

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

theorem aut_mem_hypProjUnitriangular {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {w : hypPSU h r ε}
    (hw : w ∈ hypProjUnitriangular h r ε) :
    semilinearAutHom h hr hε y w ∈ hypProjUnitriangular h r ε := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [semilinearAutHom_apply]
  exact ⟨_, conjSU_mem_hypUnitriangular hy hu, rfl⟩

theorem aut_power_map {d : HypIndex r ε → Kˣ}
    (hy : (y : SemiGL (HypIndex r ε) K).left = diagGL d) {k : ℕ}
    (hk : ∀ x : K, (y : SemiGL (HypIndex r ε) K).right x = x ^ k) {b : hypPSU h r ε}
    (hb : b ∈ hypProjBorel h r ε) :
    semilinearAutHom h hr hε y b * (b ^ k)⁻¹ ∈ hypProjUnitriangular h r ε := by
  obtain ⟨g, hg, rfl⟩ := hb
  rw [semilinearAutHom_apply]
  refine ⟨conjSU y g * (g ^ k)⁻¹, conjSU_mul_pow_inv_mem hε hy hk hg, ?_⟩
  rw [map_mul, map_inv, map_pow]
  rfl

end Conj

section Sim

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K}

theorem commutator_mem_hypProjUnitriangular (hε : ε ≤ 1) {b c : hypPSU h r ε}
    (hb : b ∈ hypProjBorel h r ε) (hc : c ∈ hypProjBorel h r ε) :
    ⁅b, c⁆ ∈ hypProjUnitriangular h r ε := by
  obtain ⟨g, hg, rfl⟩ := hb
  obtain ⟨g', hg', rfl⟩ := hc
  refine ⟨⁅g, g'⁆, ?_, map_commutatorElement _ _ _⟩
  set g1 : hypBorel h r ε := ⟨g, hg⟩
  set g2 : hypBorel h r ε := ⟨g', hg'⟩
  have hc : ⁅g1, g2⁆ ∈ (hypDiagHom h r ε hε).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hc
  simpa [g1, g2, commutatorElement_def] using hc

@[expose] def isometrySim (δ : GL (HypIndex r ε) K) (hδ : δ ∈ hypUnitary h r ε) (σ : K ≃+* K) :
    semilinearSimilitudes h r ε :=
  ⟨⟨δ, σ⟩, 1, one_ne_zero, map_one _, by rw [one_smul]; exact hδ⟩

theorem semilinearAutHom_inl (hr : 1 ≤ r) (hε : ε ≤ 1) (s : hypSU h r ε) :
    semilinearAutHom h hr hε ⟨SemidirectProduct.inl (s : GL (HypIndex r ε) K),
      inl_mem_semilinearSimilitudes s⟩ = MulAut.conj (hypProj h r ε s) := by
  ext w
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε w
  rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg _ (Subtype.ext ?_)
  change (s : GL (HypIndex r ε) K) * glAut 1 (g : GL (HypIndex r ε) K) *
    (s : GL (HypIndex r ε) K)⁻¹ = (s : GL (HypIndex r ε) K) * (g : GL (HypIndex r ε) K) *
      (s : GL (HypIndex r ε) K)⁻¹
  rw [map_one, MulAut.one_apply]

end Sim

end CFSG.AGLEmbedding.ParabAutIrr
