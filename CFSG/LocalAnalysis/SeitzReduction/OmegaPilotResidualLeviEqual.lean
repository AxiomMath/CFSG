module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviAssembly

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Similarity

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem polar_coordinateSemilinearMap (g : similarityPairs Q) (a b : Fin d → K) :
    QuadraticMap.polar Q (coordinateSemilinearMap g.val a) (coordinateSemilinearMap g.val b) =
      (multiplier Q g : K) * g.val.right (QuadraticMap.polar Q a b) := by
  simp only [QuadraticMap.polar, ← map_add, multiplier_spec, map_sub, mul_sub]

theorem mem_ker_iff_polar (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (v : Fin d → K) : v ∈ LinearMap.ker N ↔ ∀ x, QuadraticMap.polar Q (N x) v = 0 := by
  constructor
  · intro hv x
    rw [← QuadraticMap.polarBilin_apply_apply, hadj, LinearMap.mem_ker.mp hv, map_zero]
  · intro h
    rw [LinearMap.mem_ker]
    refine hB.2 _ fun x => ?_
    rw [← hadj, QuadraticMap.polarBilin_apply_apply]
    exact h x

theorem symm_mem_ker_of_mapsTo_range (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (g : similarityPairs Q)
    (hTr : ∀ u ∈ LinearMap.range N, coordinateSemilinearMap g.val u ∈ LinearMap.range N) :
    ∀ v ∈ LinearMap.ker N, (coordinateSemilinearMap g.val).symm v ∈ LinearMap.ker N := by
  intro v hv
  rw [mem_ker_iff_polar hB N hadj] at hv ⊢
  intro x
  obtain ⟨y, hy⟩ := hTr (N x) (LinearMap.mem_range_self N x)
  have h1 := polar_coordinateSemilinearMap g (N x) ((coordinateSemilinearMap g.val).symm v)
  rw [AddEquiv.apply_symm_apply, ← hy, hv y] at h1
  have h2 := (mul_eq_zero.mp h1.symm).resolve_left (Units.ne_zero _)
  exact (map_eq_zero_iff g.val.right g.val.right.injective).mp h2

end Similarity

section Kernel

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (hQ : ∃ v, Q v ≠ 0) {X : Subgroup (matrixProjectiveDerived Q)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v))

theorem mem_kerQuotHom_ker_iff (x : ↥X) :
    x ∈ (kerQuotHom hQ X N hXN).ker ↔
      ∀ v ∈ LinearMap.ker N, projLift hQ (x : matrixProjectiveDerived Q) v - v ∈
        LinearMap.range N := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v hv
    have h' := congrArg (fun f : Module.End K (LinearMap.ker N ⧸ rangeInKer N) =>
      f (Submodule.Quotient.mk ⟨v, hv⟩)) h
    change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk ⟨v, hv⟩) =
      Submodule.Quotient.mk ⟨v, hv⟩ at h'
    rw [kerQuotMap_mk'] at h'
    have h'' := (Submodule.Quotient.eq _).mp h'
    simpa [rangeInKer] using h''
  · intro h
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro z
    change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk z) = Submodule.Quotient.mk z
    rw [kerQuotMap_mk']
    apply (Submodule.Quotient.eq _).mpr
    have := h z z.2
    simpa [rangeInKer] using this

theorem kappa_mem_kerQuot (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (g : similarityPairs Q)
    (hTr : ∀ u ∈ LinearMap.range N, coordinateSemilinearMap g.val u ∈ LinearMap.range N)
    {x : matrixProjectiveDerived Q}
    (hx : ∀ v ∈ LinearMap.ker N, projLift hQ x v - v ∈ LinearMap.range N) :
    ∀ v ∈ LinearMap.ker N,
      projLift hQ (matrixProjectiveConjugationHom Q g x) v - v ∈ LinearMap.range N := by
  intro v hv
  have hv' := symm_mem_ker_of_mapsTo_range hB N hadj g hTr v hv
  have h := projLift_kappa_apply hQ g x ((coordinateSemilinearMap g.val).symm v)
  rw [AddEquiv.apply_symm_apply] at h
  rw [h]
  have e : coordinateSemilinearMap g.val (projLift hQ x ((coordinateSemilinearMap g.val).symm v)) -
      v = coordinateSemilinearMap g.val (projLift hQ x ((coordinateSemilinearMap g.val).symm v) -
        (coordinateSemilinearMap g.val).symm v) := by
    rw [map_sub, AddEquiv.apply_symm_apply]
  rw [e]
  exact hTr _ (hx _ hv')

end Kernel

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem spLeviData_of_kerQuotChart_of_mapsTo (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hNN : ∀ v, N (N v) = 0)
    (hadj : ∀ x y, QuadraticMap.polarBilin (coordinateQuadPlus n K) (N x) y =
      QuadraticMap.polarBilin (coordinateQuadPlus n K) x (N y))
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (N₂ : Subgroup ↥X) [N₂.Normal] (h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn) X N₂)
    (hTr : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ X, matrixProjectiveConjugationHom _ g x ∈ X) →
      ∀ u ∈ LinearMap.range N, coordinateSemilinearMap g.val u ∈ LinearMap.range N) :
    SpLeviData (plusFieldPart hf hK hn) X := by
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
  obtain ⟨hq₁, -⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn) X ρ.ker :=
    spLeviSection_of_kerQuot_plus hf hK hn hr N hNN hXN ρ hρ htr
  refine ⟨ρ.ker, N₂, ⊤, inferInstance, inferInstance, inferInstance, (by rwa [inf_top_eq]), ?_,
    ?_, r, hr, ⟨chartOfSurjective ρ hρ⟩, ?_⟩
  · intro N' hN' M hM hle
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hq₁ M hM hle
    · exact hq₂ M hM hle
    · exact Or.inr (top_le_iff.mp hle)
  · intro N' _ hN'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hs₁
    · exact hs₂
    · exact spLeviSection_top _ X
  · intro β hβ m hm
    obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
    rw [hρker] at hm ⊢
    rw [mem_kerQuotHom_ker_iff] at hm ⊢
    exact kappa_mem_kerQuot _ N hB hadj g (hTr g hβ) hm

end Plus

section FixedSpace

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem spLeviData_of_kerQuotChart_of_fixedSpace (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n) (hq4 : 4 ≤ Nat.card K)
    {X : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K))}
    (N : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) (hNN : ∀ v, N (N v) = 0)
    (hadj : ∀ x y, QuadraticMap.polarBilin (coordinateQuadPlus n K) (N x) y =
      QuadraticMap.polarBilin (coordinateQuadPlus n K) x (N y))
    (hXN : ∀ x ∈ X, ∀ v, projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x (N v) =
      N (projLift (exists_coordinateQuadPlus_ne_zero (by omega)) x v))
    {r : ℕ} (hr : 1 ≤ r) (ρ : ↥X →* StatedSp r K) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker = (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN).ker)
    (htr : ∀ x : ↥X, spMatTrace (ρ x) = LinearMap.trace K _
      (kerQuotHom (exists_coordinateQuadPlus_ne_zero (by omega)) X N hXN x))
    (N₂ : Subgroup ↥X) [N₂.Normal] (h12 : IsPGroup 2 ↥(ρ.ker ⊓ N₂))
    (hq₂ : ∀ M : Subgroup ↥X, M.Normal → N₂ ≤ M → M = N₂ ∨ M = ⊤)
    (hab₂ : N₂ = ⊤ ∨ ∃ a b : ↥X ⧸ N₂, a * b ≠ b * a)
    (hs₂ : SpLeviSection (plusFieldPart hf hK hn) X N₂)
    (hU : ∀ v, v ∈ LinearMap.range N ↔ ∀ x ∈ ρ.ker ⊓ N₂,
      projLift (exists_coordinateQuadPlus_ne_zero (by omega))
        (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v) :
    SpLeviData (plusFieldPart hf hK hn) X := by
  obtain ⟨-, hle₁⟩ := ker_props_of_surjective_sp hq4 hr ρ hρ
  have hR : IsPGroup 2 ↥(ρ.ker ⊓ N₂ ⊓ ⊤) := by rwa [inf_top_eq]
  have hRn : (ρ.ker ⊓ N₂ ⊓ ⊤).Normal := by
    rw [inf_top_eq]
    infer_instance
  have hN : ∀ N' ∈ ({ρ.ker, N₂, ⊤} : Set (Subgroup ↥X)),
      ∀ M : Subgroup ↥X, M.Normal → IsPGroup 2 M → M ≤ N' := by
    intro N' hN' M hM hMp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN'
    rcases hN' with rfl | rfl | rfl
    · exact hle₁ M hM hMp
    · exact le_of_isPGroup_of_eq_or_top hq₂ hab₂ M hM hMp
    · exact le_top
  have hU' : ∀ v, v ∈ LinearMap.range N ↔ ∀ x ∈ ρ.ker ⊓ N₂ ⊓ ⊤,
      projLift (exists_coordinateQuadPlus_ne_zero (by omega))
        (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v = v := by
    intro v
    rw [hU v, inf_top_eq]
  exact spLeviData_of_kerQuotChart_of_mapsTo hf hK hn hq4 N hNN hadj hXN hr ρ hρ hρker htr N₂ h12
    hq₂ hs₂ fun g hgX => mapsTo_of_fixedSpace_eq _ ρ.ker N₂ ⊤ hN hR hRn _ hU' g hgX

end FixedSpace

end CFSG.SeitzReduction.OmegaPilot
