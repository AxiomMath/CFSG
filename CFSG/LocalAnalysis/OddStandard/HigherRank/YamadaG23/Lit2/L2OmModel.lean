module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmKL
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix

private noncomputable def statedOmegaEquivCommutator {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K}
    (hQ₀ : ⇑Q = Q₀) :
    CFSG.Open.StatedOmega Q₀ ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap
      (CFSG.Open.StatedOmega Q₀)).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ₀]
      exact Subgroup.map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _))

theorem l2_stated_kl {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (h2 : (2 : K) ≠ 0) {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 10 ≤ Fintype.card ι)
    (y : Fin 4 → ↥(CFSG.Open.StatedOmega Q₀)) (hy2 : ∀ i, y i * y i = 1)
    (hyc : ∀ i j, y i * y j = y j * y i) :
    ∃ D : Finset ↥(CFSG.Open.StatedOmega Q₀), 33 ≤ D.card ∧
      ∀ d ∈ D, d * d = 1 ∧ ∀ i, y i * d = d * y i := by
  let e := statedOmegaEquivCommutator Q hQ₀
  have hy2' : ∀ i, e (y i) * e (y i) = 1 := fun i => by
    rw [← map_mul e, hy2 i, map_one]
  have hyc' : ∀ i j, e (y i) * e (y j) = e (y j) * e (y i) := fun i j => by
    rw [← map_mul e, ← map_mul e, hyc i j]
  have hd' : 10 ≤ Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hd
  obtain ⟨D', hD'card, hD'mem⟩ := l2_om_kl h2 hQ hd' (fun i => e (y i)) hy2' hyc'
  refine ⟨D'.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
  · rw [Finset.card_map]
    exact hD'card
  · intro d hd
    obtain ⟨d', hd'mem', rfl⟩ := Finset.mem_map.mp hd
    obtain ⟨hd'd', hcomm⟩ := hD'mem d' hd'mem'
    refine ⟨?_, fun i => ?_⟩
    · change e.symm d' * e.symm d' = 1
      rw [← map_mul e.symm, hd'd', map_one]
    · rw [← e.symm_apply_apply (y i)]
      change e.symm (e (y i)) * e.symm d' = e.symm d' * e.symm (e (y i))
      rw [← map_mul e.symm, ← map_mul e.symm, hcomm i]

theorem l2_stated_ker {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Nonempty ι] :
    (∀ u ∈ (CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀), u * u = 1) ∧
      Nat.card ↥((CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀)) ≤ 2 := by
  have hv : ∃ v, Q v ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    let v₀ : ι → K := Pi.single i 1
    have hv₀ : v₀ ≠ 0 := by
      intro hh
      have := congrFun hh i
      rw [Pi.zero_apply] at this
      have h1 : (1 : K) = 0 := by simpa [v₀] using this
      exact one_ne_zero h1
    refine hv₀ (hQ.1 v₀ fun y => ?_)
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h (v₀ + y), h v₀, h y]
    simp
  have hsq : ∀ u ∈ (CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀),
      u * u = 1 := by
    intro u hu
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (u : GL ι K) := by
      have hmem : (u : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι).range :=
        Subgroup.mem_subgroupOf.mp hu
      exact MonoidHom.mem_range.mp hmem
    have hc2 : (c : K) ^ 2 = 1 :=
      CFSG.LieType.Steinberg.sq_eq_one_of_scalar_mem_statedOmega hQ₀ hv (hc.symm ▸ u.2)
    have hcc : c * c = 1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_one]
      simpa [pow_two] using hc2
    have hGL : (u : GL ι K) * (u : GL ι K) = 1 := by
      rw [← hc, ← map_mul, hcc, map_one]
    exact Subtype.ext (by simpa using hGL)
  refine ⟨hsq, ?_⟩
  let φ : ↥((CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀)) →* GL ι K :=
    (Subgroup.subtype (CFSG.Open.StatedOmega Q₀)).comp
      (Subgroup.subtype ((CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀)))
  have hφ : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hforall : ∀ g : ↥((CFSG.Open.StatedScalars ι K).subgroupOf (CFSG.Open.StatedOmega Q₀)),
      ∃ u : K, u ^ 2 = 1 ∧ ((φ g : GL ι K) : Matrix ι ι K) = Matrix.scalar ι u := by
    intro g
    obtain ⟨c, hc⟩ : ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (g.1 : GL ι K) := by
      have hmem : (g.1 : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι).range :=
        Subgroup.mem_subgroupOf.mp g.2
      exact MonoidHom.mem_range.mp hmem
    refine ⟨(c : K),
      CFSG.LieType.Steinberg.sq_eq_one_of_scalar_mem_statedOmega hQ₀ hv (hc.symm ▸ g.1.2), ?_⟩
    have hphi : φ g = Matrix.GeneralLinearGroup.scalar ι c := hc.symm
    rw [hphi, Matrix.GeneralLinearGroup.coe_scalar]
  exact CFSG.LieType.Steinberg.card_le_two_of_forall_scalar hφ hforall

end CFSG.OddStandard.HigherRank.YamadaG23
