module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmFrame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmEven
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2OmSign
public import CFSG.CharacterTheory.PSL2Table.TorusCharacters

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open QuadraticMap

theorem l2_om_kl {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hd : 10 ≤ Module.finrank K V)
    (y : Fin 4 → ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hy2 : ∀ i, y i * y i = 1) (hyc : ∀ i j, y i * y j = y j * y i) :
    ∃ D : Finset ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      33 ≤ D.card ∧ ∀ d ∈ D, d * d = 1 ∧ ∀ i, y i * d = d * y i := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let O : Subgroup (V ≃ₗ[K] V) := TauCeti.QuadraticMap.orthogonalGroup Q
  let Ω : Subgroup (V ≃ₗ[K] V) := ⁅O, O⁆
  have hΩle : Ω ≤ O := Subgroup.commutator_le_self O
  let x : Fin 4 → V ≃ₗ[K] V := fun i => (y i : V ≃ₗ[K] V)
  have hxO : ∀ i, x i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun i =>
    hΩle (y i).2
  have hx2 : ∀ i, x i * x i = 1 := fun i => by
    show ((y i : ↥Ω) : V ≃ₗ[K] V) * ((y i : ↥Ω) : V ≃ₗ[K] V) = 1
    rw [← Subgroup.coe_mul, hy2 i, Subgroup.coe_one]
  have hxc : ∀ i j, x i * x j = x j * x i := fun i j => by
    show ((y i : ↥Ω) : V ≃ₗ[K] V) * ((y j : ↥Ω) : V ≃ₗ[K] V) =
        ((y j : ↥Ω) : V ≃ₗ[K] V) * ((y i : ↥Ω) : V ≃ₗ[K] V)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hyc i j]
  obtain ⟨w, hw0, hwo, hwe⟩ := l2_om_frame h2 hQ hd hxO hx2 hxc
  let c : Fin 8 → Prop := fun j => IsSquare (Q (w j))
  have hc : ∀ j k, (c j ↔ c k) → IsSquare (Q (w j) * Q (w k)) := by
    intro j k hjk
    by_cases hj : c j
    · exact hj.mul (hjk.mp hj)
    · exact CFSG.PSL2Table.isSquare_mul_of_not_isSquare hj (fun hk => hj (hjk.mpr hk))
  obtain ⟨g, _hgO, hg2, hgx, hgw, hgΩ⟩ :=
    l2_om_sign_family h2 hxO hw0 hwo hwe c hc
  have hwne : ∀ k, w k ≠ 0 := fun k h => hw0 k (by rw [h, QuadraticMap.map_zero])
  have hneg : ∀ k, -w k ≠ w k := by
    intro k h
    apply hwne k
    have h2v : (2 : K) • w k = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h.symm
    calc w k = (1 : K) • w k := (one_smul K (w k)).symm
      _ = ((2 : K)⁻¹ * (2 : K)) • w k := by rw [inv_mul_cancel₀ h2]
      _ = (2 : K)⁻¹ • ((2 : K) • w k) := by rw [smul_smul]
      _ = (2 : K)⁻¹ • (0 : V) := by rw [h2v]
      _ = 0 := smul_zero _
  have hg_inj : Function.Injective g := by
    intro J J' hJJ'
    ext k
    have hk : g J (w k) = g J' (w k) := by rw [hJJ']
    rw [hgw J k, hgw J' k] at hk
    by_cases hJ : k ∈ J <;> by_cases hJ' : k ∈ J'
    · simp [hJ, hJ']
    · rw [if_pos hJ, if_neg hJ'] at hk
      exact (hneg k hk).elim
    · rw [if_neg hJ, if_pos hJ'] at hk
      exact (hneg k hk.symm).elim
    · simp [hJ, hJ']
  let F : Finset (Finset (Fin 8)) :=
    Finset.univ.filter fun J : Finset (Fin 8) =>
      Even (J.filter c).card ∧ Even (J.filter fun j => ¬ c j).card
  have hFcard : 64 ≤ F.card := l2_even_class_count c
  have hΩmem : ∀ J ∈ F, g J ∈ Ω := by
    intro J hJ
    have hJ' : J ∈ Finset.univ.filter (fun J : Finset (Fin 8) =>
        Even (J.filter c).card ∧ Even (J.filter fun j => ¬ c j).card) := hJ
    exact hgΩ J (Finset.mem_filter.mp hJ').2.1 (Finset.mem_filter.mp hJ').2.2
  let φ : {J : Finset (Fin 8) // J ∈ F} → ↥Ω := fun J => ⟨g J.1, hΩmem J.1 J.2⟩
  let D : Finset ↥Ω := F.attach.image φ
  have hφ_inj : Function.Injective φ := by
    intro J J' h
    have hg_eq : g J.1 = g J'.1 := congrArg Subtype.val h
    exact Subtype.ext (hg_inj hg_eq)
  have hDcard : D.card = F.card := by
    change (F.attach.image φ).card = F.card
    rw [Finset.card_image_of_injective F.attach hφ_inj, Finset.card_attach]
  refine ⟨D, ?_, ?_⟩
  · rw [hDcard]
    exact le_trans (by norm_num) hFcard
  · intro d hd
    change d ∈ F.attach.image φ at hd
    rcases Finset.mem_image.mp hd with ⟨J, -, rfl⟩
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact hg2 J.1
    · intro i
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hgx J.1 i

end CFSG.OddStandard.HigherRank.YamadaG23
