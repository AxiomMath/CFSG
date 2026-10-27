module

public import CFSG.LieType.SeitzGeneration.OrthSdLines

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem polar_planeFixSpace_lineSpace (hK : KernelLineData Q p E) {N : Subgroup E}
    (hN : Nat.card N = p) {v s : V} (hv : v ∈ planeFixSpace E) (hs : s ∈ lineSpace N) :
    polar Q v s = 0 := by
  have hne : (none : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ := by simp
  have := hK.orth _ _ hne v hv s hs
  rwa [polarBilin_apply_apply] at this

theorem exists_pivot_of_mixing (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (h2 : (2 : K) ≠ 0)
    {L N : Subgroup E} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg0 : ∀ v ∈ planeFixSpace E, g v = v)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (h5 : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace L)) (h6 : 6 ≤ finrank K ↥(lineSpace N)) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  classical
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hU₀reg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace L) :=
    polarNondegOn_of_nondegenerate (regular_sup hK hL)
  have hVNreg : PolarNondegOn Q (lineSpace N) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hp0N : ∀ v ∈ planeFixSpace E, ∀ s ∈ lineSpace N, polar Q v s = 0 := fun v hv s hs =>
    polar_planeFixSpace_lineSpace hK hN hv hs
  have hpLN : ∀ v ∈ lineSpace L, ∀ s ∈ lineSpace N, polar Q v s = 0 :=
    orthSep_lineSpace hK hL hN hLN
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  obtain ⟨σ, f₁, w, f₂, hσU, hf₁U, hwU, hf₂U, hQσ, hQf₁, hQw, hQf₂, h11, h22, h12, h1f2, hf1w,
    hf1f2⟩ := hasOrthPairs_of_dim hU₀reg h5
  obtain ⟨σ₀, hσ₀, σL, hσL, hσeq⟩ := Submodule.mem_sup.mp hσU
  obtain ⟨w₀, hw₀, wL, hwL, hweq⟩ := Submodule.mem_sup.mp hwU
  rw [hLA] at hσL hwL
  obtain ⟨z₁, hz₁⟩ := hσL
  obtain ⟨z₂, hz₂⟩ := hwL
  have hσdec : σ = σ₀ + ιA z₁ := by rw [hz₁, hσeq]
  have hwdec : w = w₀ + ιA z₂ := by rw [hz₂, hweq]
  have hwf1 : polar Q w f₁ = 0 := by rw [polar_comm]; exact hf1w
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    have hw0 : w = w₀ := by rw [hwdec, h0, map_zero, add_zero]
    have : w = 0 := haniso w (hw0 ▸ hw₀) hQw
    have := h22
    rw [‹w = 0›, polar_zero_left] at this
    exact zero_ne_one this
  have hind : ∀ c : K, z₁ ≠ c • z₂ := by
    intro c hc
    have hσc : σ - c • w = σ₀ - c • w₀ := by
      rw [hσdec, hwdec, hc, map_smul]
      module
    have hmem : σ - c • w ∈ planeFixSpace E := by
      rw [hσc]; exact (planeFixSpace E).sub_mem hσ₀ ((planeFixSpace E).smul_mem _ hw₀)
    have hQ0 : Q (σ - c • w) = 0 := by
      rw [map_sub_smul', hQσ, hQw, h12]; ring
    have h0 : σ - c • w = 0 := haniso _ hmem hQ0
    have := congrArg (fun v => polar Q v f₁) h0
    simp only [polar_sub_left, polar_smul_left_eq, polar_zero_left, h11, hwf1] at this
    simp at this
  set bσ : V := ιB (β z₁) with hbσ
  set bw : V := ιB (β z₂) with hbw
  have hbσN : bσ ∈ lineSpace N := hιBN _
  have hbwN : bw ∈ lineSpace N := hιBN _
  have hbind : ∀ c : K, bσ ≠ c • bw := by
    intro c hc
    apply hind c
    apply hβ
    apply hιB
    rw [map_smul, map_smul]
    exact hc
  obtain ⟨t, htN, htw, htσ⟩ := exists_perp_not_perp hVNreg hbσN hbwN hbind
  let F : Fin 3 → V →ₗ[K] K := ![(polarBilin Q).flip bσ, (polarBilin Q).flip bw,
    (polarBilin Q).flip t]
  obtain ⟨s, hsN, hs0, hsQ, hsF⟩ := exists_singular_in_kernel h2 h6 F
  have hs1 : polar Q s bσ = 0 := by simpa [F, polarBilin_apply_apply] using hsF 0
  have hs2 : polar Q s bw = 0 := by simpa [F, polarBilin_apply_apply] using hsF 1
  have hs3 : polar Q s t = 0 := by simpa [F, polarBilin_apply_apply] using hsF 2
  have hσ' : g σ = σ₀ + (ιA (α z₁) + bσ) := by
    rw [hσdec, map_add, hg0 σ₀ hσ₀, hgact]
  have hw' : g w = w₀ + (ιA (α z₂) + bw) := by
    rw [hwdec, map_add, hg0 w₀ hw₀, hgact]
  have hpolN : ∀ (v₀ : V), v₀ ∈ planeFixSpace E → ∀ (z : W) (y : V), y ∈ lineSpace N →
      polar Q (v₀ + (ιA (α z) + ιB (β z))) y = polar Q (ιB (β z)) y := by
    intro v₀ hv₀ z y hy
    rw [polar_add_left, polar_add_left, hp0N v₀ hv₀ y hy, hpLN _ (hιAL _) y hy, zero_add,
      zero_add]
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hθ : polar Q (g σ) t ≠ 0 := by
    rw [hσ', hpolN σ₀ hσ₀ z₁ t htN, polar_comm]
    exact htσ
  have hcomm := eichler_conj_pivot (Q := Q) (σ := g σ) (w := g w) (s := s) (t := t)
    (by rw [hQg, hQσ]) (by rw [hQg, hQw]) hsQ (by rw [hOg, h12])
    (by rw [hσ', hpolN σ₀ hσ₀ z₁ s hsN, polar_comm, hs1])
    (by rw [hw', hpolN w₀ hw₀ z₂ s hsN, polar_comm, hs2]) hs3
    (by rw [hw', hpolN w₀ hw₀ z₂ t htN, polar_comm, htw])
  have hY : eichler Q s t ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN) (Submodule.mem_sup_right htN)
  have hZ : eichler Q (g σ) (g w) ∈ orthCentralizerSpan Q E := by
    rw [← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (eichler_mem_span_of_mem_sup hEΩ hL0 hσU hwU))
      (Subgroup.inv_mem _ hgH)
  have hW : eichler Q (g w) (polar Q (g σ) t • s) ∈ orthCentralizerSpan Q E := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hZ)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hY hZ) (Subgroup.inv_mem _ hY))
    rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this
  set θ : K := polar Q (g σ) t with hθdef
  have hQw' : Q (g w) = 0 := by rw [hQg, hQw]
  have hQs' : Q (θ • s) = 0 := by rw [map_smul_eq_sq, hsQ, mul_zero]
  have hpol : polar Q (g w) (θ • s) = 0 := by
    rw [polar_smul_right_eq, hw', hpolN w₀ hw₀ z₂ s hsN, polar_comm, hs2, mul_zero]
  have hdec : -(g w) = -(w₀ + bw) + -(ιA (α z₂)) := by
    rw [hw']
    abel
  have hv1 : polar Q (θ • s) (-(w₀ + bw)) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_add_right, polar_comm Q s w₀,
      hp0N w₀ hw₀ s hsN, hs2]
    ring
  have hv2 : polar Q (θ • s) (-(ιA (α z₂))) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s (ιA (α z₂)),
      hpLN _ (hιAL _) s hsN]
    ring
  have hmulE : eichler Q (θ • s) (-(w₀ + bw)) * eichler Q (θ • s) (-(ιA (α z₂))) =
      eichler Q (θ • s) (-(g w)) := by
    rw [eichler_mul hv1 hv2, ← hdec]
  have hθsN : θ • s ∈ planeFixSpace E ⊔ lineSpace N :=
    Submodule.mem_sup_right ((lineSpace N).smul_mem _ hsN)
  have hE1 : eichler Q (θ • s) (-(w₀ + bw)) ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 hθsN
      (Submodule.neg_mem _ (Submodule.add_mem_sup hw₀ hbwN))
  have hE2 : eichler Q (θ • s) (-(g w)) ∈ orthCentralizerSpan Q E := by
    rw [← eichler_swap hQw' hQs' hpol]
    exact hW
  have hE3 : eichler Q (θ • s) (-(ιA (α z₂))) ∈ orthCentralizerSpan Q E := by
    have : eichler Q (θ • s) (-(ιA (α z₂))) =
        (eichler Q (θ • s) (-(w₀ + bw)))⁻¹ * eichler Q (θ • s) (-(g w)) := by
      rw [← hmulE]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2
  refine ⟨θ • s, (lineSpace N).smul_mem _ hsN, smul_ne_zero hθ hs0, hQs', -(ιA (α z₂)),
    (lineSpace L).neg_mem (hιAL _), neg_ne_zero.mpr ((map_ne_zero_iff ιA hιA).mpr
      ((map_ne_zero_iff α hα).mpr hz₂0)), ?_, hE3⟩
  rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s (ιA (α z₂)),
    hpLN _ (hιAL _) s hsN]
  ring

end Pivot

end CFSG.LieType.SeitzGeneration.OrthBlk
