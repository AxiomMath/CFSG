module

public import CFSG.LieType.SeitzGeneration.OrthEvenSingular
public import CFSG.LieType.SeitzGeneration.OrthSdPivot

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem exists_pivot_of_data (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {g : V ≃ₗ[K] V} (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w σ₀ w₀ a₁ a₂ b₁ b₂ s t : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0)
    (hσ₀ : σ₀ ∈ planeFixSpace E) (hw₀ : w₀ ∈ planeFixSpace E) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hb₂ : b₂ ∈ lineSpace N)
    (hgσ : g σ = σ₀ + (a₁ + b₁)) (hgw : g w = w₀ + (a₂ + b₂)) (ha₂0 : a₂ ≠ 0)
    (hsN : s ∈ lineSpace N) (htN : t ∈ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hs1 : polar Q s b₁ = 0) (hs2 : polar Q s b₂ = 0) (hs3 : polar Q s t = 0)
    (htw : polar Q t b₂ = 0) (htσ : polar Q t b₁ ≠ 0) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  classical
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hp0N : ∀ v ∈ planeFixSpace E, ∀ s ∈ lineSpace N, polar Q v s = 0 := fun v hv s hs =>
    polar_planeFixSpace_lineSpace hK hN hv hs
  have hpLN : ∀ v ∈ lineSpace L, ∀ s ∈ lineSpace N, polar Q v s = 0 :=
    orthSep_lineSpace hK hL hN hLN
  have hpolN : ∀ (v₀ a b y : V), v₀ ∈ planeFixSpace E → a ∈ lineSpace L → y ∈ lineSpace N →
      polar Q (v₀ + (a + b)) y = polar Q b y := by
    intro v₀ a b y hv₀ ha hy
    rw [polar_add_left, polar_add_left, hp0N v₀ hv₀ y hy, hpLN a ha y hy, zero_add, zero_add]
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hθ : polar Q (g σ) t ≠ 0 := by
    rw [hgσ, hpolN σ₀ a₁ b₁ t hσ₀ ha₁ htN, polar_comm]
    exact htσ
  have hcomm := eichler_conj_pivot (Q := Q) (σ := g σ) (w := g w) (s := s) (t := t)
    (by rw [hQg, hQσ]) (by rw [hQg, hQw]) hsQ (by rw [hOg, hσw])
    (by rw [hgσ, hpolN σ₀ a₁ b₁ s hσ₀ ha₁ hsN, polar_comm, hs1])
    (by rw [hgw, hpolN w₀ a₂ b₂ s hw₀ ha₂ hsN, polar_comm, hs2]) hs3
    (by rw [hgw, hpolN w₀ a₂ b₂ t hw₀ ha₂ htN, polar_comm, htw])
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
    rw [polar_smul_right_eq, hgw, hpolN w₀ a₂ b₂ s hw₀ ha₂ hsN, polar_comm, hs2, mul_zero]
  have hdec : -(g w) = -(w₀ + b₂) + -a₂ := by
    rw [hgw]
    abel
  have hv1 : polar Q (θ • s) (-(w₀ + b₂)) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_add_right, polar_comm Q s w₀,
      hp0N w₀ hw₀ s hsN, hs2]
    ring
  have hv2 : polar Q (θ • s) (-a₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hpLN _ ha₂ s hsN]
    ring
  have hmulE : eichler Q (θ • s) (-(w₀ + b₂)) * eichler Q (θ • s) (-a₂) =
      eichler Q (θ • s) (-(g w)) := by
    rw [eichler_mul hv1 hv2, ← hdec]
  have hθsN : θ • s ∈ planeFixSpace E ⊔ lineSpace N :=
    Submodule.mem_sup_right ((lineSpace N).smul_mem _ hsN)
  have hE1 : eichler Q (θ • s) (-(w₀ + b₂)) ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 hθsN
      (Submodule.neg_mem _ (Submodule.add_mem_sup hw₀ hb₂))
  have hE2 : eichler Q (θ • s) (-(g w)) ∈ orthCentralizerSpan Q E := by
    rw [← eichler_swap hQw' hQs' hpol]
    exact hW
  have hE3 : eichler Q (θ • s) (-a₂) ∈ orthCentralizerSpan Q E := by
    have : eichler Q (θ • s) (-a₂) =
        (eichler Q (θ • s) (-(w₀ + b₂)))⁻¹ * eichler Q (θ • s) (-(g w)) := by
      rw [← hmulE]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2
  refine ⟨θ • s, (lineSpace N).smul_mem _ hsN, smul_ne_zero hθ hs0, hQs', -a₂,
    (lineSpace L).neg_mem ha₂, neg_ne_zero.mpr ha₂0, ?_, hE3⟩
  rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hpLN _ ha₂ s hsN]
  ring

theorem exists_pivot_of_mixing_any (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q)
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
  have hU₀reg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace L) :=
    polarNondegOn_of_nondegenerate (regular_sup hK hL)
  have hVNreg : PolarNondegOn Q (lineSpace N) :=
    polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
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
  have hbσN : ιB (β z₁) ∈ lineSpace N := hιBN _
  have hbwN : ιB (β z₂) ∈ lineSpace N := hιBN _
  have hbind : ∀ c : K, ιB (β z₁) ≠ c • ιB (β z₂) := by
    intro c hc
    apply hind c
    apply hβ
    apply hιB
    rw [map_smul, map_smul]
    exact hc
  obtain ⟨t, htN, htw, htσ⟩ := exists_perp_not_perp hVNreg hbσN hbwN hbind
  let F : Fin 3 → V →ₗ[K] K := ![(polarBilin Q).flip (ιB (β z₁)), (polarBilin Q).flip (ιB (β z₂)),
    (polarBilin Q).flip t]
  obtain ⟨s, hsN, hs0, hsQ, hsF⟩ := exists_singular_in_kernel_any (Q := Q) h6 F
  have hs1 : polar Q s (ιB (β z₁)) = 0 := by simpa [F, polarBilin_apply_apply] using hsF 0
  have hs2 : polar Q s (ιB (β z₂)) = 0 := by simpa [F, polarBilin_apply_apply] using hsF 1
  have hs3 : polar Q s t = 0 := by simpa [F, polarBilin_apply_apply] using hsF 2
  exact exists_pivot_of_data hK hp hEΩ hL hN hLN hgH hgO hσU hwU hQσ hQw h12 hσ₀ hw₀ (hιAL _)
    (hιAL _) hbwN (by rw [hσdec, map_add, hg0 σ₀ hσ₀, hgact])
    (by rw [hwdec, map_add, hg0 w₀ hw₀, hgact])
    ((map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr hz₂0)) hsN htN hs0 hsQ hs1 hs2 hs3
    htw htσ

end Pivot

end CFSG.LieType.SeitzGeneration.OrthBlk
