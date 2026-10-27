module

public import CFSG.LieType.SeitzGeneration.OrthGenLinear
public import CFSG.LieType.SeitzGeneration.OrthSdBig

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section Pivot

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem exists_pivot_of_data_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {g : V ≃ₗ[K] V} (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s t : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (htP : t ∈ planeFixSpace E ⊔ lineSpace N)
    (hs0 : s ≠ 0) (hsQ : Q s = 0) (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0)
    (hs3 : polar Q s t = 0) (htw : polar Q t p₂ = 0) (htσ : polar Q t p₁ ≠ 0) :
    ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  classical
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hLP : ∀ a ∈ lineSpace L, ∀ y ∈ planeFixSpace E ⊔ lineSpace N, polar Q a y = 0 :=
    fun a ha y hy => polar_eq_zero_of_mem_sup hK hN hL hLN ha hy
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hθ : polar Q (g σ) t ≠ 0 := by
    rw [hgσ, polar_add_left, hLP a₁ ha₁ t htP, zero_add, polar_comm]
    exact htσ
  have hcomm := eichler_conj_pivot (Q := Q) (σ := g σ) (w := g w) (s := s) (t := t)
    (by rw [hQg, hQσ]) (by rw [hQg, hQw]) hsQ (by rw [hOg, hσw])
    (by rw [hgσ, polar_add_left, hLP a₁ ha₁ s hsP, zero_add, polar_comm, hs1])
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2]) hs3
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ t htP, zero_add, polar_comm, htw])
  have hY : eichler Q s t ∈ orthCentralizerSpan Q E := eichler_mem_span_of_mem_sup hEΩ hN0 hsP htP
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
    rw [polar_smul_right_eq, hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2,
      mul_zero]
  have hdec : -(g w) = -p₂ + -a₂ := by
    rw [hgw]
    abel
  have hv1 : polar Q (θ • s) (-p₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, hs2]
    ring
  have hv2 : polar Q (θ • s) (-a₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
    ring
  have hmulE : eichler Q (θ • s) (-p₂) * eichler Q (θ • s) (-a₂) =
      eichler Q (θ • s) (-(g w)) := by
    rw [eichler_mul hv1 hv2, ← hdec]
  have hθsP : θ • s ∈ planeFixSpace E ⊔ lineSpace N := Submodule.smul_mem _ _ hsP
  have hE1 : eichler Q (θ • s) (-p₂) ∈ orthCentralizerSpan Q E :=
    eichler_mem_span_of_mem_sup hEΩ hN0 hθsP (Submodule.neg_mem _ hp₂)
  have hE2 : eichler Q (θ • s) (-(g w)) ∈ orthCentralizerSpan Q E := by
    rw [← eichler_swap hQw' hQs' hpol]
    exact hW
  have hE3 : eichler Q (θ • s) (-a₂) ∈ orthCentralizerSpan Q E := by
    have : eichler Q (θ • s) (-a₂) =
        (eichler Q (θ • s) (-p₂))⁻¹ * eichler Q (θ • s) (-(g w)) := by
      rw [← hmulE]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2
  refine ⟨θ • s, hθsP, smul_ne_zero hθ hs0, hQs', -a₂, (lineSpace L).neg_mem ha₂,
    neg_ne_zero.mpr ha₂0, ?_, hE3⟩
  rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
  ring

theorem exists_pivot_center_lineSpace (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    (hpiv : ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L,
      b ≠ 0 ∧ b ∈ rootSet Q (orthCentralizerSpan Q E) s₀) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  obtain ⟨s₀, hs₀P, hs₀0, hs₀Q, b, hbL, hb0, hbR⟩ := hpiv
  obtain ⟨s₁, hs₁N, hs₁0, hs₁Q⟩ := exists_singular_of_three_le_any (Q := Q) h3N
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN) hPN hs₀P
    (Submodule.mem_sup_right hs₁N) hs₀0 hs₁0 (by rw [hs₀Q, hs₁Q])
  have hgH : g ∈ orthCentralizerSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => eichler_mem_span_of_mem_sup hEΩ hN0 he hw) hg
  have hgb : g b = b := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hL hLN hbL hu)
  have := rootSet_map (orthCentralizerSpan_le_orthogonalGroup E) hgH hbR
  rw [hgb, hgs] at this
  exact ⟨s₁, hs₁N, hs₁0, hs₁Q, b, hbL, hb0, this⟩

theorem exists_pivot_of_triple (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    {g : V ≃ₗ[K] V} (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₁ : p₁ ∈ planeFixSpace E ⊔ lineSpace N)
    (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0) (hind : ∀ c₁ c₂ : K, p₁ ≠ c₁ • s + c₂ • p₂) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    polarNondegOn_of_nondegenerate (regular_sup hK hN)
  obtain ⟨t, htP, hts, htw, htσ⟩ := exists_perp_not_perp_two hPreg hp₁ hsP hp₂ hind
  exact exists_pivot_center_lineSpace hK hEΩ hp hL hN hLN hPN h3N
    (exists_pivot_of_data_gen hK hp hEΩ hL hN hLN hgH hgO hσU hwU hQσ hQw hσw ha₁ ha₂ hp₂ hgσ
      hgw ha₂0 hsP htP hs0 hsQ hs1 hs2 (by rw [polar_comm]; exact hts) htw htσ)

theorem exists_pivot_of_mixing_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthCentralizerSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg0 : ∀ v ∈ planeFixSpace E, g v = v)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (h5L : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace L))
    (h5N : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N)) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthCentralizerSpan Q E) s₀ := by
  classical
  have hU₀reg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace L) :=
    polarNondegOn_of_nondegenerate (regular_sup hK hL)
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    polarNondegOn_of_nondegenerate (regular_sup hK hN)
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) := hasOrthPairs_of_dim hPreg h5N
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  have hdisj : Disjoint (planeFixSpace E) (lineSpace N) := disjoint_planeFixSpace_lineSpace hK hN
  obtain ⟨σ, f₁, w, f₂, hσU, hf₁U, hwU, hf₂U, hQσ, hQf₁, hQw, hQf₂, h11, h22, h12, h1f2, hf1w,
    hf1f2⟩ := hasOrthPairs_of_dim hU₀reg h5L
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
  obtain ⟨p₁, hp₁def⟩ : ∃ p₁ : V, p₁ = σ₀ + ιB (β z₁) := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ p₂ : V, p₂ = w₀ + ιB (β z₂) := ⟨_, rfl⟩
  have hp₁P : p₁ ∈ planeFixSpace E ⊔ lineSpace N := hp₁def ▸ Submodule.add_mem_sup hσ₀ (hιBN _)
  have hp₂P : p₂ ∈ planeFixSpace E ⊔ lineSpace N := hp₂def ▸ Submodule.add_mem_sup hw₀ (hιBN _)
  have hgσ : g σ = ιA (α z₁) + p₁ := by
    rw [hσdec, map_add, hg0 σ₀ hσ₀, hgact, hp₁def]
    abel
  have hgw : g w = ιA (α z₂) + p₂ := by
    rw [hwdec, map_add, hg0 w₀ hw₀, hgact, hp₂def]
    abel
  have hli : ∀ c₁ c₂ : K, c₁ • p₁ + c₂ • p₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ h0
    have h1 : (c₁ • σ₀ + c₂ • w₀) + ιB (β (c₁ • z₁ + c₂ • z₂)) = 0 := by
      rw [← h0, hp₁def, hp₂def]
      simp only [map_add, map_smul]
      module
    have hmem0 : c₁ • σ₀ + c₂ • w₀ ∈ planeFixSpace E :=
      (planeFixSpace E).add_mem ((planeFixSpace E).smul_mem _ hσ₀)
        ((planeFixSpace E).smul_mem _ hw₀)
    have h2 : c₁ • σ₀ + c₂ • w₀ = 0 :=
      Submodule.disjoint_def.mp hdisj _ hmem0 (by
        rw [eq_neg_of_add_eq_zero_left h1]
        exact (lineSpace N).neg_mem (hιBN _))
    have h3 : c₁ • z₁ + c₂ • z₂ = 0 := by
      rw [h2, zero_add] at h1
      have h4 : β (c₁ • z₁ + c₂ • z₂) = 0 := hιB (by rw [h1, map_zero])
      exact hβ (by rw [h4, map_zero])
    have hc₁ : c₁ = 0 := by
      by_contra hc
      refine hind (-(c₁⁻¹ * c₂)) ?_
      have h5 : c₁ • z₁ = -(c₂ • z₂) := eq_neg_of_add_eq_zero_left h3
      calc z₁ = c₁⁻¹ • (c₁ • z₁) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = (-(c₁⁻¹ * c₂)) • z₂ := by rw [h5, smul_neg, smul_smul, neg_smul]
    refine ⟨hc₁, ?_⟩
    rw [hc₁, zero_smul, zero_add] at h3
    exact (smul_eq_zero.mp h3).resolve_right hz₂0
  obtain ⟨s, hsP, hs0, hsQ, hsF⟩ := exists_singular_in_kernel_fin (Q := Q) (n := 2) (by omega)
    ![(polarBilin Q).flip p₁, (polarBilin Q).flip p₂]
  have hs1 : polar Q s p₁ = 0 := by simpa [polarBilin_apply_apply] using hsF 0
  have hs2 : polar Q s p₂ = 0 := by simpa [polarBilin_apply_apply] using hsF 1
  have hss : polar Q s s = 0 := polar_self_eq_zero hsQ
  have ha₂0 : ιA (α z₂) ≠ 0 := (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr hz₂0)
  by_cases hcase : ∃ c₁ c₂ : K, p₁ = c₁ • s + c₂ • p₂
  · obtain ⟨c₁, c₂, hc⟩ := hcase
    have hc₁ : c₁ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hli 1 (-c₂) (by rw [hc]; module)).1
    have hŝU : c₁⁻¹ • (σ - c₂ • w) ∈ planeFixSpace E ⊔ lineSpace L :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hσU (Submodule.smul_mem _ _ hwU))
    have hQŝ : Q (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [map_smul_eq_sq, map_sub_smul', hQσ, hQw, h12]
      ring
    have hσŝ : polar Q σ (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQσ, h12]
      ring
    have hwŝ : polar Q w (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQw,
        polar_comm Q w σ, h12]
      ring
    have hgŝ : g (c₁⁻¹ • (σ - c₂ • w)) =
        ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) + s := by
      have h1 : p₁ - c₂ • p₂ = c₁ • s := by rw [hc]; module
      have h2 : s = c₁⁻¹ • (p₁ - c₂ • p₂) := by rw [h1, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
      rw [map_smul, map_sub, map_smul, hgσ, hgw, h2]
      simp only [map_smul, map_sub]
      module
    have hâ0 : ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) ≠ 0 := by
      refine (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr ?_)
      exact smul_ne_zero (inv_ne_zero hc₁) (sub_ne_zero.mpr (hind c₂))
    by_cases hc₂ : c₂ = 0
    ·
      refine exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := w)
        (w := c₁⁻¹ • (σ - c₂ • w)) hwU hŝU hQw hQŝ hwŝ (hιAL _) (hιAL _) hp₂P hsP hgw hgŝ hâ0
        hsP hs0 hsQ hs2 hss ?_
      intro d₁ d₂ hd
      have h1 : p₂ = (d₁ + d₂) • s := by rw [hd]; module
      have h2 : p₁ = c₁ • s := by rw [hc, hc₂]; module
      have := hli (-(d₁ + d₂)) c₁ (by rw [h2, h1]; module)
      exact hc₁ this.2
    · refine exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := σ)
        (w := c₁⁻¹ • (σ - c₂ • w)) hσU hŝU hQσ hQŝ hσŝ (hιAL _) (hιAL _) hp₁P hsP hgσ hgŝ hâ0
        hsP hs0 hsQ hs1 hss ?_
      intro d₁ d₂ hd
      have hcp : c₂ • p₂ = (d₁ + d₂ - c₁) • s := by
        have : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [this] at hc
        rw [sub_smul, hc]
        module
      have := hli (d₁ + d₂ - c₁) (-((d₁ + d₂) * c₂)) (by
        have hd' : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [hd']
        have : ((d₁ + d₂) * c₂) • p₂ = (d₁ + d₂) • (c₂ • p₂) := by rw [mul_smul]
        rw [neg_smul, this, hcp]
        module)
      obtain ⟨h5, h6⟩ := this
      have h7 : d₁ + d₂ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h6)).resolve_right hc₂
      exact hc₁ (by linear_combination h7 - h5)
  · push Not at hcase
    exact exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO hσU hwU hQσ hQw h12
      (hιAL _) (hιAL _) hp₁P hp₂P hgσ hgw ha₂0 hsP hs0 hsQ hs1 hs2 hcase

end Pivot

end CFSG.LieType.SeitzGeneration.OrthBlk
