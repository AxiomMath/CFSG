module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2210
public import CFSG.ClassicalInvolution.SmallCases.A7T22Sig
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem adj_of_twins' (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) {J J' : Subgroup G} (hJ : J ∈ twinSet Ω K)
    (hJ' : J' ∈ twinSet Ω K) (hne : J' ≠ J) : J' ∈ omegaNbr Ω J := by
  have h1 : KPerp Ω J = KPerp Ω K := A7T22.kPerp_eq_of_twin hd.hyp hd.mem hJ
  have h2 : twinSet Ω J = twinSet Ω K := twinSet_eq_of_mem_twinSet hd.hz hJ
  have h3 : J' ∈ KPerp Ω J := by rw [h1, hperp]; exact hJ'
  rcases h3 with rfl | h3
  · exact absurd rfl hne
  · exact h3

theorem exists_reps_of_family' (hΩ : HypOmegaGen Ω) {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (S : Finset (Subgroup G)) (hKS : K ∈ S)
    (hS : ∀ M ∈ S, M ∈ twinSet Ω K) :
    ∃ W ∈ WSet Ω, ∃ ρ : Subgroup G → Rep Ω W, ∀ M ∈ S, (ρ M).K = M := by
  classical
  obtain ⟨R, hRs, -, hRP⟩ := Q3T8.Asc77.T7V.exists_sylow_family hΩ hz S hS
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hRP
  have hex : ∀ M ∈ S, ∃ ρ : Rep Ω W, ρ.K = M := fun M hM => by
    obtain ⟨ρ, hρK, -⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW (hS M hM).1 (hRs M hM)
      (hWD (R M) (mem_RSet_of_isSylow2In (hS M hM).1 (hRs M hM))
        (le_iSup₂_of_le M hM le_rfl))
    exact ⟨ρ, hρK⟩
  have : Nonempty (Rep Ω W) := ⟨(hex K hKS).choose⟩
  choose! ρ hρ using hex
  exact ⟨W, hW, ρ, hρ⟩

theorem not_dbarConnected_of_wyl' (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (ρ₀ : Rep Ω W) (hρ₀ : ρ₀.K = K)
    (hμ : MuIsoWylD4 Ω W) : ¬ DbarConnected Ω W := by
  intro hconn
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hover : ∀ ρ : Rep Ω W, ρ.K ∈ twinSet Ω K := by
    intro ρ
    have := c.mem_dComp_of_connected hconn hd.mem ρ.hK ρ₀.hR ρ.hR (hρ₀ ▸ ρ₀.hRK) ρ.hRK
    exact A7T22.dComp_subset_twinSet hd.hyp hd.mem hd.hz hperp this
  have hcomm : ∀ x ∈ muDelta Ω W, ∀ y ∈ muDelta Ω W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hx
    obtain ⟨σ, hσ⟩ := exists_rep_of_mem_muDelta hy
    apply Subtype.ext
    show (x : NQuot (W ⊔ OCW W)) * y = y * x
    rw [← hρ, ← hσ]
    by_cases hK : σ.K = ρ.K
    · rw [c.img_eq_of_K_eq σ ρ hK]
    · exact c.comm_of_omega ρ σ (adj_of_twins' hd hperp (hover ρ) (hover σ) hK)
  have hcenter : ∀ y ∈ muDelta Ω W, ∀ x : ↥(muGroup Ω W), x * y = y * x := by
    intro y hy x
    have hx : x ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha]
        _ = y * a⁻¹ := by group
  have habel : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    have hy : y ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hcenter y hy x
    | one => simp
    | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
    | inv a _ ha =>
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
        _ = a⁻¹ * x := by group
  obtain ⟨e⟩ := hμ
  apply s26_coxeterD4_not_comm
  intro u v
  have h1 := habel (e.symm u) (e.symm v)
  calc u * v = e (e.symm u * e.symm v) := by simp
    _ = e (e.symm v * e.symm u) := by rw [h1]
    _ = v * u := by simp

theorem exists_fourth_twin' (hP : Q3CL.PartIHypG Ω)
    (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) (hperp : KPerp Ω K = twinSet Ω K)
    (hnc : ∀ W ∈ WSet Ω, (∃ ρ : Rep Ω W, ρ.K = K) → ¬ DbarConnected Ω W) :
    ∃ K₄ ∈ twinSet Ω K, K₄ ≠ K ∧ K₄ ≠ K' ∧ K₄ ≠ K₃ := by
  classical
  have hK : K ∈ twinSet Ω K := mem_twinSet_self hd.mem hd.hz
  obtain ⟨W, hW, ρ, hρ⟩ := exists_reps_of_family' hd.hyp hd.hz ({K, K', K₃} : Finset (Subgroup G))
    (by simp) (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl | rfl
      · exact hK
      · exact hd.hK'
      · exact hd.hK₃)
  have hρ₁ : (ρ K).K = K := hρ K (by simp)
  have hρ₂ : (ρ K').K = K' := hρ K' (by simp)
  have hρ₃ : (ρ K₃).K = K₃ := hρ K₃ (by simp)
  have hnc' : ¬ DbarConnected Ω W := hnc W hW ⟨ρ K, hρ₁⟩
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨ρ₄, h41, h42, h43, h4a, -, -, -⟩ := c.exists_fourth hP.cls hnc' (ρ K) (ρ K') (ρ K₃)
    (by rw [hρ₁, hρ₂]; exact adj_of_twins' hd hperp hK hd.hK' hd.hne)
    (by rw [hρ₁, hρ₃]; exact adj_of_twins' hd hperp hK hd.hK₃ hd.hK₃K)
    (by rw [hρ₂, hρ₃]; exact adj_of_twins' hd hperp hd.hK' hd.hK₃ hd.hK₃K')
    (by rw [hρ₁]; exact hd.hz) (by rw [hρ₂]; exact hd.hzK') (by rw [hρ₃]; exact hd.hzK₃)
  rw [hρ₁] at h41 h4a
  rw [hρ₂] at h42
  rw [hρ₃] at h43
  have hmem : ρ₄.K ∈ twinSet Ω K := by
    rw [← hperp]
    exact Or.inr h4a
  exact ⟨ρ₄.K, hmem, h41, h42, h43⟩

theorem exists_sylow_quad' (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃) {K₄ : Subgroup G}
    (hK₄ : K₄ ∈ twinSet Ω K) (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃) :
    ∃ R₁ R₂ R₃ R₄ : Subgroup G, IsSylow2In R₁ K ∧ IsSylow2In R₂ K' ∧ IsSylow2In R₃ K₃ ∧
      IsSylow2In R₄ K₄ ∧ u₁ ∈ R₁ ∧ u₂ ∈ R₂ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧
      Commutes R₂ R₃ ∧ Commutes R₁ R₄ ∧ Commutes R₂ R₄ ∧ Commutes R₃ R₄ := by
  obtain ⟨R₁, R₂, R₃, h1, h2, h3, hu₁, hu₂, -, c12, c13, c23⟩ := hd.exists_sylow_triple
  have hΩ := hd.hyp
  have hz := hd.hz
  have hz' := hd.hzK'
  have hz₃ := hd.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  have nK : K ≤ Subgroup.normalizer (K₄ : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hd.mem hK₄.1 h41.symm hz hz₄
  have nK' : K' ≤ Subgroup.normalizer (K₄ : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hd.hK'.1 hK₄.1 h42.symm hz' hz₄
  have nK₃ : K₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hd.hK₃.1 hK₄.1 h43.symm hz₃ hz₄
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPN : (R₁ ⊔ R₂) ⊔ R₃ ≤ Subgroup.normalizer (K₄ : Set G) :=
    sup_le (sup_le (h1.1.trans nK) (h2.1.trans nK')) (h3.1.trans nK₃)
  obtain ⟨R₄, h4, hQ⟩ := exists_isPGroup_sup_sylow hP hPN
  have hR₁Q : R₁ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hR₂Q : R₂ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hR₃Q : R₃ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right.trans le_sup_left
  have hR₄Q : R₄ ≤ ((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄ := le_sup_right
  refine ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, ?_, ?_, ?_⟩
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.mem hK₄.1 h41.symm hz hz₄ h1.1 h4.1
      (hQ.to_le (sup_le hR₁Q hR₄Q))
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.hK'.1 hK₄.1 h42.symm hz' hz₄ h2.1 h4.1
      (hQ.to_le (sup_le hR₂Q hR₄Q))
  · exact Sec6Gen.commutes_of_twin_of_isPGroup hΩ hd.hK₃.1 hK₄.1 h43.symm hz₃ hz₄ h3.1 h4.1
      (hQ.to_le (sup_le hR₃Q hR₄Q))

end Fam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
