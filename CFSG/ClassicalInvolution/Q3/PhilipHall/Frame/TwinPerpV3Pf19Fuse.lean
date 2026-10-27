module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf2Fourth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open scoped commutatorElement

section Fuse

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exists_fuse_cent2 (hP : Q3CL.PartIHypG Ω) (hd : A7T22.Hyp22G Ω K K' K₃ z u₁ u₂ u₃)
    (hperp : KPerp Ω K = twinSet Ω K) {K₄ : Subgroup G} (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a₁ a₂ a₃ a₄ y : G, a₁ ∈ K ∧ orderOf a₁ = 4 ∧ a₂ ∈ K' ∧ orderOf a₂ = 4 ∧
      a₃ ∈ K₃ ∧ orderOf a₃ = 4 ∧ a₄ ∈ K₄ ∧ orderOf a₄ = 4 ∧
      a₁ * a₂ = a₂ * a₁ ∧ a₁ * a₃ = a₃ * a₁ ∧ a₁ * a₄ = a₄ * a₁ ∧ a₂ * a₃ = a₃ * a₂ ∧
      a₂ * a₄ = a₄ * a₂ ∧ a₃ * a₄ = a₄ * a₃ ∧ y * z * y⁻¹ = a₁ * a₂ * a₃ * a₄ ∧
      y * z * y⁻¹ ≠ z ∧ y ∈ Subgroup.centralizer ({a₁ * a₂} : Set G) ∧
      ∃ j : G, j * a₁ * j⁻¹ = a₁⁻¹ ∧ j * a₂ * j⁻¹ = a₂ ∧ j * a₃ * j⁻¹ = a₃ ∧ j * a₄ * j⁻¹ = a₄ := by
  classical
  have hΩ := hd.hyp
  have hK := hd.mem
  have hK' : K' ∈ Ω := hd.hK'.1
  have hK₃ : K₃ ∈ Ω := hd.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hd.hz
  have hz' : IsUniqueInvolution K' z := hd.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hd.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    exists_sylow_quad' hd hK₄ h41 h42 h43
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hPP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := Q3T8.Asc77.exists_W_of_isPGroup hΩ hPP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := Q3T8.Asc77.T7D.exists_rep hΩ hW hK₄Ω h4 hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hd.hK'
    · exact hd.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hd.hne.symm
  have hKK₃ : K ≠ K₃ := hd.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hd.hK₃K'.symm
  have hK'K₄ : K' ≠ K₄ := h42.symm
  have hK₃K₄ : K₃ ≠ K₄ := h43.symm
  have hneK : ∀ i j : Fin 4, i ≠ j → ![K, K', K₃, K₄] i ≠ ![K, K', K₃, K₄] j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hKK', hKK'.symm, hKK₃, hKK₃.symm, hKK₄, hKK₄.symm,
      hK'K₃, hK'K₃.symm, hK'K₄, hK'K₄.symm, hK₃K₄, hK₃K₄.symm] at hij ⊢
  have hneρ : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact hneK i j hij
  have hnbrρ : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j hij
    rw [hρK i, hρK j]
    exact adj_of_twins' hd hperp (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    not_dbarConnected_of_wyl' hP hd hperp hW ρ₀ hρ₀K (hμ W hW)
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hRσ⟩ := c.fuse_frame hP.cls hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (Q3CL.Thompson.inf_W_of_mem_D hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid hP.cls (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (Q3T8.Asc77.T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have hj : ∃ j : G, j * g 0 * j⁻¹ = (g 0)⁻¹ ∧ j * g 1 * j⁻¹ = g 1 ∧ j * g 2 * j⁻¹ = g 2 ∧
      j * g 3 * j⁻¹ = g 3 := by
    refine ⟨(ρ 0).r, c.conj_inv (ρ 0) (hg 0).1, ?_, ?_, ?_⟩
    · rw [c.centralizes (ρ 0) (ρ 1) (hnbrρ 0 1 (by decide)) (hg 1).1, mul_inv_cancel_right]
    · rw [c.centralizes (ρ 0) (ρ 2) (hnbrρ 0 2 (by decide)) (hg 2).1, mul_inv_cancel_right]
    · rw [c.centralizes (ρ 0) (ρ 3) (hnbrρ 0 3 (by decide)) (hg 3).1, mul_inv_cancel_right]
  refine ⟨g 0, g 1, g 2, g 3, y, by simpa [hρ0K] using (hg 0).1.1, (hg 0).2,
    by simpa [hρ1K] using (hg 1).1.1, (hg 1).2, by simpa [hρ2K] using (hg 2).1.1, (hg 2).2,
    by simpa [hρ3K] using (hg 3).1.1, (hg 3).2, hcomm _ (hgW 0) _ (hgW 1),
    hcomm _ (hgW 0) _ (hgW 2), hcomm _ (hgW 0) _ (hgW 3), hcomm _ (hgW 1) _ (hgW 2),
    hcomm _ (hgW 1) _ (hgW 3), hcomm _ (hgW 2) _ (hgW 3), hyz.trans hrel, ?_, ?_, hj⟩
  swap
  ·
    have hr₂ : (ρ 2).r ∈ R₃ := hρ₂R ▸ (ρ 2).hr
    have hg0 : g 0 ∈ R₁ := hρ₀R ▸ hgR 0
    have hg1 : g 1 ∈ R₂ := hρ₁R ▸ hgR 1
    have hr2c : (ρ 2).r ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e0 : g 0 * (ρ 2).r = (ρ 2).r * g 0 := c13 _ hg0 _ hr₂
      have e1 : g 1 * (ρ 2).r = (ρ 2).r * g 1 := c23 _ hg1 _ hr₂
      calc (ρ 2).r * (g 0 * g 1) = ((ρ 2).r * g 0) * g 1 := by group
        _ = (g 0 * (ρ 2).r) * g 1 := by rw [e0]
        _ = g 0 * ((ρ 2).r * g 1) := by group
        _ = g 0 * (g 1 * (ρ 2).r) := by rw [e1]
        _ = (g 0 * g 1) * (ρ 2).r := by group
    have hσc : σ.r ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := hRσ σ.hr
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr2c hσc) (Subgroup.inv_mem _ hr2c)
  rw [hyz]
  intro h'
  have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
  have hperp' : σ.K ∈ KPerp Ω K := by rw [hperp]; exact hσK
  rcases hperp' with h'' | h''
  · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
  · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm

end Fuse

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
