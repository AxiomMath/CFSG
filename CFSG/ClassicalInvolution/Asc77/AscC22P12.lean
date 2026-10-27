module

public import CFSG.ClassicalInvolution.Asc77.AscC22P11
public import CFSG.ClassicalInvolution.Asc77.AscC22P1

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace C22P

set_option linter.unusedSectionVars false

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}


theorem fuseFrame_alpha (h : Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃) (hK₄ : K₄ ∈ twinSet Ω K)
    (h41 : K₄ ≠ K) (h42 : K₄ ≠ K') (h43 : K₄ ≠ K₃)
    (hμ : ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) :
    ∃ a a' : G, a ∈ K ∧ a' ∈ K' ∧ orderOf a = 4 ∧ orderOf a' = 4 ∧ a * a' = a' * a ∧
      ∃ (R R' : Subgroup G) (b b' y : G), IsSylow2In R K₃ ∧ IsSylow2In R' K₄ ∧ Commutes R R' ∧
        R ≤ Subgroup.centralizer ({a * a'} : Set G) ∧
        R' ≤ Subgroup.centralizer ({a * a'} : Set G) ∧ b ∈ R ∧ b' ∈ R' ∧ orderOf b = 4 ∧
        orderOf b' = 4 ∧ b * b = z ∧ b' * b' = z ∧ y ∈ rLayer Ω (a * a') ∧
        y * z * y⁻¹ = b * b' * (a * a') ∧ b * b' * (a * a') ≠ z ∧
        z * (b * b' * (a * a')) = (b * b' * (a * a')) * z ∧
        y ∈ Subgroup.normalizer
          (alphaOf (Subgroup.closure ({a * a', z} : Set G)) : Set G) := by
  classical
  have hs := h
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃ : K₃ ∈ Ω := hs.hK₃.1
  have hK₄Ω : K₄ ∈ Ω := hK₄.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := hs.hzK'
  have hz₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  have hz₄ : IsUniqueInvolution K₄ z := isUniqueInvolution_of_mem_twinSet hz hK₄
  obtain ⟨R₁, R₂, R₃, R₄, h1, h2, h3, h4, hu₁, hu₂, c12, c13, c23, c14, c24, c34⟩ :=
    exists_sylow_quad_S h hK₄ h41 h42 h43
  have hP12 : IsPGroup 2 ↥(R₁ ⊔ R₂) :=
    h1.2.1.to_sup_of_normal_right' h2.2.1 (T7A.le_normalizer_of_commutes c12.symm)
  have hP123 : IsPGroup 2 ↥((R₁ ⊔ R₂) ⊔ R₃) :=
    hP12.to_sup_of_normal_right' h3.2.1 (sup_le (T7A.le_normalizer_of_commutes c13.symm)
      (T7A.le_normalizer_of_commutes c23.symm))
  have hP : IsPGroup 2 ↥(((R₁ ⊔ R₂) ⊔ R₃) ⊔ R₄) :=
    hP123.to_sup_of_normal_right' h4.2.1 (sup_le (sup_le
      (T7A.le_normalizer_of_commutes c14.symm) (T7A.le_normalizer_of_commutes c24.symm))
      (T7A.le_normalizer_of_commutes c34.symm))
  obtain ⟨W, hW, hWD⟩ := exists_W_of_isPGroup hp hq hΩ hP
  have hD₁ : R₁ ∈ DSet Ω W := hWD R₁ (mem_RSet_of_isSylow2In hK h1)
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hD₂ : R₂ ∈ DSet Ω W := hWD R₂ (mem_RSet_of_isSylow2In hK' h2)
    (le_sup_right.trans (le_sup_left.trans le_sup_left))
  have hD₃ : R₃ ∈ DSet Ω W := hWD R₃ (mem_RSet_of_isSylow2In hK₃ h3)
    (le_sup_right.trans le_sup_left)
  have hD₄ : R₄ ∈ DSet Ω W := hWD R₄ (mem_RSet_of_isSylow2In hK₄Ω h4) le_sup_right
  obtain ⟨ρ₀, hρ₀K, hρ₀R⟩ := T7D.exists_rep hp hq hΩ hW hK h1 hD₁
  obtain ⟨ρ₁, hρ₁K, hρ₁R⟩ := T7D.exists_rep hp hq hΩ hW hK' h2 hD₂
  obtain ⟨ρ₂, hρ₂K, hρ₂R⟩ := T7D.exists_rep hp hq hΩ hW hK₃ h3 hD₃
  obtain ⟨ρ₃, hρ₃K, hρ₃R⟩ := T7D.exists_rep hp hq hΩ hW hK₄Ω h4 hD₄
  let ρ : Fin 4 → Rep Ω W := ![ρ₀, ρ₁, ρ₂, ρ₃]
  have hρK : ∀ i, (ρ i).K = ![K, K', K₃, K₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀K, hρ₁K, hρ₂K, hρ₃K]
  have hρR : ∀ i, (ρ i).R = ![R₁, R₂, R₃, R₄] i := by
    intro i; fin_cases i <;> simp [ρ, hρ₀R, hρ₁R, hρ₂R, hρ₃R]
  have hTw : ∀ i, ![K, K', K₃, K₄] i ∈ twinSet Ω K := by
    intro i
    fin_cases i
    · exact mem_twinSet_self hK hz
    · exact hs.hK'
    · exact hs.hK₃
    · exact hK₄
  have hzρ : ∀ i, IsUniqueInvolution (ρ i).K z := by
    intro i
    rw [hρK i]
    fin_cases i
    · exact hz
    · exact hz'
    · exact hz₃
    · exact hz₄
  have hKK' : K ≠ K' := hs.hne.symm
  have hKK₃ : K ≠ K₃ := hs.hK₃K.symm
  have hKK₄ : K ≠ K₄ := h41.symm
  have hK'K₃ : K' ≠ K₃ := hs.hK₃K'.symm
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
    exact T7V.adj_of_twins hs (hTw i) (hTw j) (hneK j i (Ne.symm hij))
  have hnc : ¬ DbarConnected Ω W :=
    T7V.not_dbarConnected_of_wyl hs hW ρ₀ hρ₀K (hμ W hW)
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hs.stand hW
  obtain ⟨σ, t, g, ht, hfar, hg, hrel, hR⟩ := c.fuse_frame hnc ρ hzρ hneρ hnbrρ
  have hρ0K : (ρ 0).K = K := hρ₀K
  have hρ1K : (ρ 1).K = K' := hρ₁K
  have hρ2K : (ρ 2).K = K₃ := hρ₂K
  have hρ3K : (ρ 3).K = K₄ := hρ₃K
  have hρ0R : (ρ 0).R = R₁ := hρ₀R
  have hρ1R : (ρ 1).R = R₂ := hρ₁R
  have hρ2R : (ρ 2).R = R₃ := hρ₂R
  have hρ3R : (ρ 3).R = R₄ := hρ₃R
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hgR : ∀ i, g i ∈ (ρ i).R := by
    intro i
    have h1 := (inf_W_of_mem_D hp hq hΩ hW (ρ i).hR (ρ i).hK (ρ i).hRK).1
    have hmem : g i ∈ (ρ i).R ⊓ W := by rw [h1]; exact (hg i).1
    exact hmem.1
  have hgsq : ∀ i, g i * g i = z := fun i =>
    sq_eq_involution_of_orderOf_four (hzρ i) (hg i).1.1 (hg i).2
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution (ρ 0) (hzρ 0)
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution σ ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := fun x hx y hy => c.comm_W x hx y hy
  have hu0W : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hu2 : (g 0 * g 1) * (g 0 * g 1) = 1 := by
    calc (g 0 * g 1) * (g 0 * g 1) = (g 0 * g 0) * (g 1 * g 1) := by
          rw [mul_assoc, ← mul_assoc (g 1), ← hcomm _ (hgW 0) _ (hgW 1)]; group
      _ = 1 := by rw [hgsq 0, hgsq 1]; exact (hzρ 0).sq
  have hc2 : IsPGroup 2 (Subgroup.zpowers (g 0 * g 1)) := isPGroup_zpowers_of_sq_eq_one hu2
  have hg0R₁ : g 0 ∈ R₁ := by simpa [hρ0R] using hgR 0
  have hg1R₂ : g 1 ∈ R₂ := by simpa [hρ1R] using hgR 1
  have hR₃C : R₃ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c13 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c23 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hR₄C : R₄ ≤ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g 0 * g 1) = (x * g 0) * g 1 := by group
      _ = (g 0 * x) * g 1 := by rw [c14 (g 0) hg0R₁ x hx]
      _ = g 0 * (x * g 1) := by group
      _ = g 0 * (g 1 * x) := by rw [c24 (g 1) hg1R₂ x hx]
      _ = (g 0 * g 1) * x := by group
  have hcK₃ : g 0 * g 1 ∈ trivialOnQuot K₃ :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hK₃).mpr ⟨R₃, h3, hR₃C⟩
  have hcK₄ : g 0 * g 1 ∈ trivialOnQuot K₄ :=
    (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hc2 hK₄Ω).mpr ⟨R₄, h4, hR₄C⟩
  have hex₃ : IsSylow2In R₃ (exactCore (g 0 * g 1) K₃) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK₃ hcK₃).mpr ⟨h3, hR₃C⟩
  have hex₄ : IsSylow2In R₄ (exactCore (g 0 * g 1) K₄) :=
    (isSylow2In_exactCore_iff hΩ hc2 hK₄Ω hcK₄).mpr ⟨h4, hR₄C⟩
  have hg2R₃ : g 2 ∈ R₃ := by simpa [hρ2R] using hgR 2
  have hg3R₄ : g 3 ∈ R₄ := by simpa [hρ3R] using hgR 3
  obtain ⟨y, hy⟩ : ∃ y : G, y = (ρ 2).r * σ.r * (ρ 2).r⁻¹ := ⟨_, rfl⟩
  have hr₂R : (ρ 2).r ∈ R₃ := by simpa [hρ2R] using (ρ 2).hr
  have hyC : y ∈ Subgroup.centralizer ({g 0 * g 1} : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR₃C hr₂R) (hR σ.hr))
      (Subgroup.inv_mem _ (hR₃C hr₂R))
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ρ 2).r_mem_normalizer σ.r_mem_normalizer)
      (Subgroup.inv_mem _ (ρ 2).r_mem_normalizer)
  have hbr := c.conjRep_braid (ρ 2) σ (Ne.symm (hfar 2)) (hy ▸ hyN)
  have hKy : conjSub y K₃ = σ.K := by
    have h1 := c.K_eq_of_img_eq (T7D.conjRep c.hΩ (hy ▸ hyN) (ρ 2)) σ hbr
    rw [hy, ← hρ2K]
    exact h1
  have hyz : y * z * y⁻¹ = t := by
    have h1 : IsUniqueInvolution (conjSub y K₃) (y * z * y⁻¹) := hz₃.conj y
    rw [hKy] at h1
    exact h1.eq ht
  have htz : t ≠ z := by
    intro h'
    have hσK : σ.K ∈ twinSet Ω K := ⟨σ.hK, z, hz, h' ▸ ht⟩
    have hperp : σ.K ∈ KPerp Ω K := by rw [hs.perp]; exact hσK
    rcases hperp with h'' | h''
    · exact hfar 0 (by rw [c.img_eq_of_K_eq σ (ρ 0) (h''.trans hρ0K.symm)])
    · exact hfar 0 (c.comm_of_omega (ρ 0) σ (by rw [hρ0K]; exact h'')).symm
  have hperm : g 0 * g 1 * g 2 * g 3 = g 2 * g 3 * (g 0 * g 1) := by
    calc g 0 * g 1 * g 2 * g 3 = (g 0 * g 1) * (g 2 * g 3) := by group
      _ = (g 2 * g 3) * (g 0 * g 1) := hcomm _ hu0W _ (W.mul_mem (hgW 2) (hgW 3))
  have hRL₃ : R₃ ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le R₃ (mem_RSet_of_isSylow2In hK₃ h3) (le_iSup_of_le hR₃C le_rfl)
  have hRLσ : σ.R ≤ rLayer Ω (g 0 * g 1) :=
    le_iSup₂_of_le σ.R σ.hR.1 (le_iSup_of_le hR le_rfl)
  have hyL : y ∈ rLayer Ω (g 0 * g 1) := by
    rw [hy]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRL₃ hr₂R) (hRLσ σ.hr))
      (Subgroup.inv_mem _ (hRL₃ hr₂R))
  have hKne : ∀ i, σ.K ≠ (ρ i).K := fun i h =>
    hfar i (by rw [c.img_eq_of_K_eq σ (ρ i) h])
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz.sq
  have hcomm_sq : ∀ (e x : G), e ∈ W → x ∈ W → σ.r * x * σ.r⁻¹ = e * x →
      σ.r * (x * x) * σ.r⁻¹ = e * e * (x * x) := by
    intro e x heW hxW hex
    have hcx : e * x = x * e := hcomm _ heW _ hxW
    calc σ.r * (x * x) * σ.r⁻¹ = (σ.r * x * σ.r⁻¹) * (σ.r * x * σ.r⁻¹) := by group
      _ = (e * x) * (e * x) := by rw [hex]
      _ = e * (x * e) * x := by group
      _ = e * (e * x) * x := by rw [hcx]
      _ = e * e * (x * x) := by group
  obtain ⟨e₁, he₁def⟩ : ∃ e : G, e = σ.r * g 1 * σ.r⁻¹ * (g 1)⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂def⟩ : ∃ e : G, e = σ.r * g 2 * σ.r⁻¹ * (g 2)⁻¹ := ⟨_, rfl⟩
  have he₁ : e₁ ∈ σ.K ⊓ W := he₁def ▸ c.comm_mem σ (ρ 1) (hKne 1) (hg 1).1
  have he₂ : e₂ ∈ σ.K ⊓ W := he₂def ▸ c.comm_mem σ (ρ 2) (hKne 2) (hg 2).1
  have hs₁ : σ.r * g 1 * σ.r⁻¹ = e₁ * g 1 := by rw [he₁def]; group
  have hs₂ : σ.r * g 2 * σ.r⁻¹ = e₂ * g 2 := by rw [he₂def]; group
  have hsz₁ : σ.r * z * σ.r⁻¹ = e₁ * e₁ * z := by
    have := hcomm_sq e₁ (g 1) he₁.2 (hgW 1) hs₁
    rwa [hgsq 1] at this
  have hsz₂ : σ.r * z * σ.r⁻¹ = e₂ * e₂ * z := by
    have := hcomm_sq e₂ (g 2) he₂.2 (hgW 2) hs₂
    rwa [hgsq 2] at this
  have hee : e₁ * e₁ = e₂ * e₂ := mul_right_cancel (hsz₁.symm.trans hsz₂)
  have hcσ : e₁ * e₂⁻¹ ∈ σ.K := σ.K.mul_mem he₁.1 (σ.K.inv_mem he₂.1)
  have hcc : (e₁ * e₂⁻¹) * (e₁ * e₂⁻¹) = 1 := by
    have h12 : e₂⁻¹ * e₁ = e₁ * e₂⁻¹ := hcomm _ (W.inv_mem he₂.2) _ he₁.2
    calc (e₁ * e₂⁻¹) * (e₁ * e₂⁻¹) = e₁ * (e₂⁻¹ * e₁) * e₂⁻¹ := by group
      _ = e₁ * (e₁ * e₂⁻¹) * e₂⁻¹ := by rw [h12]
      _ = (e₁ * e₁) * (e₂⁻¹ * e₂⁻¹) := by group
      _ = (e₂ * e₂) * (e₂⁻¹ * e₂⁻¹) := by rw [hee]
      _ = 1 := by group
  have hc01 := ht.unique _ hcσ hcc
  have hr₂ : ∀ i : Fin 4, i ≠ 2 → (ρ 2).r * g i = g i * (ρ 2).r := fun i hi =>
    c.centralizes (ρ 2) (ρ i) (hnbrρ 2 i (Ne.symm hi)) (hg i).1
  have hr₂fix : ∀ i : Fin 4, i ≠ 2 → (ρ 2).r * g i * (ρ 2).r⁻¹ = g i := fun i hi => by
    rw [hr₂ i hi]; group
  have hr₂g2 : (ρ 2).r * g 2 * (ρ 2).r⁻¹ = (g 2)⁻¹ := c.conj_inv (ρ 2) (hg 2).1
  have hA1 : (ρ 2).r⁻¹ * g 1 * (ρ 2).r = g 1 := by
    have h1' := hr₂ 1 (by decide)
    calc (ρ 2).r⁻¹ * g 1 * (ρ 2).r = (ρ 2).r⁻¹ * (g 1 * (ρ 2).r) := by group
      _ = (ρ 2).r⁻¹ * ((ρ 2).r * g 1) := by rw [h1']
      _ = g 1 := by group
  have hB2 : (ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r = g 2 := by
    calc (ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r
        = (ρ 2).r⁻¹ * ((ρ 2).r * g 2 * (ρ 2).r⁻¹) * (ρ 2).r := by rw [hr₂g2]
      _ = g 2 := by group
  have hA2 : (ρ 2).r⁻¹ * g 2 * (ρ 2).r = (g 2)⁻¹ := by
    calc (ρ 2).r⁻¹ * g 2 * (ρ 2).r = ((ρ 2).r⁻¹ * (g 2)⁻¹ * (ρ 2).r)⁻¹ := by group
      _ = (g 2)⁻¹ := by rw [hB2]
  have hA : (ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r = g 1 * (g 2)⁻¹ := by
    calc (ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r
        = ((ρ 2).r⁻¹ * g 1 * (ρ 2).r) * ((ρ 2).r⁻¹ * g 2 * (ρ 2).r) := by group
      _ = g 1 * (g 2)⁻¹ := by rw [hA1, hA2]
  have hB' : σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹ = (e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹) := by
    have hx : (g 2)⁻¹ * e₂⁻¹ = e₂⁻¹ * (g 2)⁻¹ :=
      hcomm _ (W.inv_mem (hgW 2)) _ (W.inv_mem he₂.2)
    have hy' : g 1 * e₂⁻¹ = e₂⁻¹ * g 1 := hcomm _ (hgW 1) _ (W.inv_mem he₂.2)
    calc σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹
        = (σ.r * g 1 * σ.r⁻¹) * (σ.r * g 2 * σ.r⁻¹)⁻¹ := by group
      _ = (e₁ * g 1) * (e₂ * g 2)⁻¹ := by rw [hs₁, hs₂]
      _ = e₁ * g 1 * ((g 2)⁻¹ * e₂⁻¹) := by group
      _ = e₁ * g 1 * (e₂⁻¹ * (g 2)⁻¹) := by rw [hx]
      _ = e₁ * (g 1 * e₂⁻¹) * (g 2)⁻¹ := by group
      _ = e₁ * (e₂⁻¹ * g 1) * (g 2)⁻¹ := by rw [hy']
      _ = (e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹) := by group
  have hrfix : (ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹ = g 1 * g 2 := by
    calc (ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹
        = ((ρ 2).r * g 1 * (ρ 2).r⁻¹) * ((ρ 2).r * g 2 * (ρ 2).r⁻¹)⁻¹ := by group
      _ = g 1 * g 2 := by rw [hr₂fix 1 (by decide), hr₂g2, inv_inv]
  have hyw : y * (g 1 * g 2) * y⁻¹ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * (g 1 * g 2) := by
    rw [hy]
    calc ((ρ 2).r * σ.r * (ρ 2).r⁻¹) * (g 1 * g 2) * ((ρ 2).r * σ.r * (ρ 2).r⁻¹)⁻¹
        = (ρ 2).r * (σ.r * ((ρ 2).r⁻¹ * (g 1 * g 2) * (ρ 2).r) * σ.r⁻¹) * (ρ 2).r⁻¹ := by group
      _ = (ρ 2).r * (σ.r * (g 1 * (g 2)⁻¹) * σ.r⁻¹) * (ρ 2).r⁻¹ := by rw [hA]
      _ = (ρ 2).r * ((e₁ * e₂⁻¹) * (g 1 * (g 2)⁻¹)) * (ρ 2).r⁻¹ := by rw [hB']
      _ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * ((ρ 2).r * (g 1 * (g 2)⁻¹) * (ρ 2).r⁻¹) := by
          group
      _ = ((ρ 2).r * (e₁ * e₂⁻¹) * (ρ 2).r⁻¹) * (g 1 * g 2) := by rw [hrfix]
  have hg2inv : (g 2)⁻¹ = g 2 * z := by
    have h1' : (g 2)⁻¹ = z⁻¹ * g 2 := by
      have : z = g 2 * g 2 := (hgsq 2).symm
      rw [this]; group
    rw [h1', hzi]
    exact hcomm _ hzW _ (hgW 2)
  have hrt : (ρ 2).r * t * (ρ 2).r⁻¹ = t * z := by
    rw [hrel]
    calc (ρ 2).r * (g 0 * g 1 * g 2 * g 3) * (ρ 2).r⁻¹
        = ((ρ 2).r * g 0 * (ρ 2).r⁻¹) * ((ρ 2).r * g 1 * (ρ 2).r⁻¹) *
            ((ρ 2).r * g 2 * (ρ 2).r⁻¹) * ((ρ 2).r * g 3 * (ρ 2).r⁻¹) := by group
      _ = g 0 * g 1 * (g 2)⁻¹ * g 3 := by
          rw [hr₂fix 0 (by decide), hr₂fix 1 (by decide), hr₂g2, hr₂fix 3 (by decide)]
      _ = g 0 * g 1 * (g 2 * z) * g 3 := by rw [hg2inv]
      _ = g 0 * g 1 * g 2 * (z * g 3) := by group
      _ = g 0 * g 1 * g 2 * (g 3 * z) := by rw [hcomm z hzW (g 3) (hgW 3)]
      _ = (g 0 * g 1 * g 2 * g 3) * z := by group
  have hw : y * (g 1 * g 2) * y⁻¹ = g 1 * g 2 ∨
      y * (g 1 * g 2) * y⁻¹ = (t * z) * (g 1 * g 2) := by
    rcases hc01 with h0 | h0
    · left
      rw [hyw, h0]
      group
    · right
      rw [hyw, h0, hrt]
  have hKdat : Hyp22Setting p f Ω K K' K₃ z (g 0) (g 1) (g 2) :=
    S22.hyp22Setting_of_sylows hs.stand hz hs.hK' hs.hne hs.perp hs.hK₃ hs.hK₃K hs.hK₃K' h1 h2
      h3 c12 c13 c23 hg0R₁ hg1R₂ hg2R₃ (hg 0).2 (hg 1).2 (hg 2).2
  have hbig : S22.Big Ω K := S22.Big.of_four hs hK₄ h41 h42 h43
  have hyα : y ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({g 0 * g 1, z} : Set G)) : Set G) :=
    mem_normalizer_alpha_of_frame hKdat hbig (Subgroup.mem_centralizer_singleton_iff.mp hyC) hyz
      (hcomm z hzW t htW) ht.sq (hcomm t htW _ (W.mul_mem (hgW 1) (hgW 2))) hw
  refine ⟨g 0, g 1, by simpa [hρ0K] using (hg 0).1.1, by simpa [hρ1K] using (hg 1).1.1,
    (hg 0).2, (hg 1).2, hcomm _ (hgW 0) _ (hgW 1), ?_⟩
  refine ⟨R₃, R₄, g 2, g 3, y, h3, h4, c34, hR₃C, hR₄C, hg2R₃, hg3R₄, (hg 2).2, (hg 3).2,
    hgsq 2, hgsq 3, hyL, ?_, ?_, ?_, hyα⟩
  · rw [hyz, hrel, hperm]
  · rw [← hperm, ← hrel]
    exact htz
  · exact hcomm _ hzW _ (W.mul_mem (W.mul_mem (hgW 2) (hgW 3)) hu0W)

end Frame

end C22P

end CFSG.ClassicalInvolution.Asc77
