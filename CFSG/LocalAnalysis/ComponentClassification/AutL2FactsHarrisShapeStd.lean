module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {K : Subgroup (PGammaL2 F)}

theorem HarrisHyp.orderOf_inv_mul_inv (hH : HarrisHyp F) {a : Fˣ} (ha : a ∈ zpowers (stdGen F))
    (ha2 : a ∉ zpowers (stdGen F ^ 2)) : orderOf (a⁻¹ * a⁻¹) = 2 ^ (twoVal F - 1) := by
  have h4 := hH.four_le
  rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by
    rw [orderOf_inv, orderOf_of_not_mem hH.odd ha ha2]; exact dvd_pow_self 2 (by omega)),
    orderOf_inv, orderOf_of_not_mem hH.odd ha ha2]
  exact Nat.div_eq_of_eq_mul_left two_pos (by rw [← pow_succ]; congr 1; omega)

theorem HarrisHyp.not_mem_centralizer_of_not_mem_sup (hH : HarrisHyp F)
    (hK : pGammaL2PSLRange F ≤ K) {α : PGammaL2 F} (hα : α ∈ stdTS F K)
    (hαH : α ∉ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K)) :
    α ∉ centralizer {v0Std F} := by
  intro hC
  apply hαH
  rw [hH.stdTS_inf hK, ← hH.stdTS_inf_centralizer_v0Std hK]
  exact ⟨hα, hC⟩

theorem HarrisHyp.shape_derived_of_ne (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
    ∀ α ∈ stdTS F K, α ∉ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
      (⁅stdTS F K, stdTS F K⁆ : Subgroup (PGammaL2 F)) =
        ⁅stdTS F K ⊓ pGammaL2PSLRange F, zpowers α⁆ := by
  intro _ α hα hαH
  have hαC := hH.not_mem_centralizer_of_not_mem_sup hK hα hαH
  obtain ⟨h1, h2, -⟩ := hH.derived_eq_zpowers hK hα hαC
  rw [hH.stdTS_inf hK, h1, h2]

theorem HarrisHyp.shape_derived_cyclic_of_ne (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
    IsCyclic (⁅stdTS F K, stdTS F K⁆ : Subgroup (PGammaL2 F)) ∧
      (⁅stdTS F K, stdTS F K⁆ : Subgroup (PGammaL2 F)) ≤ stdTS F K ⊓ pGammaL2PSLRange F ∧
      (⁅stdTS F K, stdTS F K⁆ : Subgroup (PGammaL2 F)).relIndex
        (stdTS F K ⊓ pGammaL2PSLRange F) = 2 := by
  intro hne
  obtain ⟨α, hα, hαC⟩ := hH.exists_not_mem_centralizer hK hne
  obtain ⟨h1, -, a₁, ha₁, ha₁2, hg⟩ := hH.derived_eq_zpowers hK hα hαC
  rw [hH.stdTS_inf hK, h1, hg]
  have hmem : nm F (a₁⁻¹ * a₁⁻¹) false 1 ∈ rStd F :=
    nm_mem_rStd hH.sq (by rw [← pow_two]; exact sq_mem_zpowers_sq (inv_mem ha₁)) false
  refine ⟨inferInstance, (zpowers_le).mpr hmem, ?_⟩
  have h := card_mul_relIndex ((zpowers_le).mpr hmem)
  rw [Nat.card_zpowers, orderOf_nm_false, hH.orderOf_inv_mul_inv ha₁ ha₁2, card_rStd hH] at h
  have h4 := hH.four_le
  have h2 : 2 ^ twoVal F = 2 ^ (twoVal F - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem HarrisHyp.shape_swap_of_ne (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
    ∀ α ∈ stdTS F K, α ∉ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
      ∀ y ∈ stdTS F K ⊓ pGammaL2PSLRange F, y ^ 2 = 1 →
        y ∉ centralizer ((stdTS F K ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) :
          Set (PGammaL2 F)) →
        ∀ ρ ∈ stdTS F K ⊓ pGammaL2PSLRange F, α⁻¹ * y * α ≠ ρ⁻¹ * y * ρ := by
  intro _ α hα hαH y hy hy2 hyC ρ hρ
  have hαC := hH.not_mem_centralizer_of_not_mem_sup hK hα hαH
  rw [hH.stdTS_inf hK] at hy hyC hρ
  obtain ⟨⟨a₁, ha₁, ε₁, σ₁, -, rfl⟩, -⟩ := hα
  have ha₁2 : a₁ ∉ zpowers (stdGen F ^ 2) := by
    intro h
    exact hαC (Subgroup.mem_centralizer_singleton_iff.mpr
      ((hH.commute_v0Std_iff ha₁ ε₁ σ₁).mpr h))
  obtain ⟨c, hc, ε, rfl⟩ := (mem_map_stdT_iff hH.sq y).mp hy
  obtain ⟨c', hc', ε', rfl⟩ := (mem_map_stdT_iff hH.sq ρ).mp hρ
  have hε : ε = true := by
    by_contra hne
    have hε' : ε = false := by simpa using hne
    subst hε'
    rw [pow_two, nm_mul, ← nm_one, nm_eq_nm_iff] at hy2
    have hcc : c ^ 2 = 1 := by rw [pow_two]; simpa [fu_one] using hy2.1
    exact hyC (hH.pm_one_mem_center (units_eq_one_or_neg_one hcc)).2
  subst hε
  have h4 := hH.four_le
  set m := 2 ^ (twoVal F - 2)
  have hcm : (c ^ m) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, show twoVal F - 2 + 1 = twoVal F - 1 by omega]
    exact (pow_half_eq_one_iff hH.odd).mpr hc
  have hbb : ∀ b : Fˣ, b ^ m * b ^ m = b ^ 2 ^ (twoVal F - 1) := by
    intro b
    rw [← pow_add, ← two_mul, ← pow_succ', show twoVal F - 2 + 1 = twoVal F - 1 by omega]
  set b := twist F ε₁ (fu F σ₁⁻¹ a₁⁻¹)
  have hb : b ∈ zpowers (stdGen F) := twist_mem (fu_mem_zpowers _ _ (inv_mem ha₁)) ε₁
  have hb2 : b ∉ zpowers (stdGen F ^ 2) := by
    rw [twist_mem_iff, fu_mem_zpowers_iff, inv_mem_iff]
    exact ha₁2
  set b' := twist F ε' (fu F 1 c'⁻¹)
  have hb' : b' ∈ zpowers (stdGen F ^ 2) := twist_mem (fu_mem_zpowers _ _ (inv_mem hc')) ε'
  have hinv : (nm F a₁ ε₁ σ₁)⁻¹ = nm F b ε₁ σ₁⁻¹ := nm_inv a₁ ε₁ σ₁
  have hinv' : (nm F c' ε' 1)⁻¹ = nm F b' ε' 1 := by rw [nm_inv, inv_one]
  have e1 : (nm F a₁ ε₁ σ₁)⁻¹ * nm F c true 1 * nm F a₁ ε₁ σ₁ =
      nm F (b * b * twist F ε₁ (fu F σ₁⁻¹ c)) true 1 := by
    rw [hinv, ← nm_conj_refl, ← hinv, inv_inv]
  have e2 : (nm F c' ε' 1)⁻¹ * nm F c true 1 * nm F c' ε' 1 =
      nm F (b' * b' * twist F ε' (fu F 1 c)) true 1 := by
    rw [hinv', ← nm_conj_refl, ← hinv', inv_inv]
  rw [e1, e2]
  intro heq
  have h1 := congrArg (· ^ m) (nm_injective heq).1
  simp only [mul_pow] at h1
  rw [hbb, hbb, twist_fu_pow_eq hcm, twist_fu_pow_eq hcm,
    pow_half_eq_neg_one hH.odd hb hb2, (pow_half_eq_one_iff hH.odd).mpr hb', one_mul,
    neg_one_mul] at h1
  exact hH.neg_one_ne_one (mul_right_cancel (b := c ^ m) (by rw [neg_one_mul, one_mul]; exact h1))

theorem HarrisHyp.shape_small_of_ne (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
    ∀ α ∈ stdTS F K, α ∉ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) →
      α ^ 2 = 1 → Nat.card ↥((stdTS F K ⊓ pGammaL2PSLRange F) ⊓ centralizer {α}) ≤ 4 := by
  intro _ α hα hαH hα2
  have hαC := hH.not_mem_centralizer_of_not_mem_sup hK hα hαH
  rw [hH.stdTS_inf hK]
  obtain ⟨⟨a₁, ha₁, ε₁, σ₁, -, rfl⟩, -⟩ := hα
  have ha₁2 : a₁ ∉ zpowers (stdGen F ^ 2) := by
    intro h
    exact hαC (Subgroup.mem_centralizer_singleton_iff.mpr
      ((hH.commute_v0Std_iff ha₁ ε₁ σ₁).mpr h))
  have hσ₁ : σ₁ = 1 := by
    by_contra hσ1
    have hσσ : σ₁ * σ₁ = 1 := by
      have := congrArg SemidirectProduct.right hα2
      rwa [right_pow, nm_right, pow_two] at this
    have := hH.eq_psiF hσ1 hσσ
    subst this
    exact ha₁2 (hH.mem_sq_of_involution ha₁ ε₁ (by rw [← pow_two]; exact hα2))
  subst hσ₁
  have hε₁ : ε₁ = true := by
    by_contra hne
    have hε' : ε₁ = false := by simpa using hne
    subst hε'
    rw [pow_two, nm_mul, ← nm_one, nm_eq_nm_iff] at hα2
    have : a₁ ^ 2 = 1 := by rw [pow_two]; simpa [fu_one] using hα2.1
    exact ha₁2 (nm_pm_one_mem hH (units_eq_one_or_neg_one this))
  subst hε₁
  have hsub : (((rStd F ⊓ centralizer {nm F a₁ true 1} : Subgroup (PGammaL2 F))) :
      Set (PGammaL2 F)) ⊆ {1, nm F (-1) false 1} := by
    rintro ρ ⟨hρ, hρC⟩
    replace hρC := Subgroup.mem_centralizer_singleton_iff.mp hρC
    obtain ⟨b, hb, ε', rfl⟩ := (mem_map_stdT_iff hH.sq ρ).mp hρ
    rw [nm_mul, nm_mul, nm_eq_nm_iff] at hρC
    cases ε'
    · have h1 : b * a₁ = a₁ * b⁻¹ := by simpa [fu_one] using hρC.1
      have hb2 : b ^ 2 = 1 := by
        rw [pow_two]
        have := congrArg (· * (a₁⁻¹ * b)) h1
        rw [show b * a₁ * (a₁⁻¹ * b) = b * b by group,
          show a₁ * b⁻¹ * (a₁⁻¹ * b) = 1 by rw [mul_comm a₁ b⁻¹]; group] at this
        exact this
      rcases units_eq_one_or_neg_one hb2 with rfl | rfl
      · left
        exact nm_one
      · right
        rfl
    · exfalso
      have h1 : b * a₁⁻¹ = a₁ * b⁻¹ := by simpa [fu_one] using hρC.1
      have hw : (b * a₁⁻¹) ^ 2 = 1 := by
        rw [pow_two]
        nth_rw 2 [h1]
        group
      apply ha₁2
      have ha : a₁ = (b * a₁⁻¹)⁻¹ * b := by group
      rw [ha]
      exact mul_mem (inv_mem (nm_pm_one_mem hH (units_eq_one_or_neg_one hw))) hb
  calc Nat.card ↥(rStd F ⊓ centralizer {nm F a₁ true 1}) =
      ((rStd F ⊓ centralizer {nm F a₁ true 1} : Subgroup (PGammaL2 F)) :
        Set (PGammaL2 F)).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, nm F (-1) false 1} : Set (PGammaL2 F)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      rw [Set.ncard_pair (Ne.symm hH.zStd_ne_one)]
    _ ≤ 4 := by norm_num

theorem HarrisHyp.sylowShape_stdTS (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (stdTS F K) (vStd F K) :=
  ⟨hH.shape_dihedral hK, hH.vStd_mem hK, hH.shape_not_mem hψK, hH.shape_field hψK,
    by rw [hH.vStd_pow_half hψK]; exact hH.isFieldInvModel_v0Std, hH.shape_disj hK hψK,
    hH.shape_relIndex hK, hH.shape_derived hK, hH.shape_comm_v₀ hK hψK,
    hH.shape_centralizer_v₀ hK hψK, hH.shape_centralizer_R hK hψK, hH.shape_fieldInv hK hψK,
    hH.shape_center_of_ne hK, hH.shape_derived_of_ne hK, hH.shape_derived_cyclic_of_ne hK,
    hH.shape_swap_of_ne hK, hH.shape_small_of_ne hK⟩

theorem pslRange_map_conj (g : PGammaL2 F) :
    (pGammaL2PSLRange F).map (MulAut.conj g).toMonoidHom = pGammaL2PSLRange F := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := pslRange_conj_mem g h
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
  · intro h
    have := pslRange_conj_mem g⁻¹ h
    rwa [inv_inv] at this

omit [Finite F] in
theorem isFieldInvModel_conj_iff (g x : PGammaL2 F) :
    IsFieldInvModel x ↔ IsFieldInvModel (MulAut.conj g x) := by
  rw [MulAut.conj_apply]
  constructor
  · rintro ⟨b, σ, hσ, rfl⟩
    exact ⟨g * b, σ, hσ, by group⟩
  · rintro ⟨b, σ, hσ, h⟩
    refine ⟨g⁻¹ * b, σ, hσ, ?_⟩
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group

omit [Finite F] in
theorem isFieldAutModel_conj_iff (g x : PGammaL2 F) :
    IsFieldAutModel x ↔ IsFieldAutModel (MulAut.conj g x) := by
  rw [MulAut.conj_apply]
  constructor
  · rintro ⟨b, σ, hσ, rfl⟩
    exact ⟨g * b, σ, hσ, by group⟩
  · rintro ⟨b, σ, hσ, h⟩
    refine ⟨g⁻¹ * b, σ, hσ, ?_⟩
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group

theorem HarrisHyp.inr_psiF_mem (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hk : ∃ k ∈ K, IsFieldInvModel k) : SemidirectProduct.inr (psiF F) ∈ K := by
  obtain ⟨k, hkK, b, σ, hσ, rfl⟩ := hk
  have h := conj_mem_of_pslRange_le hK b⁻¹ hkK
  rw [show b⁻¹ * (b * SemidirectProduct.inr σ * b⁻¹) * b⁻¹⁻¹ = SemidirectProduct.inr σ by group,
    hH.eq_psiF_of_orderOf hσ] at h
  exact h

theorem HarrisHyp.exists_sylowShape (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hk : ∃ k ∈ K, IsFieldInvModel k) {T : Subgroup (PGammaL2 F)} (hT : IsSylowIn T K) :
    ∃ g ∈ K, T = (stdTS F K).map (MulAut.conj g).toMonoidHom ∧
      SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel T
        (MulAut.conj g (vStd F K)) := by
  have hψK := hH.inr_psiF_mem hK hk
  obtain ⟨g, hgK, rfl⟩ := (hH.isSylowIn_stdTS hK).exists_conj hT
  exact ⟨g, hgK, rfl, (hH.sylowShape_stdTS hK hψK).map (MulAut.conj g) (pslRange_map_conj g)
    (isFieldInvModel_conj_iff g) (isFieldAutModel_conj_iff g)⟩

end CFSG.ComponentClassification.AutL2Facts
