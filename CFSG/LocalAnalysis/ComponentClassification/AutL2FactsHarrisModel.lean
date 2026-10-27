module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisT

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {K : Subgroup (PGammaL2 F)}

omit [Finite F] in
theorem nm_pm_one_comm {s : Fˣ} (hs : s = 1 ∨ s = -1) (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F s false 1 * nm F a ε σ = nm F a ε σ * nm F s false 1 := by
  rcases hs with rfl | rfl
  · rw [nm_one, one_mul, mul_one]
  · rw [z_mul_nm, nm_mul_z]

theorem nm_pm_one_mem (hH : HarrisHyp F) {s : Fˣ} (hs : s = 1 ∨ s = -1) :
    s ∈ zpowers (stdGen F ^ 2) := by
  rcases hs with rfl | rfl
  · exact one_mem _
  · exact hH.neg_one_mem

theorem right_eq_one_of_mem_rStd (hsq : IsSquare (-1 : F)) {x : PGammaL2 F} (hx : x ∈ rStd F) :
    x.right = 1 := by
  obtain ⟨c, -, ε, rfl⟩ := (mem_map_stdT_iff hsq x).mp hx
  rfl

theorem sq_mem_zpowers_sq {x : Fˣ} (hx : x ∈ zpowers (stdGen F)) :
    x ^ 2 ∈ zpowers (stdGen F ^ 2) := by
  obtain ⟨j, rfl⟩ := hx
  exact ⟨j, by
    show (stdGen F ^ 2) ^ j = (stdGen F ^ j) ^ 2
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]⟩

omit [Finite F] in
theorem orderOf_nm_false (a : Fˣ) : orderOf (nm F a false 1) = orderOf a := by
  have hinj : Function.Injective
      ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (tor F)) :=
    SemidirectProduct.inl_injective.comp (pGammaL2FullSplitTorus_injective F)
  rw [← inl_tor]
  exact orderOf_injective _ hinj a

theorem card_rStd (hH : HarrisHyp F) : Nat.card (rStd F) = 2 ^ twoVal F := by
  rw [Subgroup.card_map_of_injective (incl_injective F), card_stdT hH.odd hH.sq]

theorem card_mul_relIndex {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  rw [Subgroup.relIndex, ← Subgroup.card_mul_index (A.subgroupOf B),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

theorem HarrisHyp.mem_sq_of_involution (hH : HarrisHyp F) {a : Fˣ}
    (ha : a ∈ zpowers (stdGen F)) (ε : Bool)
    (h : nm F a ε (psiF F) * nm F a ε (psiF F) = 1) : a ∈ zpowers (stdGen F ^ 2) := by
  rw [nm_mul, ← nm_one, nm_eq_nm_iff] at h
  have h1 := h.1
  by_contra ha2
  have hψ := hH.twist_epsR_of_not_mem ha ha2
  by_cases hε : ε = epsR F
  · rw [hε, hψ] at h1
    have h4 : a ^ 4 = 1 := by
      have : a ^ 2 = -1 := by
        rw [pow_two]
        have := congrArg (· * (-1 : Fˣ)) h1
        simpa [mul_neg, neg_mul] using this
      rw [show 4 = 2 * 2 by rfl, pow_mul, this]
      norm_num
    apply ha2
    apply mem_zpowers_of_orderOf_dvd
    rw [orderOf_stdGen_sq hH.odd]
    have h4' : (4 : ℕ) ∣ 2 ^ (twoVal F - 1) := by
      have := Nat.pow_dvd_pow 2 (show 2 ≤ twoVal F - 1 by have := hH.four_le; omega)
      simpa using this
    exact (orderOf_dvd_of_pow_eq_one h4).trans h4'
  · have hε' : ε = !epsR F := by cases ε <;> cases h : epsR F <;> simp_all
    rw [hε', twist_not, hψ] at h1
    apply hH.neg_one_ne_one
    have : a * (-a)⁻¹ = -1 := by rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [← this, h1]

section Shape

theorem HarrisHyp.not_mem_centralizer_iff (hH : HarrisHyp F) {x : PGammaL2 F} (hx : x ∈ sylS0 F) :
    x ∉ centralizer {v0Std F} ↔ v0Std F * x = nm F (-1) false 1 * (x * v0Std F) := by
  obtain ⟨a, ha, ε, σ, -, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff, hH.commute_v0Std_iff ha]
  constructor
  · exact (hH.v₀_mul_nm ha ε σ).2
  · intro h ha2
    rw [← (hH.v₀_mul_nm ha ε σ).1 ha2] at h
    exact hH.zStd_ne_one (right_eq_mul.mp h)

theorem HarrisHyp.mul_mem_centralizer_v0Std (hH : HarrisHyp F) {x y : PGammaL2 F} (hx : x ∈ sylS0 F)
    (hy : y ∈ sylS0 F) (hx' : x ∉ centralizer {v0Std F}) (hy' : y ∉ centralizer {v0Std F}) :
    x * y ∈ centralizer {v0Std F} := by
  have h1 := (hH.not_mem_centralizer_iff hx).mp hx'
  have h2 := (hH.not_mem_centralizer_iff hy).mp hy'
  obtain ⟨a, -, ε, σ, -, rfl⟩ := hx
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hz := nm_pm_one_comm (s := -1) (Or.inr rfl) a ε σ
  symm
  calc v0Std F * (nm F a ε σ * y) = v0Std F * nm F a ε σ * y := by group
    _ = nm F (-1) false 1 * (nm F a ε σ * v0Std F) * y := by rw [h1]
    _ = nm F (-1) false 1 * nm F a ε σ * (v0Std F * y) := by group
    _ = nm F (-1) false 1 * nm F a ε σ * (nm F (-1) false 1 * (y * v0Std F)) := by rw [h2]
    _ = nm F (-1) false 1 * (nm F a ε σ * nm F (-1) false 1) * y * v0Std F := by group
    _ = nm F (-1) false 1 * (nm F (-1) false 1 * nm F a ε σ) * y * v0Std F := by rw [hz]
    _ = nm F (-1) false 1 * nm F (-1) false 1 * nm F a ε σ * y * v0Std F := by group
    _ = nm F a ε σ * y * v0Std F := by rw [z_mul_self, one_mul]

theorem HarrisHyp.shape_dihedral (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥(stdTS F K ⊓ pGammaL2PSLRange F) ≃* DihedralGroup (2 ^ m)) := by
  rw [hH.stdTS_inf hK]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := stdSylow F hH.odd hH.sq hH.q4
  obtain ⟨m, -, ⟨ψ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hH.odd S
  have hS : (S : Subgroup (PSL2 F)) = stdT F := coe_stdSylow hH.odd hH.sq hH.q4
  have e : ↥(rStd F) ≃* DihedralGroup (2 ^ m) :=
    (((stdT F).equivMapOfInjective (incl F) (incl_injective F)).symm.trans
      (MulEquiv.subgroupCongr hS.symm)).trans ψ
  refine ⟨m, ?_, ⟨e⟩⟩
  have hc := Nat.card_congr e.toEquiv
  rw [card_rStd hH, DihedralGroup.nat_card, ← pow_succ'] at hc
  have := Nat.pow_right_injective le_rfl hc
  have h4 := hH.four_le
  omega

theorem HarrisHyp.shape_not_mem (hH : HarrisHyp F)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) : vStd F K ∉ stdTS F K ⊓ pGammaL2PSLRange F := by
  intro h
  have := ((mem_pslRange_iff _).mp h.2).1
  exact hH.phiGam_ne_one hψK this

theorem HarrisHyp.shape_field (hH : HarrisHyp F) (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    IsFieldAutModel (vStd F K) := by
  cases hε : epsR F
  · refine ⟨1, phiGam F K, hH.phiGam_ne_one hψK, ?_⟩
    simp only [vStd, hε, nm_one_false]
    group
  · have hφ := hH.phiGam_eq_psiF hψK hε
    have : vStd F K = v0Std F := by simp only [vStd, v0Std, hφ]
    rw [this]
    exact isFieldAutModel_of_involution hH.odd hH.orderOf_v0Std (by simp [hH.psiF_ne_one])

theorem HarrisHyp.shape_disj (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    zpowers (vStd F K) ⊓ (stdTS F K ⊓ pGammaL2PSLRange F) = ⊥ := by
  rw [hH.stdTS_inf hK, eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers (x := vStd F K) (y := x)).mpr hx1
  simp only at hj
  subst hj
  rw [mem_bot]
  obtain ⟨ε', hv⟩ := vStd_pow K j
  have hr := right_eq_one_of_mem_rStd hH.sq hx2
  rw [hv, nm_right] at hr
  have hdvd : orderOf (vStd F K) ∣ j := by
    rw [hH.orderOf_vStd hψK]
    exact orderOf_dvd_of_pow_eq_one hr
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

theorem HarrisHyp.shape_relIndex (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    ((stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K)).relIndex (stdTS F K) ≤ 2 := by
  rw [hH.stdTS_inf hK, ← hH.stdTS_inf_centralizer_v0Std hK]
  apply Nat.le_of_dvd two_pos
  rw [Subgroup.relIndex, Subgroup.index_dvd_two_iff]
  by_cases hall : ∀ x ∈ stdTS F K, x ∈ centralizer {v0Std F}
  · exact ⟨1, fun b => Or.inr ⟨b.2, hall _ b.2⟩⟩
  · push Not at hall
    obtain ⟨α, hα, hαC⟩ := hall
    refine ⟨⟨α, hα⟩, fun b => ?_⟩
    by_cases hb : (b : PGammaL2 F) ∈ centralizer {v0Std F}
    · exact Or.inr ⟨b.2, hb⟩
    · exact Or.inl ⟨mul_mem b.2 hα,
        hH.mul_mem_centralizer_v0Std b.2.1 hα.1 hb hαC⟩

theorem HarrisHyp.nm_mem_commutator_rStd (hH : HarrisHyp F) {d : Fˣ}
    (hd : d ^ 2 ^ (twoVal F - 2) = 1) :
    nm F d false 1 ∈ ⁅rStd F, rStd F⁆ := by
  have h4 := hH.four_le
  have hord : orderOf ((stdGen F ^ 2) ^ 2) = 2 ^ (twoVal F - 2) := by
    rw [orderOf_pow_of_dvd (by norm_num) (by
      rw [orderOf_stdGen_sq hH.odd]; exact dvd_pow_self 2 (by omega)), orderOf_stdGen_sq hH.odd]
    exact Nat.div_eq_of_eq_mul_left two_pos (by rw [← pow_succ]; congr 1; omega)
  obtain ⟨j, rfl⟩ := mem_zpowers_of_orderOf_dvd ((stdGen F ^ 2) ^ 2) d
    (by rw [hord]; exact orderOf_dvd_of_pow_eq_one hd)
  simp only
  rw [nm_false_zpow']
  apply zpow_mem
  have hc : ⁅nm F (stdGen F ^ 2) false 1, nm F 1 true 1⁆ = nm F ((stdGen F ^ 2) ^ 2) false 1 := by
    rw [commutator_nm_eq]
    simp [fu_one, pow_two]
  rw [← hc]
  exact commutator_mem_commutator (nm_mem_rStd hH.sq (mem_zpowers _) false)
    (nm_mem_rStd hH.sq (one_mem _) true)

omit [Finite F] in
theorem commutator_nm_pow {a b : Fˣ} {m : ℕ} (ha : (a ^ 2 ^ m) ^ 2 = 1)
    (hb : (b ^ 2 ^ m) ^ 2 = 1) (ε ε' : Bool) (σ τ : F ≃+* F) :
    (a * twist F ε (fu F σ b) * (b * twist F ε' (fu F τ a))⁻¹) ^ 2 ^ m = 1 := by
  rw [mul_pow, inv_pow, mul_pow, mul_pow, twist_fu_pow_eq hb, twist_fu_pow_eq ha,
    mul_comm (b ^ 2 ^ m), mul_inv_cancel]

theorem HarrisHyp.shape_derived (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) :
    ⁅(stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K),
      (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K)⁆ =
      ⁅stdTS F K ⊓ pGammaL2PSLRange F, stdTS F K ⊓ pGammaL2PSLRange F⁆ := by
  rw [hH.stdTS_inf hK]
  apply le_antisymm
  · rw [← hH.stdTS_inf_centralizer_v0Std hK, Subgroup.commutator_le]
    rintro x ⟨⟨⟨a, ha, ε, σ, -, rfl⟩, -⟩, hxC⟩ y ⟨⟨⟨b, hb, ε', τ, -, rfl⟩, -⟩, hyC⟩
    have ha2 := (hH.commute_v0Std_iff ha ε σ).mp (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    have hb2 := (hH.commute_v0Std_iff hb ε' τ).mp (Subgroup.mem_centralizer_singleton_iff.mp hyC)
    have h4 := hH.four_le
    have hsq : ∀ c ∈ zpowers (stdGen F ^ 2), (c ^ 2 ^ (twoVal F - 2)) ^ 2 = 1 := by
      intro c hc
      rw [← pow_mul, ← pow_succ, show twoVal F - 2 + 1 = twoVal F - 1 by omega]
      exact (pow_half_eq_one_iff hH.odd).mpr hc
    rw [commutator_nm_eq]
    exact hH.nm_mem_commutator_rStd (commutator_nm_pow (hsq a ha2) (hsq b hb2) ε ε' σ τ)
  · exact Subgroup.commutator_mono le_sup_left le_sup_left

theorem HarrisHyp.shape_comm_v₀ (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) : ∀ ρ ∈ stdTS F K ⊓ pGammaL2PSLRange F,
    ρ * vStd F K ^ (orderOf (vStd F K) / 2) = vStd F K ^ (orderOf (vStd F K) / 2) * ρ := by
  rw [hH.vStd_pow_half hψK, hH.stdTS_inf hK]
  intro ρ hρ
  obtain ⟨c, hc, ε, rfl⟩ := (mem_map_stdT_iff hH.sq ρ).mp hρ
  exact (hH.commute_v0Std_iff (zpowers_sq_le hc) ε 1).mpr hc

theorem HarrisHyp.shape_centralizer_v₀ (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    stdTS F K ⊓ centralizer {vStd F K ^ (orderOf (vStd F K) / 2)} =
      (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K) := by
  rw [hH.vStd_pow_half hψK, hH.stdTS_inf hK, hH.stdTS_inf_centralizer_v0Std hK]

theorem HarrisHyp.pm_one_mem_center (hH : HarrisHyp F) {s : Fˣ} (hs : s = 1 ∨ s = -1) :
    nm F s false 1 ∈ rStd F ⊓ centralizer (rStd F : Set (PGammaL2 F)) := by
  refine ⟨nm_mem_rStd hH.sq (nm_pm_one_mem hH hs) false, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  obtain ⟨c, -, ε, rfl⟩ := (mem_map_stdT_iff hH.sq g).mp hg
  exact (nm_pm_one_comm hs c ε 1).symm

theorem HarrisHyp.shape_centralizer_R (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) :
    stdTS F K ⊓ centralizer ((stdTS F K ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) :
      Set (PGammaL2 F)) =
    ((stdTS F K ⊓ pGammaL2PSLRange F) ⊓ centralizer ((stdTS F K ⊓ pGammaL2PSLRange F :
      Subgroup (PGammaL2 F)) : Set (PGammaL2 F))) ⊔
      zpowers (vStd F K ^ (orderOf (vStd F K) / 2)) := by
  rw [hH.vStd_pow_half hψK, hH.stdTS_inf hK]
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    replace hxC := Subgroup.mem_centralizer_iff.mp hxC
    obtain ⟨s, hs, h | h⟩ := hH.eq_of_centralizes_rStd hxT.1 hxC
    · rw [h]
      exact mem_sup_left (hH.pm_one_mem_center hs)
    · have : x = nm F s false 1 * v0Std F := by
        rw [h, nm_mul]
        simp [fu_one]
      rw [this]
      exact mul_mem (mem_sup_left (hH.pm_one_mem_center hs)) (mem_sup_right (mem_zpowers _))
  · apply sup_le
    · exact inf_le_inf_right _ (hH.rStd_le_stdTS hK)
    · rw [zpowers_le]
      refine ⟨hH.v0Std_mem hK hψK, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro g hg
      obtain ⟨c, hc, ε, rfl⟩ := (mem_map_stdT_iff hH.sq g).mp hg
      exact (hH.commute_v0Std_iff (zpowers_sq_le hc) ε 1).mpr hc

theorem HarrisHyp.shape_fieldInv (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hψK : SemidirectProduct.inr (psiF F) ∈ K) : ∀ k ∈ stdTS F K, IsFieldInvModel k →
    ∃ ρ ∈ stdTS F K ⊓ pGammaL2PSLRange F, k = ρ * vStd F K ^ (orderOf (vStd F K) / 2) := by
  rw [hH.vStd_pow_half hψK, hH.stdTS_inf hK]
  rintro k ⟨⟨a, ha, ε, σ, -, rfl⟩, -⟩ ⟨b, σ', hσ', hk⟩
  have hσψ : σ' = psiF F := hH.eq_psiF_of_orderOf hσ'
  have hr : σ = σ' := by
    have := congrArg SemidirectProduct.right hk
    rwa [nm_right, right_conj] at this
  subst hr
  subst hσψ
  have hkk : nm F a ε (psiF F) * nm F a ε (psiF F) = 1 := by
    rw [hk]
    calc b * SemidirectProduct.inr (psiF F) * b⁻¹ * (b * SemidirectProduct.inr (psiF F) * b⁻¹) =
        b * (SemidirectProduct.inr (psiF F * psiF F)) * b⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [hH.psiF_mul_self, map_one, mul_one, mul_inv_cancel]
  have ha2 := hH.mem_sq_of_involution ha ε hkk
  refine ⟨nm F a (xor ε (epsR F)) 1, nm_mem_rStd hH.sq ha2 _, ?_⟩
  rw [nm_mul]
  simp [fu_one]

theorem HarrisHyp.exists_not_mem_centralizer (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hne : stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K)) :
    ∃ α ∈ stdTS F K, α ∉ centralizer {v0Std F} := by
  by_contra hall
  push Not at hall
  apply hne
  rw [hH.stdTS_inf hK, ← hH.stdTS_inf_centralizer_v0Std hK]
  exact le_antisymm (fun x hx => ⟨hx, hall x hx⟩) inf_le_left

theorem HarrisHyp.shape_center_of_ne (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    (hne : stdTS F K ≠ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (vStd F K)) :
    stdTS F K ⊓ centralizer (stdTS F K : Set (PGammaL2 F)) =
      (stdTS F K ⊓ pGammaL2PSLRange F) ⊓
        centralizer ((stdTS F K ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) :
          Set (PGammaL2 F)) := by
  obtain ⟨α, hα, hαC⟩ := hH.exists_not_mem_centralizer hK hne
  rw [hH.stdTS_inf hK]
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    replace hxC := Subgroup.mem_centralizer_iff.mp hxC
    obtain ⟨s, hs, h | h⟩ := hH.eq_of_centralizes_rStd hxT.1
      (fun g hg => hxC g (hH.rStd_le_stdTS hK hg))
    · rw [h]
      exact hH.pm_one_mem_center hs
    · exfalso
      apply hαC
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have h1 := hxC α hα
      obtain ⟨a₁, -, ε₁, σ₁, -, rfl⟩ := hα.1
      have hS := nm_pm_one_comm hs a₁ ε₁ σ₁
      have hx : x = nm F s false 1 * v0Std F := by
        rw [h, nm_mul]
        simp [fu_one]
      rw [hx] at h1
      have h2 : nm F s false 1 * (nm F a₁ ε₁ σ₁ * v0Std F) =
          nm F s false 1 * (v0Std F * nm F a₁ ε₁ σ₁) := by
        calc nm F s false 1 * (nm F a₁ ε₁ σ₁ * v0Std F) =
            nm F s false 1 * nm F a₁ ε₁ σ₁ * v0Std F := by group
          _ = nm F a₁ ε₁ σ₁ * nm F s false 1 * v0Std F := by rw [hS]
          _ = nm F a₁ ε₁ σ₁ * (nm F s false 1 * v0Std F) := by group
          _ = nm F s false 1 * v0Std F * nm F a₁ ε₁ σ₁ := h1
          _ = nm F s false 1 * (v0Std F * nm F a₁ ε₁ σ₁) := by group
      exact (mul_left_cancel h2)
  · rintro x ⟨hxR, hxC⟩
    replace hxC := Subgroup.mem_centralizer_iff.mp hxC
    obtain ⟨s, hs, h | h⟩ := hH.eq_of_centralizes_rStd (map_stdT_le_sylS0 hH.sq hxR) hxC
    · refine ⟨hH.rStd_le_stdTS hK hxR, ?_⟩
      apply Subgroup.mem_centralizer_iff.mpr
      rw [h]
      rintro g ⟨⟨a, -, ε, σ, -, rfl⟩, -⟩
      exact (nm_pm_one_comm hs a ε σ).symm
    · exfalso
      have := right_eq_one_of_mem_rStd hH.sq hxR
      rw [h, nm_right] at this
      exact hH.psiF_ne_one this

theorem HarrisHyp.derived_eq_zpowers (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {α : PGammaL2 F} (hα : α ∈ stdTS F K)
    (hαC : α ∉ centralizer {v0Std F}) :
    ⁅stdTS F K, stdTS F K⁆ = zpowers ⁅nm F 1 true 1, α⁆ ∧
      ⁅rStd F, zpowers α⁆ = zpowers ⁅nm F 1 true 1, α⁆ ∧
      ∃ a₁ : Fˣ, a₁ ∈ zpowers (stdGen F) ∧ a₁ ∉ zpowers (stdGen F ^ 2) ∧
        ⁅nm F 1 true 1, α⁆ = nm F (a₁⁻¹ * a₁⁻¹) false 1 := by
  obtain ⟨⟨a₁, ha₁, ε₁, σ₁, hσ₁, rfl⟩, hαK⟩ := hα
  have ha₁2 : a₁ ∉ zpowers (stdGen F ^ 2) := by
    intro h
    apply hαC
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((hH.commute_v0Std_iff ha₁ ε₁ σ₁).mpr h)
  have hg : ⁅nm F 1 true 1, nm F a₁ ε₁ σ₁⁆ = nm F (a₁⁻¹ * a₁⁻¹) false 1 := by
    rw [commutator_nm_eq]
    simp [fu_one]
  have h4 := hH.four_le
  have hord : orderOf (a₁⁻¹ * a₁⁻¹) = 2 ^ (twoVal F - 1) := by
    rw [← pow_two, orderOf_pow_of_dvd (by norm_num) (by
      rw [orderOf_inv, orderOf_of_not_mem hH.odd ha₁ ha₁2]; exact dvd_pow_self 2 (by omega)),
      orderOf_inv, orderOf_of_not_mem hH.odd ha₁ ha₁2]
    exact Nat.div_eq_of_eq_mul_left two_pos (by rw [← pow_succ]; congr 1; omega)
  have hle : ⁅stdTS F K, stdTS F K⁆ ≤ zpowers ⁅nm F 1 true 1, nm F a₁ ε₁ σ₁⁆ := by
    rw [Subgroup.commutator_le]
    rintro x ⟨⟨a, ha, ε, σ, -, rfl⟩, -⟩ y ⟨⟨b, hb, ε', τ, -, rfl⟩, -⟩
    have hsq : ∀ c ∈ zpowers (stdGen F), (c ^ 2 ^ (twoVal F - 1)) ^ 2 = 1 := by
      intro c hc
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
      exact pow_two_pow_twoVal_eq_one hc
    have hd := commutator_nm_pow (hsq a ha) (hsq b hb) ε ε' σ τ
    rw [hg, commutator_nm_eq]
    obtain ⟨j, hj⟩ := mem_zpowers_of_orderOf_dvd (a₁⁻¹ * a₁⁻¹)
      (a * twist F ε (fu F σ b) * (b * twist F ε' (fu F τ a))⁻¹)
      (by rw [hord]; exact orderOf_dvd_of_pow_eq_one hd)
    simp only at hj
    rw [← hj, nm_false_zpow']
    exact zpow_mem (mem_zpowers _) j
  have hge : zpowers ⁅nm F 1 true 1, nm F a₁ ε₁ σ₁⁆ ≤ ⁅rStd F, zpowers (nm F a₁ ε₁ σ₁)⁆ := by
    rw [zpowers_le]
    exact commutator_mem_commutator (nm_mem_rStd hH.sq (one_mem _) true) (mem_zpowers _)
  have hmono : ⁅rStd F, zpowers (nm F a₁ ε₁ σ₁)⁆ ≤ ⁅stdTS F K, stdTS F K⁆ :=
    Subgroup.commutator_mono (hH.rStd_le_stdTS hK)
      ((zpowers_le).mpr ⟨⟨a₁, ha₁, ε₁, σ₁, hσ₁, rfl⟩, hαK⟩)
  exact ⟨le_antisymm hle (hge.trans hmono), le_antisymm (hmono.trans hle) hge, a₁, ha₁, ha₁2, hg⟩

end Shape

end CFSG.ComponentClassification.AutL2Facts
