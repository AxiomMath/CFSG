module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisCommon

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F] {K : Subgroup (PGammaL2 F)}

omit [Finite F] in
theorem tor_mem_range_iff (y : Fˣ) :
    tor F y ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      IsSquare (y : F) := by
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F y) ∈ _ ↔ _
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have : ((Matrix.GeneralLinearGroup.det (pGammaL2FullSplitTorusGL F y) : Fˣ) : F) = y := by
    simp [pGammaL2FullSplitTorusGL]
  rw [this]

theorem HarrisHyp.stdGen_not_isSquare (hH : HarrisHyp F) : ¬ IsSquare ((stdGen F : Fˣ) : F) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (stdGen F).ne_zero hr
  set u := Units.mk0 r hr0
  have hu : u ^ 2 = stdGen F := by
    ext
    simp [u, pow_two, hr]
  have h1 : u ^ 2 ^ (twoVal F + 1) = 1 := by
    rw [pow_succ', pow_mul, hu, pow_two_pow_twoVal_eq_one (mem_zpowers _)]
  obtain ⟨i, hi, hui⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hin : i ≤ twoVal F := by
    have : 2 ^ i ∣ Nat.card F - 1 := by
      rw [← hui, ← Nat.card_units]
      exact orderOf_dvd_natCard u
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp this
  have h2 : u ^ 2 ^ twoVal F = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hui]; exact Nat.pow_dvd_pow 2 hin)
  have h3 : stdGen F ^ 2 ^ (twoVal F - 1) = 1 := by
    rw [← hu, ← pow_mul, ← pow_succ', Nat.sub_add_cancel (one_le_twoVal hH.odd), h2]
  have := orderOf_dvd_of_pow_eq_one h3
  rw [orderOf_stdGen] at this
  have h4 := hH.four_le
  have := Nat.le_of_dvd (by positivity) this
  have : 2 ^ (twoVal F - 1) < 2 ^ twoVal F := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem HarrisHyp.not_sqLeft_stdGen (hH : HarrisHyp F) : ¬ SqLeft (nm F (stdGen F) false 1) := by
  intro h
  apply hH.stdGen_not_isSquare
  rw [← tor_mem_range_iff]
  simpa using h

theorem HarrisHyp.conj_stdGen_v0Std (hH : HarrisHyp F) :
    nm F (stdGen F) false 1 * v0Std F * (nm F (stdGen F) false 1)⁻¹ =
      nm F (-1) false 1 * v0Std F := by
  have h0 := (hH.v₀_mul_nm (mem_zpowers (stdGen F)) false 1).2 hH.stdGen_not_mem
  calc nm F (stdGen F) false 1 * v0Std F * (nm F (stdGen F) false 1)⁻¹ =
      nm F (-1) false 1 * nm F (-1) false 1 * (nm F (stdGen F) false 1 * v0Std F) *
        (nm F (stdGen F) false 1)⁻¹ := by rw [z_mul_self, one_mul]
    _ = nm F (-1) false 1 * (nm F (-1) false 1 * (nm F (stdGen F) false 1 * v0Std F)) *
        (nm F (stdGen F) false 1)⁻¹ := by group
    _ = nm F (-1) false 1 * (v0Std F * nm F (stdGen F) false 1) *
        (nm F (stdGen F) false 1)⁻¹ := by rw [← h0]
    _ = nm F (-1) false 1 * v0Std F := by group

theorem HarrisHyp.fusion_std (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K) {v : PGammaL2 F}
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (stdTS F K) v)
    {ι : PGammaL2 F} (hι : ι ∈ (stdTS F K ⊓ pGammaL2PSLRange F) ⊓
      centralizer ((stdTS F K ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) : Set (PGammaL2 F)))
    (hι2 : orderOf ι = 2) {x : PGammaL2 F}
    (hx : x ∈ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers v) (hx2 : orderOf x = 2) :
    ∃ k ∈ K, k * x * k⁻¹ = ι ∨ k * x * k⁻¹ = v ^ (orderOf v / 2) ∨
      k * x * k⁻¹ = v ^ (orderOf v / 2) * ι := by
  obtain ⟨s, hs, hw⟩ := hH.pow_half_eq_of_shape hK hv
  rw [hw]
  rw [hH.stdTS_inf hK] at hι
  have hιz : ι = nm F (-1) false 1 := by
    obtain ⟨hιR, hιC⟩ := hι
    replace hιC := Subgroup.mem_centralizer_iff.mp hιC
    obtain ⟨s', hs', h | h⟩ := hH.eq_of_centralizes_rStd (map_stdT_le_sylS0 hH.sq hιR) hιC
    · rcases hs' with rfl | rfl
      · exfalso
        rw [h, nm_one, orderOf_one] at hι2
        norm_num at hι2
      · exact h
    · exfalso
      have := right_eq_one_of_mem_rStd hH.sq hιR
      rw [h, nm_right] at this
      exact hH.psiF_ne_one this
  subst hιz
  rw [hH.sup_eq_of_shape hK hv] at hx
  obtain ⟨⟨⟨a, ha, ε, σ, -, rfl⟩, -⟩, hxC⟩ := hx
  have ha2 := (hH.commute_v0Std_iff ha ε σ).mp (Subgroup.mem_centralizer_singleton_iff.mp hxC)
  have hxx : nm F a ε σ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx2])
  have hσσ : σ * σ = 1 := by
    have := congrArg SemidirectProduct.right hxx
    rwa [right_pow, nm_right, pow_two] at this
  by_cases hσ1 : σ = 1
  ·
    subst hσ1
    obtain ⟨x', hx'⟩ := rStd_le_pslRange (nm_mem_rStd hH.sq ha2 ε)
    obtain ⟨z', hz'⟩ := rStd_le_pslRange hH.zStd_mem_rStd
    have hinv : ∀ (y : PSL2 F) (w : PGammaL2 F), incl F y = w → orderOf w = 2 →
        BenderSuzuki.PFAppendixIII.IsInvolution y := by
      intro y w hyw hw2
      have hy2 : orderOf y = 2 := by
        rw [← orderOf_injective (incl F) (incl_injective F) y, hyw, hw2]
      refine ⟨fun h => ?_, orderOf_dvd_iff_pow_eq_one.mp (by rw [hy2])⟩
      rw [h, orderOf_one] at hy2
      norm_num at hy2
    obtain ⟨h, hh⟩ := psl2_involutions_conjugate_of_odd_prime_power F hH.odd x' z'
      (hinv x' _ hx' hx2) (hinv z' _ hz' hι2)
    refine ⟨incl F h, hK ⟨h, rfl⟩, Or.inl ?_⟩
    rw [← hx', ← hz', ← hh, map_mul, map_mul, map_inv]
    rfl
  ·
    have hσψ := hH.eq_psiF hσ1 hσσ
    subst hσψ
    obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hH.odd (nm F a ε (psiF F)) hx2
      (by simpa using hσ1)
    obtain ⟨C₀, hC₀⟩ := exists_conj_inr_of_involution hH.odd (v0Std F) hH.orderOf_v0Std
      (by simp [hH.psiF_ne_one])
    set h : PGammaL2 F := SemidirectProduct.inl C * (SemidirectProduct.inl C₀)⁻¹
    have hxh : nm F a ε (psiF F) = h * v0Std F * h⁻¹ := by
      rw [nm_right] at hC hC₀
      have e1 : nm F a ε (psiF F) = SemidirectProduct.inl C * SemidirectProduct.inr (psiF F) *
          (SemidirectProduct.inl C)⁻¹ := by rw [← hC]; group
      have e2 : SemidirectProduct.inr (psiF F) = (SemidirectProduct.inl C₀)⁻¹ * v0Std F *
          SemidirectProduct.inl C₀ := hC₀.symm
      rw [e1, e2]
      simp only [h]
      group
    have hh1 : h.right = 1 := by simp [h]
    by_cases hsq : SqLeft h
    · have hhL : h ∈ pGammaL2PSLRange F := (mem_pslRange_iff h).mpr ⟨hh1, hsq⟩
      refine ⟨h⁻¹, hK (inv_mem hhL), ?_⟩
      have : h⁻¹ * nm F a ε (psiF F) * h⁻¹⁻¹ = v0Std F := by rw [hxh]; group
      rw [this]
      rcases hs with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ?_)
        rw [nm_mul_z, neg_neg]
    · have hd1 : (nm F (stdGen F) false 1).right = 1 := rfl
      have hk : nm F (stdGen F) false 1 * h⁻¹ ∈ pGammaL2PSLRange F :=
        mul_mem_pslRange_of_not hd1 (by rw [SemidirectProduct.inv_right, hh1, inv_one])
          hH.not_sqLeft_stdGen (by rwa [sqLeft_inv])
      refine ⟨nm F (stdGen F) false 1 * h⁻¹, hK hk, ?_⟩
      have : nm F (stdGen F) false 1 * h⁻¹ * nm F a ε (psiF F) *
          (nm F (stdGen F) false 1 * h⁻¹)⁻¹ = nm F (-1) false 1 * v0Std F := by
        rw [hxh, ← hH.conj_stdGen_v0Std]
        group
      rw [this]
      rcases hs with rfl | rfl
      · refine Or.inr (Or.inr ?_)
        rw [z_mul_nm, nm_mul_z]
      · refine Or.inr (Or.inl ?_)
        rw [z_mul_nm]

theorem HarrisHyp.fusion (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {T : Subgroup (PGammaL2 F)} (hT : IsSylowIn T K) {v : PGammaL2 F}
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel T v)
    {ι : PGammaL2 F} (hι : ι ∈ (T ⊓ pGammaL2PSLRange F) ⊓
      centralizer ((T ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) : Set (PGammaL2 F)))
    (hι2 : orderOf ι = 2) {x : PGammaL2 F}
    (hx : x ∈ (T ⊓ pGammaL2PSLRange F) ⊔ zpowers v) (hx2 : orderOf x = 2) :
    ∃ k ∈ K, k * x * k⁻¹ = ι ∨ k * x * k⁻¹ = v ^ (orderOf v / 2) ∨
      k * x * k⁻¹ = v ^ (orderOf v / 2) * ι := by
  have hk : ∃ k ∈ K, IsFieldInvModel k := ⟨_, hT.1 (pow_mem hv.mem _), hv.field₀⟩
  obtain ⟨g, hgK, hTg, -⟩ := hH.exists_sylowShape hK hk hT
  have hv' := hv.conj_std hTg
  set c := MulAut.conj g⁻¹
  have hTc : T.map c.toMonoidHom = stdTS F K := by rw [hTg, map_conj_inv_map_conj]
  have hι' : c ι ∈ (stdTS F K ⊓ pGammaL2PSLRange F) ⊓
      centralizer ((stdTS F K ⊓ pGammaL2PSLRange F : Subgroup (PGammaL2 F)) :
        Set (PGammaL2 F)) := by
    have := Subgroup.mem_map_of_mem c.toMonoidHom hι
    rwa [map_inf_mulEquiv, map_inf_mulEquiv, map_centralizer_subgroup, map_inf_mulEquiv,
      pslRange_map_conj, hTc] at this
  have hx' : c x ∈ (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (c v) := by
    have := Subgroup.mem_map_of_mem c.toMonoidHom hx
    rwa [Subgroup.map_sup, map_inf_mulEquiv, pslRange_map_conj, hTc,
      map_zpowers_mulEquiv] at this
  obtain ⟨k', hk'K, hk'⟩ := hH.fusion_std hK hv' hι' (by rwa [MulEquiv.orderOf_eq])
    hx' (by rwa [MulEquiv.orderOf_eq])
  have hpow : c v ^ (orderOf (c v) / 2) = g⁻¹ * v ^ (orderOf v / 2) * g := by
    rw [MulEquiv.orderOf_eq, ← map_pow]
    simp [c]
  have hck : ∀ y : PGammaL2 F, c y = g⁻¹ * y * g := fun y => by
    simp [c]
  refine ⟨g * k' * g⁻¹, mul_mem (mul_mem hgK hk'K) (inv_mem hgK), ?_⟩
  have key : ∀ w : PGammaL2 F, k' * c x * k'⁻¹ = g⁻¹ * w * g →
      g * k' * g⁻¹ * x * (g * k' * g⁻¹)⁻¹ = w := by
    intro w hw
    rw [hck] at hw
    calc g * k' * g⁻¹ * x * (g * k' * g⁻¹)⁻¹ = g * (k' * (g⁻¹ * x * g) * k'⁻¹) * g⁻¹ := by
          group
      _ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hw]
      _ = w := by group
  rcases hk' with h | h | h
  · exact Or.inl (key _ (by rw [h, hck]))
  · exact Or.inr (Or.inl (key _ (by rw [h, hpow])))
  · refine Or.inr (Or.inr (key _ ?_))
    rw [h, hpow, hck]
    group

end CFSG.ComponentClassification.AutL2Facts
