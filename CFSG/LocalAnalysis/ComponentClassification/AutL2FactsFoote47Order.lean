module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Inputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Involution

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup Equiv

theorem sixteen_dvd_pow_four_sub_one {a : ℕ} (ha : Odd a) : 16 ∣ a ^ 4 - 1 := by
  have h1 : a ^ 4 % 16 = 1 := by
    rw [Nat.pow_mod]
    have hlt : a % 16 < 16 := Nat.mod_lt _ (by norm_num)
    have hodd : a % 16 % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 16)]
      exact Nat.odd_iff.mp ha
    interval_cases h : a % 16 <;> simp_all
  have h2 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at ha))
  omega

theorem sq_mem_inn_of_a7 {S : Type} [Group S] (e : S ≃* alternatingGroup (Fin 7))
    (x : MulAut S) : x ^ 2 ∈ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨π, hπ⟩ := exists_a7Conj_eq (MulAut.congr e x)
  have hmem : π ^ 2 ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, map_pow, Int.units_sq]
  refine ⟨e.symm ⟨π ^ 2, hmem⟩, (MulAut.congr e).injective ?_⟩
  rw [congr_conj_eq, MulEquiv.apply_symm_apply, map_pow, ← hπ, ← map_pow a7Conj π 2,
    a7Conj_of_mem hmem]

variable {F : Type} [Field F] [Finite F]

theorem HarrisHyp.right_mul_self_of_centralizes (hH : HarrisHyp F) (T : Sylow 2 (PSL2 F))
    {g : PGammaL2 F} {k : ℕ} (hk : orderOf g = 2 ^ k)
    (hg : ∀ t ∈ (T : Subgroup (PSL2 F)), g * incl F t = incl F t * g) :
    g.right * g.right = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hH.odd hH.sq hH.q4) T
  obtain ⟨x', hx'⟩ : ∃ x', x' = (incl F h)⁻¹ * g * incl F h := ⟨_, rfl⟩
  have hxC : ∀ g' ∈ rStd F, g' * x' = x' * g' := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : h * t * h⁻¹ ∈ (T : Subgroup (PSL2 F)) := by
      rw [← hh, mem_smul_sylow_iff_conj, coe_stdSylow,
        show h⁻¹ * (h * t * h⁻¹) * h = t by group]
      exact ht
    have h2 := hg _ h1
    rw [map_mul, map_mul, map_inv] at h2
    rw [hx']
    calc incl F t * ((incl F h)⁻¹ * g * incl F h)
        = (incl F h)⁻¹ * (incl F h * incl F t * (incl F h)⁻¹ * g) * incl F h := by group
      _ = (incl F h)⁻¹ * (g * (incl F h * incl F t * (incl F h)⁻¹)) * incl F h := by
        rw [← h2]
      _ = (incl F h)⁻¹ * g * incl F h * incl F t := by group
  have hR2 : IsPGroup 2 (rStd F) := by
    have := (stdSylow F hH.odd hH.sq hH.q4).isPGroup'
    rw [coe_stdSylow] at this
    exact this.map _
  have hox : orderOf x' = 2 ^ k := by
    rw [← hk, hx', ← (MulAut.conj (incl F h)⁻¹).orderOf_eq g, MulAut.conj_apply, inv_inv]
  have hx2 : IsPGroup 2 (zpowers x') := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hox])
  have hQ : IsPGroup 2 ↥(rStd F ⊔ zpowers x') := by
    refine IsPGroup.to_sup_of_normal_left' hR2 hx2 ?_
    rw [zpowers_le]
    exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr hxC)
  have hsyl : x' ∈ sylS0 F := hH.le_sylS0 hQ le_sup_left (mem_sup_right (mem_zpowers x'))
  obtain ⟨s, -, hs⟩ := hH.eq_of_centralizes_rStd hsyl hxC
  have hright : x'.right = g.right := by
    have := right_conj (incl F h)⁻¹ g
    rwa [inv_inv, ← hx'] at this
  rw [← hright]
  rcases hs with hs | hs <;> rw [hs, nm_right]
  · exact mul_one 1
  · exact hH.psiF_mul_self

theorem cfFoote47OuterOrderFour : Foote47.Foote47OuterOrderFour := by
  intro S _ _ hS R x ⟨k, hk⟩ h4 hinn _
  have hsq : x ^ 2 ∉ (MulAut.conj : S →* MulAut S).range := by
    intro h
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hinn 2 h))
    omega
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, -, -, hL⟩
  · exact absurd (sq_mem_inn_of_a7 e x) hsq
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hInn : (MulAut.conj : S →* MulAut S).range.map (autEquiv e).toMonoidHom =
      pGammaL2PSLRange F := map_autEquiv_innAut e
  have hσ : (autEquiv e x).right * (autEquiv e x).right ≠ 1 := by
    intro h1
    apply hsq
    have hmem : autEquiv e x * autEquiv e x ∈ pGammaL2PSLRange F := by
      rw [mem_pslRange_iff, sqLeft_mul]
      exact ⟨by rw [SemidirectProduct.mul_right]; exact h1, Iff.rfl⟩
    rw [← hInn] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x ^ 2 := by
      apply (autEquiv e).injective
      rw [pow_two, map_mul]
      exact hyx
    rw [← this]
    exact hy
  have hord : orderOf (autEquiv e x) = 2 ^ k := by rw [MulEquiv.orderOf_eq]; exact hk
  have hσdvd : orderOf (autEquiv e x).right ∣ 2 ^ k := by
    rw [← hord]
    exact orderOf_map_dvd SemidirectProduct.rightHom _
  obtain ⟨j, -, hσj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hσdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    apply hσ
    rw [← pow_two]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hσj]
    exact (Nat.pow_dvd_pow 2 (show j ≤ 1 by omega)).trans (by norm_num)
  obtain ⟨m, hm⟩ : 4 ∣ f := by
    have h1 := orderOf_dvd_natCard (autEquiv e x).right
    rw [card_ringAut F hp hF, hσj] at h1
    exact (Nat.pow_dvd_pow 2 hj2).trans h1
  have h16 : 16 ∣ p ^ f - 1 := by
    rw [hm, mul_comm, pow_mul]
    exact sixteen_dvd_pow_four_sub_one (hp.odd_of_ne_two hp2).pow
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF ⟨2 * m, by omega⟩ h16
  by_contra hcon
  push Not at hcon
  apply hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hH.right_mul_self_of_centralizes (R.mapSurjective (f := e.toMonoidHom) e.surjective)
    hord ?_
  rintro _ ⟨r, hr, rfl⟩
  have h1 : x * MulAut.conj r * x⁻¹ = MulAut.conj r := by
    rw [mulAut_conj_conj, hcon r hr]
  have h2 : x * MulAut.conj r = MulAut.conj r * x := by
    calc x * MulAut.conj r = x * MulAut.conj r * x⁻¹ * x := by group
      _ = MulAut.conj r * x := by rw [h1]
  change autEquiv e x * incl F (e r) = incl F (e r) * autEquiv e x
  rw [← autEquiv_conj, ← map_mul, ← map_mul, h2]

end CFSG.ComponentClassification.AutL2Facts
