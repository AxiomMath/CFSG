module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeIVFactsFrobenius

public section

namespace CFSG.Wreathed.OriginalAllPrime.IVFacts

open CFSG.ABGTheoremB CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.OddFieldTorus CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

variable {G : Type} [Group G]

theorem isSylowOf_map_hom [Finite G] {G' : Type*} [Group G'] {r : ℕ} [Fact r.Prime]
    {R K : Subgroup G} (f : G →* G') (h : IsSylowOf r R K) : IsSylowOf r (R.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

namespace IsWModel

variable {σ : Setting G} {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ}
  {hm : 0 < m} {heven : Even m} {Sigma : Subgroup (F ≃+* F)}
  {hSigma : ∀ τ ∈ Sigma, τ (b : F) = b}
  {φ : σ.N →* SemilinearExtension F b m hm heven Sigma hSigma}

theorem isSylowOf_map [Finite G] (hW : IsWModel σ φ) {r : ℕ} [Fact r.Prime] {P : Subgroup G}
    (hP : IsSylowOf r P σ.C) :
    IsSylowOf r ((P.subgroupOf σ.N).map φ) (ModelSignalizers.modelC b m hm heven Sigma hSigma) := by
  have hCN : σ.C ≤ σ.N := TIFacts.C_le_N σ
  have hP' : IsSylowOf r (P.subgroupOf σ.N) (σ.C.subgroupOf σ.N) := by
    rw [← isSylowOf_map_subtype_iff, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hP.le.trans hCN), inf_eq_left.mpr hCN]
    exact hP
  have h := isSylowOf_map_hom φ hP'
  rwa [hW.model.map_C] at h

theorem mem_map_W_of_odd (hW : IsWModel σ φ) {W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hW' : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g))
    {x : SemilinearExtension F b m hm heven Sigma hSigma}
    (hxC : x ∈ ModelSignalizers.modelC b m hm heven Sigma hSigma)
    (hxB : x ∈ ModelSignalizers.modelBase b m hm heven Sigma hSigma) (hodd : Odd (orderOf x)) :
    x ∈ W.map (iota b m hm heven Sigma hSigma) := by
  obtain ⟨v, rfl⟩ := hxB
  have hvC : v ∈ Subgroup.centralizer {yV b m hm heven} := by
    rw [ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff, modelY_eq_inl_yV,
      ← map_mul, ← map_mul] at hxC
    exact Subgroup.mem_centralizer_singleton_iff.mpr (SemidirectProduct.inl_injective hxC)
  have hvodd : Odd (orderOf v) := by
    rwa [orderOf_injective _ SemidirectProduct.inl_injective] at hodd
  obtain ⟨w, hw, rfl⟩ := exists_eq_iF_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' hvC hvodd
  exact ⟨w, hw, rfl⟩

omit [Fintype F] in
theorem map_W_le_modelC {W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hW' : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g)) :
    W.map (iota b m hm heven Sigma hSigma) ≤ ModelSignalizers.modelC b m hm heven Sigma hSigma := by
  rintro _ ⟨w, hw, rfl⟩
  have hwT : w * weyl F = weyl F * w := Subgroup.mem_centralizer_singleton_iff.mp ((hW' w).mp hw).1
  rw [ModelSignalizers.modelC, Subgroup.mem_centralizer_singleton_iff]
  have h := modelY_conj_iota b m hm heven Sigma hSigma w
  rw [← hwT, mul_inv_cancel_right] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem modelC_le_normalizer_map_W (hW : IsWModel σ φ)
    {W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hW' : ∀ g, g ∈ W ↔ g ∈ torus F ∧ Odd (orderOf g)) :
    ModelSignalizers.modelC b m hm heven Sigma hSigma ≤
      Subgroup.normalizer ((W.map (iota b m hm heven Sigma hSigma) : Subgroup _) : Set _) := by
  intro c hc
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨w, hw, rfl⟩
  have hxC : iota b m hm heven Sigma hSigma w ∈ ModelSignalizers.modelC b m hm heven Sigma hSigma :=
    map_W_le_modelC hW' ⟨w, hw, rfl⟩
  apply hW.mem_map_W_of_odd hW'
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxC) (Subgroup.inv_mem _ hc)
  · exact modelBase_normal.conj_mem _ ⟨_, rfl⟩ c
  · rw [show c * iota b m hm heven Sigma hSigma w * c⁻¹ =
        MulAut.conj c (iota b m hm heven Sigma hSigma w) from rfl, MulEquiv.orderOf_eq,
      orderOf_injective _ (iota_injective b m hm heven Sigma hSigma)]
    exact ((hW' w).mp hw).2

theorem center_le_L_or_inf_L_le [Finite G] (hW : IsWModel σ φ) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G,
      IsSylowOf r P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
        centerOf P ≤ σ.L ∨ P ⊓ σ.L ≤ σ.ON := by
  intro r hr hrON P hP _
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn σ.N)) (even_iff_two_dvd.mpr hrON)
  by_cases hPL : P ⊓ σ.L ≤ σ.ON
  · exact Or.inr hPL
  left
  obtain ⟨g, ⟨hgP, hgL⟩, hgON⟩ := Set.not_subset.mp hPL
  have hPC : P ≤ σ.C := hP.le
  have hCN : σ.C ≤ σ.N := TIFacts.C_le_N σ
  obtain ⟨W, hW'⟩ := exists_oddTorus F
  set Pb := (P.subgroupOf σ.N).map φ with hPb
  set Wb := W.map (iota b m hm heven Sigma hSigma) with hWb
  have hSyl : IsSylowOf r (Pb ⊓ Wb) Wb :=
    (hW.isSylowOf_map hP).inf_of_le_normalizer (map_W_le_modelC hW')
      (hW.modelC_le_normalizer_map_W hW')
  have hWb : Nat.card Wb = Nat.card W :=
    Subgroup.card_map_of_injective (iota_injective b m hm heven Sigma hSigma)
  have hcard : Nat.card (Pb ⊓ Wb : Subgroup _) = r ^ (Nat.card W).factorization r := by
    rw [hSyl.card_eq, hWb]
  have hPodd : ∀ x ∈ P, ∃ hxN : x ∈ σ.N, Odd (orderOf (φ ⟨x, hxN⟩)) := by
    intro x hx
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨x, hx⟩
    exact ⟨hCN (hPC hx), odd_orderOf_map hr hr2 ⟨x, hCN (hPC hx)⟩
      (by simpa using congrArg Subtype.val hk)⟩
  obtain ⟨hgN, hgodd⟩ := hPodd g hgP
  have hgmem : φ ⟨g, hgN⟩ ∈ Pb ⊓ Wb :=
    ⟨⟨⟨g, hgN⟩, hgP, rfl⟩, hW.mem_map_W_of_odd hW' (hW.map_mem_modelC ⟨g, hgN⟩ (hPC hgP))
      ((hW.mem_L_iff ⟨g, hgN⟩).mp hgL) hgodd⟩
  have hg1 : φ ⟨g, hgN⟩ ≠ 1 := fun h => hgON ((hW.mem_ON_iff ⟨g, hgN⟩).mpr h)
  have hv1 : 1 ≤ (Nat.card W).factorization r := by
    by_contra h0
    have h0' : (Nat.card W).factorization r = 0 := by omega
    rw [h0', pow_zero] at hcard
    have := Subgroup.eq_bot_of_card_eq _ hcard
    exact hg1 (by rw [this] at hgmem; exact hgmem)
  intro z hz
  obtain ⟨hzP, hzc⟩ := hz
  obtain ⟨hzN, hzodd⟩ := hPodd z hzP
  obtain ⟨w₁, hw₁W, τ, hτ⟩ := exists_eq_of_odd hW.p_prime hW.p_odd hW.one_le_f hW.card hm heven
    hW.two_part hW.sigma_odd hSigma hW.nonsquare hW' (hW.map_mem_modelC ⟨z, hzN⟩ (hPC hzP)) hzodd
  have hw₁T : w₁ ∈ torus F := ((hW' w₁).mp hw₁W).1
  rw [hW.mem_L_iff ⟨z, hzN⟩, hτ]
  by_contra hτ1
  have hτne : τ ≠ 1 := by
    rintro rfl
    apply hτ1
    rw [map_one, mul_one, iota_apply]
    exact ⟨_, rfl⟩
  have hτpow : ∃ j : ℕ, orderOf (τ : F ≃+* F) = r ^ j := by
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨z, hzP⟩
    have hk' : (⟨z, hzN⟩ : σ.N) ^ r ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 := congrArg (fun x => SemidirectProduct.rightHom (φ x)) hk'
    simp only [map_pow, map_one, hτ, map_mul, iota_apply, SemidirectProduct.rightHom_inl,
      SemidirectProduct.rightHom_inr, one_mul] at h1
    rw [Subgroup.orderOf_coe]
    exact (Nat.dvd_prime_pow hr).mp (orderOf_dvd_of_pow_eq_one h1) |>.imp fun _ h => h.2
  obtain ⟨j, hj⟩ := hτpow
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hτne (Subtype.ext hj)
  set τ' : F ≃+* F := (τ : F ≃+* F) ^ r ^ (j - 1) with hτ'
  have hτ'mem : τ' ∈ Sigma := Sigma.pow_mem τ.2 _
  have hτ'r : orderOf τ' = r := by
    rw [hτ', orderOf_pow_of_dvd (pow_ne_zero _ hr.ne_zero), hj]
    · rw [Nat.pow_div (Nat.sub_le j 1) hr.pos, show j - (j - 1) = 1 by omega, pow_one]
    · rw [hj]
      exact pow_dvd_pow r (by omega)
  set A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    W ⊓ (Pb ⊓ Wb).comap (iota b m hm heven Sigma hSigma) with hA
  have hAmap : A.map (iota b m hm heven Sigma hSigma) = Pb ⊓ Wb := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := hx.2
      exact ⟨w, ⟨hw, hx⟩, rfl⟩
  have hAcard : Nat.card A = r ^ (Nat.card W).factorization r := by
    rw [← hcard, ← hAmap, Subgroup.card_map_of_injective (iota_injective b m hm heven Sigma hSigma)]
  have hAfix : A ≤ fixedW W τ' := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    have hwT : w ∈ torus F := ((hW' w).mp hw.1).1
    obtain ⟨⟨y, hyP, hyw⟩, -⟩ := hw.2
    have hc : φ ⟨z, hzN⟩ * iota b m hm heven Sigma hSigma w *
        (φ ⟨z, hzN⟩)⁻¹ = iota b m hm heven Sigma hSigma w := by
      rw [← hyw]
      have hyz : (⟨z, hzN⟩ : σ.N) * y = y * ⟨z, hzN⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc y (Subgroup.mem_subgroupOf.mp hyP)).symm
      rw [← map_mul, hyz, map_mul, mul_inv_cancel_right]
    rw [hτ, conj_iota_of_mem_torus b m hm heven Sigma hSigma τ hw₁T hwT] at hc
    have hτw : fieldSL F τ w = w := iota_injective b m hm heven Sigma hSigma hc
    exact fieldSL_pow_eq hτw _
  have hdvd : r ^ (Nat.card W).factorization r ∣ Nat.card (fixedW W τ') := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le hAfix
  have hcontra := pow_succ_dvd_card_W hW.p_prime hW.p_odd hW.one_le_f hW.card hW.two_part
    hW.sigma_odd hW' τ' hτ'mem hr hr2 hτ'r hv1 hdvd
  exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hr hcontra

end IsWModel

end CFSG.Wreathed.OriginalAllPrime.IVFacts
