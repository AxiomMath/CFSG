module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisCommon

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F] {K : Subgroup (PGammaL2 F)}

theorem isFieldInvModel_mul (hodd : IsOddPrimePower (Nat.card F)) {k ι : PGammaL2 F}
    (hk : IsFieldInvModel k) (hι : ι ∈ pGammaL2PSLRange F) (h2 : (ι * k) ^ 2 = 1) :
    IsFieldInvModel (ι * k) := by
  have hr : (ι * k).right ≠ 1 := by
    rw [SemidirectProduct.mul_right, ((mem_pslRange_iff ι).mp hι).1, one_mul]
    exact hk.right_ne_one
  refine isFieldInvModel_of_involution hodd (orderOf_eq_prime h2 fun h => hr ?_) hr
  rw [h]
  rfl

theorem HarrisHyp.card_le_of_le_pslRange (hH : HarrisHyp F) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) (hPL : P ≤ pGammaL2PSLRange F) : Nat.card P ≤ 2 ^ twoVal F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (P.comap (incl F)).map (incl F) = P := Subgroup.map_comap_eq_self hPL
  have h2 : IsPGroup 2 (P.comap (incl F)) := hP.comap_of_injective _ (incl_injective F)
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  rw [← hmap, Subgroup.card_map_of_injective (incl_injective F),
    ← card_sylow_eq hH.odd hH.sq hH.q4 S]
  exact Subgroup.card_le_of_le hS

theorem HarrisHyp.card_le_core (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {k : PGammaL2 F} (hkK : k ∈ K) (hk : IsFieldInvModel k) {Q : Subgroup (PGammaL2 F)}
    (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) (hQC : Q ≤ centralizer {k}) :
    Nat.card Q ≤ Nat.card (stdTS F K ⊓ centralizer {v0Std F} : Subgroup (PGammaL2 F)) := by
  obtain ⟨p, f, hp, hp2, hF, -⟩ := hH.char
  have hRH : rStd F ≤ stdTS F K ⊓ centralizer {v0Std F} := by
    rw [hH.stdTS_inf_centralizer_v0Std hK]
    exact le_sup_left
  rw [card_eq_linearPart_mul Q, card_eq_linearPart_mul (stdTS F K ⊓ centralizer {v0Std F})]
  apply Nat.mul_le_mul
  ·
    have hk2 : k * k = 1 := by
      obtain ⟨b, σ, hσ, rfl⟩ := hk
      have : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
      calc b * SemidirectProduct.inr σ * b⁻¹ * (b * SemidirectProduct.inr σ * b⁻¹) =
          b * SemidirectProduct.inr (σ * σ) * b⁻¹ := by rw [map_mul]; group
        _ = 1 := by rw [this, map_one, mul_one, mul_inv_cancel]
    have hQL : (linearPart Q).map SemidirectProduct.inl ≤ pGammaL2PSLRange F := by
      rintro _ ⟨g, hg, rfl⟩
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hQC hg)
      exact mem_pslRange_of_commute_fieldInv hp hp2 hF k hk2 hk.right_ne_one g hc.symm
    have h1 : Nat.card (linearPart Q) ≤ 2 ^ twoVal F := by
      rw [← Subgroup.card_map_of_injective
        (f := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) SemidirectProduct.inl_injective]
      exact hH.card_le_of_le_pslRange (IsPGroup.to_le (H := (linearPart Q).map
        SemidirectProduct.inl) hQ (by rintro _ ⟨g, hg, rfl⟩; exact hg)) hQL
    have h2 : Nat.card (rStd F) ≤
        Nat.card (linearPart (stdTS F K ⊓ centralizer {v0Std F})) := by
      have hR : (linearPart (rStd F)).map SemidirectProduct.inl = rStd F := by
        apply Subgroup.map_comap_eq_self
        rintro _ ⟨t, -, rfl⟩
        exact ⟨_, rfl⟩
      rw [← hR, Subgroup.card_map_of_injective
        (f := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)) SemidirectProduct.inl_injective]
      exact Subgroup.card_le_of_le (Subgroup.comap_mono hRH)
    rw [card_rStd hH] at h2
    exact h1.trans h2
  ·
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, σ, hσ, hkb⟩ := hk
    have hσψ : σ = psiF F := hH.eq_psiF_of_orderOf hσ
    subst hσψ
    set y := b⁻¹ * x * b
    have hyK : y ∈ K := by
      have := conj_mem_of_pslRange_le hK b⁻¹ (hQK hx)
      rwa [inv_inv] at this
    have hyr : y.right = x.right := by
      have := right_conj b⁻¹ x
      rwa [inv_inv] at this
    have hyc : y * SemidirectProduct.inr (psiF F) = SemidirectProduct.inr (psiF F) * y := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hQC hx)
      rw [hkb] at hc
      have : b⁻¹ * (x * (b * SemidirectProduct.inr (psiF F) * b⁻¹)) * b =
          b⁻¹ * ((b * SemidirectProduct.inr (psiF F) * b⁻¹) * x) * b := by rw [hc]
      simp only [y]
      calc b⁻¹ * x * b * SemidirectProduct.inr (psiF F) =
          b⁻¹ * (x * (b * SemidirectProduct.inr (psiF F) * b⁻¹)) * b := by group
        _ = b⁻¹ * ((b * SemidirectProduct.inr (psiF F) * b⁻¹) * x) * b := this
        _ = SemidirectProduct.inr (psiF F) * (b⁻¹ * x * b) := by group
    have hleft : (SemidirectProduct.inr (psiF F) : PGammaL2 F) *
        SemidirectProduct.inl y.left = SemidirectProduct.inl y.left *
          SemidirectProduct.inr (psiF F) := by
      have h1 := congrArg SemidirectProduct.left hyc
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, map_one, mul_one, one_mul] at h1
      apply SemidirectProduct.ext
      · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
          SemidirectProduct.left_inl, SemidirectProduct.right_inr, one_mul,
          SemidirectProduct.right_inl, map_one, mul_one]
        exact h1.symm
      · simp
    have hψψ : (SemidirectProduct.inr (psiF F) : PGammaL2 F) * SemidirectProduct.inr (psiF F) =
        1 := by rw [← map_mul, hH.psiF_mul_self, map_one]
    have hL := mem_pslRange_of_commute_fieldInv hp hp2 hF _ hψψ (by simp [hH.psiF_ne_one])
      y.left hleft
    have hinr : SemidirectProduct.inr y.right ∈ K := by
      have : SemidirectProduct.inr y.right = (SemidirectProduct.inl y.left)⁻¹ * y := by
        rw [eq_inv_mul_iff_mul_eq, SemidirectProduct.inl_left_mul_inr_right]
      rw [this]
      exact mul_mem (inv_mem (hK hL)) hyK
    have hgal : x.right ∈ galTwo F := by
      obtain ⟨j, hj⟩ := hQ ⟨x, hx⟩
      refine ⟨j, ?_⟩
      have h1 : x ^ 2 ^ j = 1 := by
        have := congrArg Subtype.val hj
        simpa using this
      rw [← right_pow, h1]
      rfl
    refine ⟨SemidirectProduct.inr x.right, ⟨⟨⟨1, one_mem _, false, x.right, hgal, ?_⟩,
      hyr ▸ hinr⟩, ?_⟩, rfl⟩
    · exact (nm_one_false _).symm
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [← nm_one_false]
      exact (hH.commute_v0Std_iff (one_mem _) false x.right).mpr (one_mem _)

theorem HarrisHyp.card_le_of_centralizer (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {T : Subgroup (PGammaL2 F)} (hT : IsSylowIn T K) {v : PGammaL2 F}
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel T v)
    {k : PGammaL2 F} (hkK : k ∈ K) (hk : IsFieldInvModel k) {Q : Subgroup (PGammaL2 F)}
    (hQK : Q ≤ K) (hQ : IsPGroup 2 Q) (hQC : Q ≤ centralizer {k}) :
    Nat.card Q ≤ Nat.card ((T ⊓ pGammaL2PSLRange F) ⊔ zpowers v : Subgroup (PGammaL2 F)) := by
  obtain ⟨g, hgK, hTg, -⟩ := hH.exists_sylowShape hK ⟨k, hkK, hk⟩ hT
  have hv' := hv.conj_std hTg
  set c := MulAut.conj g⁻¹
  have hQ' : Q.map c.toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    have := conj_mem_of_pslRange_le hK g⁻¹ (hQK hx)
    simpa [c, MulAut.conj_apply] using this
  have hk' : c k ∈ K := by
    have := conj_mem_of_pslRange_le hK g⁻¹ hkK
    simpa [c, MulAut.conj_apply] using this
  have hQC' : Q.map c.toMonoidHom ≤ centralizer {c k} := by
    rw [← map_centralizer_singleton]
    exact Subgroup.map_mono hQC
  have h1 := hH.card_le_core hK hk' ((isFieldInvModel_conj_iff g⁻¹ k).mp hk) hQ' (hQ.map _) hQC'
  rw [card_map_mulEquiv, ← hH.sup_eq_of_shape hK hv'] at h1
  have h2 : ((T ⊓ pGammaL2PSLRange F) ⊔ zpowers v).map c.toMonoidHom =
      (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers (c v) := by
    rw [Subgroup.map_sup, map_inf_mulEquiv, map_zpowers_mulEquiv, pslRange_map_conj, hTg,
      map_conj_inv_map_conj]
  rw [← h2, card_map_mulEquiv] at h1
  exact h1

end CFSG.ComponentClassification.AutL2Facts
