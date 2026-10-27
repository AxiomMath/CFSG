module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthArith
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10RecConf

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.UnbalancedLayer CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
  (odd_orthogonal_involutions_conjugate_into_semilinear_image)

theorem exists_perfect_lift {K : Type} [Field K] {d : ℕ} {H : Subgroup (GL (Fin d) K)}
    {J : Subgroup (StatedProj H)} (hJ : ⁅J, J⁆ = J) :
    ∃ M : Subgroup (GL (Fin d) K), M ≤ H ∧ ⁅M, M⁆ = M ∧ (M.subgroupOf H).map (projH H) = J := by
  set C : Subgroup H := J.comap (projH H) with hC
  set D : Subgroup H := ⁅C, C⁆ with hD
  have hDJ : D.map (projH H) = J := by
    rw [hD, Subgroup.map_commutator, hC,
      Subgroup.map_comap_eq_self_of_surjective (projH_surjective (H := H)), hJ]
  have hCD : C = D ⊔ (projH H).ker := by
    apply le_antisymm
    · intro c hc
      obtain ⟨x, hx, hxc⟩ : projH H c ∈ D.map (projH H) := by rw [hDJ]; exact hc
      have hk : x⁻¹ * c ∈ (projH H).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxc, inv_mul_cancel]
      have : c = x * (x⁻¹ * c) := by group
      rw [this]
      exact mul_mem_sup hx hk
    · refine sup_le (commutator_le_self _) fun z hz => ?_
      rw [hC, mem_comap, MonoidHom.mem_ker.1 hz]
      exact one_mem _
  have hker : (projH H).ker ≤ center H := by
    rw [QuotientGroup.ker_mk']
    exact scalars_subgroupOf_le_center
  have hDD : ⁅D, D⁆ = D := by
    conv_rhs => rw [hD, hCD]
    exact (CatalogueBPrimeJoin.commutator_sup_central D _ hker).symm
  refine ⟨D.map H.subtype, map_subtype_le D, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hDD]
  · have e : (D.map H.subtype).subgroupOf H = D :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective D
    rw [e, hDJ]

theorem exists_conj_kappa {F : Type} [Field F] {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    {R : GL (Fin d) F}
    (hS₁ : ∀ v, oQ R (((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      ((1 : Fˣ) : F) * Q v)
    (h : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q) :
    ∀ α : MulAut (StatedProj (matrixDerived (oQ R))), α * α = 1 →
      ∃ (β : MulAut (StatedProj (matrixDerived (oQ R)))) (g : similarityPairs (oQ R)),
        β⁻¹ * α * β = oκ _ g := by
  intro α hα
  set Θ := oTransport 1 1 hS₁ with hΘ
  set α₀ := MulAut.congr Θ.symm α with hα₀
  have hα₀2 : α₀ * α₀ = 1 := by rw [hα₀, ← map_mul, hα, map_one]
  obtain ⟨β₀, g₀, hg₀⟩ := h α₀ hα₀2
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : MulAut (StatedProj (matrixDerived Q)), β₁ = β₀ := ⟨β₀, rfl⟩
  have hg₁ : oκ Q g₀ = β₁⁻¹ * α₀ * β₁ := by rw [hβ₁]; exact hg₀
  refine ⟨MulAut.congr Θ β₁, transPair 1 1 hS₁ g₀, ?_⟩
  rw [← oTransport_kappa, ← hΘ, hg₁, map_mul, map_mul, map_inv, hα₀]
  congr 2
  ext x
  simp

theorem card_of_conf_model {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) {p f : ℕ} (hp2 : p ≠ 2) {a : G} {J P₀ : Subgroup G}
    (ha : orderOf a = 2) (hJN : J ≤ N) (hJC : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p (2 * f))
    (hR : ∃ R : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ coreActionKernel J),
      (R : Subgroup _) = P₀.subgroupOf (centralizer ({a} : Set G) ⊓ coreActionKernel J))
    (hy : ∃ y ∈ P₀, Nat.card P₀ = 2 * orderOf y)
    {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hFc : Nat.card F = ℓ ^ e) {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) F}
    (hRs : (R : Matrix (Fin d) (Fin d) F)ᵀ = R) (hker : OKer (oQ R))
    (θ : N ≃* StatedProj (matrixDerived (oQ R)))
    (hconj : ∀ α : MulAut (StatedProj (matrixDerived (oQ R))), α * α = 1 →
      ∃ (β : MulAut (StatedProj (matrixDerived (oQ R)))) (g : similarityPairs (oQ R)),
        β⁻¹ * α * β = oκ _ g) :
    d = 8 ∧ Nat.card F ^ 4 = (p ^ f) ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, -⟩ := CFSG.GH74.Generic.lieModel_psl_data hJm
  obtain ⟨hα2, hα1⟩ := X10Rec.conjNormal_involutive hC ha
  set P := StatedProj (matrixDerived (oQ R)) with hP
  set α := MulAut.congr θ (MulAut.conjNormal a : MulAut N) with hαdef
  have hα2' : α * α = 1 := by rw [hαdef, ← map_mul, hα2, map_one]
  have hα1' : α ≠ 1 := fun h => hα1 ((MulAut.congr θ).injective (h.trans (map_one _).symm))
  obtain ⟨β, g, hg⟩ := hconj α hα2'
  set θ' : N ≃* P := θ.trans β.symm with hθ'
  have hcα : ∀ x, θ' (MulAut.conjNormal a x) = oκ _ g (θ' x) := fun x => by
    rw [← hg]
    change β.symm (θ (MulAut.conjNormal a x)) = β⁻¹ (α (β (β.symm (θ x))))
    rw [MulEquiv.apply_symm_apply, hαdef, MulAut.congr_apply]
    simp
  have hcongr : MulAut.congr θ' (MulAut.conjNormal a : MulAut N) = oκ _ g := by
    ext y
    change θ' (MulAut.conjNormal a (θ'.symm y)) = _
    rw [hcα, MulEquiv.apply_symm_apply]
  set J₀ := (J.subgroupOf N).map θ'.toMonoidHom with hJ₀
  obtain ⟨hJ₁X, hJ₁⟩ := X10Rec.fixed_pComponent_subgroupOf hJN hJC hJp
  obtain ⟨hJ₀X, hJ₀⟩ := CatFactsSp4.isPComponent_map_fixOf hcα hJ₁X hJ₁
  have hX := x10Hyp_of_conf hp2 ha hJN hJC hJm hR hy θ'
  rw [hcongr] at hX
  have hperf : ⁅J₀, J₀⁆ = J₀ := C.commutator_eq_of_isPComponent hJ₀X hJ₀
  obtain ⟨M, hMH, hMp, hMJ⟩ := exists_perfect_lift hperf
  have hdata : X10Data R g M ((p ^ f) ^ 2) := by
    refine ⟨hMH, hMp, ?_, ?_, ?_⟩
    · rw [hMJ]
      exact hJ₀X
    · rw [hMJ]
      exact hJ₀
    · rw [hMJ]
      exact hX
  have hss : oκ _ (g * g) = 1 := by
    rw [map_mul, ← hg]
    calc β⁻¹ * α * β * (β⁻¹ * α * β) = β⁻¹ * (α * α) * β := by group
      _ = 1 := by rw [hα2', mul_one, inv_mul_cancel]
  have hs1 : oκ _ g ≠ 1 := by
    rw [← hg]
    intro h1
    apply hα1'
    calc α = β * (β⁻¹ * α * β) * β⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hQ : Odd ((p ^ f) ^ 2) := ((hp.odd_of_ne_two hp2).pow).pow
  exact card_of_x10 hF hℓ he hFc hd hRs hker hss hs1 hdata hQ

theorem eq_sq_of_pow_four {x q : ℕ} (h : x ^ 4 = q ^ 2) : q = x ^ 2 := by
  have e : (x ^ 2) ^ 2 = q ^ 2 := by rw [← pow_mul]; exact h
  exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) e).symm

theorem cf81X10RowOrth : CF81X10RowOrth := by
  intro G _ _ N τ n p f' f hp hp2 hf hq hconf hτ hadm hmod
  obtain ⟨hNn, hC, -, a, -, J, K, P₀, ha, -, -, hJN, hJC, hJp, hJm, -, -, hR, hy, hKN, -, -, -,
    hKm⟩ := hconf
  have : N.Normal := hNn
  have hK2 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hKm
  have hKdvd : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card N :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hKN)
  have hx : Odd (p ^ f') := (hp.odd_of_ne_two hp2).pow
  have hfield : ∀ (F : Type) [Field F] [Finite F], Nat.card F = p ^ f' → ringChar F ≠ 2 := by
    intro F _ _ hFc
    have : Fintype F := Fintype.ofFinite F
    have : Fact p.Prime := ⟨hp⟩
    have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    rw [ringChar.eq F p]
    exact hp2
  have hx3 : ∀ f'', 1 ≤ f'' → 3 ≤ p ^ f'' := fun f'' h1 => by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    calc 3 ≤ p := h3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f'' := Nat.pow_le_pow_right hp.pos h1
  rcases hτ with rfl | rfl | rfl
  ·
    rcases hmod with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, hf', hn, -⟩, F, _, _, hFc, ⟨e⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n F)
      (regular_coordinateQuadOdd n F h2 hn).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadOdd n F v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinateOdd hmod F hFc e).transport 1 1 hS₁
    have hconj := exists_conj_kappa hS₁ fun α hα =>
      odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaOdd (Or.inl rfl) hmod F
        hFc e α hα
    obtain ⟨hd8, -⟩ := card_of_conf_model hC hp2 ha hJN hJC hJp hJm hR hy hF hp hf' hFc
      (by omega) hRs hker ((coordinateOddWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hconj
    omega
  ·
    rcases hmod with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, hf', hn⟩, F, _, _, hFc, ⟨e⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n F)
      (regular_coordinateQuadPlus n F (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadPlus n F v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinatePlus hmod F hFc e).transport 1 1 hS₁
    have hconj := exists_conj_kappa hS₁ fun α hα =>
      (odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaPlus
        (Or.inr (Or.inl rfl)) hmod F hFc e).1 α hα
    obtain ⟨hd8, hF4⟩ := card_of_conf_model hC hp2 ha hJN hJC hJp hJm hR hy hF hp hf' hFc
      (by omega) hRs hker ((coordinatePlusWitnessEquiv F e).trans (oTransport 1 1 hS₁)) hconj
    obtain rfl : n = 4 := by omega
    rw [hFc, ← pow_mul] at hF4
    have hqx := eq_sq_of_pow_four (x := p ^ f') (by rw [← pow_mul]; exact hF4)
    rw [hqx] at hK2
    have hN := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hmod).2.2.2.2.1 rfl
    rw [hN] at hKdvd
    exact not_dvd_ordD_four hx (hx3 f' hf') hK2 hKdvd
  ·
    rcases hmod with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    swap
    · exact absurd htag (by decide)
    have hmod := hc
    obtain ⟨⟨-, hf', hn⟩, F, _, _, hFc, b, c, hirr, ⟨e⟩⟩ := hc
    have hF := hfield F hFc
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have hn1 : 1 ≤ n := by omega
    obtain ⟨R, hRs, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n F hn1 b c)
      (regular_coordinateQuadMinus n F b c hn hirr).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) F) : Matrix _ _ F) *ᵥ v) =
        ((1 : Fˣ) : F) * coordinateQuadMinus n F hn1 b c v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := (oKer_coordinateMinus hmod F hFc b c hirr e).transport 1 1 hS₁
    have hconj := exists_conj_kappa hS₁ fun α hα =>
      odd_orthogonal_involutions_conjugate_into_semilinear_image .POmegaMinus
        (Or.inr (Or.inr rfl)) hmod hn1 F hFc b c hirr e α hα
    obtain ⟨hd8, hF4⟩ := card_of_conf_model hC hp2 ha hJN hJC hJp hJm hR hy hF hp hf' hFc
      (by omega) hRs hker ((coordinateMinusWitnessEquiv F hn1 b c e).trans
        (oTransport 1 1 hS₁)) hconj
    obtain rfl : n = 4 := by omega
    rw [hFc, ← pow_mul] at hF4
    have hqx := eq_sq_of_pow_four (x := p ^ f') (by rw [← pow_mul]; exact hF4)
    rw [hqx] at hK2
    have hN := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hmod).2.2.2.2.2 rfl
    rw [hN] at hKdvd
    exact not_dvd_ordTwistedD_four hx (hx3 f' hf') hK2 hKdvd

end CFSG.ComponentClassification.GSThmB.X10Orth
