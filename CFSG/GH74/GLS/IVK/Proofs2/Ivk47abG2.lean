module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abCh6
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2Native
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47eOmega
public import CFSG.GH74.GLS.IVK.Statements.Sec4d
public import CFSG.GH74.GLS.IVK.Statements.Sec9b
public import CFSG.LieType.HighestRoot.CentG2Main

public noncomputable section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.RankThree.PartOne CFSG.Blueprint
  CFSG.Blueprint.Chevalley Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47 (untwisted_of_lieModel_G2)

open scoped MatrixGroups

theorem odd_card_of_model {F : Type} [Field F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card F = p ^ f) : Odd (Nat.card F) := by
  rw [hcard]
  exact (hp.odd_of_ne_two hp2).pow

theorem isConj_of_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {x y : A}
    (h : IsConj (φ x) (φ y)) : IsConj x y := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨φ.symm c, φ.injective ?_⟩
  simpa [map_mul, map_inv] using hc

section G2


@[expose] def equivAdjointQuotient (F : Type) [Field F] [Finite F] :
    AdjointQuotient .G2 F ≃* G2g F :=
  (QuotientGroup.quotientMulEquivOfEq (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot)).trans
    QuotientGroup.quotientBot

theorem exists_equiv_of_lieModel {M : Type} [Group M] {p f : ℕ} (hM : LieModel M .G2 0 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧ Nonempty (M ≃* G2g F) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := untwisted_of_lieModel_G2 hM
  exact ⟨F, hF, hFin, hcard, ⟨e.trans (equivAdjointQuotient F)⟩⟩

theorem lieModel_G2g {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h3 : 3 ≤ p ^ f) (hcard : Nat.card F = p ^ f) : LieModel (G2g F) .G2 0 p f :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨hp, hf, rfl, h3⟩, F, inferInstance, inferInstance, hcard,
    ⟨(equivAdjointQuotient F).symm⟩⟩)

theorem ivk_4_7a_G2_aux {K : Type} [Group K] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : LieModel K .G2 0 p n) (z z' : K) (hz : orderOf z = 2) (hz' : orderOf z' = 2) :
    IsConj z z' := by
  obtain ⟨F, _, _, hcard, ⟨φ⟩⟩ := exists_equiv_of_lieModel hK
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card (odd_card_of_model hp hp2 hcard)
  exact isConj_of_equiv φ (CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (φ z) (φ z')
    (by rw [MulEquiv.orderOf_eq]; exact hz) (by rw [MulEquiv.orderOf_eq]; exact hz'))

theorem ivk_4_7ab_G2_aux {M : Type} [Group M] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (hM : LieModel M .G2 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (K₁ K₂ : Subgroup M) (F : Type) (_ : Field F) (_ : Finite F) (t : M),
      Nat.card F = p ^ f ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) ∧ z ∈ K₁ ∧ z ∈ K₂ ∧
        K₁ ⊓ K₂ = Subgroup.zpowers z ∧ Ch6Rem z K₁ K₂ F F t := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := exists_equiv_of_lieModel hM
  have hodd : Odd (Nat.card F) := odd_card_of_model hp hp2 hcard
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have h4 : 4 ≤ Nat.card F := by rw [hcard]; omega
  have hconj : IsConj (φ z) (z₀ F) :=
    CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (φ z) (z₀ F)
      (by rw [MulEquiv.orderOf_eq]; exact hz) (orderOf_z₀ hchar)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let ψ : M ≃* G2g F := φ.trans (MulAut.conj c)
  have hψz : ψ z = z₀ F := by simpa [ψ] using hc
  have hzz : ψ.symm (z₀ F) = z := by rw [← hψz, MulEquiv.symm_apply_apply]
  obtain ⟨S, hS⟩ := exists_native_shape hodd
  obtain ⟨K₁, K₂, t, hcomm, hz₁, hz₂, hinter, hRem⟩ :=
    Shape.exists_ch6Rem (z := z₀ F) S (by rw [hS]; rfl) h4 h4
  have key := ch6Data_map ψ.symm ⟨hcomm, hz₁, hz₂, hinter, hRem⟩
  rw [hzz] at key
  exact ⟨K₁.map ψ.symm.toMonoidHom, K₂.map ψ.symm.toMonoidHom, F, hF, hFin, ψ.symm t, hcard, key⟩

theorem isInvolutionCentralizerOfModel_G2_of_shape' {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 ≤ p ^ f) (h₁ : Nat.card F₁ = p ^ f) (h₂ : Nat.card F₂ = p ^ f) :
    IsInvolutionCentralizerOfModel ↥(oPrimeResidual 2 Y) .G2 p f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h3
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_card_of_model hp hp2 hcard
  have hchar : ringChar (GaloisField p f) ≠ 2 := ringChar_ne_two_of_odd_card hodd
  obtain ⟨S', -⟩ := exists_native_shape hodd
  have hσ₁ : Nat.card F₁ = Nat.card (GaloisField p f) := h₁.trans hcard.symm
  have hσ₂ : Nat.card F₂ = Nat.card (GaloisField p f) := h₂.trans hcard.symm
  obtain ⟨e⟩ := S.exists_mulEquiv S'
    (by
      have := Fintype.ofFinite F₁
      have := Fintype.ofFinite (GaloisField p f)
      exact FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card]))
    (by
      have := Fintype.ofFinite F₂
      have := Fintype.ofFinite (GaloisField p f)
      exact FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card]))
  obtain ⟨e₂⟩ := oPrimeResidual_mulEquiv 2 e
  exact ⟨G2g (GaloisField p f), inferInstance, z₀ (GaloisField p f),
    lieModel_G2g hp (Nat.one_le_iff_ne_zero.2 hf0) h3 hcard, orderOf_z₀ hchar,
    ⟨e₂.trans (Subgroup.equivMapOfInjective _
      (Subgroup.centralizer ({z₀ (GaloisField p f)} : Set (G2g (GaloisField p f)))).subtype
      Subtype.val_injective)⟩⟩

theorem isInvolutionCentralizerOfModel_G2_of_shape {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] {t : H}
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    (hinter : K₁ ⊓ K₂ = zpowers z) (hz : orderOf z = 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ f) (h₁ : Nat.card F₁ = p ^ f) (h₂ : Nat.card F₂ = p ^ f) :
    IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) .G2 p f := by
  obtain ⟨S⟩ := Ch6Rem.exists_shape hRem hcomm hinter hz
  have h4₁ : 4 ≤ Nat.card F₁ := by rw [h₁]; omega
  have h4₂ : 4 ≤ Nat.card F₂ := by rw [h₂]; omega
  have htop := S.oPrimeResidual_eq_top h4₁ h4₂
  obtain ⟨M, _, z', hM, hz', ⟨e⟩⟩ :=
    isInvolutionCentralizerOfModel_G2_of_shape' S hp hp2 (by omega) h₁ h₂
  exact ⟨M, inferInstance, z', hM, hz', ⟨((MulEquiv.subgroupCongr hRem.gen.symm).trans
    ((Subgroup.topEquiv (G := ↥(K₁ ⊔ K₂ ⊔ zpowers t))).symm.trans
      (MulEquiv.subgroupCongr htop.symm))).trans e⟩⟩

theorem isInvolutionCentralizerOfModel_G2_of_diag {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H}
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] {t : H} (hsq : t * t = 1)
    (hd₁ : ∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ ActsAsConj t K₁ e g)
    (hd₂ : ∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ ActsAsConj t K₂ e g)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ = zpowers z)
    (hz : orderOf z = 2)
    (hgen : oPrimeResidualOf 2 (K₁ ⊔ K₂ ⊔ zpowers t) = oPrimeResidualOf 2 (centralizer ({z} : Set H)))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ p ^ f) (h₁ : Nat.card F₁ = p ^ f)
    (h₂ : Nat.card F₂ = p ^ f) :
    IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (centralizer ({z} : Set H))) .G2 p f := by
  obtain ⟨S⟩ := exists_shape_of_diag hsq hd₁ hd₂ hcomm hinter hz
  obtain ⟨M, _, z', hM, hz', ⟨e⟩⟩ := isInvolutionCentralizerOfModel_G2_of_shape' S hp hp2 h3 h₁ h₂
  exact ⟨M, inferInstance, z', hM, hz', ⟨((MulEquiv.subgroupCongr hgen.symm).trans
    (Subgroup.equivMapOfInjective (oPrimeResidual 2 ↥(K₁ ⊔ K₂ ⊔ zpowers t))
      (K₁ ⊔ K₂ ⊔ zpowers t).subtype Subtype.val_injective).symm).trans e⟩⟩

end G2

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.Blueprint

theorem ivk_4_7a_G2
    (K : Type) [Group K] [Finite K] (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : LieModel K .G2 0 p n) (z z' : K) (hz : orderOf z = 2) (hz' : orderOf z' = 2) :
    IsConj z z' := by
  exact ivk_4_7a_G2_aux hp hp2 hK z z' hz hz'

theorem ivk_4_7ab_G2 :
    IVK_4_7ab_G2 := by
  intro M _ _ p f hp hp2 h5 hM z hz
  exact ivk_4_7ab_G2_aux p f hp hp2 h5 hM z hz

theorem ivk_4_7ab_G2_involutionCentralizer_of_ch6Rem
    {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] {t : H} (hRem : Stage4.Rest.Ch6Rem z K₁ K₂ F₁ F₂ t)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hz : orderOf z = 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (h₁ : Nat.card F₁ = p ^ f) (h₂ : Nat.card F₂ = p ^ f) :
    IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set H))) .G2 p f := by
  exact isInvolutionCentralizerOfModel_G2_of_shape hRem hcomm hinter hz hp hp2 h5 h₁ h₂

theorem ivk_4_7ab_G2_involutionCentralizer_of_diag
    {H : Type} [Group H] {z : H} {K₁ K₂ : Subgroup H} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] {t : H} (hsq : t * t = 1)
    (hd₁ : ∃ (e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁) (g : GL (Fin 2) F₁),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₁ˣ) : F₁) ∧ Stage4.Rest.ActsAsConj t K₁ e g)
    (hd₂ : ∃ (e : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (g : GL (Fin 2) F₂),
      ¬ IsSquare ((Matrix.GeneralLinearGroup.det g : F₂ˣ) : F₂) ∧ Stage4.Rest.ActsAsConj t K₂ e g)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hinter : K₁ ⊓ K₂ = Subgroup.zpowers z)
    (hz : orderOf z = 2)
    (hgen : oPrimeResidualOf 2 (K₁ ⊔ K₂ ⊔ Subgroup.zpowers t) =
      oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set H)))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ p ^ f) (h₁ : Nat.card F₁ = p ^ f)
    (h₂ : Nat.card F₂ = p ^ f) :
    IsInvolutionCentralizerOfModel ↥(oPrimeResidualOf 2 (Subgroup.centralizer ({z} : Set H))) .G2 p f := by
  exact isInvolutionCentralizerOfModel_G2_of_diag hsq hd₁ hd₂ hcomm hinter hz hgen hp hp2 h3 h₁ h₂

end CFSG.GH74.GLS.IVK.Proofs2
