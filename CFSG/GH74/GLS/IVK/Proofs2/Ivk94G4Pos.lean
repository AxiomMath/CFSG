module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Model
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Sh
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

theorem card_eq_of_sl2_equiv {F F' : Type} [Field F] [Field F'] [Finite F] [Finite F']
    (e : SL(2, F) ≃* SL(2, F')) : Nat.card F = Nat.card F' := by
  have h := Nat.card_congr e.toEquiv
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h
  have ha : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hb : 2 ≤ Nat.card F' := by
    have := Finite.one_lt_card (α := F')
    omega
  rcases lt_trichotomy (Nat.card F) (Nat.card F') with hlt | heq | hgt
  · exfalso
    have h1 : Nat.card F ^ 2 - 1 < Nat.card F' ^ 2 - 1 := by
      have : Nat.card F ^ 2 < Nat.card F' ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      have : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : Nat.card F * (Nat.card F ^ 2 - 1) < Nat.card F' * (Nat.card F' ^ 2 - 1) :=
      Nat.mul_lt_mul'' hlt h1
    omega
  · exact heq
  · exfalso
    have h1 : Nat.card F' ^ 2 - 1 < Nat.card F ^ 2 - 1 := by
      have : Nat.card F' ^ 2 < Nat.card F ^ 2 := Nat.pow_lt_pow_left hgt (by norm_num)
      have : 1 ≤ Nat.card F' ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    have h2 : Nat.card F' * (Nat.card F' ^ 2 - 1) < Nat.card F * (Nat.card F ^ 2 - 1) :=
      Nat.mul_lt_mul'' hgt h1
    omega

theorem eq_I_of_quasisimple_normal {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) (h₁ : 4 ≤ Nat.card F₁)
    (h₂ : 4 ≤ Nat.card F₂) {J : Subgroup Y} (hJn : J.Normal) (hJq : IsQuasisimple ↥J) :
    J = S.I₁ ∨ J = S.I₂ := by
  have hq₁ : IsQuasisimple ↥S.I₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₁.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h₁)
  have hq₂ : IsQuasisimple ↥S.I₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv S.e₂.symm
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h₂)
  have hc₁ : IsComponent S.I₁ := ⟨hq₁, S.normal₁.isSubnormal⟩
  have hc₂ : IsComponent S.I₂ := ⟨hq₂, S.normal₂.isSubnormal⟩
  have hcJ : IsComponent J := ⟨hJq, hJn.isSubnormal⟩
  rcases CFSG.LocalCores.distinct_components_commute hc₁ hcJ with h | h
  · exact Or.inl h.symm
  rcases CFSG.LocalCores.distinct_components_commute hc₂ hcJ with h' | h'
  · exact Or.inr h'.symm
  exfalso
  have hJ1 : J ≤ centralizer (S.I₁ : Set Y) := by
    rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
  have hJ2 : J ≤ centralizer (S.I₂ : Set Y) := by
    rw [Subgroup.commutator_comm] at h'
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h'
  have hsq : ∀ x ∈ J, x = 1 ∨ x = S.z := fun x hx =>
    S.eq_one_or_eq_z_of_centralizes (fun a ha => (Subgroup.mem_centralizer_iff.1 (hJ1 hx) a ha).symm)
      (fun a ha => (Subgroup.mem_centralizer_iff.1 (hJ2 hx) a ha).symm)
  have hcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    intro x hx y hy
    rcases hsq x hx with rfl | rfl
    · rw [one_mul, mul_one]
    rcases hsq y hy with rfl | rfl
    · rw [one_mul, mul_one]
    · rfl
  obtain ⟨-, hs, a, b, hab⟩ := hJq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  exact congrArg (QuotientGroup.mk (s := center ↥J)) (Subtype.ext (hcomm a' a'.2 b' b'.2))


section Factors

theorem le_oPrimeResidualOf_of_sl2 {G : Type} [Group G] {X I : Subgroup G} (hIX : I ≤ X)
    {F : Type} [Field F] [Finite F] (e : ↥I ≃* SL(2, F)) (h4 : 4 ≤ Nat.card F) :
    I ≤ oPrimeResidualOf 2 X := by
  have h := le_oPrimeResidual_of_equiv (I.subgroupOf X)
    ((Subgroup.subgroupOfEquivOfLe hIX).trans e) (oPrimeResidual_sl2 h4)
  intro x hx
  exact ⟨⟨x, hIX hx⟩, h (show (⟨x, hIX hx⟩ : ↥X) ∈ I.subgroupOf X from hx), rfl⟩

theorem normal_of_two_elements {G : Type*} [Group G] {X I : Subgroup G}
    (hnorm : ∀ x ∈ X, (∃ k : ℕ, x ^ 2 ^ k = 1) → ∀ a ∈ I, x * a * x⁻¹ ∈ I) :
    ∀ y ∈ oPrimeResidualOf 2 X, ∀ a ∈ I, y * a * y⁻¹ ∈ I := by
  have hle : oPrimeResidualOf 2 X ≤ normalizer (I : Set G) := by
    rw [oPrimeResidualOf_eq_closure', Subgroup.closure_le]
    rintro x ⟨hxX, k, hk⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnorm x hxX ⟨k, hk⟩ h hh
    · intro hh
      have hk' : x⁻¹ ^ 2 ^ k = 1 := by rw [inv_pow, hk, inv_one]
      have := hnorm x⁻¹ (X.inv_mem hxX) ⟨k, hk'⟩ _ hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at this
  intro y hy a ha
  exact (Subgroup.mem_normalizer_iff.1 (hle hy) a).1 ha

theorem fields_of_factors (h47 : IVK_4_7ab) {K : Type} [Group K]
    [Finite K] {t₀ : StatedLieTag} (ht₀ : t₀ = .G2 ∨ t₀ = .trialityD4) {p₀ f₀ : ℕ}
    (hp₀ : p₀.Prime) (hp₀2 : p₀ ≠ 2) (h5 : 5 ≤ p₀ ^ f₀) (hM : LieModel K t₀ 0 p₀ f₀) {z : K}
    (hz : orderOf z = 2) {I₁ I₂ : Subgroup K} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (hcomm : ∀ x ∈ I₁, ∀ y ∈ I₂, x * y = y * x) (hinter : I₁ ⊓ I₂ = zpowers z)
    (e₁ : ↥I₁ ≃* SL(2, F₁)) (e₂ : ↥I₂ ≃* SL(2, F₂)) (h4₁ : 4 ≤ Nat.card F₁)
    (h4₂ : 4 ≤ Nat.card F₂)
    (hnorm : ∀ x : K, (∃ k : ℕ, x ^ 2 ^ k = 1) → x * z = z * x →
      (∀ a ∈ I₁, x * a * x⁻¹ ∈ I₁) ∧ (∀ a ∈ I₂, x * a * x⁻¹ ∈ I₂)) :
    (t₀ = .G2 ∧ Nat.card F₁ = p₀ ^ f₀ ∧ Nat.card F₂ = p₀ ^ f₀) ∨
      (t₀ = .trialityD4 ∧ ((Nat.card F₁ = (p₀ ^ f₀) ^ 3 ∧ Nat.card F₂ = p₀ ^ f₀) ∨
        (Nat.card F₁ = p₀ ^ f₀ ∧ Nat.card F₂ = (p₀ ^ f₀) ^ 3))) := by
  have hzI₁ : z ∈ I₁ := (show z ∈ I₁ ⊓ I₂ by rw [hinter]; exact mem_zpowers z).1
  have hzI₂ : z ∈ I₂ := (show z ∈ I₁ ⊓ I₂ by rw [hinter]; exact mem_zpowers z).2
  have hI₁C : I₁ ≤ centralizer ({z} : Set K) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha z hzI₂)
  have hI₂C : I₂ ≤ centralizer ({z} : Set K) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm z hzI₁ b hb).symm
  have hI₁Y := le_oPrimeResidualOf_of_sl2 hI₁C e₁ h4₁
  have hI₂Y := le_oPrimeResidualOf_of_sl2 hI₂C e₂ h4₂
  have hN₁ := normal_of_two_elements (X := centralizer ({z} : Set K)) (I := I₁)
    (fun x hx hk a ha => (hnorm x hk (Subgroup.mem_centralizer_singleton_iff.1 hx)).1 a ha)
  have hN₂ := normal_of_two_elements (X := centralizer ({z} : Set K)) (I := I₂)
    (fun x hx hk a ha => (hnorm x hk (Subgroup.mem_centralizer_singleton_iff.1 hx)).2 a ha)
  obtain ⟨F₁', F₂', _, _, _, _, hcards, ⟨S⟩⟩ :=
    exists_shape_of_isInvolutionCentralizerOfModel h47 ht₀ hp₀ hp₀2 h5
      ⟨K, inferInstance, z, hM, hz, ⟨MulEquiv.refl _⟩⟩
  have h4' : 4 ≤ Nat.card F₁' ∧ 4 ≤ Nat.card F₂' := by
    rcases hcards with ⟨-, c1, c2⟩ | ⟨-, c1, c2⟩
    · rw [c1, c2]; exact ⟨by omega, by omega⟩
    · rw [c1, c2]
      exact ⟨le_trans (by omega) (Nat.le_self_pow (by norm_num) _), by omega⟩
  have hJ₁n : (I₁.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))).Normal := by
    refine ⟨fun a ha y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hN₁ _ y.2 _ ha
  have hJ₂n : (I₂.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))).Normal := by
    refine ⟨fun a ha y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hN₂ _ y.2 _ ha
  let ε₁ : SL(2, F₁) ≃* ↥(I₁.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))) :=
    e₁.symm.trans (Subgroup.subgroupOfEquivOfLe hI₁Y).symm
  let ε₂ : SL(2, F₂) ≃* ↥(I₂.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))) :=
    e₂.symm.trans (Subgroup.subgroupOfEquivOfLe hI₂Y).symm
  have hJ₁q : IsQuasisimple ↥(I₁.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ε₁
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4₁)
  have hJ₂q : IsQuasisimple ↥(I₂.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K)))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ε₂
      (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' h4₂)
  have h1 := eq_I_of_quasisimple_normal S h4'.1 h4'.2 hJ₁n hJ₁q
  have h2 := eq_I_of_quasisimple_normal S h4'.1 h4'.2 hJ₂n hJ₂q
  have hne : I₁.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K))) ≠
      I₂.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K))) := by
    intro h
    have hII : I₁ = I₂ := by
      ext x
      constructor
      · intro hx
        have : (⟨x, hI₁Y hx⟩ : ↥(oPrimeResidualOf 2 (centralizer ({z} : Set K)))) ∈
            I₁.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K))) := hx
        rw [h] at this
        exact this
      · intro hx
        have : (⟨x, hI₂Y hx⟩ : ↥(oPrimeResidualOf 2 (centralizer ({z} : Set K)))) ∈
            I₂.subgroupOf (oPrimeResidualOf 2 (centralizer ({z} : Set K))) := hx
        rw [← h] at this
        exact this
    have hI₁z : I₁ = zpowers z := by rw [← hinter, ← hII, inf_idem]
    have hcard : Nat.card ↥I₁ = 2 := by rw [hI₁z, Nat.card_zpowers, hz]
    have hcard' : Nat.card ↥I₁ = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := by
      rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hq2 : 15 ≤ Nat.card F₁ ^ 2 - 1 := by
      have : 16 ≤ Nat.card F₁ ^ 2 := by nlinarith
      omega
    have := Nat.mul_le_mul h4₁ hq2
    omega
  have hs₁ : ∀ {J : Subgroup ↥(oPrimeResidualOf 2 (centralizer ({z} : Set K)))} {F : Type}
      [Field F] [Finite F] {F' : Type} [Field F'] [Finite F'] {I : Subgroup ↥(oPrimeResidualOf 2 (centralizer ({z} : Set K)))}
      (ε : SL(2, F) ≃* ↥J) (e : ↥I ≃* SL(2, F')), J = I → Nat.card F = Nat.card F' := by
    intro J F _ _ F' _ _ I ε e hJI
    exact card_eq_of_sl2_equiv (ε.trans ((MulEquiv.subgroupCongr hJI).trans e))
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · have c1 := hs₁ ε₁ S.e₁ h1
    have c2 := hs₁ ε₂ S.e₂ h2
    rcases hcards with ⟨rfl, d1, d2⟩ | ⟨rfl, d1, d2⟩
    · exact Or.inl ⟨rfl, c1.trans d1, c2.trans d2⟩
    · exact Or.inr ⟨rfl, Or.inl ⟨c1.trans d1, c2.trans d2⟩⟩
  · have c1 := hs₁ ε₁ S.e₂ h1
    have c2 := hs₁ ε₂ S.e₁ h2
    rcases hcards with ⟨rfl, d1, d2⟩ | ⟨rfl, d1, d2⟩
    · exact Or.inl ⟨rfl, c1.trans d2, c2.trans d1⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨c1.trans d2, c2.trans d1⟩⟩
  · exact absurd (h1.trans h2.symm) hne

end Factors

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
