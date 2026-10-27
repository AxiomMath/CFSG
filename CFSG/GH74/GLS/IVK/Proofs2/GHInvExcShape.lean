module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvCent
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abD4

public noncomputable section

namespace CFSG.GH74.GLS.IVK.GHInv

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.RankThree.PartOne CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

theorem exists_shape_of_equiv {A B : Type} [Group A] [Group B] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (φ : A ≃* B) (a : A) (b : B) (h : φ a = b) (S : Shape ↥(centralizer ({b} : Set B)) F₁ F₂)
    (hz : (S.z : B) = b) : ∃ S' : Shape ↥(centralizer ({a} : Set A)) F₁ F₂, (S'.z : A) = a := by
  refine ⟨S.mapEquiv (centralizerEquiv φ a b h).symm, ?_⟩
  have key : (centralizerEquiv φ a b h).symm S.z =
      (⟨a, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ : ↥(centralizer ({a} : Set A))) := by
    apply (centralizerEquiv φ a b h).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [coe_centralizerEquiv]
    exact hz.trans h.symm
  show (((centralizerEquiv φ a b h).symm S.z : ↥(centralizer ({a} : Set A))) : A) = a
  rw [key]

section G2


theorem exists_shape_G2 {M : Type} [Group M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .G2 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Shape ↥(centralizer ({z} : Set M)) F F),
      Nat.card F = p ^ f ∧ (S.z : M) = z := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := exists_equiv_of_lieModel hM
  have hodd : Odd (Nat.card F) := odd_card_of_model hp hp2 hcard
  have hchar : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have hconj : IsConj (φ z) (z₀ F) :=
    CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (φ z) (z₀ F)
      (by rw [MulEquiv.orderOf_eq]; exact hz) (orderOf_z₀ hchar)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let ψ : M ≃* G2g F := φ.trans (MulAut.conj c)
  have hψz : ψ z = z₀ F := by simpa [ψ] using hc
  obtain ⟨S, hS⟩ := exists_native_shape hodd
  obtain ⟨S', hS'⟩ := exists_shape_of_equiv ψ z (z₀ F) hψz S (by rw [hS]; rfl)
  exact ⟨F, hF, hFin, S', hcard, hS'⟩

theorem mem_of_isCompIn_G2 {M : Type} [Group M] [Finite M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .G2 0 p f) (hf : 1 ≤ f) (z : M) (hz : orderOf z = 2) {B : Subgroup M}
    (hB : IsCompIn (centralizer ({z} : Set M)) B) : z ∈ B := by
  obtain ⟨F, hF, hFin, S, hcard, hSz⟩ := exists_shape_G2 hp hp2 hM z hz
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    calc 3 ≤ p := by
          have := hp.two_le
          omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have := mem_z_of_isComponent_of_card S h3 h3 hB.2
  rw [← hSz]
  exact this

end G2

section D4


theorem exists_shape_D4 {M : Type} [Group M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .trialityD4 0 p f) (z : M) (hz : orderOf z = 2) :
    ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (_ : Finite F₁) (_ : Finite F₂)
      (S : Shape ↥(centralizer ({z} : Set M)) F₁ F₂),
      Nat.card F₁ = (p ^ f) ^ 3 ∧ Nat.card F₂ = p ^ f ∧ (S.z : M) = z := by
  have : Fact p.Prime := ⟨hp⟩
  have hf := one_le_of_lieModel_D4 hM
  obtain ⟨φ⟩ := exists_equiv_concrete hp2 hM
  have hD : D4Data (GaloisField p (3 * f)) (sig0 p f) (p ^ f) := d4Data_sig0 hp2 hf
  have hσ := hD.sigma3
  have hcardF : Nat.card (fixedField (sig0 p f)) = p ^ f :=
    card_fixedField_eq (Fact.out : p.Prime) hf hD.card hD.frob
  have hsq : φ z * φ z = 1 ∧ φ z ≠ 1 := by
    refine ⟨?_, ?_⟩
    · rw [← pow_two, ← map_pow, ← hz, pow_orderOf_eq_one, map_one]
    · intro h
      have : z = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.trialityD4_involutions_conj hp2 hf
    hsq.1 (tauL_mul_self hσ) hsq.2 (tauL_ne_one hσ hD.neg_one)
  let ψ : M ≃* twistedGroup (sig0 p f) := φ.trans (MulAut.conj g)
  have hψz : ψ z = τL hσ := hg
  obtain ⟨S, hS⟩ := exists_native_shape_d4 hσ hD
  obtain ⟨S', hS'⟩ := exists_shape_of_equiv ψ z (τL hσ) hψz S (by rw [hS]; rfl)
  exact ⟨GaloisField p (3 * f), fixedField (sig0 p f), inferInstance, inferInstance, inferInstance,
    inferInstance, S', hD.card, hcardF, hS'⟩

theorem mem_of_isCompIn_D4 {M : Type} [Group M] [Finite M] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .trialityD4 0 p f) (hf : 1 ≤ f) (z : M) (hz : orderOf z = 2) {B : Subgroup M}
    (hB : IsCompIn (centralizer ({z} : Set M)) B) : z ∈ B := by
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hc₁, hc₂, hSz⟩ := exists_shape_D4 hp hp2 hM z hz
  have h3 : 3 ≤ p ^ f := by
    calc 3 ≤ p := by
          have := hp.two_le
          omega
      _ ≤ p ^ f := Nat.le_self_pow (by omega) p
  have h3₂ : 3 ≤ Nat.card F₂ := by rw [hc₂]; exact h3
  have h3₁ : 3 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 3 ≤ p ^ f := h3
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have := mem_z_of_isComponent_of_card S h3₁ h3₂ hB.2
  rw [← hSz]
  exact this

end D4

end CFSG.GH74.GLS.IVK.GHInv
