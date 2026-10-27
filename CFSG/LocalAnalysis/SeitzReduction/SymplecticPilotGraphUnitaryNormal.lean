module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K]

theorem fixedSubgroup_fieldBar_one_not_lieModel_PSp (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) (hev : Even n) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (h1 : (C : Matrix (Fin n) (Fin n) K) = 1) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) {m f' : ℕ} :
    ¬ LieModel (fixedSubgroup (primeFormFieldHom h hC σ)) .PSp m 2 f' := by
  intro hfix
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  have hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r := Or.inl h1
  have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = C := by
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1]
  obtain ⟨hcent, -, hinjU, hNinn, hNC, -, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase 1 hCl σ hσ
  have hcj := UnbalancingLocal.EvenUnitaryComponents.conj_injective_primeFormP h hC hn
  have heq : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h hC σ} =
        ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    refine le_antisymm ?_ (le_inf hNinn hNC)
    rintro x ⟨hxI, hxC⟩
    obtain ⟨g, φ, rfl⟩ := (hcent x).mp hxC
    have h1' := primeFormFieldFactor_psi h hC hn hq ⟨fixedIsometryHom h hCl g, φ⟩
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxI
    have h2 := primeFormFieldFactor_apply h hC hn hq ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one, ← hs, h1'] at h2
    change φ = 1 at h2
    subst h2
    refine ⟨g, ?_⟩
    rw [primeFormPsi_apply, map_one, mul_one]
    rfl
  let Φ : fixedSubgroup (primeFormFieldHom h hC σ) ≃*
      matrixIsometryGroup ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) :=
    (CatLeafProof.fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr heq).trans
      (MonoidHom.ofInjective hinjU).symm)
  have hch := CatLeafProof.isCharacteristicP_matrixIsometryGroup_one (k := h.fixedField) hev hn
  rw [← Units.val_one] at hch
  have hch' : IsCharacteristicP 2 (fixedSubgroup (primeFormFieldHom h hC σ)) :=
    LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv Φ.symm hch
  have : Finite (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by infer_instance
  exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch' ⊤
    (isPComponent_top_of_lieModel_PSp hfix)

theorem exists_primeFormFieldHom_eq_of_lieModel_PSU' {S : Type} [Group S] {m f : ℕ}
    (hS : LieModel S .PSU m 2 f) {θ : MulAut S} (hθθ : θ * θ = 1)
    (hout : θ ∉ (MulAut.conj : S →* MulAut S).range) {m' f' : ℕ}
    (hfix : LieModel (fixedSubgroup θ) .PSp m' 2 f') :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (C₀ : GL (Fin m) K')
      (hC₀ : IsPrimeFormGram C₀) (_ : 3 ≤ m) (_ : ¬(m = 3 ∧ 2 ^ f = 2)) (φ : K' ≃+* K')
      (ε : S ≃* primeFormP h (C₀ : Matrix (Fin m) (Fin m) K')),
      ((Odd m ∧ (C₀ : Matrix (Fin m) (Fin m) K') = 1) ∨
        ∃ r, m = 2 * r ∧ (C₀ : Matrix (Fin m) (Fin m) K') = blockSwapJ m r) ∧
      (∀ x, φ x = h.bar x) ∧ MulAut.congr ε θ = primeFormFieldHom h hC₀ φ := by
  obtain ⟨K', _, h, C₀, hC₀, hm, hq, φ, ε, hcase, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU hS hθθ hout
  refine ⟨K', inferInstance, h, C₀, hC₀, hm, hq, φ, ε, ?_, hφ, hε⟩
  rcases hcase with h1 | hJ
  · rcases Nat.even_or_odd m with hev | hodd
    · exfalso
      have hfix' : LieModel (fixedSubgroup (primeFormFieldHom h hC₀ φ)) .PSp m' 2 f' := by
        rw [← hε]
        exact LieType.CurtisTits.lieModel_of_mulEquiv
          (CatLeafProof.fixedSubgroupCongrEquiv ε θ) hfix
      exact fixedSubgroup_fieldBar_one_not_lieModel_PSp h hm hq hev hC₀ h1 φ hφ hfix'
    · exact Or.inl ⟨hodd, h1⟩
  · exact Or.inr hJ

section Neighbour

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K₀ : Type} [Field K₀]

theorem exists_surjective_primeFormP_neighbourCore_unitary' {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K₀) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {X : Subgroup G}
    (hX : X = modelToG e (rootTorusSp K₀ k)) {D : Subgroup G}
    (hD : D = modelToG e (complSp K₀ k)) {κ : Sp2mKind} (hκ : κ = .unitaryEven ∨ κ = .unitaryOdd)
    (h : HR8KindAtSp t m f X D κ) (hN : t ∈ normalizer (centralizerPerfectCore X : Set G)) :
    ∃ (r : ℕ) (K' : Type) (_ : Field K') (h' : UnitaryFieldData 2 f K') (C₀ : GL (Fin r) K')
      (hC₀ : IsPrimeFormGram C₀) (φ : K' ≃+* K')
      (ρ' : centralizerPerfectCore X →* primeFormP h' (C₀ : Matrix (Fin r) (Fin r) K')),
      ((κ = .unitaryEven ∧ r = 2 * m ∧ (C₀ : Matrix (Fin r) (Fin r) K') = blockSwapJ r m) ∨
        (κ = .unitaryOdd ∧ r = 2 * m + 1 ∧ (C₀ : Matrix (Fin r) (Fin r) K') = 1)) ∧
      (∀ x, φ x = h'.bar x) ∧ Function.Surjective ρ' ∧
        ρ'.ker ≤ center (centralizerPerfectCore X) ∧ Odd (Nat.card ρ'.ker) ∧
        ∀ y, ρ' ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ y) =
          primeFormFieldHom h' hC₀ φ (ρ' y) := by
  have hκ' : IsLinearUnitaryKind κ := by
    rcases hκ with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨S, _, ρ, τ, hρ, hker, hodd, hty, -, hρθ, hττ, hout, hfix⟩ :=
    exists_surjective_neighbourCore_linearUnitary hset hKc hf hm e htC ht k hX hD hκ' h hN
  obtain ⟨r, hS, hr⟩ : ∃ r, LieModel S .PSU r 2 f ∧
      ((κ = .unitaryEven ∧ r = 2 * m) ∨ (κ = .unitaryOdd ∧ r = 2 * m + 1)) := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hty, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨K', _, h', C₀, hC₀, -, -, φ, ε, hcase, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU' hS hττ hout hfix
  have hker' : (ε.toMonoidHom.comp ρ).ker = ρ.ker := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  refine ⟨r, K', inferInstance, h', C₀, hC₀, φ, ε.toMonoidHom.comp ρ, ?_, hφ,
    ε.surjective.comp hρ, hker'.symm ▸ hker, hker'.symm ▸ hodd, fun y => ?_⟩
  · rcases hr with ⟨hκe, rfl⟩ | ⟨hκo, rfl⟩
    · rcases hcase with ⟨hodd2, -⟩ | ⟨r', hr', hJ⟩
      · exact absurd hodd2 (Nat.not_odd_iff_even.2 (even_two_mul m))
      · obtain rfl : r' = m := by omega
        exact Or.inl ⟨hκe, rfl, hJ⟩
    · rcases hcase with ⟨-, h1⟩ | ⟨r', hr', -⟩
      · exact Or.inr ⟨hκo, rfl, h1⟩
      · omega
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hρθ, ← hε, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end Neighbour

end CFSG.SeitzReduction.SymplecticPilot
