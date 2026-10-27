module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFact

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.F4Pilot (statedSpMap statedSpMap_injective centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Model

variable {f m : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K')

theorem nonempty_gramSU_mulEquiv_statedSU {C : GL (Fin (2 * m)) K'} (hC : IsPrimeFormGram C) :
    Nonempty (gramSU h (C : Matrix (Fin (2 * m)) (Fin (2 * m)) K') ≃*
      StatedSU (2 * m + 0) (2 ^ f) K') := by
  obtain ⟨W, hW⟩ := exists_isGramHypTransport (r := m) (ε := 0) h
    (C : Matrix (Fin (2 * m)) (Fin (2 * m)) K') (hC.barTranspose h) (primeFormGram_det_ne_zero C)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := m) (ε := 0) h
  exact ⟨(gramHypEquiv h _ hW).trans (hypTransport h hR)⟩

theorem gramSU_exists_section_of_central {C : GL (Fin (2 * m)) K'} (hC : IsPrimeFormGram C)
    (hm : 2 ≤ m) (hf : 2 ≤ f) :
    ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h (C : Matrix (Fin (2 * m)) (Fin (2 * m)) K')),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : gramSU h (C : Matrix (Fin (2 * m)) (Fin (2 * m)) K') →* E', ∀ g, π' (s g) = g := by
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  obtain ⟨eS⟩ := nonempty_gramSU_mulEquiv_statedSU h hC
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact F4Pilot.forall_exists_section_of_mulEquiv eS
    (F4Pilot.statedSU_even_split (by rw [h.card, ← pow_mul, mul_comm])
      ⟨m, by omega⟩ (by omega) hq)

theorem isPerfect_gramSU {C : GL (Fin (2 * m)) K'} (hC : IsPrimeFormGram C) (hm : 2 ≤ m) :
    Group.IsPerfect (gramSU h (C : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) := by
  have : Finite K' := h.finite
  obtain ⟨eS⟩ := nonempty_gramSU_mulEquiv_statedSU h hC
  have := CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) (K := K')
    (by rw [h.card, ← pow_mul, mul_comm]) (n := 2 * m + 0) (by omega) (fun h3 => by
      have := (Prod.mk.inj h3).1
      omega)
  exact Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective

end Model

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀] {m f : ℕ}
  {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * m)) K'}

structure UnitaryNeighbourParam (e : L ≃* StatedSp (m + 1) K₀) (t : G) (k : Fin (m + 1))
    (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
    (ι : K₀ ≃+* h.fixedField) where
  Φ : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') →* G
  range_eq : Φ.range = neighbourCore e k
  ker_le : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K'))
  N1 : ∀ x : StatedSp m K₀,
    Φ (uModelSU h hC₀ (statedSpMap (ι : K₀ →+* h.fixedField) m x)) =
      ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) : L) : G)
  N3 : ∀ x : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K'),
    t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x)

end Param

section Construct

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀]

@[expose] noncomputable def complSpToNeighbourCore {m : ℕ} (e : L ≃* StatedSp (m + 1) K₀)
    (hK : 4 ≤ Nat.card K₀) (hm : 1 ≤ m) (k : Fin (m + 1)) :
    StatedSp m K₀ →* centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) :=
  ((L.subtype.comp e.symm.toMonoidHom).comp
    ((complSp K₀ k).subtype.comp (complSpEquiv k).toMonoidHom)).codRestrict _
    fun x => modelToG_complSp_le_neighbourCore e hK hm k
      ⟨e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀),
        ⟨_, (complSpEquiv k x).2, rfl⟩, rfl⟩

theorem coe_complSpToNeighbourCore {m : ℕ} (e : L ≃* StatedSp (m + 1) K₀)
    (hK : 4 ≤ Nat.card K₀) (hm : 1 ≤ m) (k : Fin (m + 1)) (x : StatedSp m K₀) :
    ((complSpToNeighbourCore e hK hm k x : centralizerPerfectCore
        (modelToG e (rootTorusSp K₀ k))) : G) =
      ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) : L) : G) :=
  rfl

theorem complSpToNeighbourCore_injective {m : ℕ} (e : L ≃* StatedSp (m + 1) K₀)
    (hK : 4 ≤ Nat.card K₀) (hm : 1 ≤ m) (k : Fin (m + 1)) :
    Function.Injective (complSpToNeighbourCore e hK hm k) := by
  intro x y hxy
  have h1 := congrArg (fun z : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) =>
    (z : G)) hxy
  simp only [coe_complSpToNeighbourCore] at h1
  exact (complSpEquiv k).injective (Subtype.ext (e.symm.injective (Subtype.ext h1)))

variable [Finite G] in
theorem exists_param_of_proj {m f r : ℕ} [Finite K₀] [CharP K₀ 2] (e : L ≃* StatedSp (m + 1) K₀)
    (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (k : Fin (m + 1)) {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') {C₀ : GL (Fin r) K'} (hC : IsPrimeFormGram C₀)
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h (C₀ : Matrix (Fin r) (Fin r) K')),
      Function.Surjective π' → π'.ker ≤ center E' →
        ∃ s : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →* E', ∀ g, π' (s g) = g)
    (hperf : Group.IsPerfect (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')))
    (μ : StatedSp m h.fixedField →* gramSU h (C₀ : Matrix (Fin r) (Fin r) K'))
    (hμ : Function.Injective ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)).comp μ))
    (hμr : ((QuotientGroup.mk' (normOneScalars h
      (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)).comp μ).range =
        fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)))
    (hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G))
    (ρ' : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) →*
      primeFormP h (C₀ : Matrix (Fin r) (Fin r) K'))
    (hρs : Function.Surjective ρ')
    (hρker : ρ'.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))))
    (hρt : ∀ y, ρ' ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
      ⟨t, hN⟩ y) = primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (ρ' y)) :
    ∃ (ι : K₀ ≃+* h.fixedField) (Φ : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →* G),
      Φ.range = neighbourCore e k ∧ Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) ∧
      (∀ x : StatedSp m K₀, Φ (μ (statedSpMap (ι : K₀ →+* h.fixedField) m x)) =
        ((e.symm ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) : L) : G)) ∧
      ∀ x, t * Φ x * t⁻¹ = Φ (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h) x) := by
  have hK4 : 4 ≤ Nat.card K₀ := hKc ▸ four_le_two_pow hf
  have : Finite K' := h.finite
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  have := CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h
  set π := QuotientGroup.mk' (normOneScalars h (gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) r)
    with hπdef
  set ε := complSpToNeighbourCore e hK4 (by omega : 1 ≤ m) k with hεdef
  have hεinj : Function.Injective ε := complSpToNeighbourCore_injective e hK4 (by omega) k
  have hρεinj : Function.Injective (ρ'.comp ε) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hc : ε x ∈ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) := hρker hx
    have hxc : x ∈ center (StatedSp m K₀) := by
      rw [mem_center_iff]
      intro y
      apply hεinj
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hc (ε y)
    rw [center_statedSp_eq_bot m] at hxc
    exact hxc
  have hfix : ∀ x, primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) ((ρ'.comp ε) x) =
      (ρ'.comp ε) x := by
    intro x
    rw [MonoidHom.comp_apply, ← hρt]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : ((ε x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G) ∈ L :=
      (e.symm _).2
    rw [← mem_centralizer_iff.1 htC _ hxL, mul_inv_cancel_right]
  obtain ⟨y, ι, hy, hyε⟩ := exists_conj_eq_of_range_eq_fixedSubgroup hm
    (hKc.trans h.card_fixedField.symm) (π.comp μ) hμ hμr (ρ'.comp ε) hρεinj hfix
  set ρ₁ := (MulAut.conj y).toMonoidHom.comp ρ' with hρ₁def
  have hρ₁s : Function.Surjective ρ₁ := (MulAut.conj y).surjective.comp hρs
  have hρ₁ker : ρ₁.ker ≤ center (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) := by
    intro z hz
    apply hρker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact (MulAut.conj y).map_eq_one_iff.mp hz
  have hρ₁t : ∀ z, ρ₁ ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
      ⟨t, hN⟩ z) = primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (ρ₁ z) := by
    intro z
    rw [hρ₁def, MonoidHom.comp_apply, MonoidHom.comp_apply, hρt, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hy]
  have hρ₁ε : ∀ x, ρ₁ (ε x) = π (μ (statedSpMap (ι : K₀ →+* h.fixedField) m x)) := by
    intro x
    rw [← MonoidHom.comp_apply π μ, ← hyε x]
    rfl
  clear_value ρ₁
  have : Group.IsPerfect (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) :=
    isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := F4Pilot.exists_lift_of_central π (QuotientGroup.mk'_surjective _)
    hsplit ρ₁ hρ₁s hρ₁ker
  refine ⟨ι, (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).subtype.comp Φ₀, ?_, ?_, ?_,
    ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  · intro g hg
    have hg₀ : Φ₀ g = 1 :=
      (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).subtype_injective
        (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact normOneScalars_le_center h _ _ h1
  · intro x
    have : Group.IsPerfect (StatedSp m K₀) := isPerfect_statedSp_of_four_le hK4 m
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center (S := StatedSp m K₀) hρ₁ker
      (φ := Φ₀.comp (μ.comp (statedSpMap (ι : K₀ →+* h.fixedField) m)))
      (ψ := ε) (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hΦ₀, hρ₁ε])
    exact congrArg (fun F : StatedSp m K₀ →* centralizerPerfectCore
      (modelToG e (rootTorusSp K₀ k)) =>
        ((F x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G)) heq
  · intro x
    have heq := LinearPilot.eq_of_comp_eq_of_ker_le_center
      (S := gramSU h (C₀ : Matrix (Fin r) (Fin r) K')) hρ₁ker
      (φ := ((centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))).normalizerMonoidHom
        ⟨t, hN⟩).toMonoidHom.comp Φ₀)
      (ψ := Φ₀.comp (primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h)).toMonoidHom)
      (fun x => by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.coe_toMonoidHom, hρ₁t, hΦ₀, hΦ₀]
        change primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h)
          (x : primeFormP h (C₀ : Matrix (Fin r) (Fin r) K')) = _
        rw [primeFormFieldAut_mk]
        rfl)
    have h1 := congrArg (fun F : gramSU h (C₀ : Matrix (Fin r) (Fin r) K') →*
      centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) =>
        ((F x : centralizerPerfectCore (modelToG e (rootTorusSp K₀ k))) : G)) heq
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    exact h1

variable [Finite G]
  in
theorem nonempty_unitaryNeighbourParam {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K₀ = 2 ^ f) (hf : 2 ≤ f) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K₀)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1))
    (hk : RootKindSp e t f k .unitaryEven) :
    ∃ (K' : Type) (_ : Field K') (h : UnitaryFieldData 2 f K') (_ : CharP h.fixedField 2)
      (C₀ : GL (Fin (2 * m)) K') (hC : IsPrimeFormGram C₀)
      (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
      (ι : K₀ ≃+* h.fixedField), Nonempty (UnitaryNeighbourParam h e t k hC hC₀ ι) := by
  have : Finite K₀ := LinearPilot.finite_of_card_eq_two_pow hKc
  have : CharP K₀ 2 := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have hN : t ∈ normalizer (centralizerPerfectCore (modelToG e (rootTorusSp K₀ k)) : Set G) :=
    le_normalizer_neighbourCore e htC k
  obtain ⟨r, K', _, h', C₀, hC, φ, ρ', hcase, hφ, hρs, hρker, -, hρt⟩ :=
    exists_surjective_primeFormP_neighbourCore_unitary' hset hKc hf (by omega : 2 ≤ m) e htC ht
      k rfl rfl (Or.inl rfl) hk hN
  obtain ⟨-, rfl, hJ⟩ : Sp2mKind.unitaryEven = .unitaryEven ∧ r = 2 * m ∧
      (C₀ : Matrix (Fin r) (Fin r) K') = blockSwapJ r m := by
    rcases hcase with h1 | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by decide)
  have hφb : φ = UnitaryPilot.barRingEquiv h' := RingEquiv.ext fun x =>
    (hφ x).trans (UnitaryPilot.barRingEquiv_apply h' x).symm
  subst hφb
  have hk2 : CharP h'.fixedField 2 :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_charP h'
  have hq : ¬(2 * m = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  obtain ⟨ι, Φ, hrange, hker, hN1, hN3⟩ := exists_param_of_proj e hKc hf hm htC k h' hC
    (gramSU_exists_section_of_central h' hC (by omega) hf) (isPerfect_gramSU h' hC (by omega))
    (uModelSU h' hJ) (uModelP_injective (h := h') (by omega) hJ)
    (range_uModelP (h := h') (by omega) hq hC hJ) hN ρ' hρs hρker hρt
  exact ⟨K', inferInstance, h', hk2, C₀, hC, hJ, ι,
    ⟨{ Φ := Φ, range_eq := hrange, ker_le := hker, N1 := hN1, N3 := hN3 }⟩⟩

end Construct

end CFSG.SeitzReduction.SymplecticPilot
