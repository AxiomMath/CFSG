module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagField
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterFamilies
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar

abbrev CatT (idx : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie idx).Group

@[expose] def CrossCharTwoFamCat (k : LieFamily) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → 5 < p →
    idx.1.characteristic ≠ p →
    (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
      IsEmpty (CatT idx ≃* CatT idx')) → IsLocallyBalancedAbs p 2 (CatT idx)

@[expose] def CrossCharTwoFamAt (k : LieFamily)
    (R : TauCeti.ValidLieTypeIndex → ℕ → Prop) : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → 5 < p →
    idx.1.characteristic ≠ p → R idx p →
    (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex p idx'.1 →
      IsEmpty (CatT idx ≃* CatT idx')) → IsLocallyBalancedAbs p 2 (CatT idx)

theorem crossCharTwoFamCat_of_at {k : LieFamily} (R : TauCeti.ValidLieTypeIndex → ℕ → Prop)
    (h₁ : CrossCharTwoFamAt k R) (h₂ : CrossCharTwoFamAt k fun idx p => ¬ R idx p) :
    CrossCharTwoFamCat k := fun idx hk p hp hp5 hc hnexc => by
  by_cases hr : R idx p
  · exact h₁ idx hk p hp hp5 hc hr hnexc
  · exact h₂ idx hk p hp hp5 hc hr hnexc

theorem CrossCharTwoFamAt.of_cat {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : CrossCharTwoFamCat k) : CrossCharTwoFamAt k R :=
  fun idx hk p hp hp5 hc _ hnexc => h idx hk p hp hp5 hc hnexc

theorem localTwoBalanceCrossCharGtFive_of_families (h : ∀ k, CrossCharTwoFamCat k) :
    LocalTwoBalanceCrossCharGtFive := by
  intro S _ _ _ _ idx ⟨e⟩ p hp hp5 hc hnexc
  obtain ⟨k, hk⟩ := exists_lieFamily idx.1
  refine IsLocallyBalancedAbs.of_mulEquiv e (h k idx hk p hp hp5 hc ?_)
  intro idx' hidx'
  exact ⟨fun f => (hnexc idx' hidx').false (e.trans f)⟩

@[expose] def IsExceptionalFam : LieFamily → Prop
  | .E6 | .E7 | .E8 | .F4 | .G2 | .twistedE6 | .trialityD4 => True
  | _ => False

theorem localTwoBalanceCrossCharGtFive_of_classical_and_exceptional
    (hcl : ∀ k, ¬ IsExceptionalFam k → CrossCharTwoFamCat k)
    (hex : ∀ k, IsExceptionalFam k → CrossCharTwoFamCat k) :
    LocalTwoBalanceCrossCharGtFive :=
  localTwoBalanceCrossCharGtFive_of_families fun k => by
    by_cases hk : IsExceptionalFam k
    · exact hex k hk
    · exact hcl k hk

@[expose] def InnerPlaneBalance (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), E ≤ innerAut K → IsElemAbelian p E → Nat.card E = p ^ 2 →
    ∀ H : Subgroup (MulAut K), innerAut K ≤ H → localDeltaIn p H E = ⊥

theorem isLocallyBalancedAbs_two_of_planes_and_fields {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hin : InnerPlaneBalance p K)
    (hout : ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 2 →
      ¬ D ≤ innerAut K → ∃ x ∈ D, x ∉ innerAut K ∧ FieldCoreAt p x) :
    IsLocallyBalancedAbs p 2 K := by
  intro D hD hcard H hH _
  by_cases hDin : D ≤ innerAut K
  · exact hin D hDin hD hcard H hH
  · obtain ⟨x, hxD, hxin, hfc⟩ := hout D hD hcard hDin
    have hx1 : x ≠ 1 := fun h => hxin (by rw [h]; exact one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 hfc

section Canonical

variable {K : Type*} [Group K]

theorem exists_fixed_orderOf_of_canonical_conj [Finite K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {δ : MulAut K}
    {x h : MulAut K} (hxh : x = h * δ * h⁻¹) {y : MulAut K} (hy : y ∈ innerAut K) (hy1 : y ≠ 1)
    (hyp : y ^ p = 1) (hcomm : y * x = x * y) : ∃ k : K, δ k = k ∧ orderOf k = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k₀, hk₀⟩ := hy
  have hy' : h⁻¹ * y * h = MulAut.conj (h⁻¹ k₀) := by
    rw [← hk₀]
    ext z
    simp [MulAut.conj_apply]
  have hc' : (h⁻¹ * y * h) * δ = δ * (h⁻¹ * y * h) := by
    subst hxh
    calc (h⁻¹ * y * h) * δ = h⁻¹ * (y * (h * δ * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * δ * h⁻¹) * y) * h := by rw [hcomm]
      _ = δ * (h⁻¹ * y * h) := by group
  rw [hy'] at hc'
  have hmem : (MulAut.conj (h⁻¹ k₀) : MulAut K) ∈ Subgroup.centralizer ({δ} : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc'
  refine ⟨h⁻¹ k₀, (conj_mem_centralizer_iff_apply_eq hinj).1 hmem, ?_⟩
  have h1 : orderOf (MulAut.conj (h⁻¹ k₀)) = orderOf (h⁻¹ k₀) := orderOf_injective _ hinj _
  have h2 : orderOf (MulAut.conj (h⁻¹ k₀)) = p := by
    rw [← hy']
    have h3 : orderOf (h⁻¹ * y * h) = orderOf y := by
      have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) y
      rw [MulAut.conj_apply, inv_inv] at this
      exact this
    rw [h3]
    exact orderOf_eq_prime hyp fun h1 => hy1 h1
  rw [← h1, h2]

theorem fieldCoreAt_of_canonical_conj [Finite K] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {δ : MulAut K}
    (hδp : orderOf δ = p) {J : Subgroup K} (hJq : CFSG.IsQuasisimple J)
    (hJ : ∀ g : K, g ∈ J ↔ δ g = g)
    (hfix : ∀ β : MulAut K, (∀ u ∈ J, β u = u) → β ∈ Subgroup.zpowers δ)
    {x h : MulAut K} (hxh : x = h * δ * h⁻¹) {y : MulAut K} (hy : y ∈ innerAut K) (hy1 : y ≠ 1)
    (hyp : y ^ p = 1) (hcomm : y * x = x * y) : FieldCoreAt p x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hy hy1 hyp hcomm
  have hJp : ¬ Nat.Coprime p (Nat.card J) := by
    have hkJ : k ∈ J := (hJ k).2 hkδ
    have hdvd : p ∣ Nat.card J := by
      have : orderOf (⟨k, hkJ⟩ : J) = p := by
        rw [Subgroup.orderOf_mk]
        exact hkord
      rw [← this]
      exact orderOf_dvd_natCard _
    exact fun hc => (Nat.Prime.coprime_iff_not_dvd hp).1 hc hdvd
  have hδ : FieldCoreAt p δ := fieldCoreAt_of_fixSub_eq hδp hJq hJ hfix hJp
  exact fieldCoreAt_of_conj hδ h⁻¹ (by rw [hxh]; group)

end Canonical

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
