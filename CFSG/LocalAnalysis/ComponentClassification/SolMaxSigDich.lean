module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigUniq
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxInputsSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Swap
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCoverBasic
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSetup

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem subgroupOf_map_subtype_self {H : Subgroup X} (K : Subgroup ↥H) :
    (K.map H.subtype).subgroupOf H = K :=
  comap_map_eq_self_of_injective H.subtype_injective K

theorem mem_normalizer_map_subtype' {H : Subgroup X} {K : Subgroup ↥H} {h : ↥H}
    (hh : h ∈ normalizer (K : Set ↥H)) :
    (h : X) ∈ normalizer ((K.map H.subtype : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq] at hh ⊢
  have h1 := map_subtype_map_conj K h
  have hh' : K.map (MulAut.conj h).toMonoidHom = K := hh
  rw [hh'] at h1
  exact h1.symm

theorem fusionZStar_eq_of_alt {L : Type*} [Group L] {m : ℕ} (hm : 4 ≤ m)
    (φ : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin m)) :
    Open.fusionZStar L = pPrimeCore 2 L := by
  rw [Sol78.fusionZStar_eq_iff]
  have h1 : (center (L ⧸ pPrimeCore 2 L)).map φ.toMonoidHom = ⊥ := by
    have h2 := map_center_eq φ
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h2
    exact h2
  exact (map_eq_bot_iff_of_injective _ φ.injective).mp h1

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_normalizer_completion (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput) :
    centralizer ({t} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) :=
  (S.centralizer_le_normalizer hT13 hML hSch).trans
    (S.normalizer_le_normalizer_completion h33 h35)

theorem exists_fixed_or_cover_swap (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hSwap : SignalizerSwapAltExclusion) :
    ∃ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ∧
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) ∧
      ((t ∈ normalizer (M : Set X) ∧ J ≤ M) ∨
        (M.map (MulAut.conj t).toMonoidHom ≠ M ∧ J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
          Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin n)) ∧
          Open.fusionZStar ↥M ≠ pPrimeCore 2 ↥M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCH := S.centralizer_le_normalizer_completion h33 h35 hT13 hML hSch
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have htH : t ∈ H := hCH (mem_centralizer_singleton_iff.mpr rfl)
  have hJH : J ≤ H := S.pair.1.2.1.trans hCH
  set t' : ↥H := ⟨t, htH⟩ with ht'def
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact S.pair.1.1
  have htt : t' * t' = 1 := by rw [← sq, ← ht', pow_orderOf_eq_one]
  have htinv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right htt
  set J' := J.subgroupOf H with hJ'def
  have hJ'C : J' ≤ centralizer ({t'} : Set ↥H) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (S.pair.1.2.1 (mem_subgroupOf.mp hx)))
  have hJ'pc : IsPComponent 2 (J'.subgroupOf (centralizer ({t'} : Set ↥H))) := by
    rw [ht'def, centralizer_mk_eq htH, inf_of_le_left hCH,
      UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCH 2 Nat.prime_two]
    exact S.pair.1.2.2.1
  have hJ'E : J' ≤ pLayer ↥H 2 :=
    FooteLit.le_pLayer_of_isPComponent_centralizer_singleton ht' hJ'C hJ'pc
  obtain ⟨M', hM', hJM', hJM'pc⟩ :=
    UnbalancedLayer.two_layer_fixed_component_orbit_location ht' hJ'C hJ'pc hJ'E
  by_cases hfix : conjugate M' t' = M'
  · refine ⟨M'.map H.subtype, map_subtype_le M', ?_, Or.inl ⟨?_, ?_⟩⟩
    · rwa [subgroupOf_map_subtype_self]
    · exact mem_normalizer_map_subtype' (mem_normalizer_of_conjugate_eq' hfix)
    · rw [hfix, sup_idem] at hJM'
      intro x hx
      exact ⟨⟨x, hJH hx⟩, hJM' (show (⟨x, hJH hx⟩ : ↥H) ∈ J' from hx), rfl⟩
  obtain ⟨φ⟩ := CatLeaf.swap_case_type ht' M' hM' (Ne.symm hfix) J' (le_inf hJM' hJ'C) hJM'pc
  let eJ' : ↥J' ⧸ pPrimeCore 2 ↥J' ≃* alternatingGroup (Fin n) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hJH)).trans e
  have hZJ' : Open.fusionZStar ↥J' = pPrimeCore 2 ↥J' :=
    fusionZStar_eq_of_alt (by have := S.nine_le; omega) eJ'
  let ψ' : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin n) :=
    φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZJ').trans eJ')
  set M := M'.map H.subtype with hMdef
  set Mt := (conjugate M' t').map H.subtype with hMtdef
  have hMpc : IsPComponent 2 (M.subgroupOf H) := by rwa [hMdef, subgroupOf_map_subtype_self]
  let eM : ↥M' ≃* ↥M := M'.equivMapOfInjective H.subtype H.subtype_injective
  have hMne : Mt ≠ M := fun h => hfix (map_injective H.subtype_injective h)
  have hMtconj : M.map (MulAut.conj t).toMonoidHom = Mt := by
    have h1 := map_subtype_map_conj M' t'
    have h2 : M'.map (MulAut.conj t').toMonoidHom = conjugate M' t' := by
      change _ = M'.map (MulAut.conj t'⁻¹).toMonoidHom
      rw [htinv]
    rw [h2] at h1
    exact h1.symm
  have hJMMt : J ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom := by
    rw [hMtconj, hMdef, hMtdef, ← Subgroup.map_sup]
    intro x hx
    exact ⟨⟨x, hJH hx⟩, hJM' (show (⟨x, hJH hx⟩ : ↥H) ∈ J' from hx), rfl⟩
  by_cases hZ : Open.fusionZStar ↥M = pPrimeCore 2 ↥M
  ·
    exfalso
    have hZ' : Open.fusionZStar ↥M' = pPrimeCore 2 ↥M' :=
      (fusionZStar_eq_iff_of_mulEquiv eM).mpr hZ
    let eM'alt : ↥M' ⧸ pPrimeCore 2 ↥M' ≃* alternatingGroup (Fin n) :=
      (QuotientGroup.quotientMulEquivOfEq hZ'.symm).trans ψ'
    exact hSwap X t J n e E D S hCH M (map_subtype_le _) hMpc (by rw [hMtconj]; exact hMne)
      hJMMt ⟨(Sol78.coreQuotCongr eM).symm.trans eM'alt⟩
  ·
    exact ⟨M, map_subtype_le _, hMpc, Or.inr ⟨by rw [hMtconj]; exact hMne, hJMMt,
      ⟨(Sol78.fusionZStarQuotCongr eM).symm.trans ψ'⟩, hZ⟩⟩

end Sig36

end CFSG.ComponentClassification.SolMax
