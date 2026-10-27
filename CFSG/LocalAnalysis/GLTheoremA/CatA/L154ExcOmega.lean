module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Inn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267
open CFSG.LocalAnalysis.GLTheoremA.T158

@[expose] def L154OmegaNID (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω)
    (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    catalogIs (PSimple p S) Q → x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J →
    y ∈ Subgroup.normalizer (J : Set Ω) →
    NonInnDiag p y J

@[expose] def L154OmegaTD4 (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω)
    (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    catalogIs (PSimple p S) Q → x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J →
    y ∈ Subgroup.normalizer (J : Set Ω) →
    ¬ (p = 3 ∧ IsTD4 3 J)

theorem l154_omega_passage {Q : TauCeti.CFSGIndex → Prop} {p : ℕ} (hp : p.Prime) {Γ : Type}
    [Group Γ] [Finite Γ] {X K J : Subgroup Γ} {x y : Γ} (hK : GLAPComponent p X K)
    (hc : IsChevSimple 2 (PSimple p K)) (hQ : catalogIs (PSimple p K) Q) (hxp : x ^ p = 1)
    (hyp : y ^ p = 1) (hxy : x * y = y * x) (hN1 : x ∈ Subgroup.normalizer (K : Set Γ))
    (hN2 : y ∈ Subgroup.normalizer (K : Set Γ)) (hInn : InnDiagOn p (Subgroup.zpowers x) K)
    (hF : FieldOn p y K) (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set Γ)) :
    ∃ (Ω : Type) (_ : Group Ω) (_ : Finite Ω) (S : Subgroup Ω) (x' y' : Ω) (J' : Subgroup Ω),
      S.Normal ∧ CFSG.Open.IsQuasisimple ↥S ∧ GLAPPrimeCore p ↥S = ⊥ ∧
      IsChevSimple 2 (PSimple p S) ∧ catalogIs (PSimple p S) Q ∧ x' ^ p = 1 ∧ y' ^ p = 1 ∧
      x' * y' = y' * x' ∧ InnDiagOn p (Subgroup.zpowers x') S ∧ FieldOn p y' S ∧
      GLAPComponent p (S ⊓ Subgroup.centralizer ({x'} : Set Ω)) J' ∧
      y' ∈ Subgroup.normalizer (J' : Set Ω) ∧ (NonInnDiag p y' J' → NonInnDiag p y J) ∧
      (p = 3 → IsTD4 3 J → IsTD4 3 J') := by
  set H : Subgroup Γ := K ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y with hHdef
  have hK1H : K ⊔ Subgroup.zpowers x ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_left.trans hK1H
  have hxH : x ∈ H := hK1H (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) :=
    sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hN1)) (Subgroup.zpowers_le.2 hN2)
  set M : Subgroup ↥H := K.subgroupOf H with hMdef
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hN0n : (GLAPPrimeCoreOf p M).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
    rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
  have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
  set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
    have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hcS : IsChevSimple 2 (PSimple p S) := isChevSimple_congr (psimpleIso eK) hc
  have hQS : catalogIs (PSimple p S) Q := catalog_forth hp hKH hN hQ
  have hxp' : (⟨x, hxH⟩ : ↥H) ^ p = 1 := Subtype.ext hxp
  have hyp' : (⟨y, hyH⟩ : ↥H) ^ p = 1 := Subtype.ext hyp
  have hxpΩ : (π ⟨x, hxH⟩) ^ p = 1 := by rw [← map_pow, hxp', map_one]
  have hypΩ : (π ⟨y, hyH⟩) ^ p = 1 := by rw [← map_pow, hyp', map_one]
  have hcommΩ : π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hxy)
  have hJH : J ≤ H := hJ.1.trans (inf_le_left.trans hKH)
  have hInnΩ := innDiagOn_forth hp hKH hN hxH hInn
  have hFΩ := fieldOn_forth hp hKH hN hyH hN2 hF
  have hJΩ := glaPComponent_forth hp hKH hxH hN1 hxp hN hJ
  have hJyΩ : π ⟨y, hyH⟩ ∈ Subgroup.normalizer (((J.subgroupOf H).map π : Subgroup _) : Set _) :=
    map_normalizer_mem π (mem_normalizer_subgroupOf' hyH hJy)
  refine ⟨↥H ⧸ N0, inferInstance, inferInstance, S, π ⟨x, hxH⟩, π ⟨y, hyH⟩,
    (J.subgroupOf H).map π, hSn, hqS, hSp, hcS, hQS, hxpΩ, hypΩ, hcommΩ, hInnΩ, hFΩ, hJΩ, hJyΩ,
    nonInnDiag_back hp hJH hN hyH hJy, fun hp3 hT => ?_⟩
  exact (isTD4_congr hp3 (compIso hp (Subgroup.map_subgroupOf_eq_of_le hJH) π hN)).1 hT

theorem l154NIDOn_of_omegaNID {Q : TauCeti.CFSGIndex → Prop} (hΩ : L154OmegaNID Q) :
    L154NIDOn Q := by
  intro p hp hp2 Γ _ _ X K J x y _ hK hc hQ _ hxp hyp hxy _ hN1 hN2 _ hInn hF hJ hJy
  obtain ⟨Ω, _, _, S, x', y', J', hSn, hqS, hSp, hcS, hQS, hxp', hyp', hxy', hInn', hF', hJ', hJy',
    hback, -⟩ := l154_omega_passage hp hK hc hQ hxp hyp hxy hN1 hN2 hInn hF hJ hJy
  exact hback (hΩ p hp hp2 Ω S x' y' J' hSn hqS hSp hcS hQS hxp' hyp' hxy' hInn' hF' hJ' hJy')

theorem l154TD4On_of_omegaTD4 {Q : TauCeti.CFSGIndex → Prop} (hΩ : L154OmegaTD4 Q) :
    L154TD4On Q := by
  intro p hp hp2 Γ _ _ X K J x y _ hK hc hQ _ hxp hyp hxy _ hN1 hN2 _ hInn hF hJ hJy
  obtain ⟨Ω, _, _, S, x', y', J', hSn, hqS, hSp, hcS, hQS, hxp', hyp', hxy', hInn', hF', hJ', hJy',
    -, hfwd⟩ := l154_omega_passage hp hK hc hQ hxp hyp hxy hN1 hN2 hInn hF hJ hJy
  rintro ⟨hp3, hT⟩
  exact hΩ p hp hp2 Ω S x' y' J' hSn hqS hSp hcS hQS hxp' hyp' hxy' hInn' hF' hJ' hJy'
    ⟨hp3, hfwd hp3 hT⟩

end CFSG.LocalAnalysis.GLTheoremA.K155X
