module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158FgRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154AmbU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267

@[expose] def T158FgFldOn (p : ℕ) (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω) (x y : Ω) (J : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ → IsChevSimple 2 (PSimple p S) →
    catalogIs (PSimple p S) Q →
    x ^ p = 1 → y ^ p = 1 → x * y = y * x → x ∉ Subgroup.zpowers y → y ∉ Subgroup.zpowers x →
    InnDiagOn p (Subgroup.zpowers x) S → FieldOn p y S →
    GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J → y ∈ Subgroup.normalizer (J : Set Ω) →
    FGOn p y J

theorem t158FgFldOn_of_omegaFld {Q : TauCeti.CFSGIndex → Prop} (h : L154OmegaFld Q) (p : ℕ) :
    T158FgFldOn p Q := by
  intro hp hp2 Ω _ _ S x y J hSn hSq hSp hSc hQ hxp hyp hxy _ _ hInn hF hJ hJy
  exact Or.inl (h p hp hp2 Ω S x y J hSn hSq hSp hSc hQ hxp hyp hxy hInn hF hJ hJy)

section Certs

theorem t158FgOmega_of_families {p : ℕ} (hLin : T158FgFldOn p l154Lin) (hUni : T158FgFldOn p l154Uni)
    (hSymp : T158FgFldOn p l154Symp) (hOrth : T158FgFldOn p l154Orth)
    (hTwOrth : T158FgFldOn p l154TwOrth) (hExc : T158FgFldOn p l154Exc)
    (hAmbAlt : T158FgFldOn p l154AmbAlt) (hAmbU33 : T158FgFldOn p l154AmbU33) :
    T158FgOmega p := by
  intro hp hp2 Ω _ _ S x y J hSn hSq hSp hSc hxp hyp hxy hxny hynx hInn hF hJ hJy
  obtain ⟨i, hi, e⟩ := catalogIs_l154Chev2 hSc
  rcases l154_cover i hi with h | h | h | h | h | h | h | h
  · exact hLin hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hUni hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hSymp hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hOrth hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hTwOrth hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hExc hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hAmbAlt hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy
  · exact hAmbU33 hp hp2 Ω S x y J hSn hSq hSp hSc ⟨i, h, e⟩ hxp hyp hxy hxny hynx hInn hF hJ hJy

theorem t158FgFldOn_lin (p : ℕ) : T158FgFldOn p l154Lin := by
  intro hp hp2 Ω _ _ S x y J _ _ hSp _ hQ hxp hyp _ _ _ hInn hF hJ hJy
  exact Or.inl (l154_lin_fieldOn Y10GInnLin.linLabelDict_holds hp hp2 hSp hxp hyp hQ hInn hF hJ hJy)

theorem t158FgFldOn_ambAlt (p : ℕ) : T158FgFldOn p l154AmbAlt := by
  intro hp hp2 Ω _ _ S _ y _ _ hSq hSp hSc hQ _ hyp _ _ _ _ hF _ _
  exact (l154_false_of_odd_inner hp hp2 (glaPComponent_self_p hSq hSp) hSc hF.1 hyp hF
    (l154_oddInner_of_ambAlt hQ)).elim

theorem t158FgFldOn_ambU33 (p : ℕ) : T158FgFldOn p l154AmbU33 := by
  intro hp hp2 Ω _ _ S _ y _ _ hSq hSp hSc hQ _ hyp _ _ _ _ hF _ _
  exact (l154_false_of_odd_inner hp hp2 (glaPComponent_self_p hSq hSp) hSc hF.1 hyp hF
    (l154_oddInner_of_u33 hQ)).elim

theorem t158FgOmega_of_rest {p : ℕ} (hUni : T158FgFldOn p l154Uni) (hSymp : T158FgFldOn p l154Symp)
    (hOrth : T158FgFldOn p l154Orth) (hTwOrth : T158FgFldOn p l154TwOrth) (hExc : T158FgFldOn p l154Exc) :
    T158FgOmega p :=
  t158FgOmega_of_families (t158FgFldOn_lin p) hUni hSymp hOrth hTwOrth hExc (t158FgFldOn_ambAlt p)
    (t158FgFldOn_ambU33 p)

end Certs

theorem fgOn_of_fgFldOn {p : ℕ} {Q : TauCeti.CFSGIndex → Prop} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΩ : T158FgFldOn p Q) {G : Type} [Group G] [Finite G] {X K : Subgroup G} {x y : G} {J : Subgroup G}
    (hK : GLAPComponent p X K) (hc : IsChevSimple 2 (PSimple p K)) (hQ : catalogIs (PSimple p K) Q)
    (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hxy : x * y = y * x) (hxny : x ∉ Subgroup.zpowers y)
    (hynx : y ∉ Subgroup.zpowers x) (hInn : InnDiagOn p (Subgroup.zpowers x) K) (hF : FieldOn p y K)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set G)) J)
    (hJy : y ∈ Subgroup.normalizer (J : Set G)) : FGOn p y J := by
  have hN1 : x ∈ Subgroup.normalizer (K : Set G) := hInn.1 (Subgroup.mem_zpowers x)
  have hN2 : y ∈ Subgroup.normalizer (K : Set G) := hF.1
  set H : Subgroup G := K ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers y with hHdef
  have hK1H : K ⊔ Subgroup.zpowers x ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_left.trans hK1H
  have hxH : x ∈ H := hK1H (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
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
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
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
  have hxnyΩ := not_mem_zpowers_forth hp hN hxH hyH hxp hyp hxy hxny
  have hynxΩ := not_mem_zpowers_forth hp hN hyH hxH hyp hxp hxy.symm hynx
  have hInnΩ := innDiagOn_forth hp hKH hN hxH hInn
  have hFΩ := fieldOn_forth hp hKH hN hyH hN2 hF
  have hJΩ := glaPComponent_forth hp hKH hxH hN1 hxp hN hJ
  have hJyΩ : π ⟨y, hyH⟩ ∈ Subgroup.normalizer (((J.subgroupOf H).map π : Subgroup _) : Set _) :=
    map_normalizer_mem π (mem_normalizer_subgroupOf' hyH hJy)
  exact fgOn_back hp hJH hN hyH hJy
    (hΩ hp hp2 (↥H ⧸ N0) S (π ⟨x, hxH⟩) (π ⟨y, hyH⟩) ((J.subgroupOf H).map π) hSn hqS hSp hcS hQS hxpΩ
      hypΩ hcommΩ hxnyΩ hynxΩ hInnΩ hFΩ hJΩ hJyΩ)

end CFSG.LocalAnalysis.GLTheoremA.T158

end
