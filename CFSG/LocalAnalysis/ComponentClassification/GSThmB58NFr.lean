module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFq
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafL34Fixed
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10T
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFp
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.HNOddCore.OuterFix

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace NFPump

theorem false_of_HN_fixed_card
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* Blueprint.NativeSporadic.Carrier .HN) {σ : MulAut S} {P : Subgroup S}
    (h : CatLeaf.ProperFixedComponent σ P) (hP : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 360) :
    False := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
    CatLeaf.oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (CatLeaf.mulAut_oddCore_eq_bot_of_sporadicOddCoreFree
        Sporadic.HNOddCore.sporadicOddCoreFree_HN hna e) hσ2
  have hO : pPrimeCore 2 ↥(fixedSubgroup σ) = ⊥ := by
    rw [← Sol78.oddCore_eq_pPrimeCore]
    exact hcore
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hcomp : IsComponent L := B5a.isComponent_of_isPComponent hO h.2.2.1
  have hOL : pPrimeCore 2 ↥L = ⊥ := B5a.pPrimeCore_eq_bot_of_isComponent hO hcomp
  have hL : Nat.card (↥L ⧸ center ↥L) = 360 := by
    let eL : ↥L ≃* ↥P := subgroupOfEquivOfLe h.2.1
    let e1 : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot
    rw [← Nat.card_congr (Sol78.centerQuotCongr e1).toEquiv,
      Nat.card_congr (Sol78.coreQuotientCenterEquiv ↥L).toEquiv,
      Nat.card_congr (Sol78.fusionZStarQuotCongr eL).toEquiv, hP]
  rcases CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact SolMax.fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    have h1 := RestrictedStd.Spor.hnLocalComponentsInput_holds S e t ht2 _
      (CatLeaf.isComponent_map_mulEquiv φ hcomp)
    rw [← Nat.card_congr (Sol78.centerQuotCongr
      (L.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv, hL] at h1
    norm_num at h1
  ·
    have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    obtain ⟨θ⟩ := Sporadic.HNOddCore.hn_outer_involution_fixSub e σ hσ2 hout
    have hiso : RestrictedStd.Spor.IsoInvariant
        fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({1814400} : Set ℕ) := by
      intro Y Y' _ _ e' h'
      rw [Set.mem_singleton_iff] at h' ⊢
      rw [Nat.card_congr (Sol78.centerQuotCongr e').toEquiv]
      exact h'
    have hcs := RestrictedStd.Spor.CompsSatisfy.of_mulEquiv hiso θ
      RestrictedStd.Spor.compsSatisfy_perm_ten
    have h1 : Nat.card (↥(L.map φ.toMonoidHom) ⧸ center ↥(L.map φ.toMonoidHom)) ∈
        ({1814400} : Set ℕ) := hcs _ (CatLeaf.isComponent_map_mulEquiv φ hcomp)
    rw [Set.mem_singleton_iff, ← Nat.card_congr (Sol78.centerQuotCongr
      (L.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv, hL] at h1
    norm_num at h1

theorem false_of_HN_A6
    {G : Type} [Group G] [Finite G] {a : G} (ha : orderOf a = 2) {M T : Subgroup G}
    (hM : IsPComponent 2 M) (hMa : conjugate M a = M)
    (hTM : T ≤ M ⊓ centralizer ({a} : Set G))
    (hTp : IsPComponent 2 (T.subgroupOf (M ⊓ centralizer ({a} : Set G))))
    (hTO : Nat.card (↥T ⧸ pPrimeCore 2 ↥T) = 360)
    (hTZ : Nat.card (↥T ⧸ Open.fusionZStar ↥T) = 360)
    (eM : ↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.Carrier .HN) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlt : (pPrimeCore 2 ↥T).index < (pPrimeCore 2 ↥M).index := by
    rw [index_eq_card, index_eq_card, hTO]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (↥M ⧸ pPrimeCore 2 ↥M))
    rw [Nat.card_congr ((Sol78.coreQuotientCenterEquiv ↥M).trans eM).toEquiv,
      show Nat.card (Blueprint.NativeSporadic.Carrier .HN) = 273030912000000 from
        Sporadic.HNSchreier.card_HN] at h1
    have h2 : 0 < Nat.card ↥(center (↥M ⧸ pPrimeCore 2 ↥M)) := Nat.card_pos
    omega
  obtain ⟨σ, hPF, ⟨eP⟩⟩ := CatLeaf.exists_properFixedComponent_of_stable_image ha hM hMa hTM hTp hlt
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).2.2
  have : IsSimpleGroup ((↥M ⧸ pPrimeCore 2 ↥M) ⧸ center (↥M ⧸ pPrimeCore 2 ↥M)) := hMq.2.1
  refine false_of_HN_fixed_card hMq.2.2 ((Sol78.coreQuotientCenterEquiv ↥M).trans eM) hPF ?_
  rw [← Nat.card_congr eP.toEquiv]
  exact hTZ

end NFPump

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem SecCond.mem_normalizer_T (hc : h.SecCond y) : y ∈ normalizer (h.T : Set X) :=
  Subgroup.inf_normalizer_le_normalizer_inf
    (mem_inf.mpr ⟨hc.mem_normalizer_Q, le_normalizer hc.mem_P⟩)

theorem sq_mem_secB0_of_row515 (hc : h.SecCond y) (h15 : h.Row515) {b : X} (hb : b ∈ h.B) :
    b ^ 2 ∈ h.secB0 y := by
  obtain ⟨-, hsq⟩ := CatFactsSmall.cfProp21A10 X h h15
  have h1 : y * b * y⁻¹ ∈ h.T := (mem_normalizer_iff.mp hc.mem_normalizer_T b).mp (B5a.B_le_T h hb)
  refine mem_inf.mpr ⟨pow_mem hb 2, ?_⟩
  rw [mem_conjugate_iff, ← conj_pow]
  exact hsq _ h1

theorem card_B_le_of_row515 (hc : h.SecCond y) (h15 : h.Row515) :
    Nat.card h.B ≤ 4 * Nat.card (h.secB0 y) := by
  obtain ⟨hT4, -⟩ := CatFactsSmall.cfProp21A10 X h h15
  have hByT : conjugate h.B y ≤ h.T := by
    rw [← conjugate_eq_of_mem_normalizer hc.mem_normalizer_T]
    exact map_mono (B5a.B_le_T h)
  have hTN : h.T ≤ normalizer (h.B : Set X) := inf_le_left.trans inf_le_right
  have hcardT : Nat.card h.T = 4 * Nat.card h.B := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (h.B.subgroupOf h.T)
    rw [hT4, Nat.card_congr (subgroupOfEquivOfLe (B5a.B_le_T h)).toEquiv] at h1
    exact h1
  have hcardBy : Nat.card (conjugate h.B y) = Nat.card h.B :=
    card_map_of_injective (MulAut.conj y⁻¹).injective
  have hprod := RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hByT.trans hTN)
  rw [hcardBy] at hprod
  have hsupT : Nat.card ↥(h.B ⊔ conjugate h.B y) ≤ Nat.card h.T :=
    card_le_of_le (sup_le (B5a.B_le_T h) hByT)
  have hpos : 0 < Nat.card h.B := Nat.card_pos
  have h1 : Nat.card h.B * Nat.card h.B ≤ Nat.card h.B * (4 * Nat.card (h.secB0 y)) := by
    rw [← hprod, show h.B ⊓ conjugate h.B y = h.secB0 y from rfl]
    calc Nat.card ↥(h.B ⊔ conjugate h.B y) * Nat.card ↥(h.secB0 y)
        ≤ Nat.card h.T * Nat.card ↥(h.secB0 y) := Nat.mul_le_mul_right _ hsupT
      _ = Nat.card h.B * (4 * Nat.card (h.secB0 y)) := by rw [hcardT]; ring
  exact Nat.le_of_mul_le_mul_left h1 hpos

theorem noFusion_of_row515 (hEAP : EvenAltPumpUp)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u) (hc : h.SecCond y)
    (hSyl : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    {g : X} (hgG : g ∈ h.secG0 y)
    (hgN : g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X))
    (hgS : g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X)) (hg2 : IsPGroup 2 (zpowers g))
    (hga : g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y)
    (hb2 : (h.S ⊓ h.secG0 y ⊔ zpowers g) ⊓ normalizer (h.B : Set X) ≤ h.S ⊓ h.secG0 y)
    (h15 : h.Row515) : g * h.a = h.a * g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hB0 : h.secB0 y = ⊥
  · rw [hB0, mem_bot] at hga
    calc g * h.a = g * h.a * g⁻¹ * h.a⁻¹ * (h.a * g) := by group
      _ = h.a * g := by rw [hga, one_mul]
  obtain ⟨M, hMY, hM, hVM, hJM, hJpc, hMN, hMa⟩ := exists_component_row515 hc h15
  have hG₀ne : h.secG0 y ≠ ⊤ :=
    UnbalancedCorr.normalizer_ne_top_of_isSimpleGroup hnonab hB0 (h.isPGroup_secB0 y)
  have hKG : SectionRank.IsKGroupCat ↥(h.secG0 y) :=
    UnbalancedCorr.isKGroupCat_of_ne_top h.kProper hG₀ne
  have hYG : centralizer (h.secB0 y : Set X) ≤ h.secG0 y := h.centralizer_le_G0 y
  have hMG : M ≤ h.secG0 y := hMY.trans hYG
  have hM₁ : IsPComponent 2 (M.subgroupOf (h.secG0 y)) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hMY hYG
      (Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)) hM
  have hBG : h.B ≤ h.secG0 y := Hyp52.SecCond.B_le_G0 hc
  have hB0G : h.secB0 y ≤ h.secG0 y := (h.secB0_le_B y).trans hBG
  have hE2 : IsPGroup 2 (h.B.subgroupOf (h.secG0 y)) := (B5a.isPGroup_B h).comap_subtype
  have hBN : ∀ b ∈ h.B, b ∈ normalizer (M : Set X) := fun b hb =>
    hMN b (hBG hb) (Hyp52.mem_normalizer_secJ0 (hBG hb) (mem_inf.mp (h.S_le (h.B_le hb).1)).2)
  have hEN : h.B.subgroupOf (h.secG0 y) ≤
      normalizer ((M.subgroupOf (h.secG0 y) : Subgroup ↥(h.secG0 y)) : Set ↥(h.secG0 y)) :=
    fun e he => UnbalancedLayer.mem_normalizer_subgroupOf_of_mem (hBN e (mem_subgroupOf.mp he))
  have hB0K : ∀ b : ↥(h.secG0 y), (b : X) ∈ h.secB0 y →
      b ∈ coreActionKernel (M.subgroupOf (h.secG0 y)) := fun b hb =>
    NFAlt.mem_coreActionKernel_of_commute fun m hm =>
      Subtype.ext (mem_centralizer_iff.mp (hMY (mem_subgroupOf.mp hm)) b hb).symm
  have hEsq : ∀ e ∈ h.B.subgroupOf (h.secG0 y),
      e ^ 2 ∈ coreActionKernel (M.subgroupOf (h.secG0 y)) := fun e he =>
    hB0K _ (by simpa using sq_mem_secB0_of_row515 hc h15 (mem_subgroupOf.mp he))
  have hEcard : Nat.card ↥(h.B.subgroupOf (h.secG0 y)) ≤
      4 * Nat.card ↥(h.B.subgroupOf (h.secG0 y) ⊓
        coreActionKernel (M.subgroupOf (h.secG0 y))) := by
    have hle : (h.secB0 y).subgroupOf (h.secG0 y) ≤
        h.B.subgroupOf (h.secG0 y) ⊓ coreActionKernel (M.subgroupOf (h.secG0 y)) :=
      fun b hb => mem_inf.mpr ⟨mem_subgroupOf.mpr (h.secB0_le_B y (mem_subgroupOf.mp hb)),
        hB0K b (mem_subgroupOf.mp hb)⟩
    calc Nat.card ↥(h.B.subgroupOf (h.secG0 y)) = Nat.card h.B :=
          Nat.card_congr (subgroupOfEquivOfLe hBG).toEquiv
      _ ≤ 4 * Nat.card (h.secB0 y) := card_B_le_of_row515 hc h15
      _ = 4 * Nat.card ↥((h.secB0 y).subgroupOf (h.secG0 y)) := by
          rw [Nat.card_congr (subgroupOfEquivOfLe hB0G).toEquiv]
      _ ≤ _ := Nat.mul_le_mul_left 4 (card_le_of_le hle)
  have hKV : h.K ≤ h.V := le_sup_left.trans h.layer_eq_K.le
  have hKM : h.K ≤ M := hKV.trans hVM
  have hTM : h.K.subgroupOf (h.secG0 y) ≤ M.subgroupOf (h.secG0 y) :=
    fun z hz => mem_subgroupOf.mpr (hKM (mem_subgroupOf.mp hz))
  have hKC : h.K ≤ centralizer (h.B : Set X) := hKV.trans (B5a.V_le_centralizer h)
  have hcE : centralizer ((h.B.subgroupOf (h.secG0 y) : Subgroup ↥(h.secG0 y)) :
      Set ↥(h.secG0 y)) = (centralizer (h.B : Set X)).subgroupOf (h.secG0 y) :=
    B5a.centralizer_subgroupOf hBG
  have hCBG : centralizer (h.B : Set X) ≤ h.secG0 y :=
    (centralizer_le (SetLike.coe_subset_coe.mpr (h.secB0_le_B y))).trans hYG
  have hTC : h.K.subgroupOf (h.secG0 y) ≤ centralizer ((h.B.subgroupOf (h.secG0 y) :
      Subgroup ↥(h.secG0 y)) : Set ↥(h.secG0 y)) := by
    rw [hcE]
    exact fun z hz => mem_subgroupOf.mpr (hKC (mem_subgroupOf.mp hz))
  have hTpc : IsPComponent 2 ((h.K.subgroupOf (h.secG0 y)).subgroupOf
      (centralizer ((h.B.subgroupOf (h.secG0 y) : Subgroup ↥(h.secG0 y)) :
        Set ↥(h.secG0 y)))) := by
    rw [hcE, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hCBG 2 Nat.prime_two]
    exact UnbalancedCorr.isPComponent_subgroupOf_of_le hKC (centralizer_le_normalizer _)
      h.isPComponent_K.2
  have hTA : Nonempty (↥(h.K.subgroupOf (h.secG0 y)) ⧸ pPrimeCore 2 ↥(h.K.subgroupOf (h.secG0 y))
      ≃* alternatingGroup (Fin 10)) := by
    obtain ⟨eK⟩ := h15.2.2
    exact ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe (hKM.trans hMG))).trans eK⟩
  rcases hEAP ↥(h.secG0 y) hKG _ hM₁ _ hE2 hEN hEsq hEcard _ hTM hTC hTpc hTA with
    ⟨n, hn, ⟨θ⟩⟩ | hHN
  ·
    exact noFusion_of_alternating h hc hSyl hgG hgN hgS hg2 hga hb2 hMY hVM hJM hMN (by omega)
      ((Sol78.coreQuotCongr (subgroupOfEquivOfLe hMG)).symm.trans θ)
  ·
    exfalso
    obtain ⟨eHN⟩ := hHN
    set Y := centralizer (h.secB0 y : Set X) with hY
    have haY : h.a ∈ Y := a_mem_centralizer_secB0
    set t : ↥Y := ⟨h.a, haY⟩ with ht
    have hto : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_a
    have hMt : conjugate (M.subgroupOf Y) t = M.subgroupOf Y := by
      rw [conjugate_subgroupOf_eq, hMa]
    have hCeq : M.subgroupOf Y ⊓ centralizer ({t} : Set Y) =
        (M ⊓ centralizer ({h.a} : Set X)).subgroupOf Y := by
      rw [UGSChain.centralizer_mk_eq_subgroupOf haY]
      ext z
      simp only [mem_inf, mem_subgroupOf]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, z.2⟩⟩
    have hJMa : h.secJ0 y ≤ M ⊓ centralizer ({h.a} : Set X) :=
      le_inf hJM ((h.secJ0_le y).trans inf_le_left)
    have hTM' : (h.secJ0 y).subgroupOf Y ≤ M.subgroupOf Y ⊓ centralizer ({t} : Set Y) := by
      rw [hCeq]
      exact fun z hz => mem_subgroupOf.mpr (hJMa (mem_subgroupOf.mp hz))
    have hTp' : IsPComponent 2 (((h.secJ0 y).subgroupOf Y).subgroupOf
        (M.subgroupOf Y ⊓ centralizer ({t} : Set Y))) := by
      rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
        (inf_le_left.trans hMY) 2 Nat.prime_two]
      exact hJpc
    obtain ⟨hTO, hTZ⟩ := card_secJ0_row515 (h := h) (y := y) h15
    exact NFPump.false_of_HN_A6 hto hM hMt hTM' hTp' hTO hTZ
      ((Sol78.fusionZStarQuotCongr ((subgroupOfEquivOfLe hMY).trans
        (subgroupOfEquivOfLe hMG).symm)).trans eHN)

end Hyp52

@[expose] def NoFusionB2Row515Statement58 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J →
      ∀ y : X, h.SecCond y →
      Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y) →
      ∀ g : X, g ∈ h.secG0 y →
        g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
        g ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X) → IsPGroup 2 (zpowers g) →
        g * h.a * g⁻¹ * h.a⁻¹ ∈ h.secB0 y →
        (h.S ⊓ h.secG0 y ⊔ zpowers g) ⊓ normalizer (h.B : Set X) ≤ h.S ⊓ h.secG0 y →
        (∀ t ∈ h.S ⊓ h.secG0 y ⊔ zpowers g, conjugate h.B t ≤ h.S ⊓ coreActionKernel h.J →
          Nat.card ↥(h.S ⊓ normalizer (conjugate h.B t : Set X)) ≤
            Nat.card ↥(h.S ⊓ normalizer (h.B : Set X))) →
        h.T ≠ h.B ⊔ zpowers h.a →
        h.Row515 →
        g * h.a = h.a * g

theorem noFusionB2Row515Statement58_of_pumpUp (hEAP : EvenAltPumpUp) :
    NoFusionB2Row515Statement58 :=
  fun _ _ _ _ hnonab _ _ _ _ _ _ _ _ _ hc hSyl _ hgG hgN hgS hg2 hga hb2 _ _ h15 =>
    Hyp52.noFusion_of_row515 hEAP hnonab hc hSyl hgG hgN hgS hg2 hga hb2 h15

end CFSG.ComponentClassification.GSThmB
