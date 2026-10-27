module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6XiStep3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartnerClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Chevalley.E6SecondGraphFixed (SecondGraphFixedSubgroup)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Perfect


theorem commutator_centralizer_of_coe_eq_two {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2)
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
      twistedFixedGroup TwistTag.E6 k (RingHom.id k))
    {s : adjointGroup Tag.F4 k} (hs : (s : ModGL Tag.F4 k) = e6FixedToF4 k ⟨_, ht⟩) :
    ⁅centralizer ({s} : Set (adjointGroup Tag.F4 k)),
      centralizer ({s} : Set (adjointGroup Tag.F4 k))⁆ =
    centralizer ({s} : Set (adjointGroup Tag.F4 k)) := by
  obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
  set c' : adjointGroup Tag.F4 k := ⟨c, hcC⟩
  have hcs : MulAut.conj c'⁻¹ (yRep k .t) = s := by
    apply Subtype.ext
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, ← hc, hs]
    change c⁻¹ * (c * _ * c⁻¹) * c = _
    group
  have h := commutator_centralizer_map (factF3PerfectTwo hk .t (by decide)) (MulAut.conj c'⁻¹)
  rwa [hcs] at h

theorem commutator_fixSubgroup_xi_E6_two {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2) {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K') :
    ⁅E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η),
      E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η)⁆ =
    E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η) := by
  have hK1 : Nat.card K' = 2 ^ 1 := by rw [hK', pow_one]
  have := charP_two_of_natCard_eq_two_pow hK1
  have hM' : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by omega)]
    norm_num
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card le_rfl hK1 hM'
  let _ : Algebra K' (GaloisField 2 (2 * 1)) := ι.toAlgebra
  have hσM : ∀ c : GaloisField 2 (2 * 1), iterateFrobenius (GaloisField 2 (2 * 1)) 2 1 c =
      c ^ 2 ^ 1 := fun c => iterateFrobenius_def (p := 2) 1 c
  obtain ⟨ht, -, -, -, ⟨eJ, -, heJ, hsec⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup 1 le_rfl K' (GaloisField 2 (2 * 1)) hK1 hM' _
      hσM
  exact commutator_fixSubgroup_of_secondGraph hsec hη hx fun htJ =>
    commutator_centralizer_of_coe_eq_two hK' ht (heJ htJ)

end Perfect

section CaseS


theorem false_of_xi_partner_inner_of_conj {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {e : L ≃* adjointGroup .F4 K} {t : G}
    (hw : F4Work L K t 1) {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ 1)
    {G₀ : Subgroup G} (hG₀ : ⁅G₀, G₀⁆ = G₀)
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup TwistTag.E6.tag K')
    (hZ : Odd (Nat.card (center G₀))) (hC : Odd (Nat.card (centralizer (G₀ : Set G))))
    (htN : t ∈ normalizer (G₀ : Set G)) {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (h₀ : G₀ ⊓ centralizer ({t} : Set G) = L)
    (hstep : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₀ h : Set G) →
      CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → CFSG.conjugate G₀ h = G₀)
    (g : G) (hMC : CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L)
    {w : G} (hw2 : w * w = 1) (htw : t * w = w * t)
    (hgs : g⁻¹ * (t * w) * g ∈ normalizer (G₀ : Set G))
    (hη' : ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K'),
      φ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ⁻¹ = η)
    (htwN : t * w ∈ normalizer (G₀ : Set G)) (y : G₀)
    (hS : normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ =
      MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)) *
        normalizerQuotMulAut e₀ ⟨t, htN⟩ *
          (MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)))⁻¹) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have hs2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * (w * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * (w * w) := by group
      _ = 1 := by rw [ht2, hw2, mul_one]
  obtain ⟨n, hnN, hsn⟩ := exists_conj_eq_of_normalizerQuotMulAut_eq_conj hG₀ hC e₀ hs2 ht2 htwN
    htN y hS
  set g' : G := n⁻¹ * g with hg'def
  have hg'e : g'⁻¹ * t * g' = g⁻¹ * (t * w) * g := by
    rw [hsn, hg'def]
    group
  have hg' : g'⁻¹ * t * g' ∈ normalizer (G₀ : Set G) := hg'e ▸ hgs
  have htM' := mem_normalizer_conjugate_inv hg'
  have hA : normalizerQuotMulAut
      ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g'⁻¹).symm.trans e₀) ⟨t, htM'⟩ =
        normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ := by
    rw [normalizerQuotMulAut_conjugate e₀ hg' htM']
    congr 2
  obtain ⟨φ', hφ'⟩ := hη'
  rw [← hA] at hφ'
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g'⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate G₀ g'⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hCM : CFSG.conjugate G₀ g'⁻¹ ⊓ centralizer ({t} : Set G) = L := by
    rcases inf_centralizer_eq_or_xi_E6_quot_27 hw.standard hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hMp hZM hK'
        ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g'⁻¹).symm.trans e₀) htM' with
      ⟨hC', -⟩ | ⟨η₁, hη₁, hx, φ₁, hφ₁⟩
    · exact hC'
    · exfalso
      have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      refine not_conj_eta_xi_E6 hw.one_le hK' hη hx (φ₁ * φ'⁻¹) ?_
      calc φ₁ * φ'⁻¹ * η * (φ₁ * φ'⁻¹)⁻¹
          = φ₁ * φ'⁻¹ * (φ' * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ'⁻¹) * (φ₁ * φ'⁻¹)⁻¹ := by rw [hφ']
        _ = φ₁ * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ₁⁻¹ := by group
        _ = MulAut.conj ⟨_, hx⟩ * η := by rw [hφ₁, h1]
  have hg'N : g' ∈ normalizer (G₀ : Set G) :=
    mem_normalizer_of_conjugate_inv_eq (hstep g'⁻¹ htM' hCM)
  have hgN : g ∈ normalizer (G₀ : Set G) := by
    have : g = n * g' := by rw [hg'def, mul_inv_cancel_left]
    rw [this]
    exact mul_mem hnN hg'N
  have hMeq : CFSG.conjugate G₀ g⁻¹ = G₀ := by
    rw [conjugate_inv_eq_map]
    exact (mem_normalizer_iff_map_conj_eq.1 hgN)
  exact hMC (by rw [hMeq]; exact h₀)

end CaseS

section CaseL


@[expose] def TwoE6XiCaseLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .linear6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaMinus8 →
      ∀ φF : ∀ J, (e6Datum K).leviAmalgam J →* G, IsTwoE6GraphFamily (twoE6Span e X₀) t K φF →
    ∀ (e₀ : twoE6Span e X₀ ⧸ center (twoE6Span e X₀) ≃* adjointGroup TwistTag.E6.tag K)
      (M : Subgroup G), (∃ g : G, M = CFSG.conjugate (twoE6Span e X₀) g) →
    ∀ (htM : t ∈ normalizer (M : Set G)) (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K)
      (η : MulAut (adjointGroup TwistTag.E6.tag K)),
      (∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
        diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹) →
    ∀ (hx : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
      (φ : MulAut (adjointGroup TwistTag.E6.tag K)),
      φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η →
    ∀ (w : G) (hwM : w ∈ M), w ∈ L → w * w = 1 → t * w = w * t →
      eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ ⟨_, hx⟩ →
      w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)) →
      (∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c) →
    ∀ (htwM : t * w ∈ normalizer (M : Set G)),
      (∃ φ₁ : MulAut (adjointGroup TwistTag.E6.tag K),
        φ₁ * normalizerQuotMulAut eM ⟨t * w, htwM⟩ * φ₁⁻¹ = η) →
    ∀ (htN : t ∈ normalizer (twoE6Span e X₀ : Set G))
      (htwN : t * w ∈ normalizer (twoE6Span e X₀ : Set G)),
      twoE6Span e X₀ ⊓ centralizer ({t} : Set G) = L →
      (∃ ψ : MulAut (adjointGroup TwistTag.E6.tag K),
        ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η) →
      (∃ φ' : MulAut (adjointGroup TwistTag.E6.tag K),
        φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj ⟨_, hx⟩ * η) →
      False

theorem twoE6XiExclusionInput_of_caseL (hC3 : TwoE6ConjugateInput) (hL : TwoE6XiCaseLInput) :
    TwoE6XiExclusionInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' φF hφF M hM htM eM η hη hx φ hφ
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have htCL := hw.mem_centralizer
  obtain ⟨hZ0, e₆₀, -⟩ := exists_mulEquiv_twoE6Span_of_family hK e X₀ htCL hφF
  set e₀ : twoE6Span e X₀ ⧸ center (twoE6Span e X₀) ≃* adjointGroup TwistTag.E6.tag K := e₆₀
    with he₀def
  have hG₀ := commutator_twoE6Span e X₀
  have hLG₀ := le_twoE6Span e X₀
  have htN := mem_normalizer_twoE6Span e X₀ htCL
  have h36 : 2 ^ (36 * 1) ∣ Nat.card (adjointGroup TwistTag.E6.tag K) := by
    change 2 ^ (36 * 1) ∣ Nat.card (adjointGroup Tag.E6 K)
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hw.card_eq]
    obtain ⟨r, -, hr⟩ := (EvenExc.profile_ordE6' (le_refl 1)).two
    rw [hr, mul_comm 36 1]
    exact Dvd.intro r rfl
  have htC : t ∉ centralizer (twoE6Span e X₀ : Set G) :=
    not_mem_centralizer_of_two_pow_dvd_quot hw.standard hw.one_le hw.card_eq e htCL
      hw.orderOf_eq hG₀ e₀ h36
  have hC := EPilot.odd_card_centralizer_of_inf_eq_zpowers hw.inf_eq hLG₀ hw.orderOf_eq htN htC
  have hZ : Odd (Nat.card (center (twoE6Span e X₀))) := by
    rw [hZ0, Subgroup.card_bot]
    exact odd_one
  have hK'2 : ringChar K = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card hw.one_le hw.card_eq
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨g₁, hg₁⟩ := hM
  set g : G := g₁⁻¹ with hgdef
  have hMg : M = CFSG.conjugate (twoE6Span e X₀) g⁻¹ := by rw [hgdef, inv_inv]; exact hg₁
  subst hMg
  have hZM : Odd (Nat.card (center (CFSG.conjugate (twoE6Span e X₀) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  obtain ⟨hx2, hηx, hfix⟩ := xi_data_of_le hK'2 le_rfl hη hx
  obtain ⟨w, hww, htw, hwq, htwM, hφw⟩ :=
    exists_partner_of_conj_eq_conj_mul hZM eM htM hx2 hηx hφ
  have hperfA := fixSubgroup_perfect_of_conj hφ (commutator_fixSubgroup_xi_E6_two hK hη hx)
  have hwΛ := mem_perfectCore_of_fixSubgroup_perfect hZM eM hw.orderOf_eq htM hperfA hww htw
  have hwL : (w : G) ∈ L :=
    perfectCore_inf_centralizer_le hw.standard hOut htCL hw.orderOf_eq _ hwΛ
  have hwG₀ : (w : G) ∈ twoE6Span e X₀ := hLG₀ hwL
  have hcomm : ∀ c ∈ CFSG.conjugate (twoE6Span e X₀) g⁻¹ ⊓ centralizer ({t} : Set G),
      c * w = w * c := fun c hc =>
    commute_partner_of_fix hZM eM htM hφ hfix hww hwq hc.1
      (mem_centralizer_singleton_iff.1 hc.2)
  have hww' : (w : G) * w = 1 := by rw [← Subgroup.coe_mul, hww, Subgroup.coe_one]
  rcases inf_centralizer_eq_or_xi_E6_quot_27 hw.standard hw.card_eq e htCL hw.orderOf_eq
      hw.inf_eq hG₀ hZ hw.card_eq e₀ htN with
    ⟨hC₀, η₀, hη₀, φ₀, hφ₀⟩ | ⟨η₀, hη₀, hx₀, φ₀, hφ₀⟩
  swap
  · exact false_of_le_of_conj_xi_E6 hLG₀ hw.center_eq_bot hw.card_eq e hw.card_eq e₀ htCL
      htN hη₀ hx₀ hφ₀
  have hηη₀ : η₀ = η := MulEquiv.ext fun x => Subtype.ext ((hη₀ x).trans (hη x).symm)
  rw [hηη₀] at hφ₀
  have hM' : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by omega)]
    norm_num
  obtain ⟨ι⟩ :=
    CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hw.one_le hw.card_eq hM'
  let _ : Algebra K (GaloisField 2 (2 * 1)) := ι.toAlgebra
  obtain ⟨⟨-, hPP, -, -, hexh, hfaith, -⟩, -⟩ :=
    even_E6_graph_inner_coset_exhaustion 1 hw.one_le K (GaloisField 2 (2 * 1)) hw.card_eq hM'
      (iterateFrobenius (GaloisField 2 (2 * 1)) 2 1)
      (fun c => iterateFrobenius_def (p := 2) 1 c)
  have hfaith' : ∀ c ∈ adjointGroup TwistTag.E6.tag K,
      (∀ h ∈ adjointGroup TwistTag.E6.tag K, c * h * c⁻¹ = h) → c = 1 := fun c hc h =>
    hfaith c (Subgroup.mem_sup_left hc) h
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htw2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * ((w : G) * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * ((w : G) * w) := by group
      _ = 1 := by rw [ht2, hww', mul_one]
  have hgs : g⁻¹ * (t * w) * g ∈ normalizer (twoE6Span e X₀ : Set G) :=
    conj_mem_normalizer_of_mem_normalizer_conjugate_inv htwM
  have hη' : ∃ φ₂ : MulAut (adjointGroup TwistTag.E6.tag K),
      φ₂ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ₂⁻¹ = η := by
    rw [← normalizerQuotMulAut_conjugate e₀ hgs htwM]
    set eM' := (E6Pilot.coverConjugateQuotientCenterEquiv (twoE6Span e X₀) g⁻¹).symm.trans e₀
    have heM : eM = eM'.trans (eM'.symm.trans eM) := MulEquiv.ext fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [heM] at hφw
    exact (exists_conj_eq_iff_trans eM' (eM'.symm.trans eM) _ η).1 ⟨φ, hφw⟩
  have hMC : CFSG.conjugate (twoE6Span e X₀) g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L := by
    intro hCM
    have hLM : L ≤ CFSG.conjugate (twoE6Span e X₀) g⁻¹ := fun x hx => by
      rw [← hCM] at hx
      exact hx.1
    exact false_of_le_of_conj_xi_E6 hLM hw.center_eq_bot hw.card_eq e hw.card_eq eM htCL
      htM hη hx hφ
  have hstep : ∀ h : G, t ∈ normalizer (CFSG.conjugate (twoE6Span e X₀) h : Set G) →
      CFSG.conjugate (twoE6Span e X₀) h ⊓ centralizer ({t} : Set G) = L →
        CFSG.conjugate (twoE6Span e X₀) h = twoE6Span e X₀ :=
    fun h hth hCh => hC3 G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φF hφF h hth hCh
  rcases inner_or_xi_of_mem hPP hexh hfaith' hx hη e₀ htN hφ₀ hwG₀ htw2 with
    ⟨y, hy⟩ | ⟨φ', hφ'⟩
  · exact false_of_xi_partner_inner_of_conj (e := e) hw hw.card_eq hG₀ e₀ hZ hC htN hη hC₀ hstep g
      hMC hww' htw hgs hη' (mul_mem htN (le_normalizer hwG₀)) y hy
  · exact hL G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' φF hφF e₀ _ ⟨g⁻¹, rfl⟩ htM eM η hη hx φ hφ w w.2
      hwL hww' htw hwq hwΛ hcomm htwM ⟨φ, hφw⟩ htN (mul_mem htN (le_normalizer hwG₀)) hC₀
      ⟨φ₀, hφ₀⟩ ⟨φ', hφ'⟩

theorem twoE6UniqueInput_of_notDvd_caseL (hN : TwoE6CoreNotDvdInput) (hL : TwoE6XiCaseLInput) :
    TwoE6UniqueInput :=
  twoE6UniqueInput_of_inputs
    (twoE6XiExclusionInput_of_caseL (twoE6ConjugateInput_of_notDvd hN) hL)
    (twoE6ConjugateInput_of_notDvd hN)

end CaseL

end CFSG.SeitzReduction.F4Pilot
