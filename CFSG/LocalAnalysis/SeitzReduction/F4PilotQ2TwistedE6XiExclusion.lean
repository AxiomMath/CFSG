module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6XiStep3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6XiExclusion

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Perfect

theorem commutator_fixSubgroup_xi_twistedE6_two {K₂ : Type} [Field K₂] [Finite K₂]
    (σ : K₂ →+* K₂) (hK₂ : Nat.card K₂ = 4) (hσ : ∀ c, σ c = c ^ 2)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ) :
    ⁅E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η),
      E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η)⁆ =
    E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : graphFixedRootGroup TwistTag.E6 K₂ σ) * η) := by
  have hK₂' : Nat.card K₂ = (2 ^ 1) ^ 2 := by rw [hK₂]; norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ c
  have hk : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  have := charP_two_of_natCard_eq_two_pow hk
  have : Finite (GaloisField 2 1) := finite_of_natCard_eq_two_pow hk
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card le_rfl hk hK₂'
  let _ : Algebra (GaloisField 2 1) K₂ := ι.toAlgebra
  obtain ⟨ht, -, -, -, -, ⟨eJ, -, heJ, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup 1 le_rfl (GaloisField 2 1) K₂ hk hK₂' σ hσ1
  have hk2 : Nat.card (GaloisField 2 1) = 2 := by rw [hk, pow_one]
  exact commutator_fixSubgroup_of_secondGraph hsec hη hx fun htJ =>
    commutator_centralizer_of_coe_eq_two hk2 ht (heJ htJ)

end Perfect

section CaseS

theorem false_of_xi_partner_inner_twistedE6_of_conj {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {e : L ≃* adjointGroup .F4 K}
    {t : G} (hw : F4Work L K t 1) {K₂ : Type} [Field K₂] [Finite K₂]
    (hK₂ : Nat.card K₂ = (2 ^ 1) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {G₀ : Subgroup G} (hG₀ : ⁅G₀, G₀⁆ = G₀)
    (e₀ : G₀ ⧸ center G₀ ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (hZ : Odd (Nat.card (center G₀))) (hC : Odd (Nat.card (centralizer (G₀ : Set G))))
    (htN : t ∈ normalizer (G₀ : Set G)) {η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (h₀ : G₀ ⊓ centralizer ({t} : Set G) = L)
    (hstep : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₀ h : Set G) →
      CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → CFSG.conjugate G₀ h = G₀)
    (g : G) (hMC : CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L)
    {w : G} (hw2 : w * w = 1) (htw : t * w = w * t)
    (hgs : g⁻¹ * (t * w) * g ∈ normalizer (G₀ : Set G))
    (hη' : ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
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
    rcases inf_centralizer_eq_or_xi_twistedE6_quot_27 hw.standard hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hMp hZM hK₂ σ hσ
        ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ g'⁻¹).symm.trans e₀) htM' with
      ⟨hC', -⟩ | ⟨hx, φ₁, η₁, hη₁, hφ₁⟩
    · exact hC'
    · exfalso
      have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      refine not_conj_eta_xi_twistedE6 hw.one_le hK₂ hσ hη hx (φ₁ * φ'⁻¹) ?_
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

section Statements

@[expose] def TwoTwistedE6XiCaseLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (k : Type) [Field k] [Finite k] (σ' : k ≃+* k), Nat.card k = 4 → (∀ c, σ' c = c ^ 2) →
      ∀ G₀ : Subgroup G, G₀ = centralizerPerfectCore (subgroupToG e X₀) ⊔ L →
      ∀ (e₀ : G₀ ⧸ center G₀ ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (M : Subgroup G), (∃ g : G, M = CFSG.conjugate G₀ g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (η : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)),
        (∀ h : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom, (η h : ModGL TwistTag.E6.tag k) =
          diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) →
      ∀ (hx : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
          graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (φ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)),
        φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η →
      ∀ (w : G) (hwM : w ∈ M), w ∈ L → w * w = 1 → t * w = w * t →
        eM (QuotientGroup.mk' (center M) ⟨w, hwM⟩) = φ⁻¹ ⟨_, hx⟩ →
        w ∈ perfectCore (M ⊓ centralizer ({t} : Set G)) →
        (∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c) →
      ∀ (htwM : t * w ∈ normalizer (M : Set G)),
        (∃ φ₁ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
          φ₁ * normalizerQuotMulAut eM ⟨t * w, htwM⟩ * φ₁⁻¹ = η) →
      ∀ (htN : t ∈ normalizer (G₀ : Set G)) (htwN : t * w ∈ normalizer (G₀ : Set G)),
        G₀ ⊓ centralizer ({t} : Set G) = L →
        (∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
          ψ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * ψ⁻¹ = η) →
        (∃ φ' : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
          φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹ = MulAut.conj ⟨_, hx⟩ * η) →
        False

@[expose] def TwoTwistedE6SpanXiExclusionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (k : Type) [Field k] [Finite k] (σ' : k ≃+* k), Nat.card k = 4 → (∀ c, σ' c = c ^ 2) →
      ∀ G₀ : Subgroup G, G₀ = centralizerPerfectCore (subgroupToG e X₀) ⊔ L →
      ∀ (_e₀ : G₀ ⧸ center G₀ ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (M : Subgroup G), (∃ g : G, M = CFSG.conjugate G₀ g) →
      ∀ (htM : t ∈ normalizer (M : Set G))
        (eM : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (hx : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
          graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)
        (ψ η : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom)),
        (∀ h : graphFixedRootGroup TwistTag.E6 k σ'.toRingHom, (η h : ModGL TwistTag.E6.tag k) =
          diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) →
        ψ * normalizerQuotMulAut eM ⟨t, htM⟩ * ψ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η

@[expose] def TwoTwistedE6SpanUniqueInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (e : L ≃* adjointGroup .F4 K) (t : G), F4Work L K t 1 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 → TwoKindAt e t X₀ .unitary6 →
      TwoKindAt (e.trans (graphAutF4 K).symm) t X₀ .omegaPlus8 →
      ∀ (k : Type) [Field k] [Finite k] (σ' : k ≃+* k), Nat.card k = 4 → (∀ c, σ' c = c ^ 2) →
      ∀ M : Subgroup G, M = centralizerPerfectCore (subgroupToG e X₀) ⊔ L →
      ∀ (_e₆ : M ⧸ center M ≃* graphFixedRootGroup TwistTag.E6 k σ'.toRingHom) (g : G),
        g⁻¹ * t * g ∈ normalizer (M : Set G) → g ∈ normalizer (M : Set G)

end Statements

section Reduction

theorem twoTwistedE6SpanXiExclusionInput_of_caseL (hC3 : TwoTwistedE6SpanConjugateInput)
    (hL : TwoTwistedE6XiCaseLInput) : TwoTwistedE6SpanXiExclusionInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' k _ _ σ' hk hσ' G₀ hG₀ e₀ M hM htM eM hx φ η
    hη hφ
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ'.toRingHom c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ' c
  obtain ⟨hG₀p, hLG₀, htN, hC, hZ, hC₀, η₀, hη₀, φ₀, hφ₀⟩ :=
    twoTwistedSpan_facts hw X₀ σ' hk hσ' hG₀ e₀
  have hηη₀ : η₀ = η := MulEquiv.ext fun x => Subtype.ext ((hη₀ x).trans (hη x).symm)
  rw [hηη₀] at hφ₀
  have hk2' : Nat.card k = 2 ^ (2 * 1) := by rw [hk]; norm_num
  have hk2 : ringChar k = 2 :=
    CFSG.LieType.Chevalley.E6SecondGraphFixed.ringChar_eq_two_of_card (by omega) hk2'
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  obtain ⟨g₁, hg₁⟩ := hM
  set g : G := g₁⁻¹ with hgdef
  have hMg : M = CFSG.conjugate G₀ g⁻¹ := by rw [hgdef, inv_inv]; exact hg₁
  subst hMg
  have hZM : Odd (Nat.card (center (CFSG.conjugate G₀ g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  obtain ⟨hx2, hηx, hfix⟩ :=
    xi_data_of_le hk2 (graphFixedRootGroup_E6_le_adjointGroup σ'.toRingHom) hη hx
  obtain ⟨w, hww, htw, hwq, htwM, hφw⟩ :=
    exists_partner_of_conj_eq_conj_mul hZM eM htM hx2 hηx hφ
  have hperfA := fixSubgroup_perfect_of_conj hφ
    (commutator_fixSubgroup_xi_twistedE6_two σ'.toRingHom hk hσ' hη hx)
  have hwΛ := mem_perfectCore_of_fixSubgroup_perfect hZM eM hw.orderOf_eq htM hperfA hww htw
  have hwL : (w : G) ∈ L :=
    perfectCore_inf_centralizer_le hw.standard hOut hw.mem_centralizer hw.orderOf_eq _ hwΛ
  have hwG₀ : (w : G) ∈ G₀ := hLG₀ hwL
  have hcomm : ∀ c ∈ CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G),
      c * w = w * c := fun c hc =>
    commute_partner_of_fix hZM eM htM hφ hfix hww hwq hc.1
      (mem_centralizer_singleton_iff.1 hc.2)
  have hww' : (w : G) * w = 1 := by rw [← Subgroup.coe_mul, hww, Subgroup.coe_one]
  have hkG : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card le_rfl hkG hk'
  let _ : Algebra (GaloisField 2 1) k := ι.toAlgebra
  obtain ⟨-, ⟨-, hPP, -, -, hexh, hfaith, -⟩⟩ :=
    even_E6_graph_inner_coset_exhaustion 1 le_rfl (GaloisField 2 1) k hkG hk' σ'.toRingHom hσ1
  have hfaith' : ∀ c ∈ graphFixedRootGroup TwistTag.E6 k σ'.toRingHom,
      (∀ h ∈ graphFixedRootGroup TwistTag.E6 k σ'.toRingHom, c * h * c⁻¹ = h) → c = 1 :=
    fun c hc h => hfaith c (Subgroup.mem_sup_left hc) h
  have ht2 : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htw2 : (t * w) * (t * w) = 1 := by
    calc (t * w) * (t * w) = t * ((w : G) * t) * w := by group
      _ = t * (t * w) * w := by rw [htw]
      _ = (t * t) * ((w : G) * w) := by group
      _ = 1 := by rw [ht2, hww', mul_one]
  have hgs : g⁻¹ * (t * w) * g ∈ normalizer (G₀ : Set G) :=
    conj_mem_normalizer_of_mem_normalizer_conjugate_inv htwM
  have hη' : ∃ φ₂ : MulAut (graphFixedRootGroup TwistTag.E6 k σ'.toRingHom),
      φ₂ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ₂⁻¹ = η := by
    rw [← normalizerQuotMulAut_conjugate e₀ hgs htwM]
    set eM' := (E6Pilot.coverConjugateQuotientCenterEquiv G₀ g⁻¹).symm.trans e₀
    have heM : eM = eM'.trans (eM'.symm.trans eM) := MulEquiv.ext fun x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [heM] at hφw
    exact (exists_conj_eq_iff_trans eM' (eM'.symm.trans eM) _ η).1 ⟨φ, hφw⟩
  have hMC : CFSG.conjugate G₀ g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L := by
    intro hCM
    have hLM : L ≤ CFSG.conjugate G₀ g⁻¹ := fun x hx => by
      rw [← hCM] at hx
      exact hx.1
    exact false_of_le_of_conj_xi_twistedE6 hLM hw.center_eq_bot hw.card_eq e hk' hσ1 eM
      hw.mem_centralizer htM hη hx hφ
  have hstep : ∀ h : G, t ∈ normalizer (CFSG.conjugate G₀ h : Set G) →
      CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → CFSG.conjugate G₀ h = G₀ :=
    fun h hth hCh => hC3 G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' k σ' hk hσ' G₀ hG₀ e₀ h hth hCh
  rcases inner_or_xi_of_mem hPP hexh hfaith' hx hη e₀ htN hφ₀ hwG₀ htw2 with
    ⟨y, hy⟩ | ⟨φ', hφ'⟩
  · exact false_of_xi_partner_inner_twistedE6_of_conj (e := e) hw hk' hσ1 hG₀p e₀ hZ hC htN hη
      hC₀ hstep g hMC hww' htw hgs hη' (mul_mem htN (le_normalizer hwG₀)) y hy
  · exact hL G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' k σ' hk hσ' G₀ hG₀ e₀ _ ⟨g⁻¹, rfl⟩ htM eM η hη
      hx φ hφ w w.2 hwL hww' htw hwq hwΛ hcomm htwM ⟨φ, hφw⟩ htN
      (mul_mem htN (le_normalizer hwG₀)) hC₀ ⟨φ₀, hφ₀⟩ ⟨φ', hφ'⟩

theorem twoTwistedE6SpanUniqueInput_of_inputs (hξ : TwoTwistedE6SpanXiExclusionInput)
    (hC : TwoTwistedE6SpanConjugateInput) : TwoTwistedE6SpanUniqueInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ hκ' k _ _ σ' hk hσ' M hM e₆ g hg
  have hk' : Nat.card k = (2 ^ 1) ^ 2 := by rw [hk]; norm_num
  have hσ1 : ∀ c, σ'.toRingHom c = c ^ 2 ^ 1 := fun c => by
    rw [pow_one]
    exact hσ' c
  obtain ⟨hMp, -, -, -, hZ, -⟩ := twoTwistedSpan_facts hw X₀ σ' hk hσ' hM e₆
  have htM' := mem_normalizer_conjugate_inv hg
  have hMp' := E6Pilot.commutator_conjugate_eq hMp g⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate M g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  rcases inf_centralizer_eq_or_xi_twistedE6_quot_27 hw.standard hw.card_eq e hw.mem_centralizer
      hw.orderOf_eq hw.inf_eq hMp' hZM hk' σ'.toRingHom hσ1
      ((E6Pilot.coverConjugateQuotientCenterEquiv M g⁻¹).symm.trans e₆) htM' with
    ⟨hCM, -⟩ | ⟨hx, ψ, η, hη, hψ⟩
  · exact mem_normalizer_of_conjugate_inv_eq
      (hC G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' k σ' hk hσ' M hM e₆ g⁻¹ htM' hCM)
  · exact absurd hψ (hξ G L K e t hw X₀ hXJ hcyc hX₀ hκ hκ' k σ' hk hσ' M hM e₆ _
      ⟨g⁻¹, rfl⟩ htM' _ hx ψ η hη)

end Reduction

section Row

local instance f4PilotQ2TwistedE6XiExclusionNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

end Row

end CFSG.SeitzReduction.F4Pilot
