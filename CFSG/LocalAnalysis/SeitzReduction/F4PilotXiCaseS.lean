module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiInner

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

section Lift

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_eq_of_normalizerQuotMulAut_eq_conj {G₀ : Subgroup G} (hG₀ : ⁅G₀, G₀⁆ = G₀)
    (hC : Odd (Nat.card (centralizer (G₀ : Set G)))) {X : Type*} [Group X]
    (e₀ : G₀ ⧸ center G₀ ≃* X) {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hsN : s ∈ normalizer (G₀ : Set G)) (htN : t ∈ normalizer (G₀ : Set G)) (y : G₀)
    (h : normalizerQuotMulAut e₀ ⟨s, hsN⟩ =
      MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)) * normalizerQuotMulAut e₀ ⟨t, htN⟩ *
        (MulAut.conj (e₀ (QuotientGroup.mk' (center G₀) y)))⁻¹) :
    ∃ n ∈ normalizer (G₀ : Set G), s = n * t * n⁻¹ := by
  have : Group.IsPerfect G₀ := Subgroup.isPerfect_iff.2 hG₀
  have hyN : (y : G) ∈ normalizer (G₀ : Set G) := le_normalizer y.2
  set t' : G := y * t * (y : G)⁻¹ with ht'def
  have ht'N : t' ∈ normalizer (G₀ : Set G) :=
    mul_mem (mul_mem hyN htN) (inv_mem hyN)
  have hA : normalizerQuotMulAut e₀ ⟨t', ht'N⟩ = normalizerQuotMulAut e₀ ⟨s, hsN⟩ := by
    have e1 : (⟨t', ht'N⟩ : normalizer (G₀ : Set G)) =
        ⟨y, hyN⟩ * ⟨t, htN⟩ * (⟨y, hyN⟩ : normalizer (G₀ : Set G))⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, h,
      EPilot.normalizerQuotMulAut_of_mem e₀ y.2]
  set c : G := t'⁻¹ * s with hcdef
  have hcN : c ∈ normalizer (G₀ : Set G) := mul_mem (inv_mem ht'N) hsN
  have hc1 : normalizerQuotMulAut e₀ ⟨c, hcN⟩ = 1 := by
    have e1 : (⟨c, hcN⟩ : normalizer (G₀ : Set G)) =
        (⟨t', ht'N⟩ : normalizer (G₀ : Set G))⁻¹ * ⟨s, hsN⟩ := rfl
    rw [e1, map_mul, map_inv, hA, inv_mul_cancel]
  have hcC : c ∈ centralizer (G₀ : Set G) := by
    have hk : (⟨c, hcN⟩ : normalizer (G₀ : Set G)) ∈ (normalizerQuotMulAut e₀).ker := hc1
    rw [EPilot.ker_normalizerQuotMulAut e₀, mem_subgroupOf] at hk
    exact hk
  have ht'2 : t' * t' = 1 := by
    rw [ht'def]
    calc (y : G) * t * (y : G)⁻¹ * ((y : G) * t * (y : G)⁻¹) = (y : G) * (t * t) * (y : G)⁻¹ := by
          group
      _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
  have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have hsc : s = t' * c := by rw [hcdef, ← mul_assoc, mul_inv_cancel, one_mul]
  have hinv : t' * c * t'⁻¹ = c⁻¹ := by
    have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    calc t' * c * t'⁻¹ = t' * (t'⁻¹ * s) * t'⁻¹ := by rw [hcdef]
      _ = s * t' := by rw [← mul_assoc, mul_inv_cancel, one_mul, ht'i]
      _ = c⁻¹ := by rw [hcdef, mul_inv_rev, inv_inv, hsi]
  have hinvpow : ∀ j : ℕ, t' * c ^ j * t'⁻¹ = c⁻¹ ^ j := by
    intro j
    rw [← hinv, ← MulAut.conj_apply, ← MulAut.conj_apply, map_pow]
  have hcodd : Odd (orderOf c) := by
    have h1 := orderOf_dvd_natCard (⟨c, hcC⟩ : centralizer (G₀ : Set G))
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hC h1
  obtain ⟨k, hk⟩ := hcodd
  have hck : c ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one c
  refine ⟨c ^ k * y, mul_mem (pow_mem (centralizer_le_normalizer _ hcC) k) hyN, ?_⟩
  have h2 : c ^ k * t' * (c ^ k)⁻¹ = c ^ (2 * k) * t' := by
    have h3 : t' * (c ^ k)⁻¹ = c ^ k * t' := by
      have h4 := hinvpow k
      rw [inv_pow] at h4
      calc t' * (c ^ k)⁻¹ = (t' * c ^ k * t'⁻¹)⁻¹ * t' := by group
        _ = c ^ k * t' := by rw [h4, inv_inv]
    rw [mul_assoc, h3, ← mul_assoc, ← pow_add, ← two_mul]
  have h5 : c ^ (2 * k) = c⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, hck]
  have h6 : c⁻¹ * t' = t' * c := by
    calc c⁻¹ * t' = t' * c * t'⁻¹ * t' := by rw [hinv]
      _ = t' * c := by group
  calc s = t' * c := hsc
    _ = c ^ k * t' * (c ^ k)⁻¹ := by rw [h2, h5, h6]
    _ = c ^ k * y * t * (c ^ k * y)⁻¹ := by rw [ht'def]; group

end Lift

section Transfer


theorem mem_normalizer_of_eta_conjugate {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : L ≃* adjointGroup .F4 K) {t : G} (ht : orderOf t = 2)
    (hZ : Odd (Nat.card (center (pieceSpan e)))) {X : Type*} [Group X]
    (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* X) (η : MulAut X)
    (htN : t ∈ normalizer (pieceSpan e : Set G))
    (h₀ : pieceSpan e ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut X, φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = η)
    (g : G) (htM : t ∈ normalizer (CFSG.conjugate (pieceSpan e) g⁻¹ : Set G))
    (hM : CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) = L ∧
        ∃ φ : MulAut X, φ * normalizerQuotMulAut
          ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹).symm.trans e₀)
            ⟨t, htM⟩ * φ⁻¹ = η) :
    g ∈ normalizer (pieceSpan e : Set G) := by
  obtain ⟨hC₀, φ₀, hφ₀⟩ := h₀
  obtain ⟨hCM, φM, hφM⟩ := hM
  set χ := E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g⁻¹ with hχ
  set eM := χ.symm.trans e₀ with heM
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hfix₀ := fixSubgroup_eq_map_of_inf_eq hZ e₀ ht htN hC₀
  have hfixM := fixSubgroup_eq_map_of_inf_eq hZM eM ht htM hCM
  have hmap₀ := map_eqLocus_eq_of_conj hφ₀
  have hmapM := map_eqLocus_eq_of_conj hφM
  set ψ : MulAut (pieceSpan e ⧸ center (pieceSpan e)) :=
    ((e₀.trans φ₀).trans φM.symm).trans e₀.symm with hψ
  have hLM : L ≤ CFSG.conjugate (pieceSpan e) g⁻¹ := by
    intro x hx
    have h1 : x ∈ CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) := by
      rw [hCM]
      exact hx
    exact h1.1
  have hgL : L.map (MulAut.conj g⁻¹).toMonoidHom ≤ pieceSpan e := by
    rintro _ ⟨l, hl, rfl⟩
    have h1 := hLM hl
    rw [mem_conjugate_iff_of_mul] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  refine mem_normalizer_of_quotAut_map_eq hf hK e hgL ψ ?_
  rw [← map_coverConjugateQuotientCenterEquiv_symm g]
  apply Subgroup.map_injective (f := e₀.toMonoidHom) e₀.injective
  have hmap₀' : (E6Pilot.fixSubgroup (normalizerQuotMulAut e₀ ⟨t, htN⟩)).map φ₀.toMonoidHom =
      E6Pilot.fixSubgroup η := hmap₀
  have hφM' : (E6Pilot.fixSubgroup η).map φM.symm.toMonoidHom =
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
    change (η.toMonoidHom.eqLocus (MonoidHom.id X)).map φM.symm.toMonoidHom = _
    rw [← hmapM, Subgroup.map_map]
    have : φM.symm.toMonoidHom.comp φM.toMonoidHom = MonoidHom.id X :=
      MonoidHom.ext fun x => φM.symm_apply_apply x
    rw [this, Subgroup.map_id]
    rfl
  have hL1 : (((L.subgroupOf (pieceSpan e)).map (QuotientGroup.mk' (center (pieceSpan e)))).map
        ψ.toMonoidHom).map e₀.toMonoidHom =
      (((L.subgroupOf (pieceSpan e)).map
        (e₀.toMonoidHom.comp (QuotientGroup.mk' (center (pieceSpan e))))).map
          φ₀.toMonoidHom).map φM.symm.toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψ, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
  have hR1 : (((L.subgroupOf (CFSG.conjugate (pieceSpan e) g⁻¹)).map
        (QuotientGroup.mk' (center (CFSG.conjugate (pieceSpan e) g⁻¹)))).map
          χ.symm.toMonoidHom).map e₀.toMonoidHom =
      (L.subgroupOf (CFSG.conjugate (pieceSpan e) g⁻¹)).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center (CFSG.conjugate (pieceSpan e) g⁻¹)))) := by
    simp only [Subgroup.map_map]
    rfl
  rw [hL1, hR1, ← hfixM, ← hfix₀, hmap₀', hφM']

end Transfer

section CaseS


theorem not_conj_eta_xi_E6 {f : ℕ} (hf : 1 ≤ f) {K' : Type} [Field K'] (hK' : Nat.card K' = 2 ^ f)
    {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K')
    (φ : MulAut (adjointGroup TwistTag.E6.tag K')) :
    φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η := by
  have hM' : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hK' hM'
  let _ : Algebra K' (GaloisField 2 (2 * f)) := ι.toAlgebra
  obtain ⟨⟨-, -, -, -, -, -, ht, η₀, hη₀, -, hnc⟩, -⟩ :=
    even_E6_graph_inner_coset_exhaustion f hf K' (GaloisField 2 (2 * f)) hK' hM'
      (iterateFrobenius (GaloisField 2 (2 * f)) 2 f) (fun c => iterateFrobenius_def (p := 2) f c)
  have hηη₀ : η = η₀ := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη₀ h).symm)
  subst hηη₀
  exact hnc φ

theorem false_of_xi_partner_inner_E6 {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K 2] {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2 ^ f)
    (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup TwistTag.E6.tag K')
    (hZ : Odd (Nat.card (center (pieceSpan e))))
    (hC : Odd (Nat.card (centralizer (pieceSpan e : Set G))))
    (htN : t ∈ normalizer (pieceSpan e : Set G)) {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (h₀ : pieceSpan e ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K'),
        φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = η)
    (g : G) (hMC : CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L)
    {w : G} (hw2 : w * w = 1) (htw : t * w = w * t)
    (hgs : g⁻¹ * (t * w) * g ∈ normalizer (pieceSpan e : Set G))
    (hη' : ∃ φ : MulAut (adjointGroup TwistTag.E6.tag K'),
      φ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ⁻¹ = η)
    (htwN : t * w ∈ normalizer (pieceSpan e : Set G)) (y : pieceSpan e)
    (hS : normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ =
      MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)) *
        normalizerQuotMulAut e₀ ⟨t, htN⟩ *
          (MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)))⁻¹) : False := by
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hG₀ := commutator_pieceSpan e
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
  have hg' : g'⁻¹ * t * g' ∈ normalizer (pieceSpan e : Set G) := hg'e ▸ hgs
  have htM' := mem_normalizer_conjugate_inv hg'
  have hA : normalizerQuotMulAut
      ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀) ⟨t, htM'⟩ =
        normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ := by
    rw [normalizerQuotMulAut_conjugate e₀ hg' htM']
    congr 2
  obtain ⟨φ', hφ'⟩ := hη'
  rw [← hA] at hφ'
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g'⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g'⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hCM : CFSG.conjugate (pieceSpan e) g'⁻¹ ⊓ centralizer ({t} : Set G) = L := by
    rcases inf_centralizer_eq_or_xi_E6_quot hw.standard hf hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hMp hZM hK'
        ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀) htM' with
      ⟨hC', -⟩ | ⟨η₁, hη₁, hx, φ₁, hφ₁⟩
    · exact hC'
    · exfalso
      have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      refine not_conj_eta_xi_E6 hw.one_le hK' hη hx (φ₁ * φ'⁻¹) ?_
      calc φ₁ * φ'⁻¹ * η * (φ₁ * φ'⁻¹)⁻¹
          = φ₁ * φ'⁻¹ * (φ' * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ'⁻¹) * (φ₁ * φ'⁻¹)⁻¹ := by rw [hφ']
        _ = φ₁ * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ₁⁻¹ := by group
        _ = MulAut.conj ⟨_, hx⟩ * η := by rw [hφ₁, h1]
  have hg'N := mem_normalizer_of_eta_conjugate hf hw.card_eq e hw.orderOf_eq hZ e₀ η htN h₀ g'
    htM' ⟨hCM, φ', hφ'⟩
  have hgN : g ∈ normalizer (pieceSpan e : Set G) := by
    have : g = n * g' := by rw [hg'def, mul_inv_cancel_left]
    rw [this]
    exact mul_mem hnN hg'N
  have hMeq : CFSG.conjugate (pieceSpan e) g⁻¹ = pieceSpan e := by
    rw [conjugate_inv_eq_map]
    exact (mem_normalizer_iff_map_conj_eq.1 hgN)
  exact hMC (by rw [hMeq]; exact h₀.1)

end CaseS

section CaseSTwisted


theorem not_conj_eta_xi_twistedE6 {f : ℕ} (hf : 1 ≤ f) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K₂ e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K₂ σ)
    (φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)) :
    φ * η * φ⁻¹ ≠ MulAut.conj ⟨_, hx⟩ * η := by
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK₂
  let _ : Algebra (GaloisField 2 f) K₂ := ι.toAlgebra
  obtain ⟨-, ⟨-, -, -, -, -, -, ht, η₀, hη₀, -, hnc⟩⟩ :=
    even_E6_graph_inner_coset_exhaustion f hf (GaloisField 2 f) K₂ hk hK₂ σ hσ
  have hηη₀ : η = η₀ := MulEquiv.ext fun h => Subtype.ext ((hη h).trans (hη₀ h).symm)
  subst hηη₀
  exact hnc φ

theorem false_of_xi_partner_inner_twistedE6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {e : L ≃* adjointGroup .F4 K} {t : G} {f : ℕ}
    (hw : F4Work L K t f) (hf : 2 ≤ f) {K₂ : Type} [Field K₂] [Finite K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) {σ : K₂ →+* K₂} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e₀ : pieceSpan e ⧸ center (pieceSpan e) ≃* graphFixedRootGroup TwistTag.E6 K₂ σ)
    (hZ : Odd (Nat.card (center (pieceSpan e))))
    (hC : Odd (Nat.card (centralizer (pieceSpan e : Set G))))
    (htN : t ∈ normalizer (pieceSpan e : Set G))
    {η : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ)}
    (hη : ∀ h : graphFixedRootGroup TwistTag.E6 K₂ σ, (η h : ModGL TwistTag.E6.tag K₂) =
      diagramMap TwistTag.E6 K₂ * h * (diagramMap TwistTag.E6 K₂)⁻¹)
    (h₀ : pieceSpan e ⊓ centralizer ({t} : Set G) = L ∧
      ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
        φ * normalizerQuotMulAut e₀ ⟨t, htN⟩ * φ⁻¹ = η)
    (g : G) (hMC : CFSG.conjugate (pieceSpan e) g⁻¹ ⊓ centralizer ({t} : Set G) ≠ L)
    {w : G} (hw2 : w * w = 1) (htw : t * w = w * t)
    (hgs : g⁻¹ * (t * w) * g ∈ normalizer (pieceSpan e : Set G))
    (hη' : ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K₂ σ),
      φ * normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ * φ⁻¹ = η)
    (htwN : t * w ∈ normalizer (pieceSpan e : Set G)) (y : pieceSpan e)
    (hS : normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ =
      MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)) *
        normalizerQuotMulAut e₀ ⟨t, htN⟩ *
          (MulAut.conj (e₀ (QuotientGroup.mk' (center (pieceSpan e)) y)))⁻¹) : False := by
  have hG₀ := commutator_pieceSpan e
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
  have hg' : g'⁻¹ * t * g' ∈ normalizer (pieceSpan e : Set G) := hg'e ▸ hgs
  have htM' := mem_normalizer_conjugate_inv hg'
  have hA : normalizerQuotMulAut
      ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀) ⟨t, htM'⟩ =
        normalizerQuotMulAut e₀ ⟨g⁻¹ * (t * w) * g, hgs⟩ := by
    rw [normalizerQuotMulAut_conjugate e₀ hg' htM']
    congr 2
  obtain ⟨φ', hφ'⟩ := hη'
  rw [← hA] at hφ'
  have hMp := E6Pilot.commutator_conjugate_eq hG₀ g'⁻¹
  have hZM : Odd (Nat.card (center (CFSG.conjugate (pieceSpan e) g'⁻¹))) := by
    rw [E6Pilot.card_center_conjugate]
    exact hZ
  have hout := not_inner_quot_twistedE6_row hw.standard hf hw.card_eq e hw.mem_centralizer
    hw.orderOf_eq hw.inf_eq hMp hZM hK₂ hσ
    ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀) htM'
  have hCM : CFSG.conjugate (pieceSpan e) g'⁻¹ ⊓ centralizer ({t} : Set G) = L := by
    rcases inf_centralizer_eq_or_xi_twistedE6_quot hw.standard hw.card_eq e hw.mem_centralizer
        hw.orderOf_eq hw.inf_eq hZM hK₂ σ hσ
        ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀) htM'
        hout with ⟨hC', -⟩ | ⟨hx, φ₁, η₁, hη₁, hφ₁⟩
    · exact hC'
    · exfalso
      have h1 : η₁ = η := MulEquiv.ext fun x => Subtype.ext ((hη₁ x).trans (hη x).symm)
      refine not_conj_eta_xi_twistedE6 hw.one_le hK₂ hσ hη hx (φ₁ * φ'⁻¹) ?_
      calc φ₁ * φ'⁻¹ * η * (φ₁ * φ'⁻¹)⁻¹
          = φ₁ * φ'⁻¹ * (φ' * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ'⁻¹) * (φ₁ * φ'⁻¹)⁻¹ := by rw [hφ']
        _ = φ₁ * normalizerQuotMulAut
              ((E6Pilot.coverConjugateQuotientCenterEquiv (pieceSpan e) g'⁻¹).symm.trans e₀)
                ⟨t, htM'⟩ * φ₁⁻¹ := by group
        _ = MulAut.conj ⟨_, hx⟩ * η := by rw [hφ₁, h1]
  have hg'N := mem_normalizer_of_eta_conjugate hf hw.card_eq e hw.orderOf_eq hZ e₀ η htN h₀ g'
    htM' ⟨hCM, φ', hφ'⟩
  have hgN : g ∈ normalizer (pieceSpan e : Set G) := by
    have : g = n * g' := by rw [hg'def, mul_inv_cancel_left]
    rw [this]
    exact mul_mem hnN hg'N
  have hMeq : CFSG.conjugate (pieceSpan e) g⁻¹ = pieceSpan e := by
    rw [conjugate_inv_eq_map]
    exact (mem_normalizer_iff_map_conj_eq.1 hgN)
  exact hMC (by rw [hMeq]; exact h₀.1)

end CaseSTwisted

end CFSG.SeitzReduction.F4Pilot
