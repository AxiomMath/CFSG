module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PField
public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CL34
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionSemidirectTwo
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.TBLit.L34P
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

private theorem pPrimeCore_eq_bot_of_l34 {H : Type} [Group H] [Finite H] (hH : IsQuasisimple H)
    (hZ : IsPGroup 2 ↥(center H)) (hL : Blueprint.LieModel (H ⧸ center H) .PSL 3 2 2) :
    pPrimeCore 2 H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hH pPrimeCore_normal with
    h | h
  · rw [h, Subgroup.card_top, card_eq_card_quotient_mul_card_subgroup (center H),
      CatLeafProof.X10CL.card_of_lieModel_L34 hL] at hcop
    exact absurd (Nat.Coprime.coprime_dvd_right (dvd_mul_right 20160 _) hcop) (by norm_num)
  · rcases (hZ.to_le h).card_eq_or_dvd with h1 | h2
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop h2) (by norm_num)

variable {X : Type} [Group X] [Finite X]

private theorem card_eq_of_l34Frame
    {K L : Subgroup X} {β : X}
    (hK : ⁅K, K⁆ = K) (hOK : pPrimeCore 2 ↥K = ⊥) (hL34 : IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hβK : ¬ ∀ k ∈ K, β⁻¹ * k * β = k)
    (hLK : L ≤ K) (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9)
    (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F)) :
    Nat.card F = 7 ∧ Nat.card (center ↥K) = 16 := by
  have hodd : Odd (Nat.card F) := by rcases hF with h | h | h <;> rw [h] <;> decide
  obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβq⟩ := exists_frame hL34 hβN hβ2
  have hdvd : ∀ C : Subgroup (Equiv.Perm (Fin 42)), (imageHom hLK q).range ≤ C →
      Nat.card F * (Nat.card F ^ 2 - 1) ∣ 2 * Nat.card C := fun C hC => by
    have h := card_sl2_dvd hLK (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) e q
      hqker
    rw [card_sl2] at h
    exact h.trans (mul_dvd_mul_left 2 (Subgroup.card_dvd_of_le hC))
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  ·
    refine (hβK fun k hk => ?_).elim
    have : Group.IsPerfect (Jhat K) := ⟨commutator_jhat hK⟩
    have hid := PerfectAutomorphisms.hom_eq_id_of_central_displacement
      (betaHat K hβN).toMonoidHom fun x => by
        rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, hβq x,
          one_mul, inv_one, mul_one, inv_mul_cancel]
    have h1 : jq K (conjJ K hβN ⟨k, hk⟩) = jq K ⟨k, hk⟩ := by
      rw [← betaHat_jq]
      exact DFunLike.congr_fun hid (jq K ⟨k, hk⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hOK, mem_bot,
      inv_mul_eq_one] at h1
    have h2 := congrArg Subtype.val h1
    rwa [coe_conjJ] at h2
  ·
    have h := hdvd C₁ (range_imageHom_le hLK hβN hLβ hqS hβq)
    rw [card_C₁] at h
    rcases hF with h' | h' | h' <;> rw [h'] at h <;> norm_num at h
  ·
    have h7 : Nat.card F = 7 := by
      have h := hdvd C₂ (range_imageHom_le hLK hβN hLβ hqS hβq)
      rw [card_C₂] at h
      rcases hF with h' | h' | h'
      · rw [h'] at h
        norm_num at h
      · exact h'
      · rw [h'] at h
        norm_num at h
    refine ⟨h7, ?_⟩
    have h16 := card_zStarIn_of_field hK hL34 hβN hβ2 hLK hLβ h7 e
      (isL34Field_of_frame hβN hβ2 hqS hqsurj hqker hβq)
    rwa [zStarIn, oddIn, hOK, Subgroup.map_bot, Subgroup.card_bot, mul_one,
      Subgroup.card_map_of_injective K.subtype_injective,
      fusionZStar_eq_center_of_pPrimeCore_eq_bot hOK] at h16
  ·
    exact (false_of_graph hK hβN hLK hLβ hodd e hqS hqsurj hqker h3 hβq).elim
  ·
    have h := hdvd C₄ (range_imageHom_le hLK hβN hLβ hqS hβq)
    rw [card_C₄] at h
    rcases hF with h' | h' | h' <;> rw [h'] at h <;> norm_num at h

private theorem not_forall_conj_inl {H : Type} [Group H] {σ : MulAut H} (hσ1 : σ ≠ 1) :
    ¬ ∀ k ∈ (SemidirectProduct.inl (φ := MonoidHom.id (MulAut H))).range,
      (SemidirectProduct.inr σ)⁻¹ * k * SemidirectProduct.inr σ = k := by
  intro h
  refine hσ1 (MulEquiv.ext fun y => ?_)
  have h1 := h _ ⟨y, rfl⟩
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv] at h1
  have h2 : σ⁻¹ y = y := SemidirectProduct.inl_injective h1
  calc σ y = σ (σ⁻¹ y) := by rw [h2]
    _ = y := MulAut.apply_inv_self H σ y

private theorem card_eq_of_holomorph
    {H : Type} [Group H]
    [Finite H] (hH : Group.IsPerfect H) (hOH : pPrimeCore 2 H = ⊥)
    (hL : Blueprint.LieModel (H ⧸ center H) .PSL 3 2 2) {σ : MulAut H} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {N : Subgroup H} (hN : ∀ n ∈ N, σ n = n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9)
    (eN : ↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, F)) :
    Nat.card F = 7 ∧ Nat.card (center H) = 16 := by
  have : Finite (H ⋊[MonoidHom.id (MulAut H)] MulAut H) :=
    AschbacherComponentInvolution.semidirect_finite _
  have hKn := AschbacherComponentInvolution.semidirect_base_normal (MonoidHom.id (MulAut H))
  have hinj := SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut H))
  have hOK : pPrimeCore 2 ↥(SemidirectProduct.inl (φ := MonoidHom.id (MulAut H))).range = ⊥ := by
    rw [← pPrimeCore_map_iso 2 (MonoidHom.ofInjective hinj), hOH, Subgroup.map_bot]
  have hLβ : N.map (SemidirectProduct.inl (φ := MonoidHom.id (MulAut H))) ≤
      centralizer ({SemidirectProduct.inr σ} : Set (H ⋊[MonoidHom.id (MulAut H)] MulAut H)) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (AschbacherComponentInvolution.semidirect_fixed_commute _ σ n (hN n hn)).eq.symm
  obtain ⟨h7, h16⟩ := card_eq_of_l34Frame
    (K := (SemidirectProduct.inl (φ := MonoidHom.id (MulAut H))).range)
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)) hOK
    ((hL.of_mulEquiv (QuotientGroup.congr _ _ (MonoidHom.ofInjective hinj)
      (Subgroup.map_center_eq _))).of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOK).symm))
    (by rw [normalizer_eq_top_iff.mpr hKn]; exact mem_top _) (by rw [← map_mul, hσ2, map_one])
    (not_forall_conj_inl hσ1) (Subgroup.map_le_range _ _) hLβ hF
    ((QuotientGroup.congr _ _ (N.equivMapOfInjective _ hinj)
      (pPrimeCore_map_iso 2 _)).symm.trans eN)
  exact ⟨h7, (Nat.card_congr (Subgroup.centerCongr (MonoidHom.ofInjective hinj)).toEquiv).trans
    h16⟩

theorem l34CentralSLTwoFact_holds :
    L34CentralSLTwoFact := by
  intro H _ _ hH hZ hL σ hσ2 hσ1 N hNσ q₀ hq₀ hSL _ _ _ _
  obtain ⟨F, _, _, hFq, ⟨eN⟩⟩ := hSL
  have hF : Nat.card F = 5 ∨ Nat.card F = 7 ∨ Nat.card F = 9 := by
    rw [Nat.card_eq_fintype_card, hFq]
    simpa using hq₀
  obtain ⟨h7, h16⟩ := card_eq_of_holomorph hH.1 (pPrimeCore_eq_bot_of_l34 hH hZ hL) hL
    (MulEquiv.ext hσ2) hσ1 (fun n hn => hNσ hn) hF eN
  exact ⟨by rw [← hFq, ← Nat.card_eq_fintype_card, h7], h16⟩

end CFSG.ComponentClassification.GS82PumpInputs
