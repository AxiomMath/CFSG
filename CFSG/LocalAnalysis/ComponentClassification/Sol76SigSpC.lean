module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigSpB
public import CFSG.LocalAnalysis.ComponentClassification.Sol76R12Sp4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverMult

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4

section Sp4

variable {F : Type} [Field F]

theorem eq_one_or_eq_negS_of_mem_center {c : StatedSp 2 F} (hc : c ∈ center (StatedSp 2 F)) :
    c = 1 ∨ c = negS F := by
  rw [LieType.Universal.Symplectic.center_eq 2 F] at hc
  rcases (mem_spScalars_iff c).mp hc with h | h
  · exact Or.inl (sp_ext h)
  · exact Or.inr (eq_negS_of_coe h)

theorem negS_mem_center : negS F ∈ center (StatedSp 2 F) :=
  mem_center_of_mem_spScalars ((mem_spScalars_iff _).mpr (Or.inr rfl))

theorem spJ_mul_spJ (hF : ringChar F ≠ 2) : R12.spJ F * R12.spJ F = negS F :=
  (eq_one_or_eq_negS_of_mem_center (R12.spJ_sq_mem_center F)).resolve_left
    (R12.spJ_sq_ne_one hF)

theorem exists_commute_sq_eq_negS (hF : ringChar F ≠ 2) {x : StatedSp 2 F} (hx : x * x = 1)
    (hx1 : x ≠ 1) : ∃ k : StatedSp 2 F, k * x = x * k ∧ k * k = negS F := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hJ := spJ_mul_spJ hF
  by_cases hxn : x = negS F
  · refine ⟨R12.spJ F, ?_, hJ⟩
    rw [hxn]
    exact ((mem_center_iff.mp negS_mem_center) (R12.spJ F))
  have hT1 : R12.spT F ≠ 1 := fun h =>
    R12.spT_not_mem_center hF (h ▸ one_mem _)
  have hTn : R12.spT F ≠ negS F := fun h =>
    R12.spT_not_mem_center hF (h ▸ negS_mem_center)
  obtain ⟨g, hg⟩ := exists_conj_T1_of_sq h2 hx hx1 hxn
  obtain ⟨h, hh⟩ := exists_conj_T1_of_sq h2 (R12.spT_mul_self F) hT1 hTn
  set u := g * h⁻¹ with hu
  have hxu : x = u * R12.spT F * u⁻¹ := by
    have e : g⁻¹ * x * g = h⁻¹ * R12.spT F * h := hg.trans hh.symm
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (h⁻¹ * R12.spT F * h) * g⁻¹ := by rw [e]
      _ = u * R12.spT F * u⁻¹ := by rw [hu]; group
  refine ⟨u * R12.spJ F * u⁻¹, ?_, ?_⟩
  · rw [hxu]
    calc u * R12.spJ F * u⁻¹ * (u * R12.spT F * u⁻¹)
        = u * (R12.spJ F * R12.spT F) * u⁻¹ := by group
      _ = u * (R12.spT F * R12.spJ F) * u⁻¹ := by rw [R12.spJ_mul_spT]
      _ = u * R12.spT F * u⁻¹ * (u * R12.spJ F * u⁻¹) := by group
  · calc u * R12.spJ F * u⁻¹ * (u * R12.spJ F * u⁻¹) = u * (R12.spJ F * R12.spJ F) * u⁻¹ := by
          group
      _ = negS F := by
          rw [hJ, (mem_center_iff.mp negS_mem_center) u, mul_inv_cancel_right]

theorem exists_conj_mem_of_isKleinFour [Finite F] (hF : ringChar F ≠ 2)
    {E : Subgroup (StatedSp 2 F)} (hE : IsKleinFour E) {x : StatedSp 2 F} (hx : x * x = 1)
    (hx1 : x ≠ 1) :
    ∃ g : StatedSp 2 F, g⁻¹ * x * g ∈ E := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hsq : ∀ y ∈ E, y * y = 1 := fun y hy => by
    rw [← sq]
    exact Sig.sq_eq_one_of_isKleinFour hE hy
  obtain ⟨a, haE, ha1⟩ := exists_mem_ne_one_of_isKleinFour hE
  obtain ⟨b, hbE, hbz⟩ := exists_not_mem_zpowers_of_isKleinFour hE haE
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ one_mem _)
  have hab : a ≠ b := fun h => hbz (h ▸ mem_zpowers a)
  have habc : a * b = b * a := comm_of_isKleinFour hE a haE b hbE
  have habE : a * b ∈ E := mul_mem haE hbE
  obtain ⟨y, hyE, hy1, hyn⟩ : ∃ y ∈ E, y ≠ 1 ∧ y ≠ negS F := by
    by_cases han : a = negS F
    · exact ⟨b, hbE, hb1, fun h => hab (han.trans h.symm)⟩
    · exact ⟨a, haE, ha1, han⟩
  by_cases hxn : x = negS F
  · refine ⟨1, ?_⟩
    rw [inv_one, one_mul, mul_one, hxn]
    rcases neg_one_mem_of_four_group h2 (hsq a haE) (hsq b hbE) habc ha1 hb1 hab with h | h | h
    · exact h ▸ haE
    · exact h ▸ hbE
    · exact h ▸ habE
  obtain ⟨g₁, hg₁⟩ := exists_conj_T1_of_sq h2 hx hx1 hxn
  obtain ⟨g₂, hg₂⟩ := exists_conj_T1_of_sq h2 (hsq y hyE) hy1 hyn
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have e : (g₁ * g₂⁻¹)⁻¹ * x * (g₁ * g₂⁻¹) = g₂ * (g₁⁻¹ * x * g₁) * g₂⁻¹ := by group
  rw [e, hg₁, ← hg₂]
  have e2 : g₂ * (g₂⁻¹ * y * g₂) * g₂⁻¹ = y := by group
  rw [e2]
  exact hyE

end Sp4

theorem sp4_facts_of_mulEquiv {Q : Type} [Group Q] {F : Type} [Field F] (hF : ringChar F ≠ 2)
    (ι : Q ≃* StatedSp 2 F) {z : Q} (hz : z ∈ center Q) (hz1 : z ≠ 1) :
    (∀ q ∈ center Q, q = 1 ∨ q = z) ∧
      ∀ s : Q, s * s = 1 → s ≠ 1 → ∃ k : Q, k * s = s * k ∧ k * k = z := by
  have hcen : ∀ q ∈ center Q, ι q ∈ center (StatedSp 2 F) := fun q hq =>
    mem_center_iff.mpr fun g => by
      obtain ⟨y, rfl⟩ := ι.surjective g
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hq) y]
  have hιz : ι z = negS F := (eq_one_or_eq_negS_of_mem_center (hcen z hz)).resolve_left
    (fun h => hz1 (ι.injective (h.trans (map_one ι).symm)))
  refine ⟨fun q hq => ?_, fun s hs hs1 => ?_⟩
  · rcases eq_one_or_eq_negS_of_mem_center (hcen q hq) with h | h
    · exact Or.inl (ι.injective (h.trans (map_one ι).symm))
    · exact Or.inr (ι.injective (h.trans hιz.symm))
  · have hs' : ι s * ι s = 1 := by rw [← map_mul, hs, map_one]
    have hs1' : ι s ≠ 1 := fun h => hs1 (ι.injective (h.trans (map_one ι).symm))
    obtain ⟨k, hk, hkk⟩ := exists_commute_sq_eq_negS hF hs' hs1'
    refine ⟨ι.symm k, ι.injective ?_, ι.injective ?_⟩
    · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hk]
    · rw [map_mul, MulEquiv.apply_symm_apply, hkk, hιz]

theorem exists_mulEquiv_statedSp_of_symplectic (hS : R12.QuasisimpleRankTwoSymplecticInput)
    (hGA : TBLit.GriessMultipliersAllModels) {Q : Type} [Group Q] [Finite Q]
    (hQq : IsQuasisimple Q) (hQO : pPrimeCore 2 Q = ⊥)
    (hQcat : Blueprint.Catalog (Q ⧸ center Q)) (hQr : CFSG.pRank 2 Q = 2) {z : Q}
    (hz : z ∈ center Q) (hz2 : orderOf z = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧ Nonempty (Q ≃* StatedSp 2 F) := by
  classical
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := hS Q hQq hQO hQcat hQr ⟨z, hz, hz2⟩
  have : Fintype k := Fintype.ofFinite k
  have : CharP k (ringChar k) := ringChar.charP k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hm : Blueprint.LieModel (Q ⧸ center Q) .PSp 2 (ringChar k) n := by
    refine Or.inl ⟨by decide, ⟨hp, hn, le_refl 2, fun hh => hk ?_⟩, k, inferInstance,
      inferInstance, by rw [Nat.card_eq_fintype_card, hcard], ⟨e⟩⟩
    have h2 : ringChar k ^ (n : ℕ) = 2 := (Prod.mk.inj hh).2
    have hle : ringChar k ≤ ringChar k ^ (n : ℕ) := Nat.le_self_pow (by omega) _
    have := hp.two_le
    omega
  have hZ : center Q ≠ ⊥ := fun h => hz1 (by rw [h] at hz; exact mem_bot.mp hz)
  obtain ⟨F, _, _, hFcard, ⟨ι⟩⟩ := exists_mulEquiv_statedSp hGA
    (@Milestones.cl_lit_griess_schur_multipliers_central_covers) hQq hZ hp hk hm
  have hFodd : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    refine (FiniteField.even_card_iff_char_two (F := F)).not.mpr ?_
    have hodd : Odd (ringChar k ^ (n : ℕ)) := (hp.odd_of_ne_two hk).pow
    rw [← Nat.card_eq_fintype_card, hFcard]
    have h1 := Nat.odd_iff.mp hodd
    omega
  exact ⟨F, inferInstance, inferInstance, hFodd, ⟨ι⟩⟩

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem sp4CoreFacts_of_symplectic (hS : R12.QuasisimpleRankTwoSymplecticInput)
    (hGA : TBLit.GriessMultipliersAllModels) (hKK : KStarKProper G)
    (hK : K ∈ kStarComponents N) (h2K : CFSG.Open.pRank 2 K ≤ 2) {b : G} (hbK : b ∈ K)
    (hb2 : orderOf b = 2) (hbQ : b ∈ coreActionKernel K) : Sp4CoreFacts K b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQr : CFSG.pRank 2 (↥K ⧸ pPrimeCore 2 ↥K) = 2 := by
    rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
    have := two_le_pRank_of_mem_solomonKStar hK.2
    omega
  set Q := ↥K ⧸ pPrimeCore 2 ↥K with hQdef
  have hQq : IsQuasisimple Q := isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hQO : pPrimeCore 2 Q = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2
  have hQcat := catalog_coreQuotient_of_mem_solomonKStar hKK hK.1 hK.2
  set z : Q := QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨b, hbK⟩ with hzdef
  have hz : z ∈ center Q := Sig.mk_mem_center_quot_of_mem_coreActionKernel hbQ
  have hz2 : orderOf z = 2 :=
    Sig.orderOf_mk_eq_two (y := ⟨b, hbK⟩) (by rw [Subgroup.orderOf_mk]; exact hb2)
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  obtain ⟨F, _, _, hFodd, ⟨ι⟩⟩ :=
    exists_mulEquiv_statedSp_of_symplectic hS hGA hQq hQO hQcat hQr hz hz2
  obtain ⟨hcen, hinv⟩ := sp4_facts_of_mulEquiv hFodd ι hz hz1
  refine ⟨fun y hyK hyQ => ?_, fun s hsK hs2 => ?_⟩
  · rcases hcen _ (Sig.mk_mem_center_quot_of_mem_coreActionKernel (y := ⟨y, hyK⟩) hyQ) with h | h
    · exact Or.inl ((mk_eq_one_iff (N := K)).mp h)
    · right
      rw [hzdef] at h
      exact (mk_eq_mk_iff (N := K)).mp h
  · have hs2' : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨s, hsK⟩ : ↥K)) = 2 :=
      Sig.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hs2)
    have hss : QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨s, hsK⟩ : ↥K) *
        QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨s, hsK⟩ : ↥K) = 1 := by
      have h := pow_orderOf_eq_one (QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨s, hsK⟩ : ↥K))
      rw [hs2', sq] at h
      exact h
    have hs1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨s, hsK⟩ : ↥K) ≠ 1 := fun h => by
      rw [h, orderOf_one] at hs2'
      norm_num at hs2'
    obtain ⟨kbar, hks, hkk⟩ := hinv _ hss hs1
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) kbar
    refine ⟨k₀, k₀.2, (mk_mul_comm_iff (⟨s, hsK⟩ : ↥K) k₀).mp hks.symm, ?_⟩
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) (k₀ * k₀) =
        QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨b, hbK⟩ : ↥K) := by
      rw [map_mul, hkk]
    exact (mk_eq_mk_iff (N := K)).mp h1

theorem forcedSharedRankTwoFor_of_symplectic (hS : R12.QuasisimpleRankTwoSymplecticInput)
    (hGA : TBLit.GriessMultipliersAllModels) : ForcedSharedRankTwoFor :=
  forcedSharedRankTwoFor_of_facts fun _ _ _ hG _ _ _ hK h2K _ hbK hb2 hbQ =>
    sp4CoreFacts_of_symplectic hS hGA (kStarKProper_of_simpleAmbient hG) hK h2K hbK hb2 hbQ

end CFSG.ComponentClassification.Sol76.Sig
