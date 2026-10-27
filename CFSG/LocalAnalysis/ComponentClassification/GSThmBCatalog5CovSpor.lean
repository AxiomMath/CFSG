module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovOrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovJ2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovM12
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovHS
public import CFSG.LocalAnalysis.SteinbergCCHSMultiplier
public import CFSG.Sporadic.Recognition.HeMultiplier

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

include hKa in
theorem alphaK_mul_self : alphaK hKa * alphaK hKa = 1 := by
  have ha2 : (⟨h.a, h.a_mem_normalizer⟩ : h.W) * ⟨h.a, h.a_mem_normalizer⟩ = 1 :=
    Subtype.ext (by
      show h.a * h.a = 1
      rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one])
  rw [← map_mul, ha2, map_one]

include hKa in
theorem coe_phi_abar :
    ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h)) =
      CFSG.GH74.KGroups.inducedHom (alphaK hKa) := by
  show rhoBar hKa (abar h) = _
  rw [rhoBar_mk]
  rfl

include hKa in
theorem exists_cover_data {X : Type} [Group X] (e : ZStarBar h.K ≃* X)
    (hZJ : center (OddBar h.J) = ⊥) (hJ : SmallQ (OddBar h.J)) :
    ∃ (π : OddBar h.K →* X) (β : MulAut X) (M : Subgroup X),
      Function.Surjective π ∧ π.ker = center (OddBar h.K) ∧
      (∀ x, π (alphaK hKa x) = β (π x)) ∧
      CFSG.Assembly.IsComponentOf M (fixSub β) ∧ SmallQ (↥M ⧸ center ↥M) := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eL, -⟩ : ∃ f : LK h ≃* X, f = eZ.trans e := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ g : MulAut (LK h), g = ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h)) :=
    ⟨_, rfl⟩
  obtain ⟨M₀, hM₀, ⟨eM⟩⟩ := exists_fix_component center_LK (inn_le_GAut hKa)
    (phi hKa (abar h)) (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2
  rw [← hφ] at hM₀
  have hφα : φ = CFSG.GH74.KGroups.inducedHom (alphaK hKa) := by rw [hφ, coe_phi_abar]
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  refine ⟨eL.toMonoidHom.comp (QuotientGroup.mk' (center (OddBar h.K))),
    (eL.symm.trans φ).trans eL, M₀.map eL.toMonoidHom, ?_, ?_, ?_,
    isComponentOf_fixSub_map eL φ hM₀, ?_⟩
  · rw [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact eL.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  · intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hφα, QuotientGroup.mk'_apply, CFSG.GH74.KGroups.inducedHom_mk]
  · refine CovHS.smallQ_of_equiv (CovHS.quotCenterEquiv
      ((((M₀.equivMapOfInjective _ eL.injective).symm.trans eM)))).symm ?_
    rcases hJ with ⟨p, f, hp, hp2, hf, hq, hm⟩ | ⟨⟨e7⟩⟩
    · exact Or.inl ⟨p, f, hp, hp2, hf, hq, OddQuot.lieModel_of_equiv eJ.symm hm⟩
    · exact Or.inr ⟨eJ.trans e7⟩

theorem exists_zpowers_of_card_two {G : Type*} [Group G] {Z : Subgroup G} [Finite Z]
    (hZ : Nat.card Z = 2) : ∃ t : G, orderOf t = 2 ∧ Z = zpowers t := by
  have hne : Z ≠ ⊥ := fun h' => by
    rw [h', Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  obtain ⟨⟨t, htZ⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hdvd : orderOf t ∣ 2 := by
    rw [← hZ, ← Subgroup.orderOf_mk t htZ]
    exact orderOf_dvd_natCard _
  have ht2 : orderOf t = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1'
    · exact h1
  refine ⟨t, ht2, (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htZ) ?_).symm⟩
  rw [hZ, Nat.card_zpowers, ht2]

include hKa in
theorem twist_center_of {t : OddBar h.K} (ht : orderOf t = 2)
    (hZ : center (OddBar h.K) = zpowers t) (htw : ∃ k, alphaK hKa k = k * t) :
    ∀ c ∈ center (OddBar h.K), ∃ k, (alphaK hKa k)⁻¹ * k = c := by
  have ht2 : t * t = 1 := by
    have h0 := pow_orderOf_eq_one t
    rw [ht, sq] at h0
    exact h0
  intro c hc
  rw [hZ] at hc
  rcases eq_one_or_eq_of_mem_zpowers ht2 hc with rfl | rfl
  · exact ⟨1, by rw [map_one, inv_one, one_mul]⟩
  · obtain ⟨k, hk⟩ := htw
    refine ⟨k, ?_⟩
    have h1 : (alphaK hKa k)⁻¹ * k = (k * c)⁻¹ * k := congrArg (fun y => y⁻¹ * k) hk
    rw [h1, mul_inv_rev, inv_mul_cancel_right]
    exact inv_eq_of_mul_eq_one_right ht2

theorem card_center_le_two_of_hs
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ center Q ≃* Blueprint.NativeSporadic.HS) : Nat.card (center Q) ≤ 2 := by
  have h1 := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess
    (S := Blueprint.NativeSporadic.HS) hQ e
  have h2 : Nat.card (CFSG.Open.griessHopfMultiplier Blueprint.NativeSporadic.HS) = 2 :=
    (Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      Blueprint.NativeSporadic.HS).toEquiv).trans
      CFSG.LocalAnalysis.HigmanSimsCover.card_hopfMultiplier
  rw [h2] at h1
  exact Nat.le_of_dvd (by norm_num) h1

theorem card_center_eq_two (hZK : center (OddBar h.K) ≠ ⊥)
    (hle : Nat.card (center (OddBar h.K)) ≤ 2) : Nat.card (center (OddBar h.K)) = 2 := by
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  rcases n with _ | n
  · exfalso
    apply hZK
    rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  · rw [hn] at hle ⊢
    rcases n with _ | n
    · rfl
    · exfalso
      have : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

include hKa in
theorem concl_of_card_two (hI : CF23InnerFusion) (hZK : center (OddBar h.K) ≠ ⊥)
    (hle : Nat.card (center (OddBar h.K)) ≤ 2)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hexc : ¬ CF23Exception ↥(NL hKa) (↥(Jhat hKa) ⧸ center ↥(Jhat hKa)))
    (htw : ∀ t : OddBar h.K, orderOf t = 2 → center (OddBar h.K) = zpowers t →
      ∃ k, alphaK hKa k = k * t) : h.Fus23Concl := by
  have hZJ : center (OddBar h.J) = ⊥ := by
    rcases hJ with hA | ⟨p, f, -, -, -, -, hm⟩
    · obtain ⟨e⟩ := hA
      exact IdxRed.center_eq_bot_of_alt (by norm_num) e
    · exact IdxRed.center_eq_bot_of_psl2 hm
  obtain ⟨t, ht, hZ⟩ := exists_zpowers_of_card_two (card_center_eq_two hZK hle)
  exact concl_of_twist hKa hI hZJ hJ hexc (twist_center_of hKa ht hZ (htw t ht hZ))

include hKa in
theorem card_NL : Nat.card ↥(NL hKa) = Nat.card (ZStarBar h.K) := by
  obtain ⟨eN⟩ := nonempty_NL_equiv hKa
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  rw [Nat.card_congr eN.toEquiv, Nat.card_congr eZ.toEquiv]

theorem center_eq_bot_of_small {Y : Type} [Group Y]
    (hJ : Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel Y .PSL 2 p f) :
    center Y = ⊥ := by
  rcases hJ with hA | ⟨p, f, -, -, -, -, hm⟩
  · obtain ⟨e⟩ := hA
    exact IdxRed.center_eq_bot_of_alt (by norm_num) e
  · exact IdxRed.center_eq_bot_of_psl2 hm

include hKa in
theorem concl_of_j2
    (hI : CF23InnerFusion) (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .J2) : h.Fus23Concl := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLq : CFSG.Assembly.IsQuasisimple (OddBar h.K) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).2 h.isQuasisimple_K
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hle : Nat.card (center (OddBar h.K)) ≤ 2 :=
    StandardRecognition.m12J2CentralTwoGroupOrderBound (OddBar h.K) hLq hZ2
      (Or.inr ⟨eZ.trans e⟩)
  have hcard : Nat.card ↥(NL hKa) = 604800 :=
    (card_NL hKa).trans ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2)
  have hexc := not_cf23Exception_of_card (J := ↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) hcard
    (by rintro k (rfl | rfl | rfl | rfl | rfl) <;> decide +kernel) CovJ2.ordA_one_ne_604800
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num)
  obtain ⟨π, β, M, hπ, hker, hβ, hM, hMt⟩ :=
    exists_cover_data hKa (e : ZStarBar h.K ≃* Blueprint.NativeSporadic.J2)
      (center_eq_bot_of_small hJ) hJ.symm
  exact concl_of_card_two hKa hI hZK hle hJ hexc fun t ht hZ =>
    CovJ2.twist hLq ht hZ π hπ (hker.trans hZ) (alphaK hKa) (alphaK_mul_self hKa) β hβ hM hMt

include hKa in
theorem concl_of_m12
    (hI : CF23InnerFusion) (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .M12) : h.Fus23Concl := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLq : CFSG.Assembly.IsQuasisimple (OddBar h.K) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).2 h.isQuasisimple_K
  have hZ2 : IsPGroup 2 (center (OddBar h.K)) :=
    isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  have hle : Nat.card (center (OddBar h.K)) ≤ 2 :=
    StandardRecognition.m12J2CentralTwoGroupOrderBound (OddBar h.K) hLq hZ2
      (Or.inl ⟨eZ.trans e⟩)
  have hcard : Nat.card ↥(NL hKa) = 95040 :=
    (card_NL hKa).trans ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12)
  have hexc := not_cf23Exception_of_card (J := ↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) hcard
    (by rintro k (rfl | rfl | rfl | rfl | rfl) <;> decide +kernel) CovM12.ordA_one_ne_95040
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num)
  obtain ⟨π, β, M, hπ, hker, hβ, hM, hMt⟩ :=
    exists_cover_data hKa (e : ZStarBar h.K ≃* ↥Blueprint.NativeSporadic.M12)
      (center_eq_bot_of_small hJ) hJ.symm
  exact concl_of_card_two hKa hI hZK hle hJ hexc fun t ht hZ =>
    CovM12.twist hLq ht hZ π hπ (hker.trans hZ) (alphaK hKa) (alphaK_mul_self hKa) β hβ hM hMt

include hKa in
theorem concl_of_hs
    (hI : CF23InnerFusion) (hZK : center (OddBar h.K) ≠ ⊥)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .HS) : h.Fus23Concl := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  have hLq : CFSG.Assembly.IsQuasisimple (OddBar h.K) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).2 h.isQuasisimple_K
  have hle : Nat.card (center (OddBar h.K)) ≤ 2 :=
    card_center_le_two_of_hs h.isQuasisimple_K.1 (eZ.trans e)
  have hcard : Nat.card ↥(NL hKa) = 44352000 :=
    (card_NL hKa).trans ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS)
  have hexc := not_cf23Exception_of_card (J := ↥(Jhat hKa) ⧸ center ↥(Jhat hKa)) hcard
    (by rintro k (rfl | rfl | rfl | rfl | rfl) <;> decide +kernel) CovHS.ordA_one_ne_44352000
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by norm_num)
  obtain ⟨π, β, M, hπ, hker, hβ, hM, hMt⟩ :=
    exists_cover_data hKa ((e : ZStarBar h.K ≃* Blueprint.NativeSporadic.HS).trans hsPermEquiv)
      (center_eq_bot_of_small hJ) hJ.symm
  exact concl_of_card_two hKa hI hZK hle hJ hexc fun t ht hZ =>
    CovHS.twist hLq ht hZ π hπ (hker.trans hZ) (alphaK hKa) (alphaK_mul_self hKa) β hβ hM hMt

end CFSG.ComponentClassification.GSThmB.Cov
