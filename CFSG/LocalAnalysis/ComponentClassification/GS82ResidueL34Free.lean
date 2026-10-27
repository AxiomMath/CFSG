module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDatum
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4
public import CFSG.LocalAnalysis.ComponentClassification.GS82P10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10S8
public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueVertData
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34Theta
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128Cop

public section

namespace CFSG.ComponentClassification

open CFSG Subgroup

@[expose] def GSThmB.GS82ResidueStatement' : Prop :=
  ∀ (X : Type) [Group X] [Finite X], GSThmB.GS82HAmbient X →
    ∀ q₀ : ℕ, q₀ ∈ ({5, 7, 9} : Finset ℕ) →
    ∀ (t : X) (K R T : Subgroup X) (w : X), GSThmB.GS82HConfig q₀ t K R T w →
      t ∈ GH74.GLS.pLayerOf 2 (centralizer ({t} : Set X)) →
      ¬ (GH74.GLS.IsL34Quotient (GH74.GLS.kBar K) ∧ Nat.card ↥(center (GH74.GLS.kBar K)) = 16) →
      False

namespace GS82PumpInputs.Residue

open CFSG.Semidihedral.Principal
open scoped commutatorElement MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem typQ_of_gs82HConfig' (hP10 : KGSLTwoSmallInput)
    (hP11 : L34CentralSLTwoFact) {q₀ : ℕ} (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ)) {t : X}
    {K R T : Subgroup X} {w : X} (h : GSThmB.GS82HConfig q₀ t K R T w)
    (hKg : SectionRank.IsKGroupCat ↥(centralizer ({t} : Set X)))
    (hK16 : ¬ (GH74.GLS.IsL34Quotient (GH74.GLS.kBar K) ∧
      Nat.card ↥(center (GH74.GLS.kBar K)) = 16)) : TypQ q₀ ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hKt, hKc, hR2, hRt, hRK, hTKR, hTc, hSL, hw, hwT, hwK⟩ := h
  have hTK : T ≤ K := hTKR.trans inf_le_left
  have hTt : T ≤ centralizer ({t} : Set X) := hTK.trans hKt
  have hKRt : K ⊓ centralizer (R : Set X) ≤ centralizer ({t} : Set X) := inf_le_left.trans hKt
  have hq5 : 5 ≤ q₀ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    omega
  have hdvd : q₀ * (q₀ ^ 2 - 1) ∣ Nat.card (↥K ⧸ pPrimeCore 2 ↥K) := by
    rw [← card_of_isSLTwoOver hSL]
    exact card_quot_dvd_of_le hTK
  set C := centralizer ({t} : Set X) with hC
  have hB : IsPGroup 2 (R.subgroupOf C) := hR2.of_equiv (subgroupOfEquivOfLe hRt).symm
  have hBM : R.subgroupOf C ≤ normalizer ((K.subgroupOf C : Subgroup _) : Set _) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    have h1 := mem_normalizer_iff.mp (hRK (mem_subgroupOf.mp hb)) (x : X)
    simpa using h1
  have hMB : (K.subgroupOf C) ⊓ centralizer ((R.subgroupOf C : Subgroup _) : Set _) =
      (K ⊓ centralizer (R : Set X)).subgroupOf C := by
    ext x
    rw [mem_inf, mem_subgroupOf, mem_subgroupOf, mem_inf, mem_centralizer_iff,
      mem_centralizer_iff]
    constructor
    · rintro ⟨hxK, hxR⟩
      exact ⟨hxK, fun r hr => congrArg Subtype.val (hxR ⟨r, hRt hr⟩ (mem_subgroupOf.mpr hr))⟩
    · rintro ⟨hxK, hxR⟩
      exact ⟨hxK, fun r hr => Subtype.ext (hxR r (mem_subgroupOf.mp hr))⟩
  have hTM : T.subgroupOf C ≤ (K.subgroupOf C) ⊓
      centralizer ((R.subgroupOf C : Subgroup _) : Set _) := by
    rw [hMB]
    intro x hx
    exact mem_subgroupOf.mpr (hTKR (mem_subgroupOf.mp hx))
  have hTc' : IsPComponent 2 ((T.subgroupOf C).subgroupOf
      ((K.subgroupOf C) ⊓ centralizer ((R.subgroupOf C : Subgroup _) : Set _))) := by
    rw [hMB]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hKRt 2 Nat.prime_two).mpr hTc
  have hSL' : HarrisLit.IsSLTwoOver q₀ (↥(T.subgroupOf C) ⧸ pPrimeCore 2 ↥(T.subgroupOf C)) :=
    DPrime.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hTt).symm hSL
  have hwC : w ∈ C := hTt hwT
  have hwC2 : orderOf (⟨w, hwC⟩ : ↥C) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
  set eK : ↥(K.subgroupOf C) ≃* ↥K := subgroupOfEquivOfLe hKt with heK
  have hwM : (⟨w, hwC⟩ : ↥C) ∈
      (Open.fusionZStar ↥(K.subgroupOf C)).map (K.subgroupOf C).subtype := by
    obtain ⟨k, hk, hkw⟩ := hwK
    refine ⟨eK.symm k, apply_mem_fusionZStar eK.symm hk, ?_⟩
    apply Subtype.ext
    exact hkw
  rcases hP10 _ hKg _ hKc _ hB hBM _ hTM hTc' q₀ hq₀ hSL' ⟨w, hwC⟩ hwC2
      (mem_subgroupOf.mpr hwT) hwM with ⟨q₂, hq₂, hq₀₂, hSL₂⟩ | hodd | ⟨n, hn, h2A⟩ | ⟨hL, -⟩
  ·
    refine ⟨Or.inl (oddLieType_of_mulEquiv (Sol78.coreQuotientCenterEquiv ↥K) ?_), hdvd⟩
    exact oddLieType_center_quot_of_isSLTwoOver (DPrime.isSLTwoOver_of_mulEquiv eK hSL₂) hq₂
      (hq5.trans hq₀₂)
  · exact ⟨Or.inl (oddLieType_of_mulEquiv (Sol78.fusionZStarQuotCongr eK) hodd), hdvd⟩
  · exact ⟨Or.inr ⟨n, hn, isDoubleCoverOfAlt_of_mulEquiv (Sol78.coreQuotCongr eK) h2A⟩, hdvd⟩
  exfalso
  have hL' : GH74.GLS.IsL34Quotient (↥K ⧸ pPrimeCore 2 ↥K) :=
    Blueprint.LieModel.of_mulEquiv (Sol78.centerQuotCongr (Sol78.coreQuotCongr eK)) hL
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKt)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hKc)
  let α : ↥R →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hRK)
  have hα : ∀ (a : ↥R) (y : ↥K), ((α a y : ↥K) : X) = a * y * (a : X)⁻¹ := fun a y => rfl
  set F := (K ⊓ centralizer (R : Set X)).subgroupOf K with hFdef
  have hF : ∀ y : ↥K, y ∈ F ↔ ∀ a : ↥R, α a y = y := by
    intro y
    rw [mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨-, hy⟩ a
      apply Subtype.ext
      rw [hα]
      calc (a : X) * y * (a : X)⁻¹ = y * a * (a : X)⁻¹ := by rw [hy a a.2]
        _ = y := by group
    · intro hy
      refine ⟨y.2, fun r hr => ?_⟩
      have h1 := congrArg Subtype.val (hy ⟨r, hr⟩)
      rw [hα] at h1
      calc r * (y : X) = r * y * r⁻¹ * r := by group
        _ = y * r := by rw [h1]
  have hTF : T.subgroupOf K ≤ F := fun y hy => mem_subgroupOf.mpr (hTKR (mem_subgroupOf.mp hy))
  have hTF' : IsPComponent 2 ((T.subgroupOf K).subgroupOf F) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTc
  have hSLK : HarrisLit.IsSLTwoOver q₀ (↥(T.subgroupOf K) ⧸ pPrimeCore 2 ↥(T.subgroupOf K)) :=
    DPrime.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hTK).symm hSL
  obtain ⟨k, hk, hkw⟩ := hwK
  have hk2 : orderOf k = 2 := by
    rw [← hw, ← hkw]
    exact (Subgroup.orderOf_coe k).symm
  have hkT : k ∈ T.subgroupOf K := mem_subgroupOf.mpr (by rw [← hkw] at hwT; exact hwT)
  have h16 := card_center_eq_sixteen_of_twoGroup hP11 hKq hL' hR2 α hF hTF hTF' hq₀ hSLK hk2
    hkT hk
  exact hK16 ⟨hL', h16⟩

theorem false_of_escData
    {q₀ : ℕ} (hodd : Odd q₀) (hq1 : q₀ ≠ 1) {v x : X}
    {M Λ : Subgroup X} (hv : orderOf v = 2) (hMv : M ≤ centralizer ({v} : Set X))
    (hMc : IsPComponent 2 (M.subgroupOf (centralizer ({v} : Set X)))) (hML : TypL16 ↥M)
    (hx : orderOf x = 2) (hxv : x ∈ centralizer ({v} : Set X))
    (hxN : x ∈ normalizer (M : Set X))
    (hxin : x ∈ zpowers v ⊔ GH74.GLS.pLayerOf 2 (centralizer ({v} : Set X)))
    (hnt : ∃ m ∈ M, m⁻¹ * (x⁻¹ * m * x) ∉ GH74.GLS.pPrimeCoreOf 2 M)
    (hΛ : Λ ≤ M ⊓ centralizer ({x} : Set X))
    (hdvd : q₀ * (q₀ ^ 2 - 1) ∣ Nat.card (↥Λ ⧸ pPrimeCore 2 ↥Λ)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hpq)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥Λ ⧸ pPrimeCore 2 ↥Λ) p
    ((hpq.trans (dvd_mul_right _ _)).trans hdvd)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
  have hlM : (l : X) ∈ M := (hΛ l.2).1
  have hlx : (l : X) * x = x * l := mem_centralizer_singleton_iff.mp (hΛ l.2).2
  have hfix : (l : X)⁻¹ * (x⁻¹ * l * x) ∈ GH74.GLS.pPrimeCoreOf 2 M := by
    have e : x⁻¹ * (l : X) * x = l := by rw [mul_assoc, hlx, inv_mul_cancel_left]
    rw [e, inv_mul_cancel]
    exact one_mem _
  obtain ⟨k, hk⟩ := GSThmB.lemmaTheta v x hv hx (mem_centralizer_singleton_iff.mp hxv).symm M
    ⟨hMv, hMc⟩ hxN hML.1 hML.2 hnt hxin (l : X) hlM hfix
  have hkΛ : ((l ^ (2 ^ k) : ↥Λ) : X) ∈ GH74.GLS.pPrimeCoreOf 2 Λ :=
    GH74.GLS.Stage2.Bender.Thm2.L128.pPrimeCoreOf_inf_le (hΛ.trans inf_le_left)
      ⟨by rw [Subgroup.coe_pow]; exact hk, (l ^ (2 ^ k)).2⟩
  obtain ⟨z, hz, hzeq⟩ := hkΛ
  have e : z = l ^ (2 ^ k) := Subtype.ext hzeq
  rw [e] at hz
  have h1 : (QuotientGroup.mk l : ↥Λ ⧸ pPrimeCore 2 ↥Λ) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hz
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

theorem gs82ResidueStatement'_of
    (hP : TypPumpInput) (hP10 : KGSLTwoSmallInput) (hP11 : L34CentralSLTwoFact)
    (hH1 : HarrisLit.Harris82Theorem1KProper) (hSol : GSThmB.Solomon2AnInput)
    (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) : GSThmB.GS82ResidueStatement' := by
  intro X _ _ hamb q₀ hq₀ t K R T w h htL hK16
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnonab, hKP, hcat, hz, hU⟩ := id hamb
  haveI := hsimple
  have hKg : ∀ v : X, orderOf v = 2 → SectionRank.IsKGroupCat ↥(centralizer ({v} : Set X)) :=
    fun v hv => GSThmB.isKGroupCat_of_ne_top' hKP
      (Helpers.centralizer_ne_top_of_involution X hnonab v hv)
  have hq5 : 5 ≤ q₀ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    omega
  have hodd : Odd q₀ := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq₀ with rfl | rfl | rfl <;> decide
  have hTypK : TypQ q₀ ↥K := typQ_of_gs82HConfig' hP10 hP11 hq₀ h (hKg t h.1) hK16
  rcases theoremDPrimeEscData_holds hodd hq5 (verticalCentralEsc'_typQ hP hP11 hq₀)
      (coreInvariant_typQ q₀) coreInvariant_typL16 (diagonalTransfer_typQ q₀) hKg
      (GSThmB.isDatum_of_gs82HConfig h) hTypK htL with
    ⟨w', J, N', hJd, hw'J, hJtype, -⟩ |
      ⟨v, x, M, Λ, hv, hMv, hMc, hML, hx, hxv, hxN, hxin, hnt, hΛ, hΛQ⟩
  swap
  · exact false_of_escData hodd (by omega) hv hMv hMc hML hx hxv hxN hxin hnt hΛ hΛQ.2
  obtain ⟨hw', hJw', hJc, hN'J, -, hN'SL, -, hw'N', -, hw'Z⟩ := hJd
  have hJ := (HarrisLit.isTwoComponentIn_iff hJw').mpr hJc
  rcases hJtype with hoddLie | ⟨n, hn, h2A⟩
  ·
    obtain ⟨τ, m, p, f, hp, hp2, -, hm⟩ := hoddLie
    have hSLJ : HarrisLit.IsSLTwoOver q₀
        (↥(N'.subgroupOf J) ⧸ pPrimeCore 2 ↥(N'.subgroupOf J)) :=
      DPrime.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hN'J).symm hN'SL
    have hcZ : (⟨w', hw'J⟩ : ↥J) ∈ Open.fusionZStar ↥J := by
      obtain ⟨k, hk, hkw⟩ := hw'Z
      have : k = ⟨w', hw'J⟩ := Subtype.ext hkw
      rwa [← this]
    have hM := mTypeOfSLTwoSection_holds ↥J hJ.2.2 p hp hp2 ⟨τ, m, f, hm⟩ (N'.subgroupOf J) q₀
      hodd hq5 hSLJ ⟨w', hw'J⟩ (by rw [Subgroup.orderOf_mk]; exact hw')
      (mem_subgroupOf.mpr hw'N') hcZ
    exact HarrisLit.not_isMTypeSchur_of_kProper hH1 hnonab hKP hcat hw' hJ hw'J hp hp2 hM
  rcases hn.lt_or_eq with h8 | rfl
  ·
    rcases hSol X w' hw' J n (by omega) hJw' hJc hw'J h2A.1.1 h2A.2.1 h2A.2.2 with e | e
    · exact hcat (.inr (.inr (.inr (.inr ⟨.McL, e⟩))))
    · exact hcat (.inr (.inr (.inr (.inr ⟨.Ly, e⟩))))
  have hwit := (GSThmB.X10.classical_of_twoA7 hJw' hJc h2A).2.2
  have hrank : CFSG.pRank 2 J ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
    obtain ⟨hq, hc, hφ⟩ := h2A
    obtain ⟨π, hπ⟩ := GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt
      (H := J ⧸ pPrimeCore 2 J) (n := 7) ⟨hq, inferInstance, hc, hφ⟩
    exact (GH74.GLS.IVK.Lifted.pRank_eq_one_of_twoCover_seven hπ).le
  exact GSThmB.intrinsic_rank_one_exclusion hCI hUc hnonab hz hU hw' hJw' hJc hw'J hrank hwit

theorem gs82ResidueStatement'_of_typPump
    (hP : TypPumpInput) (hP11 : L34CentralSLTwoFact) (hH1 : HarrisLit.Harris82Theorem1KProper)
    (hSol : GSThmB.Solomon2AnInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) : GSThmB.GS82ResidueStatement' :=
  gs82ResidueStatement'_of hP (kgSLTwoSmallInput_of_typPump hP) hP11 hH1 hSol hCI hUc

end GS82PumpInputs.Residue

end CFSG.ComponentClassification
