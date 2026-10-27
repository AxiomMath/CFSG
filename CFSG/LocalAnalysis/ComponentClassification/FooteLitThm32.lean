module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneBranch

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_commutator_self {H : Subgroup G} {g x : G} (hg : g ∈ normalizer (H : Set G))
    (hx : x ∈ ⁅H, H⁆) : g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  have hle : ⁅H, H⁆ ≤ (⁅H, H⁆).comap (MulAut.conj g).toMonoidHom := by
    rw [commutator_le]
    intro y hy z hz
    change g * ⁅y, z⁆ * g⁻¹ ∈ ⁅H, H⁆
    rw [show g * ⁅y, z⁆ * g⁻¹ = ⁅g * y * g⁻¹, g * z * g⁻¹⁆ by
      rw [commutatorElement_def, commutatorElement_def]; group]
    exact commutator_mem_commutator ((mem_normalizer_iff.mp hg y).mp hy)
      ((mem_normalizer_iff.mp hg z).mp hz)
  exact hle hx

theorem foote_thm32_target (hLB : FooteLBalanceInput) (hcore : FooteCoreAt G) {a b k : G}
    (ha : orderOf a = 2) (hk : orderOf k = 2) (hab : a * b = b * a) (hak : a * k = k * a)
    {K J : Subgroup G} (hK : IsTwoComponentAt b K) (hkK : k ∈ K)
    (hkC : k ∈ coreActionKernel K)
    (hD : ¬ ⁅oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) ⊓ centralizer ({k} : Set G),
      oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) ⊓ centralizer ({k} : Set G)⁆ ≤
        coreActionKernel K)
    (hJ : IsTwoComponentAt k J) (hTJ : UnbalancedGS.gsFixedLayer K k ≤ J) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 2 p f) ∧ k ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := UnbalancedGS.gsFixedLayer K k with hT
  set D := oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) ⊓ centralizer ({k} : Set G)
    with hDdef
  have hkT : k ∈ T := mem_gsFixedLayer_self hK hkK hk hkC
  refine ⟨?_, hTJ hkT⟩
  obtain ⟨-, hKb, hKpc⟩ := hK
  have hKq := isQuasisimple_quotient_of_isPComponent hKb hKpc
  have hTK : T ≤ K := (UnbalancedGS.gsFixedLayer_le_inf K k).trans inf_le_left
  have hTsup : T ⊔ oddCoreIn K = K := gsFixedLayer_sup_map_pPrimeCore hk hKq hkC.1 hkC.2
  have hDK : D ≤ normalizer (K : Set G) :=
    (inf_le_left : D ≤ _).trans (oddCoreOfCentralizer_inf_le_normalizer hLB ha hab hKb hKpc)
  have hDk : D ≤ oddCoreOfCentralizer a ⊓ centralizer ({k} : Set G) :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hDT : D ≤ normalizer (T : Set G) := fun d hd => by
    have h1 : d ∈ normalizer ((K ⊓ centralizer ({k} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf' (hDK hd)
        (mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2))
    exact mem_normalizer_twoLayerIn h1
  have hDJ' : ¬ ⁅D, D⁆ ≤ coreActionKernel J := by
    intro h
    apply hD
    intro x hx
    have hxD : x ∈ D := commutator_self_le D hx
    exact mem_coreActionKernel_of_sup hTK hTsup (hDK hxD)
      (mem_coreActionKernel_of_le hTJ (hDT hxD) (h hx))
  rcases hcore a k ha hk hak J hJ.2.1 hJ.2.2 with hL | h2
  · exact hL
  · exfalso
    apply hDJ'
    refine (commutator_mono hDk hDk).trans (le_coreActionKernel_of_commutator_le ?_ hJ.2.1 h2)
    exact (commutator_self_le _).trans
      (oddCoreOfCentralizer_inf_le_normalizer hLB ha hak hJ.2.1 hJ.2.2)

theorem foote_theorem_3_2 (hLB : FooteLBalanceInput) (hcore : FooteCoreAt G)
    (hβ : ∀ B : Subgroup G, (∃ b : G, IsTwoComponentAt b B) → FooteFamilyType B →
      Nat.card (center (B ⧸ pPrimeCore 2 B)) ≤ 2)
    (hnoCl : ∀ (x : G) (X : Subgroup G), IsTwoComponentAt x X → x ∈ X →
      CFSG.pRank 2 ↥X ≤ 1 → False)
    {a b : G} (ha : orderOf a = 2) (hab : a * b = b * a) {K : Subgroup G}
    (hK : IsTwoComponentAt b K)
    (hY : ¬ ⁅oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G),
      oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G)⁆ ≤ coreActionKernel K) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G) with hYdef
  obtain ⟨hb, hKb, hKpc⟩ := id hK
  have hKq := isQuasisimple_quotient_of_isPComponent hKb hKpc
  have hYK : Y ≤ normalizer (K : Set G) :=
    oddCoreOfCentralizer_inf_le_normalizer hLB ha hab hKb hKpc
  have hcl : ∀ (x : G) (B : Subgroup G), IsTwoComponentAt x B → x ∈ B → FooteFamilyType B →
      False := by
    intro x B hB hxB hBfam
    have hBq := isQuasisimple_quotient_of_isPComponent hB.2.1 hB.2.2
    have hZ := center_ne_bot_of_mem_coreActionKernel hxB hB.1
      (GSLit.mem_coreActionKernel_of_le_centralizer hB.2.1)
    exact hnoCl x B hB hxB (pRank_le_one_of_center_ne_bot hBq hBfam (hβ B ⟨x, hB⟩ hBfam) hZ)
  obtain ⟨p, f, hp, hp2, hf, hL⟩ : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (K ⧸ Open.fusionZStar K) .PSL 2 p f := by
    rcases hcore a b ha hb hab K hKb hKpc with hL | h2
    · exact hL
    · exact absurd (le_coreActionKernel_of_commutator_le
        ((commutator_self_le Y).trans hYK) hKb h2) hY
  have hKfam : FooteFamilyType K := footeFamilyType_of_lieModel hp hp2 hf hL
  by_cases hZ : center (K ⧸ pPrimeCore 2 K) = ⊥
  · obtain ⟨e⟩ := nonempty_fusionZStar_quotient_equiv ↥K
    exact ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv
      (e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)) hL⟩
  exfalso
  have hKrank : CFSG.pRank 2 ↥K ≤ 1 :=
    pRank_le_one_of_center_ne_bot hKq hKfam (hβ K ⟨b, hK⟩ hKfam) hZ
  by_cases hbK : b ∈ K
  · exact hnoCl b K hK hbK hKrank
  have haK : a ∈ normalizer (K : Set G) := by
    by_contra haK
    have hne : conjugate K a ≠ K := fun h => haK (mem_normalizer_of_conjugate_eq h)
    exact hY ((commutator_self_le Y).trans
      (le_coreActionKernel_of_balance hLB ha hab hKb hKpc (Or.inl hne)))
  obtain ⟨k, hkZ, hk, hak⟩ := exists_involution_commute ha
    (mem_normalizer_inf' haK (mem_normalizer_coreActionKernel haK))
    (two_dvd_card_inf_coreActionKernel hZ)
  obtain ⟨hkK, hkC⟩ := mem_inf.mp hkZ
  have hbk : b * k = k * b := (mem_centralizer_singleton_iff.mp (hKb hkK)).symm
  have hne : b ≠ k := fun h => hbK (h ▸ hkK)
  have hkCa : k ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hak.symm
  have hkY : k ∈ normalizer (Y : Set G) :=
    mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer hkCa)
      (mem_normalizer_centralizer_singleton hbk.symm)
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le inf_le_left)
  set D := Y ⊓ centralizer ({k} : Set G) with hDdef
  have hD : ¬ ⁅D, D⁆ ≤ coreActionKernel K := fun h =>
    hY (commutator_le_coreActionKernel_of_inf_centralizer hYodd hYK hkY hk hkC h)
  obtain ⟨J, hJ, -, hTJJ, -, hcase⟩ := exists_footeStep hLB hK hk hbk hne hkC
  have hkT : k ∈ UnbalancedGS.gsFixedLayer K k := mem_gsFixedLayer_self hK hkK hk hkC
  rcases hcase with ⟨hJb, -, -⟩ | ⟨hJb, -, -⟩ | ⟨hJb, -, -⟩
  · rw [hJb, sup_idem] at hTJJ
    obtain ⟨⟨p', f', hp', hp2', hf', hL'⟩, hkJ⟩ :=
      foote_thm32_target hLB hcore ha hk hab hak hK hkK hkC hD hJ hTJJ
    exact hcl k J hJ hkJ (footeFamilyType_of_lieModel hp' hp2' hf' hL')
  · rw [hJb, sup_idem] at hTJJ
    obtain ⟨⟨p', f', hp', hp2', hf', hL'⟩, hkJ⟩ :=
      foote_thm32_target hLB hcore ha hk hab hak hK hkK hkC hD hJ hTJJ
    exact hcl k J hJ hkJ (footeFamilyType_of_lieModel hp' hp2' hf' hL')
  set J' := conjugate J b with hJ'def
  have hbCk : b ∈ centralizer ({k} : Set G) := mem_centralizer_singleton_iff.mpr hbk
  have hJ' : IsTwoComponentAt k J' :=
    ⟨hk, conjugate_le_of_mem hJ.2.1 hbCk, isPComponent_conjugate_subgroupOf hbCk hJ.2.2⟩
  have hJJ'ne : J ≠ J' := fun h => hJb h.symm
  have hJ'J : J' ≤ coreActionKernel J :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJ.2.1 hJ'.2.1 hJ.2.2 hJ'.2.2 hJJ'ne
  have hJJ' : J ≤ coreActionKernel J' :=
    GSThmB.B5a.le_coreActionKernel_of_ne hJ'.2.1 hJ.2.1 hJ'.2.2 hJ.2.2 (Ne.symm hJJ'ne)
  set T := UnbalancedGS.gsFixedLayer K k with hT
  have hTK : T ≤ K := (UnbalancedGS.gsFixedLayer_le_inf K k).trans inf_le_left
  have hTsup : T ⊔ oddCoreIn K = K := gsFixedLayer_sup_map_pPrimeCore hk hKq hkC.1 hkC.2
  have hDK : D ≤ normalizer (K : Set G) := (inf_le_left : D ≤ Y).trans hYK
  have hDT : D ≤ normalizer (T : Set G) := fun d hd => by
    have h1 : d ∈ normalizer ((K ⊓ centralizer ({k} : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_inf' (hDK hd)
        (mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2))
    exact mem_normalizer_twoLayerIn h1
  have hkey : ∀ x ∈ D, x ∈ coreActionKernel J → x ∈ coreActionKernel J' →
      x ∈ coreActionKernel K := fun x hx hxJ hxJ' =>
    mem_coreActionKernel_of_sup hTK hTsup (hDK hx)
      (mem_coreActionKernel_of_sup_conjugate (fun y hy => (hJ'J hy).1) (fun y hy => (hJJ' hy).1)
        hTJJ (hDT hx) hxJ hxJ')
  set D₁ := oddCoreOfCentralizer a ⊓ centralizer ({k} : Set G) with hD₁def
  have hDD₁ : D ≤ D₁ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hD₁J : D₁ ≤ normalizer (J : Set G) :=
    oddCoreOfCentralizer_inf_le_normalizer hLB ha hak hJ.2.1 hJ.2.2
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hbD₁ : b ∈ normalizer (D₁ : Set G) :=
    mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer hbCa)
      (mem_normalizer_centralizer_singleton hbk)
  have hsym : ∀ x, b * x * b⁻¹ ∈ coreActionKernel J → x ∈ coreActionKernel J' :=
    fun x hx => mem_coreActionKernel_conjugate hx
  have haJ : a ∈ normalizer (J : Set G) := by
    by_contra haJ
    have hne1 : conjugate J a ≠ J := fun h => haJ (mem_normalizer_of_conjugate_eq h)
    have hD₁C : D₁ ≤ coreActionKernel J :=
      le_coreActionKernel_of_balance hLB ha hak hJ.2.1 hJ.2.2 (Or.inl hne1)
    apply hD
    intro x hx
    have hxD : x ∈ D := commutator_self_le D hx
    exact hkey x hxD (hD₁C (hDD₁ hxD))
      (hsym x (hD₁C ((mem_normalizer_iff.mp hbD₁ x).mp (hDD₁ hxD))))
  have hD₁' : ¬ ⁅D₁, D₁⁆ ≤ coreActionKernel J := by
    intro h
    apply hD
    intro x hx
    have hxD : x ∈ D := commutator_self_le D hx
    have hx₁ : x ∈ ⁅D₁, D₁⁆ := commutator_mono hDD₁ hDD₁ hx
    exact hkey x hxD (h hx₁) (hsym x (h (conj_mem_commutator_self hbD₁ hx₁)))
  have hZJ : center (J ⧸ pPrimeCore 2 J) ≠ ⊥ :=
    center_ne_bot_of_mem_sup hk hJ hJ' hJJ'ne
      (center_quotient_eq_bot_of_mulEquiv
        (J.equivMapOfInjective (MulAut.conj b⁻¹).toMonoidHom (MulAut.conj b⁻¹).injective))
      (hTJJ hkT)
  have hJfam : FooteFamilyType J := by
    rcases hcore a k ha hk hak J hJ.2.1 hJ.2.2 with ⟨p', f', hp', hp2', hf', hL'⟩ | h2
    · exact footeFamilyType_of_lieModel hp' hp2' hf' hL'
    · exact absurd (le_coreActionKernel_of_commutator_le ((commutator_self_le D₁).trans hD₁J)
        hJ.2.1 h2) hD₁'
  have hJq := isQuasisimple_quotient_of_isPComponent hJ.2.1 hJ.2.2
  have hJrank : CFSG.pRank 2 ↥J ≤ 1 :=
    pRank_le_one_of_center_ne_bot hJq hJfam (hβ J ⟨k, hJ⟩ hJfam) hZJ
  by_cases hkJ : k ∈ J
  · exact hnoCl k J hJ hkJ hJrank
  obtain ⟨j, hjZ, hj, haj⟩ := exists_involution_commute ha
    (mem_normalizer_inf' haJ (mem_normalizer_coreActionKernel haJ))
    (two_dvd_card_inf_coreActionKernel hZJ)
  obtain ⟨hjJ, hjC⟩ := mem_inf.mp hjZ
  have hkj : k * j = j * k := (mem_centralizer_singleton_iff.mp (hJ.2.1 hjJ)).symm
  have hnekj : k ≠ j := fun h => hkJ (h ▸ hjJ)
  have hkL : k ∈ twoLayerOf j :=
    mem_twoLayerOf_of_mem_sup hk hj hkj hJ hJ' hjC (hJJ' hjJ) (hTJJ hkT)
  obtain ⟨I, hI, -, hTI, -, -⟩ := exists_footeStep hLB hJ hj hkj hnekj hjC
  have hIk : conjugate I k = I :=
    conjugate_eq_of_mem_normalizer (twoLayerIn_le_normalizer hI.2.1 hI.2.2 hkL)
  rw [hIk, sup_idem] at hTI
  have hjCa : j ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr haj.symm
  have hjD₁ : j ∈ normalizer (D₁ : Set G) :=
    mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer hjCa)
      (mem_normalizer_centralizer_singleton hkj.symm)
  have hD₁odd : Odd (Nat.card D₁) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le inf_le_left)
  have hD₂ : ¬ ⁅D₁ ⊓ centralizer ({j} : Set G), D₁ ⊓ centralizer ({j} : Set G)⁆ ≤
      coreActionKernel J := fun h =>
    hD₁' (commutator_le_coreActionKernel_of_inf_centralizer hD₁odd hD₁J hjD₁ hj hjC h)
  obtain ⟨⟨p', f', hp', hp2', hf', hL'⟩, hjI⟩ :=
    foote_thm32_target hLB hcore ha hj hak haj hJ hjJ hjC hD₂ hI hTI
  exact hcl j I hI hjI (footeFamilyType_of_lieModel hp' hp2' hf' hL')

theorem not_classical_of_counterexample (hCI : GSLit.ClassicalInvolutionInput) [IsSimpleGroup G]
    {t : G} {L : Subgroup G} (hce : FooteCounterexample G t L) (x : G) (X : Subgroup G)
    (hX : IsTwoComponentAt x X) (hxX : x ∈ X) (hXr : CFSG.pRank 2 ↥X ≤ 1) : False := by
  obtain ⟨⟨-, -, ⟨ht, hLt, hLpc⟩, -, -, -⟩, hcon⟩ := hce
  have hLq := isQuasisimple_quotient_of_isPComponent hLt hLpc
  obtain ⟨u, v, huv⟩ := exists_mul_ne_mul_of_isQuasisimple hLq
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  have hna : ∃ g h : G, g * h ≠ h * g := by
    refine ⟨u', v', fun h => huv ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show u' * v' = v' * u' from Subtype.ext h]
  have hodd := oddLieType_of_classical_twoComponent hCI hna hX.1 hX.2.1 hX.2.2 hxX hXr
  have hLne : L ≠ ⊥ := by
    rintro rfl
    apply huv
    rw [show u' = 1 from Subtype.ext ((Subgroup.mem_bot).1 u'.2),
      show v' = 1 from Subtype.ext ((Subgroup.mem_bot).1 v'.2)]
  have hA : conjClosure L (pLayer G 2) = ⊤ := by
    rw [pLayer_two_eq_top_of_isSimpleGroup hna ht, conjClosure_top_eq_top hLne]
  apply hcon
  rw [hA]
  obtain ⟨eX⟩ := nonempty_quotient_top_equiv ht
  right; right; right; right
  exact ⟨eX.isSimpleGroup, (ClassicalInvolution.oddLieType_congr eX).2 hodd⟩

theorem foote_theorem_3_2_of_counterexample (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) [IsSimpleGroup G] {t : G}
    {L : Subgroup G} (hce : FooteCounterexample G t L) {a b : G} (ha : orderOf a = 2)
    (hab : a * b = b * a) {K : Subgroup G} (hK : IsTwoComponentAt b K)
    (hY : ¬ ⁅oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G),
      oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G)⁆ ≤ coreActionKernel K) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f :=
  foote_theorem_3_2 hLB (footeCoreAt_of_mulEquiv Subgroup.topEquiv.symm (hce.1.2.1 ⊤))
    (card_center_le_two_of_footeFamilyType hGA hGC hSA G) (not_classical_of_counterexample hCI hce)
    ha hab hK hY

end CFSG.ComponentClassification.FooteLit
