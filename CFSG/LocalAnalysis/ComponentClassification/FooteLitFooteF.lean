module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma43ii

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem footeF_conj {L : Subgroup G}
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M) (a g : G) :
    footeF L (g⁻¹ * a * g) = conjugate (footeF L a) g := by
  classical
  have hφa : (MulAut.conj g⁻¹) a = g⁻¹ * a * g := by rw [MulAut.conj_apply, inv_inv]
  by_cases h : ∃ B : Subgroup G, IsTwoComponentAt a B ∧ B ∈ footeFamilyOf L
  · obtain ⟨B, hB, hBF⟩ := h
    rw [eq_footeF huniq hB hBF]
    have hB' : IsTwoComponentAt (g⁻¹ * a * g) (conjugate B g) := by
      have h1 := isTwoComponentAt_map_mulEquiv (MulAut.conj g⁻¹) hB
      rwa [hφa] at h1
    exact eq_footeF huniq hB' (conjugate_mem_footeFamilyOf hBF g)
  · have h' : ¬ ∃ B : Subgroup G, IsTwoComponentAt (g⁻¹ * a * g) B ∧ B ∈ footeFamilyOf L := by
      rintro ⟨B, hB, hBF⟩
      apply h
      refine ⟨conjugate B g⁻¹, ?_, conjugate_mem_footeFamilyOf hBF g⁻¹⟩
      have h1 := isTwoComponentAt_map_mulEquiv (MulAut.conj g) hB
      rw [MulAut.conj_apply, show g * (g⁻¹ * a * g) * g⁻¹ = a by group] at h1
      have e1 : conjugate B g⁻¹ = B.map (MulAut.conj g).toMonoidHom := by
        ext x
        rw [mem_conjugate_iff, inv_inv, mem_map_equiv, MulAut.conj_symm_apply]
      rw [e1]
      exact h1
    rw [footeF_eq_bot h, footeF_eq_bot h']
    ext x
    rw [mem_conjugate_iff, mem_bot, mem_bot]
    constructor
    · intro hx
      rw [hx]; group
    · intro hx
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [hx]; group

theorem le_oddResidualIn_inf_centralizer_sup {A P : Subgroup G} (hP : IsPGroup 2 P)
    (hPA : P ≤ coreActionKernel A) (hA : A ≤ oddResidualIn A) :
    A ≤ oddResidualIn (A ⊓ centralizer (P : Set G)) ⊔ oddCoreIn A := by
  set W := A ⊓ centralizer (P : Set G) with hW
  have hcov := le_inf_centralizer_sup_oddCoreIn hP hPA
  have hWN : W ≤ normalizer ((oddResidualIn W ⊔ oddCoreIn A : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_sup (mem_normalizer_oddResidualIn (le_normalizer hx))
      (mem_normalizer_oddCoreIn (le_normalizer (mem_inf.mp hx).1))
  refine hA.trans ((closure_le _).mpr fun g hg => ?_)
  obtain ⟨hgA, h2⟩ := hg
  have hg' : g ∈ W ⊔ (oddResidualIn W ⊔ oddCoreIn A) :=
    (sup_le le_sup_left (le_sup_right.trans le_sup_right) : W ⊔ oddCoreIn A ≤ _) (hcov hgA)
  exact mem_of_two_element_of_mem_sup hWN le_sup_left hg' h2

theorem footeFixed_le_of_oddResidualIn_le {L B : Subgroup G} {b : G}
    (hBN : centralizer ({b} : Set G) ≤ normalizer (B : Set G))
    (hLB : oddResidualIn (L ⊓ centralizer ({b} : Set G)) ≤ B) : footeFixed L b ≤ B := by
  set O := oddCoreOfCentralizer b with hO
  set N := B ⊔ O with hN
  have hON : O ≤ normalizer (B : Set G) := (oddCoreOfCentralizer_le_centralizer b).trans hBN
  have hCN : L ⊓ centralizer ({b} : Set G) ≤ normalizer (N : Set G) := fun x hx =>
    mem_normalizer_sup (hBN (mem_inf.mp hx).2)
      (mem_normalizer_oddCoreOfCentralizer (mem_inf.mp hx).2)
  rw [footeFixed_eq_oddResidualIn]
  refine (closure_le _).mpr fun g hg => ?_
  obtain ⟨hgX, h2⟩ := hg
  have hg' : g ∈ (L ⊓ centralizer ({b} : Set G)) ⊔ N :=
    (sup_le le_sup_left (le_sup_right.trans le_sup_right) :
      (L ⊓ centralizer ({b} : Set G)) ⊔ O ≤ _) hgX
  have hgN := mem_of_two_element_of_mem_sup hCN (hLB.trans le_sup_left) hg' h2
  have hg'' : g ∈ O ⊔ B := by rw [sup_comm]; exact hgN
  exact mem_of_two_element_of_mem_sup hON
    (by rw [oddResidualIn_eq_bot_of_odd (odd_card_oddCoreOfCentralizer b)]; exact bot_le) hg'' h2

theorem isSimpleGroup_quotient_of_mem_footeFamilyOf (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) {L : Subgroup G}
    (hLfam : FooteFamilyType L) (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hA : IsTwoComponentAt z A) (hAF : A ∈ footeFamilyOf L) :
    IsSimpleGroup (A ⧸ pPrimeCore 2 A) ∧
      Nonempty (A ⧸ pPrimeCore 2 A ≃* L ⧸ Open.fusionZStar L) := by
  obtain ⟨-, ⟨eAL⟩⟩ := id hAF
  obtain ⟨e₁⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA ⟨z, hA⟩
    (footeFamilyType_of_equiv eAL hLfam) (by rw [hrank2 A hAF])
  refine ⟨?_, ⟨e₁.trans eAL⟩⟩
  obtain ⟨hz, hAz, hApc⟩ := hA
  obtain ⟨hs, -⟩ := zStarQuotient_simple hApc
  obtain ⟨e₂⟩ := nonempty_quotient_fusionZStar_equiv
    (subgroupOfEquivOfLe hAz : ↥(A.subgroupOf (centralizer ({z} : Set G))) ≃* ↥A)
  exact (e₂.trans e₁.symm).symm.isSimpleGroup

theorem footeFixed_eq_footeF (hLB : FooteLBalanceInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) {L : Subgroup G}
    (hLfam : FooteFamilyType L)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {b : G} (hb : orderOf b = 2) (hbA : b ∈ coreActionKernel A) :
    footeFixed A b = footeF L b ∧ IsTwoComponentAt b (footeF L b) ∧
      footeF L b ∈ footeFamilyOf L := by
  obtain ⟨B, hB, -, hBF, hBA⟩ :=
    exists_mem_footeFamilyOf_of_mem_coreActionKernel hLB huniq hAmax hAF hb hbA
  rw [eq_footeF huniq hB hBF]
  refine ⟨le_antisymm ?_ ?_, hB, hBF⟩
  · exact footeFixed_le_of_oddResidualIn_le (le_normalizer_of_mem_footeFamilyOf huniq hB hBF) hBA
  ·
    obtain ⟨hsA, ⟨eA⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf hGA hGC hSA hLfam hrank2
      hAmax.1 hAF
    obtain ⟨-, ⟨eB⟩⟩ := isSimpleGroup_quotient_of_mem_footeFamilyOf hGA hGC hSA hLfam hrank2
      hB hBF
    set T := oddResidualIn (A ⊓ centralizer ({b} : Set G)) with hT
    have hTA : T ≤ A := (oddResidualIn_le _).trans inf_le_left
    have hb2 : IsPGroup 2 (zpowers b) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hb, pow_one]
    have hbK : zpowers b ≤ coreActionKernel A := zpowers_le.mpr hbA
    have hAres : A ≤ oddResidualIn A :=
      (oddResidualIn_eq_self_of_isPComponent hAmax.1.2.1 hAmax.1.2.2).ge
    have hAcov : A ≤ T ⊔ oddCoreIn A := by
      have h := le_oddResidualIn_inf_centralizer_sup hb2 hbK hAres
      rwa [centralizer_zpowers_eq] at h
    have heven : 2 ∣ Nat.card (A ⧸ pPrimeCore 2 A) := by
      by_contra hodd
      have hsol : Group.IsSolvable (A ⧸ pPrimeCore 2 A) := CFSG.FeitThompson.isSolvable_of_odd_natCard _
        (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
      have hq := isQuasisimple_quotient_of_isPComponent hAmax.1.2.1 hAmax.1.2.2
      obtain ⟨g, h, hgh⟩ := exists_mul_ne_mul_of_isQuasisimple hq
      exact hgh ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) g h)
    have hTcard : Nat.card (T ⧸ pPrimeCore 2 T) = Nat.card (A ⧸ pPrimeCore 2 A) :=
      card_quotient_eq_of_le_sup hTA hAcov heven
    have hBcov : B ≤ T ⊔ oddCoreIn B := le_sup_oddCoreIn_of_card_le hBA (by
      rw [hTcard, Nat.card_congr (eB.trans eA.symm).toEquiv])
    have hBres : B ≤ oddResidualIn B :=
      (oddResidualIn_eq_self_of_isPComponent hB.2.1 hB.2.2).ge
    refine hBres.trans ((closure_le _).mpr fun g hg => ?_)
    obtain ⟨hgB, h2⟩ := hg
    rw [footeFixed_eq_oddResidualIn]
    refine mem_oddResidualIn ?_ h2
    have hOB : oddCoreIn B ≤ oddCoreOfCentralizer b :=
      oddCoreIn_le_of_isTwoComponentIn ⟨hB.2.1, hB.2.2⟩
    have hTX : T ≤ (A ⊓ centralizer ({b} : Set G)) ⊔ oddCoreOfCentralizer b :=
      (oddResidualIn_le _).trans le_sup_left
    exact (sup_le hTX (hOB.trans le_sup_right)) (hBcov hgB)

end CFSG.ComponentClassification.FooteLit
