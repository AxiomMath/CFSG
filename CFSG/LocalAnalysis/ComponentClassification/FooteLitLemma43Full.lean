module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41Main
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma43

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_centralizer_of_type (hSolv : FooteL2InvolutionSolvable)
    {K : Subgroup G}
    (htype : Nonempty (K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f)
    {v : G} (hvK : v ∈ K) (hv : orderOf v = 2) :
    Group.IsSolvable ↥(K ⊓ centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := K ⧸ pPrimeCore 2 K with hS
  set π := QuotientGroup.mk' (pPrimeCore 2 K) with hπ
  set v' : K := ⟨v, hvK⟩ with hv'
  have hv'2 : v' * v' = 1 := Subtype.ext (by
    show v * v = 1
    rw [← sq, ← hv, pow_orderOf_eq_one])
  have hvbar : orderOf (π v') = 2 := by
    apply orderOf_eq_prime
    · rw [sq, ← map_mul, hv'2, map_one]
    · intro h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      have h1 := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 K) h
      rw [Subgroup.orderOf_mk, hv] at h1
      have h2 := Nat.Coprime.coprime_dvd_right h1 (pPrimeCore_coprime_card (p := 2) (G := ↥K))
      exact absurd h2 (by norm_num)
  have hC : Group.IsSolvable ↥(centralizer ({π v'} : Set S)) := hSolv S htype (π v') hvbar
  let f : ↥(K ⊓ centralizer ({v} : Set G)) →* ↥(centralizer ({π v'} : Set S)) :=
    { toFun := fun x => ⟨π ⟨x, (mem_inf.mp x.2).1⟩, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2)⟩
      map_one' := Subtype.ext (show π 1 = 1 from map_one π)
      map_mul' := fun x y => Subtype.ext (by
        show π ⟨x * y, _⟩ = π ⟨x, _⟩ * π ⟨y, _⟩
        rw [← map_mul]
        rfl) }
  set O := oddCoreIn K ⊓ centralizer ({v} : Set G) with hO
  have hOs : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard _
    (Odd.of_dvd_nat (odd_card_oddCoreIn K) (card_dvd_of_le inf_le_left))
  have hOK : O ≤ K ⊓ centralizer ({v} : Set G) :=
    inf_le_inf_right _ (map_subtype_le _)
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hOK) f fun x hx => ?_
  have h1 : π ⟨x, (mem_inf.mp x.2).1⟩ = 1 := congrArg Subtype.val hx
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨x, mem_inf.mpr ⟨⟨_, h1, rfl⟩, (mem_inf.mp x.2).2⟩⟩, rfl⟩

theorem foote_lemma_4_1_of_counterexample (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) [IsSimpleGroup G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {E V : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A) (hV : IsKleinFour V)
    (hVA : V ≤ A ⊓ centralizer (E : Set G)) {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) :
    ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)) := by
  classical
  have hLfam : FooteFamilyType L := hce.1.2.2.2.2.1
  have hex : ∀ e : G, ∃ B : Subgroup G, e ∈ E → e ≠ 1 → IsTwoComponentAt e B ∧
      B ∈ footeFamilyOf L ∧ oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ B := by
    intro e
    by_cases he : e ∈ E ∧ e ≠ 1
    · have hord : orderOf e = 2 := orderOf_eq_prime (hexp e he.1) he.2
      obtain ⟨B, hB, -, hBF, hBA⟩ :=
        exists_mem_footeFamilyOf_of_mem_coreActionKernel hLB huniq hAmax hAF hord (hEA he.1)
      exact ⟨B, fun _ _ => ⟨hB, hBF, hBA⟩⟩
    · exact ⟨⊥, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose K hK using hex
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  have hVL₀ : V ≤ oddResidualIn (A ⊓ centralizer (E : Set G)) := fun v hv =>
    mem_oddResidualIn (hVA hv) (exists_orderOf_eq_two_pow hVp hv)
  have hVK : ∀ b ∈ E, b ≠ 1 → V ≤ K b := fun b hb hb1 =>
    hVL₀.trans ((oddResidualIn_mono (inf_le_inf_left A (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr hb)))).trans (hK b hb hb1).2.2)
  have hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G) := fun e he => mem_centralizer_iff.mpr
    fun v hv => ((mem_centralizer_iff.mp (mem_inf.mp (hVA hv)).2) e he).symm
  have htype : ∀ b ∈ E, b ≠ 1 →
      Nonempty (K b ⧸ pPrimeCore 2 (K b) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Blueprint.LieModel (K b ⧸ pPrimeCore 2 (K b)) .PSL 2 p f := by
    intro b hb hb1
    obtain ⟨hB, hBF, -⟩ := hK b hb hb1
    obtain ⟨-, ⟨eBL⟩⟩ := id hBF
    have hBfam := footeFamilyType_of_equiv eBL hLfam
    obtain ⟨e₁⟩ := nonempty_quotient_equiv_fusionZStar hGA hGC hSA ⟨b, hB⟩ hBfam
      (by rw [hrank2 _ hBF])
    rcases hBfam with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
    · exact Or.inl ⟨e₁.trans e7⟩
    · exact Or.inr ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv e₁.symm hL⟩
  have hKs : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      Group.IsSolvable ↥(K b ⊓ centralizer ({v} : Set G)) := by
    intro b hb hb1 v hv hv1
    have hv2 : orderOf v = 2 := orderOf_eq_prime
      (by rw [sq]; exact congrArg Subtype.val (@IsKleinFour.mul_self V _ hV ⟨v, hv⟩)) hv1
    exact isSolvable_inf_centralizer_of_type hSolv (htype b hb hb1) (hVK b hb hb1 hv) hv2
  exact foote_lemma_4_1 hLB hOut hAb h9 hRk
    (fun ha hab _ hK hY => foote_theorem_3_2_of_counterexample hLB hCI hGA hGC hSA hce ha hab hK
      hY)
    hEc hexp h8 hV hVE K
    (fun b hb hb1 _ _ _ => inf_le_left.trans
      (le_normalizer_of_mem_footeFamilyOf huniq (hK b hb hb1).1 (hK b hb hb1).2.1))
    hVK hKs ha ha1

theorem foote_lemma_4_3_i_of_counterexample (hLB : FooteLBalanceInput)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hSolv : FooteL2InvolutionSolvable) [IsSimpleGroup G] {t : G} {L : Subgroup G}
    (hce : FooteCounterexample G t L)
    (huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
      K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M)
    (hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2)
    {z : G} {A : Subgroup G} (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L)
    {E V : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) (hEA : E ≤ coreActionKernel A) (hV : IsKleinFour V)
    (hVA : V ≤ A ⊓ centralizer (E : Set G)) :
    ∃ K : G → Subgroup G, (∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (K e) ∧ K e ∈ footeFamilyOf L) ∧
      Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (K e)) ≤ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) ≤
        oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn (⨆ e ∈ E, ⨆ (_ : e ≠ 1), K e) :=
  foote_lemma_4_3_i_of_mem_footeFamilyOf hLB hGA hGC hSA hce.1.2.2.2.2.1 huniq hrank2 hAmax hAF
    hEc hexp h8 hEA hV hVA fun _ ha ha1 =>
      foote_lemma_4_1_of_counterexample hLB hCI hGA hGC hSA hOut hAb h9 hRk hSolv hce huniq
        hrank2 hAmax hAF hEc hexp h8 hEA hV hVA ha ha1

end CFSG.ComponentClassification.FooteLit
