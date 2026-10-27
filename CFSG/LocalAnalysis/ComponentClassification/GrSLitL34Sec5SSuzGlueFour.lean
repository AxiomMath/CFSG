module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFourLift
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Lemma44SuzFourGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzLocal
public import CFSG.GroupTheory.SupCommute
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Idx

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem exists_kleinFour_layer_of_suz
    {S : Type} [Group S] [Finite S] (hS : Blueprint.NativeSporadic.IsSporadic S .Suz) :
    ∃ E₀ H₀ : Subgroup S, IsKleinFour E₀ ∧ ⁅H₀, H₀⁆ = H₀ ∧ H₀ ≠ ⊥ ∧
      ⁅centralizer (E₀ : Set S), centralizer (E₀ : Set S)⁆ = H₀ ∧
      ∀ e ∈ E₀, e ≠ 1 →
        H₀ ≤ (pLayer ↥(centralizer ({e} : Set S)) 2).map (centralizer ({e} : Set S)).subtype := by
  obtain ⟨E₀, H₀, _, hbody⟩ :=
    CFSG.EvenSporadicStandard.Solomon78.sol78Lemma44SuzFourGroup_l34_holds S hS
  obtain ⟨hbig, hLie⟩ := hbody
  obtain ⟨hEcard, hsq, hCecard, hCE, hHE, hH0CE, hCEderiv, hHderiv, hHcard,
    -, -, -, -⟩ := hbig
  haveI : Finite ↥E₀ := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hE₀ : IsKleinFour ↥E₀ := by
    refine IsKleinFour.mk hEcard ?_
    have hdvd : Monoid.exponent ↥E₀ ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        simpa [pow_two] using hsq (x : S) x.2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      have hsub : Subsingleton ↥E₀ := Monoid.exp_eq_one_iff.mp h1
      have hle : Nat.card ↥E₀ ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
      omega
    · exact h1
  have hH0ne : H₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hHcard
    omega
  haveI hSimple : IsSimpleGroup ↥H₀ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isSimpleGroup_of_lieModel_l34 hLie
  haveI hPerf : Group.IsPerfect ↥H₀ := Subgroup.isPerfect_iff.mpr hHderiv
  haveI hNontrivial : Nontrivial ↥H₀ := (Subgroup.nontrivial_iff_ne_bot H₀).mpr hH0ne
  have hq : CFSG.IsQuasisimple ↥H₀ := by
    have hnotcomm : ¬ IsMulCommutative ↥H₀ :=
      Group.IsPerfect.not_isMulCommutative (G := ↥H₀)
    have hnc : ∃ a b : ↥H₀, a * b ≠ b * a := by
      simpa only [isMulCommutative_iff, not_forall] using hnotcomm
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  refine ⟨E₀, H₀, hE₀, hHderiv, hH0ne, hCEderiv, ?_⟩
  intro e he hne
  let C : Subgroup S := centralizer ({e} : Set S)
  have hCEleC : centralizer (E₀ : Set S) ≤ C := by
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hx) e he).symm
  have hH0leC : H₀ ≤ C := fun x hx => hCEleC (hH0CE hx)
  have hCEmul : Nat.card (centralizer (E₀ : Set S)) = 80640 := by
    have hcomm : ∀ a ∈ H₀, ∀ b ∈ E₀, Commute a b := fun a ha b hb =>
      ((Subgroup.mem_centralizer_iff.mp (hH0CE ha)) b hb).symm
    calc Nat.card (centralizer (E₀ : Set S)) = Nat.card ↥(H₀ ⊔ E₀) := by rw [hCE]
      _ = Nat.card H₀ * Nat.card E₀ := CFSG.card_sup_eq_mul_of_commute H₀ E₀ hcomm hHE
      _ = 20160 * 4 := by rw [hHcard, hEcard]
      _ = 80640 := by norm_num
  have hCcard : Nat.card C = 161280 := hCecard e he hne
  have hindex : ((centralizer (E₀ : Set S)).subgroupOf C).index = 2 := by
    rw [Subgroup.index_eq_card_div]
    have hcard : Nat.card ↥((centralizer (E₀ : Set S)).subgroupOf C) = 80640 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCEleC).toEquiv, hCEmul]
    rw [hcard, hCcard]
  have hCEnormal : ((centralizer (E₀ : Set S)).subgroupOf C).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  have hCnormCE : C ≤ Subgroup.normalizer (centralizer (E₀ : Set S) : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCEleC).mp hCEnormal
  have hCnormH0 : C ≤ Subgroup.normalizer (H₀ : Set S) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hCEderiv, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCnormCE hc)]
  have hH0normal : (H₀.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH0leC).mpr hCnormH0
  exact CFSG.ComponentClassification.Sol76.le_pLayer_of_isQuasisimple hH0leC hq
    hH0normal.isSubnormal

variable {G : Type} [Group G] [Finite G]

theorem exists_kleinFour_perfect_of_suz
    {P : Subgroup G} (hperf : ⁅P, P⁆ = P)
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .Suz) :
    ∃ E H : Subgroup G, E ≤ P ∧ IsKleinFour E ∧ H ≤ P ∧ ⁅H, H⁆ = H ∧
      (∀ f ∈ E, f ≠ 1 → H ≤ gsFixedLayer P f) ∧
      ∀ N : Subgroup G, N ≤ P → (N.subgroupOf P).Normal → H ≤ N → N = P := by
  obtain ⟨E₀, H₀, hE₀, hH₀, hH₀1, hCE, hlayer⟩ := exists_kleinFour_layer_of_suz hsuz
  exact exists_kleinFour_perfect_of_layer hperf
    (EvenSporadicStandard.Solomon78.suz_isSimpleGroup_of_isSporadic hsuz) hE₀ hH₀ hH₀1 hCE hlayer

end CFSG.ComponentClassification.GrSLit.L34Sec5S
