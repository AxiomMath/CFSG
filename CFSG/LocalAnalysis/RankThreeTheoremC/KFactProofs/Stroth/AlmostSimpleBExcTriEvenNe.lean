module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriRoots3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriOdd
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriSplit

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley.TrialitySplitInner CFSG.RankThree.PartOne.FOC
open CFSG.RankThree.PartOne
open scoped commutatorElement Pointwise

section Ne


theorem oddPCoreInClosure_triality_three_ne {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hq : 2 ^ f % 3 = 1)
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) {A B : Kˣ} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hB1 : B ≠ 1)
    (hxa : ((g * x * g⁻¹ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag (d4Tuple A A B A))
    (C : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hC : ∀ c, c ∈ C ↔ c * x = x * c) : OddPCoreInClosure 3 ↥C := by
  classical
  obtain rfl : C = Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    Subgroup.ext fun c => (hC c).trans Subgroup.mem_centralizer_singleton_iff.symm
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    have : Fintype K := Fintype.ofFinite K
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul,
      show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 by ring, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  have hq4 : 4 ≤ 2 ^ f := by
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hev : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  obtain ⟨-, ⟨eT, heT⟩, -, -, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3
  have hkcard : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f :=
    card_trialityFixedField Nat.prime_two hf hK σ hσ
  have hodd : Odd (Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom)) := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_units, Nat.card_units, hK, hkcard]
    refine Odd.mul ?_ ?_
    · obtain ⟨m, hm⟩ : Even ((2 ^ f) ^ 3) := Nat.even_pow.2 ⟨hev, by norm_num⟩
      exact ⟨m - 1, by
        have : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by positivity)
        omega⟩
    · obtain ⟨m, hm⟩ := hev
      exact ⟨m - 1, by
        have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        omega⟩
  refine oddPCoreInClosure_of_conj_toral Nat.prime_three _ x g _ hxa ?_
  rcases triality_toral_centralizer_cases3 σ (a := d4Tuple A A B A) (A := A) (B := B) rfl rfl rfl
    rfl hA hB hB1 with ⟨-, hDH⟩ | ⟨v, hv, b, -, -, hD, -⟩
  · left
    rw [hDH]
    exact hodd
  · right
    have h4 : ∃ s : Finset (orbitField TwistTag.D4 K σ.toRingHom b), s.card = 4 := by
      have : Fintype (orbitField TwistTag.D4 K σ.toRingHom b) := Fintype.ofFinite _
      have hcardL := card_orbitField_D4_orientation Nat.prime_two hf hK (r := 1) (Or.inl rfl)
        (σ := σ.toRingHom) (by simpa using hσ) b
      have hle : 4 ≤ (Finset.univ : Finset (orbitField TwistTag.D4 K σ.toRingHom b)).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardL]
        have hpos : 1 ≤ (TwistTag.D4.orbit b).card := TwistTag.D4.card_orbit_pos b
        calc 4 ≤ 2 ^ f := hq4
          _ ≤ (2 ^ f) ^ (TwistTag.D4.orbit b).card := Nat.le_self_pow (by omega) _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
      exact ⟨s, hs⟩
    obtain ⟨hquasi, hcomm, hcent, hZH⟩ := triality_orbitPair_structure σ hσ3 hv b h4 _ hD
    have hpQ : 3 ∣ Nat.card (graphFixedRootPair TwistTag.D4 K σ.toRingHom
        (fixedOrbitImage TwistTag.D4 v b)) := by
      rcases foldedD4_cases b with rfl | rfl
      · obtain ⟨e⟩ := nonempty_SL2_mulEquiv_outer σ hσ3 h3 hv
        rw [← Nat.card_congr e.toEquiv]
        exact three_dvd_card_SL2 (f := f) (c := 3) hK
      · obtain ⟨e⟩ := nonempty_SL2_mulEquiv_middle σ hσ3 hv
        rw [← Nat.card_congr e.toEquiv]
        exact three_dvd_card_SL2 (f := f) (c := 1) (by rw [pow_one]; exact hkcard)
    set D := graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.centralizer
      ({rootDiagUnit TwistTag.D4.tag (d4Tuple A A B A)} : Set (ModGL TwistTag.D4.tag K)) with hDdef
    refine ⟨graphFixedRootPair TwistTag.D4 K σ.toRingHom (fixedOrbitImage TwistTag.D4 v b),
      (Subgroup.center D).map D.subtype, hcomm, hquasi, hpQ, hcent.le, ?_⟩
    rw [Subgroup.card_map_of_injective D.subtype_injective]
    have hdvd : Nat.card (Subgroup.center D) ∣
        Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective]
      exact Subgroup.card_dvd_of_le hZH
    exact Odd.of_dvd_nat hodd hdvd

end Ne

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
