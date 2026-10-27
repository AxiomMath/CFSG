module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeLines
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Q1Main
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBLines

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial CFSG CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator


theorem d4_toral_q1_data
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hE : IsElementaryAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 2)
    (hanis : ∀ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p R →
      R ≠ ⊥ → ¬ E ≤ Subgroup.normalizer (R : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ v ∈ E.map (β⁻¹).toMonoidHom, ∃ n ∈ E.map (β⁻¹).toMonoidHom, v ≠ 1 ∧
        (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom ∧
        ∃ F : D4SteinbergFrame K σ (p ^ f) 1, F.Contains (E.map (β⁻¹).toMonoidHom) := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β, v, hv, n, hn, hv1, hvT, hnM, hnT⟩ :=
    d4_aniso_plane_q1 hp hp2 hf K hK σ hσ hq E hEcard hanis
  refine ⟨β, v, hv, n, hn, hv1, hvT, hnM, hnT, ?_⟩
  set E' := E.map (β⁻¹).toMonoidHom with hE'
  have hE'ea : IsElementaryAbelian 3 E' := IsElementaryAbelian.map (β⁻¹).toMonoidHom
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (β⁻¹).injective]
    exact hEcard
  have hE'3 : ∀ e ∈ E', e ^ 3 = 1 := fun e he => elemPow_eq_one_of_isElementaryAbelian e he
  have hnv : n * v = v * n :=
    congrArg Subtype.val ((inferInstance : IsMulCommutative E').is_comm.comm ⟨n, hn⟩ ⟨v, hv⟩)
  have hnz : n ∉ Subgroup.zpowers v := by
    intro h
    apply hnT
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [Subgroup.coe_zpow]
    exact zpow_mem hvT k
  have hgen := plane_le_of_pair E' hcard' hE'3 hv hn hv1 hnz
  obtain ⟨y, z, hy, hz, hFy, hyE, hcase⟩ := q1_toral_data hp2 hf hq K hK σ hσ E' v n hgen hvT hv1
    (hE'3 v hv) (hE'3 n hn) hnv hnM hnT
  rcases hcase with hzT | ⟨u, hu⟩
  · exfalso
    obtain ⟨R, hRp, hR1, hER⟩ := d4_toral_split_normalizes hf K hK σ hσ E' hy hzT hFy hyE
    obtain ⟨R', hR'p, hR'1, hER'⟩ := normalizes_of_map (β⁻¹) E R hRp hR1 hER
    exact hanis R' hR'p hR'1 hER'
  · exact d4SteinbergFrame_of_toral K σ hσ (Or.inl rfl) E' hE'3 hy hz hFy hyE u hu

theorem exists_singular_SL3_of_frame {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hq2 : 2 < ℓ ^ f) (hℓ3 : ℓ ≠ 3) (F : D4SteinbergFrame K σ (ℓ ^ f) 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hEcard : Nat.card E = 3 ^ 2)
    (hE3 : ∀ y ∈ E, y ^ 3 = 1)
    (hFE : F.Contains E) {v : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hvE : v ∈ E)
    (hv1 : v ≠ 1) :
    ∃ x ∈ E, x ∉ Subgroup.zpowers v ∧
      ⁅⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆,
        ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆⁆ =
        ⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ ∧
      Nat.card ↥⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ =
        Nat.card SL(3, RingHom.eqLocusField F.Fr (RingHom.id (AlgebraicClosure K))) ∧
      Nat.card (RingHom.eqLocusField F.Fr (RingHom.id (AlgebraicClosure K))) = ℓ ^ f := by
  classical
  obtain ⟨c, hc⟩ := hFE
  obtain ⟨x₁, hx₁E, x₂, hx₂E, hx₁1, hx₂1, hx₂z, hdata⟩ :=
    exists_two_singular_lines_threeSix_plane K σ (ε := 1) (Or.inl rfl) (AlgebraicClosure K) F.Fr
      F.hFr E hEcard c hc
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨x, hxE, hxz, hxd⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers v ∧
      ∃ a : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus (AlgebraicClosure K) F.Fr 1 ∧
        orderOf (rootDiagUnit TwistTag.D4.tag a) = 3 ∧
        (∃ i, survivingRoots a = trialitySigma i) ∧
        threeSixEmb K (AlgebraicClosure K) σ (c * x * c⁻¹) = F.g * rootDiagUnit TwistTag.D4.tag a *
          F.g⁻¹ := by
    by_cases h₁ : x₁ ∈ Subgroup.zpowers v
    · refine ⟨x₂, hx₂E, fun h₂ => hx₂z ?_, hdata x₂ (Or.inr rfl)⟩
      have hv3 : v ^ 3 = 1 := hE3 v hvE
      have hx₁3 : x₁ ^ 3 = 1 := hE3 x₁ hx₁E
      have hvord : orderOf v = 3 := orderOf_eq_prime hv3 hv1
      have hx₁ord : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1
      have hle : Subgroup.zpowers x₁ ≤ Subgroup.zpowers v := Subgroup.zpowers_le.2 h₁
      have heq : Subgroup.zpowers x₁ = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hvord,
          hx₁ord])
      rw [heq]
      exact h₂
    · exact ⟨x₁, hx₁E, h₁, hdata x₁ (Or.inl rfl)⟩
  obtain ⟨a, ha, hord, ⟨i, hi⟩, hx⟩ := hxd
  obtain ⟨w, hw⟩ : ∃ w : WeylGroup Tag.D4, (fun α => w • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w', -, -, hw'⟩ := hcomp i
    exact ⟨w', by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw']⟩
  have hd : ((((ℓ ^ f) ^ 2 + 1 * ℓ ^ f + 1 : ℕ)) : ℤ) =
      ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 * (ℓ ^ f : ℕ) + 1 := by push_cast; ring
  obtain ⟨-, -, hR, hSL, -, hq, -, -, -, hk, -⟩ :=
    triality_three_six_singular_fixed_centralizers_gen hℓ hf K hK σ hσ (AlgebraicClosure K) F.Fr
      F.hFr (Or.inl rfl) hd F.g F.hgG F.hFg Nat.prime_three (by norm_num) hℓ3 hq2 a ha hord w hw
      (c * x * c⁻¹) hx
  obtain ⟨e, -⟩ := hSL rfl
  set ψ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := MulAut.conj c with hψ
  have hψx : ψ x = c * x * c⁻¹ := rfl
  have hCmap := CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.centralizer_singleton_map ψ x
  rw [hψx] at hCmap
  have hRmap : ⁅Subgroup.centralizer ({c * x * c⁻¹} : Set _),
      Subgroup.centralizer ({c * x * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ =
      (⁅Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆).map
          ψ.toMonoidHom := by
    rw [hCmap, Subgroup.map_commutator]
  refine ⟨x, hxE, hxz, ?_, ?_, hk⟩
  · have hperf : ⁅threeSixSingularR (AlgebraicClosure K) K σ F.Fr 1 w F.g,
        threeSixSingularR (AlgebraicClosure K) K σ F.Fr 1 w F.g⁆ =
        threeSixSingularR (AlgebraicClosure K) K σ F.Fr 1 w F.g := Subgroup.isPerfect_iff.1 hq.1
    rw [← hR, hRmap, ← Subgroup.map_commutator] at hperf
    exact Subgroup.map_injective ψ.injective hperf
  · rw [← Nat.card_congr e.toEquiv, ← hR, hRmap, Subgroup.card_map_of_injective ψ.injective]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
