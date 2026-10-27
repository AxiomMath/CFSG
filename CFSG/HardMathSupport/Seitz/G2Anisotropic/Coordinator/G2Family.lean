module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.NativeReduction
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2SplitThree
public import CFSG.LieType.SeitzGeneration.ExcParabolicUntw
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddResidual
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.PairNormalForm
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies

public section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge TauCeti

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

@[expose] def G2NativePlaneGen (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ E₁ : Subgroup ↥(adjointGroup .G2 K), IsElemAbelian p E₁ → Nat.card E₁ = p ^ 2 →
    Subgroup.closure {k : ↥(adjointGroup .G2 K) | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤

@[expose] def G2NativePlaneGenSplit : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    p ∣ Nat.card K - 1 → G2NativePlaneGen K p

@[expose] def G2NativePlaneGenPlus : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    p ∣ Nat.card K + 1 → G2NativePlaneGen K p

@[expose] def G2NativePlaneGenCyclic : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ¬ p ∣ Nat.card K → ¬ p ∣ Nat.card K ^ 2 - 1 → G2NativePlaneGen K p

section Center

theorem conj_injective_of_mulEquiv_adjointGroup {C : Type*} [Group C] {K : Type} [Field K]
    [Finite K] (e : C ≃* ↥(adjointGroup .G2 K)) :
    Function.Injective (MulAut.conj : C →* MulAut C) := by
  refine conj_injective_of_center_eq_bot (eq_bot_iff.2 fun z hz => ?_)
  have hez : e z ∈ Subgroup.center ↥(adjointGroup .G2 K) := by
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨c, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz c]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hez
  exact Subgroup.mem_bot.2 (e.injective (hez.trans (map_one e).symm))

end Center

section Reduction

theorem seitzExcAnisotropicG2_of_native
    (h : ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card K → G2NativePlaneGen K p) : SeitzExcAnisotropicG2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hcard ⟨hin, ⟨q, rfl⟩, -, -⟩
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hq3 : 3 ≤ Nat.card K := by
    rw [hK]
    exact (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hpq : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp (by simpa using hpd)
  exact planeGen_of_inner_model (conj_injective_of_mulEquiv_adjointGroup e) e
    (h K hq3 p hp hp2 hpq) hE hcard hin

end Reduction

section ThreePlus

theorem g2NativePlaneGen_three_of_dvd_add_one (K : Type) [Field K] [Finite K]
    (hK : 3 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) : G2NativePlaneGen K 3 := by
  intro E₁ hE hcard
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := ExceptionsTransport.finite_adjointGroup_G2 K
  have h3K : ¬ 3 ∣ Nat.card K := fun h => by omega
  obtain ⟨P, hFP, z, hzF, hz1, hzp, hzc⟩ :=
    exists_sylow_central_in_plane (rankLE2_three_adjointGroup_G2 K h3K) hE hcard
  obtain ⟨e, heF, hez⟩ : ∃ e ∈ E₁, e ∉ Subgroup.zpowers z := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card E₁ ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hne
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf z ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hzp)
    omega
  have he1 : e ≠ 1 := fun h => hez (h ▸ one_mem _)
  have htop := g2NativeCentralizerPairsSylow_of_residuals
    UnitaryEmbedding.g2SylowPairNormalForm_of_instances
    ExceptionsTransport.g2SplitPairGenerationCentral_proved
    K hK h3 P z (hFP hzF) hzc hz1 hzp e (hFP heF) he1 (hE.2 e heF) hez
  rw [eq_top_iff, ← htop]
  refine sup_le (fun k hk => Subgroup.subset_closure ⟨z, hzF, hz1, ?_⟩)
    (fun k hk => Subgroup.subset_closure ⟨e, heF, he1, ?_⟩)
  · exact Subgroup.mem_centralizer_singleton_iff.1 hk
  · exact Subgroup.mem_centralizer_singleton_iff.1 hk

end ThreePlus

section ThreeMinus

theorem g2NativePlaneGen_three_of_dvd_sub_one (K : Type) [Field K] [Finite K]
    (hK : 3 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K - 1) : G2NativePlaneGen K 3 := by
  intro E₁ hE hcard
  have : IsSimpleGroup ↥(adjointGroup .G2 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK)
  have : CFSG.IsElementaryAbelian 3 E₁ :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hE.2 g g.2) }
  exact CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_closure_centralizers_three_split K h3 E₁ hcard

end ThreeMinus

section Parts

theorem g2NativePlaneGen_of_parts (hS : G2NativePlaneGenSplit) (hP : G2NativePlaneGenPlus)
    (hC : G2NativePlaneGenCyclic) (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) : G2NativePlaneGen K p := by
  have hK1 : 1 ≤ Nat.card K := by omega
  rcases eq_three_or_five_le hp hp2 with rfl | h5
  · have : 3 ∣ Nat.card K + 1 ∨ 3 ∣ Nat.card K - 1 := by omega
    rcases this with h | h
    · exact g2NativePlaneGen_three_of_dvd_add_one K hK h
    · exact g2NativePlaneGen_three_of_dvd_sub_one K hK h
  · by_cases h1 : p ∣ Nat.card K - 1
    · exact hS K hK p hp h5 h1
    by_cases h2 : p ∣ Nat.card K + 1
    · exact hP K hK p hp h5 h2
    refine hC K hK p hp h5 hpK fun h => ?_
    have hsq : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
      zify [hK1, Nat.one_le_pow 2 _ hK1]
      ring
    rw [hsq] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact h1 h
    · exact h2 h

theorem seitzExcAnisotropicG2_of_parts (hS : G2NativePlaneGenSplit) (hP : G2NativePlaneGenPlus)
    (hC : G2NativePlaneGenCyclic) : SeitzExcAnisotropicG2 :=
  seitzExcAnisotropicG2_of_native fun K _ _ hK p hp hp2 hpK =>
    g2NativePlaneGen_of_parts hS hP hC K hK p hp hp2 hpK

end Parts

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
