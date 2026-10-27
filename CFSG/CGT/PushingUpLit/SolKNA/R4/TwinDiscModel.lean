module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


open scoped MatrixGroups

theorem not_isPGroup_two_sl2_threeR : ¬ IsPGroup 2 SL(2, ZMod 3) := by
  intro h
  obtain ⟨x, hx, hne⟩ : ∃ x : SL(2, ZMod 3), x ^ 3 = 1 ∧ x ≠ 1 := by
    refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> decide
    · intro e
      have := congrArg (fun g : SL(2, ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1) e
      simp at this
  have h3 : orderOf x = 3 := orderOf_eq_prime hx hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h x
  rw [h3] at hk
  have h32 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
  omega

section Model

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem tightCore_eq_self_of_twoGroup_quot (hΦ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) :
    ∀ K ∈ Φ, tightCore K = K := by
  intro K hK
  rcases hΦ.omega2 K hK with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd ((h2 K hK).of_equiv e) not_isPGroup_two_sl2_threeR

theorem dstarConnected_of_inO2_R {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n)
    (hlt : Nat.card X < n) (hΦ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hq : ∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hO : classicalInvolutionOddCore X = ⊥) (hA : ∀ J ∈ Φ, AEmpty Φ J)
    (hgen : omegaGen Φ = ⊤) (htr : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (htw : ∃ K ∈ Φ, ∃ K' ∈ twinSet Φ K, K' ≠ K) : T3.DStarConnected Φ := by
  obtain ⟨K, hK, K', hK', hne⟩ := htw
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ hK
  have htc := tightCore_eq_self_of_twoGroup_quot hΦ h2
  have hΦeq : CoreAssembly.conjClass K = Φ := by
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact hΦ.conjInvariant g K hK
    · intro hL
      obtain ⟨g, hg⟩ := htr K hK L hL
      exact ⟨g, hg⟩
  obtain S : Sylow 2 ↥K := Classical.choice inferInstance
  have hPs : IsSylow2In ((S : Subgroup K).map K.subtype) K := Asc77.isSylow2In_map_subtype K S
  obtain ⟨e0⟩ := hq K hK _ hPs
  have eS : ↥(S : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).trans e0
  have hcardP : Nat.card ↥((S : Subgroup K).map K.subtype) = 2 ^ r := by
    rw [Nat.card_congr e0.toEquiv]
    exact card_quaternion_pow (by omega)
  have hd : Q8TwinDatum K S z :=
    ⟨⟨r, by omega, ⟨eS⟩⟩,
      mem_of_isUniqueInvolution_of_isPGroup hz hPs.1 hPs.2.1 (by
        rw [hcardP]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)),
      orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one,
      le_centralizer_of_unique hz, h2 K hK⟩
  have hgenK : TightSelfGen K := by
    unfold TightSelfGen
    rw [htc K hK, eq_top_iff, ← hgen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, hg⟩ := htr K hK L hL
    rw [← hg]
    exact le_iSup (fun g : X => conjSub g K) g
  have hE2 : TightInO2 z := by
    refine hT X hlt K S z hd ⟨eS⟩ hgenK hO ?_ ?_ ?_
    · rw [htc K hK, hΦeq]; exact hΦ
    · rw [htc K hK, hΦeq]; exact hA K hK
    · rw [htc K hK, hΦeq]; exact ⟨K', hK', hne⟩
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := hE2
  have hθ : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ :=
    TwinExitPf12.oddCoreIn_centralizer_eq_bot_of_mem_normal hO hQn hQ2 hzQ
  have hK2 : IsPGroup 2 ↥K := isPGroup_of_oddCent hΦ hK hz hθ (h2 K hK)
  have h2' : ∀ J ∈ Φ, IsPGroup 2 ↥J := by
    intro J hJ
    obtain ⟨g, hg⟩ := htr K hK J hJ
    rw [← hg]
    exact isPGroup_conjSub g hK2
  have h8 : ∀ J ∈ Φ, Nat.card ↥J = 2 ^ r := by
    intro J hJ
    obtain ⟨e⟩ := hq J hJ J ⟨le_rfl, h2' J hJ, fun V' hV'J _ hJV' => le_antisymm hV'J hJV'⟩
    rw [Nat.card_congr e.toEquiv]
    exact card_quaternion_pow (by omega)
  have hinO2 : ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u →
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 ↥Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨g, hg⟩ := htr K hK L hL
    have hzg : IsUniqueInvolution L (g * z * g⁻¹) := hg ▸ hz.conj g
    have hug : u = g * z * g⁻¹ := hu.eq hzg
    exact ⟨Q, hQn, hQ2, hug ▸ hQn.conj_mem z hzQ g⟩
  intro K₁ hK₁ J hJ
  by_cases hJK : J = K₁
  · subst hJK
    exact Relation.ReflTransGen.refl
  obtain ⟨z₁, hz₁⟩ := Sec6Gen.exists_uniqueInvolution hΦ hK₁
  have hzJ := mem_normalizer_of_four_le hr hΦ h2' h8 hinO2 hJ hK₁ hz₁
  have hstar := mem_omegaStarNbr_of_normalizes hΦ h2' h8 hA hO hinO2 hK₁ hJ hJK hz₁ hzJ
  exact Relation.ReflTransGen.single ⟨hJ, Or.inl hstar⟩

@[expose] def DStarConnectedTwinR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), HypOmegaGen Φ →
    (∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) →
    (∀ J ∈ Φ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) →
    classicalInvolutionOddCore X = ⊥ → (∀ J ∈ Φ, AEmpty Φ J) → omegaGen Φ = ⊤ →
    (∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) → TwinTriple Φ → T3.DStarConnected Φ

theorem dstarConnectedTwinR_of {r n : ℕ} (hr : 4 ≤ r) (hT : Thm1RTwinInO2 r n) :
    DStarConnectedTwinR r n := by
  intro X _ _ hlt Φ hΦ h2 hq hO hA hgen htr htt
  obtain ⟨K, hK, K', hK', hne, -⟩ := htt
  exact dstarConnected_of_inO2_R hr hT hlt hΦ h2 hq hO hA hgen htr ⟨K, hK, K', hK', hne⟩

end Model

end CFSG.CGT.PushingUpLit.SolKNA.R4
