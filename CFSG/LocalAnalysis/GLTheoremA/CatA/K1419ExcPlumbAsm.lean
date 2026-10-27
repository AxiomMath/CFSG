module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcPlumbEmb
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial

section Assembly


theorem noL3U3Layer_exc_inner_untw_two {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hres : ∀ k, Char2L3U3 τ k)
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    NoL3U3Layer β := by
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ'' : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ''' : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := single_edge_perfect τ K hτ''
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h5
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5)
    omega
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ''' Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three h3K Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf β h hhL hβ hp1 hh1
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  refine noL3U3Layer_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three h3L
      (fun h' => absurd h' (by rcases hτ with h | h | h | h <;> simp [h])) hT hap h1) ?_
  intro i hq hL3
  exact hres _ _ _ S a hT hap h1 i rfl hq hL3

theorem noL3U3Layer_inndiag_twE6_two (hres : ∀ k, Char2L3U3 Tag.E6 k) {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (β : MulAut ↥(twistedE6RootGroup K σ))
    (h : ModGL TwistTag.E6.tag K) (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    NoL3U3Layer β := by
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3))
    omega
  have hτ''' : Tag.E6 = .G2 ∨ Tag.E6 = .F4 ∨ Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨
      Tag.E6 = .E8 := by simp
  have hmon : MonomialToralAt Tag.E6 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ''' Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hf hK σ hσ Nat.prime_three
      (by norm_num) Nat.prime_five (by norm_num) (Or.inl le_rfl) hmon β h hh hβ hp1 hh1
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  refine noL3U3Layer_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three h3L (fun h' => absurd h' (by simp)) hT hap h1) ?_
  intro i hq hL3
  exact hres _ _ _ S a hT hap h1 i rfl hq hL3

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
