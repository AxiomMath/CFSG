module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OutTwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

namespace Up34Chev2

section Diag

set_option linter.unusedSectionVars false


theorem noL34Layer_inndiag_twE6_two (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut ↥(twistedE6RootGroup K σ)) (h : ModGL TwistTag.E6.tag K)
    (hh : h ∈ twistedE6InndiagGL K σ)
    (hβ : ∀ c, (β c : ModGL TwistTag.E6.tag K) = h * c * h⁻¹) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1) :
    NoL34Layer β := by
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
  refine noL34Layer_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three h3L (fun h' => absurd h' (by simp)) hT hap h1) ?_
  intro i hq hL34
  cases hk : twistKind S.ρ (rootCharHom a) i with
  | inner => exact hI _ _ S a hT hap h1 i hk hq hL34
  | suN => exact hS _ _ S a hT hap h1 i hk hq hL34
  | twoD => exact hD _ _ S a hT hap h1 i hk hq hL34
  | exc => exact hE _ _ S a hT hap h1 i hk hq hL34

theorem noL34Layer_twistedE6InndiagConj_two (hI : Char2Hrat Tag.E6 .inner)
    (hS : Char2Hrat Tag.E6 .suN) (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc)
    {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (g : ↥(twistedE6InndiagGL K σ))
    (hg3 : (g : ModGL TwistTag.E6.tag K) ^ 3 = 1) (hg1 : (g : ModGL TwistTag.E6.tag K) ≠ 1) :
    NoL34Layer (twistedE6InndiagConj K σ g) :=
  noL34Layer_inndiag_twE6_two hI hS hD hE hf hK σ hσ (twistedE6InndiagConj K σ g)
    (g : ModGL TwistTag.E6.tag K) g.2 (fun c => twistedE6InndiagConj_apply g c) hg3 hg1

theorem up34C2OutDiag_TwE6_holds (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) : Up34C2OutDiag_TwE6 := by
  intro f K _ _ σ hf hK hσ ψ hψd _ hp
  obtain ⟨hψ3, hψ1, hno⟩ := (up34Pumpup_iff ψ).1 hp
  rw [← range_twistedE6InndiagConj K σ] at hψd
  obtain ⟨g, rfl⟩ := hψd
  have hg3 : g ^ 3 = 1 := by
    apply twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ
    rw [map_pow, map_one]
    exact hψ3
  refine hno (noL34Layer_twistedE6InndiagConj_two hI hS hD hE hf hK σ hσ g ?_ ?_)
  · have := congrArg (fun x : ↥(twistedE6InndiagGL K σ) => (x : ModGL TwistTag.E6.tag K)) hg3
    simpa using this
  · intro h1
    apply hψ1
    have : g = 1 := Subtype.ext h1
    rw [this, map_one]

end Diag

section Family

set_option linter.unusedSectionVars false


theorem up34C2Inn_TwE6_holds (hI : Char2Hrat Tag.E6 .inner) (hS : Char2Hrat Tag.E6 .suN)
    (hD : Char2Hrat Tag.E6 .twoD) (hE : Char2Hrat Tag.E6 .exc) : Up34Chev2Inn FamTwE6 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ x hp
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 := hc
    have hm := blueprintLieModel_twistedE6 q hv e
    have hT : TwistedChevalleyModel S TwistTag.E6 (q.p ^ q.exponent) := by
      rcases hm with ⟨ht', -⟩ | ⟨-, -, hE'⟩ | ⟨-, ht', -⟩ | ⟨-, ht', -⟩
      · exact absurd ht' (by decide)
      · exact hE'.2
      · exact absurd ht' (by decide)
      · exact absurd ht' (by decide)
    obtain ⟨K, _, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_twistedE6RootGroup_equiv q.prime_p q.exponent_pos hT
    rw [hq2] at hK hσ
    let θ : S ≃* twistedE6RootGroup K σ := eK.symm
    obtain ⟨hx3, hx1, -⟩ := (up34Pumpup_iff _).1 hp
    have hZ : Subgroup.center S = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        apply hab
        have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.1 ha b).symm
    have hx3' : x ^ 3 = 1 := by
      have h1 : (MulAut.conj (x ^ 3) : MulAut S) = MulAut.conj 1 := by
        rw [map_pow, map_one]
        exact hx3
      have h2 : x ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := DFunLike.congr_fun h1 g
        simp only [MulAut.conj_apply, MulAut.one_apply, inv_one, mul_one, one_mul] at this
        calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [this]
          _ = x ^ 3 * g := by group
      rwa [hZ, Subgroup.mem_bot] at h2
    have hp' := hp.of_congr θ
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at hp'
    obtain ⟨-, -, hno⟩ := (up34Pumpup_iff _).1 hp'
    set y : ↥(twistedE6RootGroup K σ) := θ x with hy
    set g : ↥(twistedE6InndiagGL K σ) :=
      ⟨(y : ModGL TwistTag.E6.tag K), le_sup_left (b := twistedE6DiagGL K σ) y.2⟩ with hg
    have hconj : twistedE6InndiagConj K σ g = MulAut.conj y :=
      MulEquiv.ext fun c => Subtype.ext (by simp [twistedE6InndiagConj_apply, hg, MulAut.conj_apply])
    refine hno ?_
    rw [← hconj]
    refine noL34Layer_twistedE6InndiagConj_two hI hS hD hE q.exponent_pos hK σ hσ g ?_ ?_
    · change ((y : ModGL TwistTag.E6.tag K)) ^ 3 = 1
      have : y ^ 3 = 1 := by rw [hy, ← map_pow, hx3', map_one]
      rw [← Subgroup.coe_pow, this]
      rfl
    · intro h1
      apply hx1
      have hy1 : y = 1 := Subtype.ext h1
      have : x = 1 := θ.injective (by rw [← hy, hy1, map_one])
      rw [this, map_one]
  | _ => exact hF.elim

end Family

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
