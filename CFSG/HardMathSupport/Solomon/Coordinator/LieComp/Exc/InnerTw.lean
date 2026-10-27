module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerUntw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

theorem ringChar_eq_of_card_eq_pow {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n) {K : Type} [Field K]
    (hK : Nat.card K = ℓ ^ n) : ringChar K = ℓ := by
  have hK0 : Nat.card K ≠ 0 := by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ringChar.eq K ℓ


theorem lieCompExport_inner_twE6 (hres : ExcRationalLieTypes) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hpℓ : 3 ≠ ℓ) (hmon : MonomialToralAt Tag.E6 3)
    (h : ↥(twistedE6InndiagGL K σ)) (hp1 : h ^ 3 = 1) (hh1 : h ≠ 1)
    (hlayer : PerfectInLayer (twistedE6InndiagConj K σ h)) :
    LieCompExport ℓ (twistedE6InndiagConj K σ h) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := f * 2) hℓ (by omega) (by rw [hK, ← pow_mul])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf Nat.prime_three (by norm_num) hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  exact lieCompExport_of_langSetup hres S ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three
      (natCast_ne_zero_algebraicClosure_of_ne hℓ Nat.prime_three hK hpℓ)
      (fun h => absurd h (by decide)) hT hap h1) hlayer hAC

theorem lieCompExport_inner_triD4 (hres : ExcRationalLieTypes) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hpℓ : 3 ≠ ℓ) (hmon : MonomialToralAt Tag.D4 3)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hxp : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hlayer : PerfectInLayer (MulAut.conj x)) : LieCompExport ℓ (MulAut.conj x) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hAC : ringChar (AlgebraicClosure K) = ℓ := by
    rw [ringChar_algebraicClosure]
    exact ringChar_eq_of_card_eq_pow (n := f * 3) hℓ (by omega) (by rw [hK, ← pow_mul])
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf Nat.prime_three (by norm_num) hpℓ
  obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime hℓ hf hK σ hσ Nat.prime_three hpℓ hp₀ hp₀ℓ hq₀
      hmon x hxp hx1
  exact lieCompExport_of_langSetup hres S ι hinj hrange _ hconj hT hap h1
    (langSetup_hTame_of_prime S Nat.prime_three
      (natCast_ne_zero_algebraicClosure_of_ne hℓ Nat.prime_three hK hpℓ)
      (fun h => absurd h (by decide)) hT hap h1) hlayer hAC

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
