module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3LinModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Iso
import CFSG.LieType.Steinberg.CentralExt.PSLSmall

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3

@[expose] noncomputable def pslReindex {F : Type} [Field F] {m n : Type} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    ProjectiveSpecialLinearGroup m F ≃* ProjectiveSpecialLinearGroup n F :=
  QuotientGroup.congr _ _ (slReindex e) (Subgroup.map_center_eq (slReindex e))

theorem eq_one_of_pow_three {F : Type} [Field F] [Finite F] (hF : ¬ 3 ∣ Nat.card F - 1) {x : F}
    (hx : x ^ 3 = 1) : x = 1 := by
  have hx0 : x ≠ 0 := fun h => by rw [h, zero_pow (by norm_num)] at hx; exact zero_ne_one hx
  set u : Fˣ := Units.mk0 x hx0
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx]; rfl)
  have hd1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hd2 : orderOf u ∣ Nat.card Fˣ := orderOf_dvd_natCard u
  have hcard : Nat.card Fˣ = Nat.card F - 1 := by
    classical
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hcard] at hd2
  have h1 : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd1 with h | h
    · exact h
    · exact absurd (h ▸ hd2) hF
  have := orderOf_eq_one_iff.1 h1
  exact congrArg Units.val this

theorem cast_ne_zero_galois {ℓ f n : ℕ} [Fact ℓ.Prime] (hn : n.Prime) (hℓ : ℓ ≠ n) :
    ((n : ℕ) : GaloisField ℓ f) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (GaloisField ℓ f) ℓ]
  intro h
  exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) hn).1 h)

theorem concA_of_A {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {r : ℕ} (hr : r = 5 ∨ r = 6) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.A r Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.A r Q, hv⟩).Group) (h3 : 3 ∣ Q.card + 1) :
    S267ConcA 3 S B := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set F := GaloisField Q.p Q.exponent with hFdef
  have hFcard : Nat.card F = Q.card := by
    rw [hFdef, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have h3' : ¬ 3 ∣ Q.card - 1 := by
    intro h
    have hQ1 : 1 ≤ Q.card := by
      rw [TauCeti.PrimePower.card_def]; exact Nat.one_le_pow _ _ Q.prime_p.pos
    have : 3 ∣ (Q.card + 1) - (Q.card - 1) := Nat.dvd_sub h3 h
    rw [show Q.card + 1 - (Q.card - 1) = 2 by omega] at this
    omega
  have hQ5 : 5 ≤ Q.card := by
    have hp5 : 5 ≤ Q.p := Q.prime_p.five_le_of_ne_two_of_ne_three hp2 hp3
    rw [TauCeti.PrimePower.card_def]
    exact hp5.trans (Nat.le_self_pow Q.exponent_pos.ne' _)
  have e₁ : PSimple 3 S ≃* ProjectiveSpecialLinearGroup (Fin (r + 1)) F :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r Q hv)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl_of_ne Q.p
      Q.exponent (r + 1) Q.exponent_pos (by omega) (by omega) (by omega) (by omega)
    rw [Nat.card_congr eM.toEquiv]
    have hex : CFSG.Open.griessPSLExceptional (r + 1) (Q.p ^ Q.exponent) = (1, 1) := by
      rcases hr with rfl | rfl <;> simp [CFSG.Open.griessPSLExceptional]
    rw [hex, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_zmod, mul_one]
    intro hd
    apply h3'
    rw [TauCeti.PrimePower.card_def]
    exact hd.trans (Nat.gcd_dvd_right _ _)
  have hcardN : Fintype.card (Fin (r + 1)) = Fintype.card (Top (Fin (r - 5))) := by
    simp only [Top, Kap, Lam, Fintype.card_sum, Fintype.card_fin]
    omega
  have e₂ : ProjectiveSpecialLinearGroup (Fin (r + 1)) F ≃* X (Fin (r - 5)) (F := F) :=
    pslReindex (Fintype.equivOfCardEq hcardN)
  obtain ⟨φ, hφ, hφS⟩ := exists_embedding_of_mulEquiv H hZ (e₂.symm.trans e₁.symm)
  have hF3 : ∀ x : F, x ^ 3 = 1 → x = 1 := fun x hx =>
    eq_one_of_pow_three (by rwa [hFcard]) hx
  refine concA_of_modelA H hZ φ hφ hφS (modelA_psl (Fin (r - 5)) hF3 ?_ ?_ (by rw [hFcard]; omega))
  · exact_mod_cast cast_ne_zero_galois (f := Q.exponent) Nat.prime_three hp3
  · exact_mod_cast cast_ne_zero_galois (f := Q.exponent) Nat.prime_two hp2

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

end
