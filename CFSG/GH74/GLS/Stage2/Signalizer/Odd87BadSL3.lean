module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Block
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem involved_qdSL_projectiveSL3 {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] :
    CFSG.Glauberman.Involved (CFSG.Glauberman.qdSL p) (projectiveSL 3 F) := by
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hf : Function.Injective f := f.injective
  let φ : SpecialLinearGroup (Fin 2) (ZMod p) →* SpecialLinearGroup (Fin 2) F :=
    SpecialLinearGroup.map f
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
    exact Matrix.map_injective hf this
  let ψ : CFSG.Glauberman.qdSL p →* projectiveSL (2 + 1) F :=
    ((proj (2 + 1) F).comp (slBlock F 2 1)).comp φ
  have hψ : Function.Injective ψ := (injective_proj_slBlock (by norm_num)).comp hφ
  exact ⟨ψ.range, ⊥, Subgroup.normal_bot,
    ⟨(QuotientGroup.quotientBot).trans (MonoidHom.ofInjective hψ).symm⟩⟩

theorem not_card_dvd_factorial_projectiveSL3 {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) :
    ¬ Nat.card (projectiveSL 3 F) ∣ Nat.factorial 11 := by
  intro hdvd
  have hSL : Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
    rw [card_SL_eq (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
      Finset.prod_pair (by norm_num)]
  have hPS : Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card (projectiveSL 3 F) * Nat.card (scalars 3 F) :=
    (scalars 3 F).card_eq_card_quotient_mul_card_subgroup
  have hZ : Nat.card (scalars 3 F) ∣ 3 := by
    rw [card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)]
    exact Nat.gcd_dvd_left _ _
  have hd : Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) ∣
      3 * Nat.factorial 11 := by
    rw [← hSL, hPS, mul_comm 3]
    exact Nat.mul_dvd_mul hdvd hZ
  have h1 : Nat.card F ^ 3 ∣ 3 * Nat.factorial 11 := dvd_trans (dvd_mul_right _ _) hd
  have hodd : Nat.card F % 2 = 1 := Nat.odd_iff.mp hF
  have hle : Nat.card F ^ 3 ≤ 3 * Nat.factorial 11 := Nat.le_of_dvd (by positivity) h1
  have hq : Nat.card F = 3 := by
    generalize Nat.card F = q at *
    have hq' : q ≤ 500 := by
      by_contra hcon
      have : 500 ^ 3 < q ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
      have h11 : Nat.factorial 11 = 39916800 := by decide
      rw [h11] at hle
      omega
    interval_cases q <;> first | omega | (exfalso; revert h1; decide)
  rw [hq] at hd
  revert hd
  norm_num [Nat.factorial]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
