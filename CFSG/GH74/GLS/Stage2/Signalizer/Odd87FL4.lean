module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Block

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem exists_injective_qdSL_projectiveSL4 {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] :
    ∃ ψ : CFSG.Glauberman.qdSL p →* projectiveSL 4 F, Function.Injective ψ := by
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have hf : Function.Injective f := f.injective
  let φ : SpecialLinearGroup (Fin 2) (ZMod p) →* SpecialLinearGroup (Fin 2) F :=
    SpecialLinearGroup.map f
  have hφ : Function.Injective φ := fun a b h => by
    apply Subtype.ext
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
    exact Matrix.map_injective hf this
  exact ⟨((proj (2 + 2) F).comp (slBlock F 2 2)).comp φ,
    (injective_proj_slBlock (by norm_num)).comp hφ⟩

theorem not_pow_six_dvd_four_factorial {q : ℕ} (hodd : q % 2 = 1) (h3 : 3 ≤ q) :
    ¬ q ^ 6 ∣ 159667200 := by
  intro key
  have hle : q ^ 6 ≤ 159667200 := Nat.le_of_dvd (by norm_num) key
  have hq' : q ≤ 23 := by
    by_contra hcon
    have : 24 ^ 6 < q ^ 6 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  clear hle
  interval_cases q <;> omega

theorem not_card_dvd_factorial_projectiveSL4 {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F) :
    ¬ Nat.card (projectiveSL 4 F) ∣ Nat.factorial 11 := by
  intro hdvd
  have hSL : Nat.card (SpecialLinearGroup (Fin 4) F) =
      Nat.card F ^ 6 * ((Nat.card F ^ 2 - 1) * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 4 - 1))) := by
    rw [card_SL_eq (by norm_num), show Finset.Icc 2 4 = {2, 3, 4} by decide,
      Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  have hPS : Nat.card (SpecialLinearGroup (Fin 4) F) =
      Nat.card (projectiveSL 4 F) * Nat.card (scalars 4 F) :=
    (scalars 4 F).card_eq_card_quotient_mul_card_subgroup
  have hZ : Nat.card (scalars 4 F) ∣ 4 := by
    rw [card_scalars_eq_gcd F (by norm_num : 1 ≤ 4)]
    exact Nat.gcd_dvd_left _ _
  have hd : Nat.card F ^ 6 * ((Nat.card F ^ 2 - 1) * ((Nat.card F ^ 3 - 1) *
      (Nat.card F ^ 4 - 1))) ∣ 4 * Nat.factorial 11 := by
    rw [← hSL, hPS, mul_comm 4]
    exact Nat.mul_dvd_mul hdvd hZ
  have h1 : Nat.card F ^ 6 ∣ 4 * Nat.factorial 11 := dvd_trans (dvd_mul_right _ _) hd
  have h4f : 4 * Nat.factorial 11 = 159667200 := by decide
  rw [h4f] at h1
  exact not_pow_six_dvd_four_factorial (Nat.odd_iff.mp hF) h3 h1

theorem not_kindFactorAll_fl4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {Y : Type}
    [Group Y] (hL : CFSG.Blueprint.LieModel Y .PSL 4 p f) (k : Kind) : ¬ KindFactorAll k Y := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  have hFodd : Odd (Nat.card F) := by
    rw [hcard, Nat.odd_iff]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hp2).pow)
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have := Nat.odd_iff.mp hFodd
    omega
  obtain ⟨ψ, hψ⟩ := exists_injective_qdSL_projectiveSL4 (F := F) (p := p)
  have hinv := involved_of_injective ((e.symm : projectiveSL 4 F →* Y).comp ψ)
    (e.symm.injective.comp hψ)
  have hord : ¬ Nat.card Y ∣ Nat.factorial 11 := by
    rw [Nat.card_congr e.toEquiv]
    exact not_card_dvd_factorial_projectiveSL4 hFodd h3
  exact not_kindFactorAll hp2 hinv hord

theorem cell87_FL4_of_surv (hInv : InvSec) (h : Cell87Surv FL4) :
    Cell87 FL4 :=
  cell87_of_surv hInv (fun k Y _ hF => by
    obtain ⟨p, f, hp, hf, hp2, -, hL⟩ := hF
    exact not_kindFactorAll_fl4 hp hp2 hf hL k) h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
