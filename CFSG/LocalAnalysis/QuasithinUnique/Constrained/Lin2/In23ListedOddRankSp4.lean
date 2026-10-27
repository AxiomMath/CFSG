module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ListedOddRankProj
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.QuasithinUnique.Lin2.OddRank

open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (card_statedSp)
open CFSG.QuasithinUnique.Id2519

section Torus

variable {F : Type} [Field F] [Finite F]

@[expose] def spFam (t : Fin 2 → Fˣ) : (Fin 2 ⊕ Fin 2) → Fˣ := Sum.elim t fun i => (t i)⁻¹

omit [Finite F] in
theorem spFam_pow (t : Fin 2 → Fˣ) (n : ℕ) : spFam t ^ n = spFam (t ^ n) := by
  funext i
  rcases i with i | i <;> simp [spFam, inv_pow]

omit [Finite F] in
theorem torusDiag_spFam (t : Fin 2 → Fˣ) :
    torusDiag (spFam t) = ((torusHom t : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) := by
  apply Units.ext
  rw [coe_torusDiag, coe_torusHom]
  congr 1
  funext i
  rcases i with i | i <;> simp [spFam]

omit [Finite F] in
theorem torusDiag_spFam_mem (t : Fin 2 → Fˣ) : torusDiag (spFam t) ∈ StatedSp 2 F := by
  rw [torusDiag_spFam]
  exact (torusHom t : StatedSp 2 F).2

theorem two_le_pRank_psp_of_dvd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hdvd : p ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp 2 F))) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by rw [Nat.card_units]; exact hdvd)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.out.one_lt.ne hζ
  have hpow (i : Fin 2) : torusDiag (spFam (Pi.mulSingle i ζ)) ^ p = 1 := by
    rw [← map_pow, spFam_pow, ← Pi.mulSingle_pow, ← hζ, pow_orderOf_eq_one, Pi.mulSingle_one]
    have : spFam (1 : Fin 2 → Fˣ) = 1 := by
      funext j
      rcases j with j | j <;> simp [spFam]
    rw [this, map_one]
  have hent {d d' : (Fin 2 ⊕ Fin 2) → Fˣ} (h : torusDiag d = torusDiag d') (i : Fin 2 ⊕ Fin 2) :
      d i = d' i := congrFun (torusDiag_injective h) i
  refine two_le_pRank_statedProj (H := StatedSp 2 F) (x := torusDiag (spFam (Pi.mulSingle 0 ζ)))
    (y := torusDiag (spFam (Pi.mulSingle 1 ζ))) (torusDiag_spFam_mem _) (torusDiag_spFam_mem _)
    (hpow 0) (hpow 1) ((Commute.all _ _).map torusDiag) ?_ ?_
  · rintro ⟨c, hc⟩
    rw [scalar_eq_torusDiag] at hc
    have e0 := hent hc (Sum.inl 0)
    have e1 := hent hc (Sum.inl 1)
    simp [spFam] at e0 e1
    exact hζ1 (e0.symm.trans e1)
  · rintro n c ⟨c', rfl⟩ h
    rw [← map_pow, spFam_pow, scalar_eq_torusDiag, ← map_mul] at h
    have e0 := hent h (Sum.inl 0)
    have e1 := hent h (Sum.inl 1)
    have e2 := hent h (Sum.inr 0)
    simp [spFam, Pi.mulSingle_apply] at e0 e1 e2
    rw [e1] at e0 e2
    have hn1 : ζ ^ n = ζ⁻¹ := eq_inv_of_mul_eq_one_left e0
    rw [hn1, inv_inv] at e2
    have h2 : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := by simp only [pow_succ, pow_zero, one_mul]
        _ = 1 := e2
    have hd2 : p ∣ 2 := hζ ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hd2)

end Torus

section Interface

theorem three_dvd_two_pow_sub_one_of_even {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 2 ^ (k + k) - 1 = 4 ^ k - 1 := by rw [← two_mul, pow_mul]; norm_num
  rw [h]
  simpa using Nat.sub_one_dvd_pow_sub_one 4 k

theorem exists_prime_pRank_psp4 {X : Type} [Group X] [Finite X] {m n : ℕ} (hn : 2 ≤ n)
    (hX : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (X ≃* StatedProj (StatedSp 2 F)))
    (hdvd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ (2 * n) - 1 → ℓ ∣ Nat.card X) :
    ∃ p : ℕ, p.Prime ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hX
  by_cases hev : Even n
  · refine ⟨3, Nat.prime_three, three_dvd_two_pow_sub_one_of_even hev, ?_⟩
    rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
    obtain ⟨A, hA, hc⟩ := hasElemAb_nine_psp_four F
    exact le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num)
  · have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd (n := 2 ^ n - 1) (by omega)
    have hℓ2 : ℓ ≠ 2 := ne_two_of_dvd_two_pow_sub_one (by omega) hℓn
    have hℓ2n : ℓ ∣ 2 ^ (2 * n) - 1 := hℓn.trans (pow_sub_one_dvd (dvd_mul_left n 2))
    have hcardX : Nat.card X ∣ Nat.card (StatedSp 2 F) := by
      rw [Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    have hℓSp := (hdvd ℓ hℓ hℓ2n).trans hcardX
    have hB : (2 ^ m) ^ (2 * 1) = 2 ^ (2 * m) := by rw [← pow_mul]; congr 1; ring
    have hC : (2 ^ m) ^ (2 * 2) = 2 ^ (4 * m) := by rw [← pow_mul]; congr 1; ring
    rw [card_statedSp, hF, show Finset.Icc 1 2 = {1, 2} by decide,
      Finset.prod_pair (by norm_num), hB, hC] at hℓSp
    have h4m : ℓ ∣ 2 ^ (4 * m) - 1 := by
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓSp with h | h
      · exfalso
        have h1 : ℓ ∣ 2 ^ m := hℓ.dvd_of_dvd_pow h
        have h2 : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow h1
        exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
      · rcases (Nat.Prime.dvd_mul hℓ).mp h with h' | h'
        · exact h'.trans (pow_sub_one_dvd (⟨2, by ring⟩ : 2 * m ∣ 4 * m))
        · exact h'
    have hg : ℓ ∣ 2 ^ Nat.gcd n (4 * m) - 1 := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one]
      exact Nat.dvd_gcd hℓn h4m
    have hodd : Odd n := Nat.not_even_iff_odd.mp hev
    have hcop : Nat.Coprime 4 n := by
      have : Nat.Coprime (2 ^ 2) n := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
      simpa using this
    rw [Nat.Coprime.gcd_mul_left_cancel_right m hcop] at hg
    have hpm : ℓ ∣ Nat.card F - 1 := by
      rw [hF]
      exact hg.trans (pow_sub_one_dvd (Nat.gcd_dvd_right n m))
    refine ⟨ℓ, hℓ, hℓn, ?_⟩
    have : Fact ℓ.Prime := ⟨hℓ⟩
    rw [pRank_top_eq_of_mulEquiv hℓ.one_lt e]
    exact two_le_pRank_psp_of_dvd hℓ2 hpm

end Interface


end CFSG.QuasithinUnique.Lin2.OddRank
