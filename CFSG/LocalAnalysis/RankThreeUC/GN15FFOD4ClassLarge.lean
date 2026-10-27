module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeSetup
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeBounds
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeTypes
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4LargeDescent
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
open CFSG.Quasithin CFSG.QuasithinUnique.Setup
open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Periods


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

private theorem chi_dC_pow_card_D4 {ρ : Representation k (adjointGroup .D4 K) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : adjointGroup .D4 K → k}
    {J : Finset (Fin Tag.D4.rank)} (ht : IsChevType .D4 K 2 hw ρ y χ J) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (i : Fin Tag.D4.rank) (t : Kˣ) :
    χ (dC .D4 K i t) ^ (2 ^ n) = χ (dC .D4 K i t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  have hpow : ∀ N : ℕ, χ (dC .D4 K i (t ^ N)) = χ (dC .D4 K i t) ^ N := by
    intro N
    induction N with
    | zero => rw [pow_zero, dC_one, pow_zero]; exact hμ.chi_one
    | succ N ih =>
      rw [pow_succ, dC_mul, hμ.chi_mul (dC_mem_H i _) (dC_mem_H i _), ih, pow_succ]
  have h1 : t ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := t)
    rwa [Nat.card_units, hK] at this
  have h2 : χ (dC .D4 K i t) ^ (2 ^ n - 1) = 1 := by
    rw [← hpow, h1, dC_one]
    exact hμ.chi_one
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc χ (dC .D4 K i t) ^ (2 ^ n) = χ (dC .D4 K i t) ^ (2 ^ n - 1) * χ (dC .D4 K i t) := by
        rw [← pow_succ]; congr 1; omega
    _ = χ (dC .D4 K i t) := by rw [h2, one_mul]

end Periods

theorem exists_natural_of_quadratic_offender_four_le
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (L E : Subgroup (MulAut V)) (θ : L ≃* orthElementaryGroup (quadPlus 4 K))
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hE : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    (hEq : IsQuadratic E) (hoff : Nat.card V ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ (ψ : L ≃* orthElementaryGroup (quadPlus 4 K)) (φ : Additive V ≃+ (Fin 4 ⊕ Fin 4 → K)),
      ∀ (l : L) (v : V), φ (Additive.ofMul ((l : MulAut V) v)) =
        (ψ l : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (φ (Additive.ofMul v)) := by
  classical
  have _hEq := hEq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hKn⟩ : ∃ n : ℕ, Nat.card K = 2 ^ n := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hn2 : 2 ≤ n := by
    by_contra h
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn1 : 1 ≤ n := by omega
  let ι : adjointGroup .D4 K ≃* L := (eta K).trans θ.symm
  obtain ⟨δ, m, k, _, _, _, _, ρ, ν, hδ, -, hρ, hinj, hνinj, hcardV, hνeq, hrank, hent⟩ :=
    exists_periodic_rep hV hirr ι hn1 hKn
  have hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α :=
    ⟨_, invWord_four_smul⟩
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (p := 2) (hw := hw) hρ
  have hδper : ∀ (i : Fin Tag.D4.rank) (z : Kˣ),
      χ (dC .D4 K i z) ^ (2 ^ δ) = χ (dC .D4 K i z) :=
    fun i z => chi_pow_of_entries δ hρ hent ht _ (dC_mem_H i z)
  have hnper : ∀ (i : Fin Tag.D4.rank) (z : Kˣ),
      χ (dC .D4 K i z) ^ (2 ^ n) = χ (dC .D4 K i z) :=
    fun i z => chi_dC_pow_card_D4 hρ ht hKn i z
  have hg : 1 ≤ Nat.gcd δ n := Nat.gcd_pos_of_pos_right _ (by omega)
  have hgn : Nat.gcd δ n ∣ n := Nat.gcd_dvd_right δ n
  have hgδ : Nat.gcd δ n ≤ δ := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left δ n)
  have hper : ∀ (i : Fin 4) (z : Kˣ),
      χ (dC .D4 K i z) ^ (2 ^ Nat.gcd δ n) = χ (dC .D4 K i z) :=
    fun i z => pow_two_pow_gcd _ δ n (hδper i z) (hnper i z)
  have hgt : Nat.gcd δ n * (n / Nat.gcd δ n) = n := Nat.mul_div_cancel' hgn
  have hnδ : n / Nat.gcd δ n = 1 → n ≤ δ := by
    intro h1
    have h2 : Nat.gcd δ n = n := Nat.eq_of_dvd_of_div_eq_one hgn h1
    rw [← h2]
    exact hgδ
  obtain ⟨x, hxL, hx1, hx2, hxV⟩ :=
    exists_involution_card_le_of_offender hn1 hKn hV L E θ hirr hEN hE hEel hoff
  let g₀ : adjointGroup .D4 K := ι.symm ⟨x, hxL⟩
  have hιg₀ : ((ι g₀ : L) : MulAut V) = x := by simp [g₀]
  have hg₀2 : g₀ * g₀ = 1 := by
    have h : (⟨x, hxL⟩ : L) * ⟨x, hxL⟩ = 1 := Subtype.ext hx2
    change ι.symm ⟨x, hxL⟩ * ι.symm ⟨x, hxL⟩ = 1
    rw [← map_mul, h, map_one]
  have hg₀1 : g₀ ≠ 1 := by
    intro h
    apply hx1
    rw [← hιg₀, h, map_one]
    rfl
  have hrk : δ * Module.finrank k (LinearMap.range (ρ g₀ - 1)) ≤ 7 * n + 2 := by
    have h1 := hrank g₀
    rw [hιg₀] at h1
    have : Nonempty {v : V // x v = v} := ⟨⟨1, map_one x⟩⟩
    have hpos : 0 < Nat.card {v : V // x v = v} := Nat.card_pos
    have h2 : 2 ^ (δ * Module.finrank k (LinearMap.range (ρ g₀ - 1))) ≤ 2 ^ (7 * n + 2) := by
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      rw [← h1]
      exact hxV
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  rcases d4_type_bound hn1 hKn hρ hinj ht hg hgn hper with
    ⟨h1, b, σ, β, -, hβ⟩ | hdim | ⟨h1, h9⟩ | ⟨h2, h7⟩
  ·
    have hm8 : m = 8 := by
      have := β.finrank_eq
      simpa using this
    refine exists_natural_of_frobNat hV θ hirr ρ ν hνinj (fun g v => hνeq g v) b σ β hβ ?_
    rw [hcardV, hKn, hm8, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right 8 (hnδ h1))
  ·
    exfalso
    have hlt := card_lt_of_quadratic_offender hV L E θ hirr hEN hE hEel hoff
    rw [hcardV, hKn] at hlt
    have hlt' : δ * m < 28 * n + 2 := by
      have h3 : 2 ^ (δ * m) < 2 ^ (28 * n + 2) := by
        calc 2 ^ (δ * m) < 4 * (2 ^ n) ^ 28 := hlt
          _ = 2 ^ (28 * n + 2) := by rw [← pow_mul, pow_add]; ring
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h3
    rw [Module.finrank_fin_fun] at hdim
    have h3 : Nat.gcd δ n * (28 * (n / Nat.gcd δ n) + 2) ≤ δ * m := Nat.mul_le_mul hgδ hdim
    have h4 : Nat.gcd δ n * (28 * (n / Nat.gcd δ n) + 2) = 28 * n + 2 * Nat.gcd δ n := by
      calc Nat.gcd δ n * (28 * (n / Nat.gcd δ n) + 2)
          = 28 * (Nat.gcd δ n * (n / Nat.gcd δ n)) + 2 * Nat.gcd δ n := by ring
        _ = 28 * n + 2 * Nat.gcd δ n := by rw [hgt]
    omega
  ·
    exfalso
    have h3 : n * 9 ≤ δ * Module.finrank k (LinearMap.range (ρ g₀ - 1)) :=
      Nat.mul_le_mul (hnδ h1) (h9 g₀ hg₀2 hg₀1)
    omega
  ·
    exfalso
    have h3 : Nat.gcd δ n * (7 * (n / Nat.gcd δ n) + 3) ≤
        δ * Module.finrank k (LinearMap.range (ρ g₀ - 1)) :=
      Nat.mul_le_mul hgδ (h7 g₀ hg₀2 hg₀1)
    have h4 : Nat.gcd δ n * (7 * (n / Nat.gcd δ n) + 3) = 7 * n + 3 * Nat.gcd δ n := by
      calc Nat.gcd δ n * (7 * (n / Nat.gcd δ n) + 3)
          = 7 * (Nat.gcd δ n * (n / Nat.gcd δ n)) + 3 * Nat.gcd δ n := by ring
        _ = 7 * n + 3 * Nat.gcd δ n := by rw [hgt]
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
