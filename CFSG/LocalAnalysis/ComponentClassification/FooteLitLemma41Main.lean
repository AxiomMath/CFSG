module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41Outer
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_three_and_eq_two_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h : p ^ f = 9) :
    p = 3 ∧ f = 2 := by
  have h3 : 3 ∣ p ^ f := by rw [h]; norm_num
  have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  refine ⟨hp3, ?_⟩
  rw [hp3, show (9 : ℕ) = 3 ^ 2 by norm_num] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h

theorem foote_lemma_4_1 (hLB : FooteLBalanceInput) (hOut : FooteL2OutAbelian)
    (hAb : FooteL2AbelianCore) (h9 : FooteL2NineOddInner) (hRk : FooteL2RankThree)
    (hT32 : ∀ {a b : G}, orderOf a = 2 → a * b = b * a → ∀ {K : Subgroup G},
      IsTwoComponentAt b K →
      ¬ ⁅oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G),
        oddCoreOfCentralizer a ⊓ centralizer ({b} : Set G)⁆ ≤ coreActionKernel K →
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p f)
    {E V : Subgroup G} (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1)
    (h8 : Nat.card E = 8) (hV : IsKleinFour V) (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (K : G → Subgroup G)
    (hKN : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      centralizer ({b} : Set G) ⊓ centralizer ({v} : Set G) ≤ normalizer (K b : Set G))
    (hVK : ∀ b ∈ E, b ≠ 1 → V ≤ K b)
    (hKs : ∀ b ∈ E, b ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      Group.IsSolvable ↥(K b ⊓ centralizer ({v} : Set G)))
    {a : G} (ha : a ∈ E) (ha1 : a ≠ 1) :
    ⁅oddCoreOfCentralizer a, V⁆ ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer (V : Set G)) := by
  have : IsKleinFour V := hV
  have hord : orderOf a = 2 := orderOf_eq_prime (hexp a ha) ha1
  have ha2 : a * a = 1 := by rw [← sq]; exact hexp a ha
  have hsqV : ∀ x ∈ V, x * x = 1 := fun x hx =>
    congrArg Subtype.val (@IsKleinFour.mul_self V _ hV ⟨x, hx⟩)
  have hcommV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.mp (@IsKleinFour.isMulCommutative V _ hV)
      ⟨x, hx⟩ ⟨y, hy⟩)
  have hEV : ∀ e ∈ E, ∀ x ∈ V, x * e = e * x := fun e he x hx =>
    (mem_centralizer_iff.mp (hVE e he)) x hx
  have haV : V ≤ centralizer ({a} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hEV a ha x hx)
  refine inf_centralizer_le_oddCoreIn_of_forall hLB hV hord haV
    fun v hv hv1 w hw hw1 hwv J hJv hJ hJa haJ => ?_
  have hvord : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hsqV v hv) hv1
  have hav : a * v = v * a := (hEV a ha v hv).symm
  have hwC : w ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hcommV w hw v hv)
  set Y := oddCoreOfCentralizer a ⊓ centralizer ({v} : Set G) with hY
  have hwY : w ∈ normalizer (Y : Set G) := mem_normalizer_inf'
    (mem_normalizer_oddCoreOfCentralizer (haV hw)) (mem_normalizer_centralizer_singleton
      (hcommV w hw v hv))
  have hXY : ⁅Y, zpowers w⁆ ≤ Y := commutator_le_self_of_le_normalizer (zpowers_le.mpr hwY)
  by_cases hYK : ⁅Y, Y⁆ ≤ coreActionKernel J
  · exact (commutator_mono hXY hXY).trans hYK
  obtain ⟨p, f, hp, hp2, hf, hL⟩ := hT32 hord hav ⟨hvord, hJv, hJ⟩ hYK
  have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) := isQuasisimple_quotient_of_isPComponent hJv hJ
  have hYN : Y ≤ normalizer (J : Set G) :=
    oddCoreOfCentralizer_inf_le_normalizer hLB hord hav hJv hJ
  have haN : a ∈ normalizer (J : Set G) := mem_normalizer_of_conjugate_eq hJa
  have hYa : Y ≤ centralizer ({a} : Set G) :=
    inf_le_left.trans (oddCoreOfCentralizer_le_centralizer a)
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le inf_le_left)
  have hCY : ∀ k ∈ J, k * a = a * k → k ∈ normalizer (Y : Set G) := fun k hk hka =>
    mem_normalizer_inf' (mem_normalizer_oddCoreOfCentralizer
      (mem_centralizer_singleton_iff.mpr hka)) (le_normalizer (hJv hk))
  have hS : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f := ⟨p, f, hp, hp2, hf, hL⟩
  by_cases hp9 : p ^ f = 9
  · exfalso
    obtain ⟨rfl, rfl⟩ := eq_three_and_eq_two_of_pow_eq_nine hp hp9
    exact hYK (commutator_le_coreActionKernel_of_oddOuterInner hAb hJq hS (h9 _ hL) hYN haN ha2
      haJ hYa hYodd hCY)
  by_cases hwN : w ∈ normalizer (J : Set G)
  · exact commutator_le_coreActionKernel_of_inner hOut hAb hJq hS hYN hwN haN ha2 haJ hYa hYodd
      hCY hwY
  exfalso
  have hwJ : conjugate J w ≠ J := fun h => hwN (mem_normalizer_of_conjugate_eq h)
  have hEv : E ≤ centralizer ({v} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hEV e he v hv).symm
  exact false_of_conjugate_ne hLB hRk hEc hexp h8 ha hvord hEv hwC (hsqV w hw) hJv hJ hJq
    ⟨p, f, hp, hp2, hf, hp9, hL⟩ hJa haJ hwJ K (fun b hb hb1 => hKN b hb hb1 v hv hv1)
    (fun b hb hb1 => hVK b hb hb1 hw)
    (fun b hb hb1 => hKs b hb hb1 v hv hv1)

end CFSG.ComponentClassification.FooteLit
