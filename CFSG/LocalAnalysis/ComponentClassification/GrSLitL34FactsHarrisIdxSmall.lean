module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.HarrisLit (fixedPoints innAut twoPart IsTwoComponentIn)

theorem dvd_ordA_one {q : ℕ} (hq : Odd q) : q ∣ Open.ordA 1 q := by
  obtain ⟨k, rfl⟩ := hq
  have hIcc : Finset.Icc 2 (1 + 1) = {2} := by decide
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have h2 : 2 ∣ (2 * k + 1) ^ 2 - 1 := ⟨2 * k * k + 2 * k, by ring_nf; omega⟩
  unfold Open.ordA
  rw [hIcc, Finset.prod_singleton, hg, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one,
    Nat.mul_div_assoc _ h2]
  exact dvd_mul_right _ _

theorem not_pow_dvd_1920 {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) : ¬ p ^ m ∣ 1920 := by
  intro h
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  have h15 : p ^ m ∣ 15 :=
    (Nat.Coprime.pow_right 7 hodd.coprime_two_right).dvd_of_dvd_mul_left
      (by norm_num; exact h)
  have hp15 : p ∣ 3 * 5 := (dvd_pow_self p (by omega)).trans h15
  have hp35 : p = 3 ∨ p = 5 := by
    rcases (Nat.Prime.dvd_mul hp).1 hp15 with h3 | h5
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5)
  have hm1 : m = 1 := by
    by_contra hne
    have hm2 : 2 ≤ m := by omega
    have hsq : p ^ 2 ∣ 15 := (pow_dvd_pow p hm2).trans h15
    rcases hp35 with rfl | rfl <;> norm_num at hsq
  subst hm1
  rcases hp35 with rfl | rfl <;> norm_num at h16

theorem not_pow_dvd_64 {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    ¬ p ^ m ∣ 64 := by
  intro h
  have h2 : p ∣ 2 ^ 6 := (dvd_pow_self p (show m ≠ 0 by omega)).trans (by norm_num; exact h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))

theorem pow_dvd_card_fixedPoints {Y : Type} [Group Y] [Finite Y] {τ : MulAut Y}
    {K : Subgroup Y} (hK : IsTwoComponentIn K (fixedPoints τ)) {p m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m) :
    p ^ m ∣ Nat.card (fixedPoints τ) := by
  have h1 := GSThmB.card_of_lieModel_psl_two hp2 hL
  have h2 : p ^ m ∣ Open.ordA 1 (p ^ m) := dvd_ordA_one (hp.odd_of_ne_two hp2).pow
  have h3 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card K ∣ Nat.card (fixedPoints τ) := Subgroup.card_dvd_of_le hK.1
  rw [h1] at h3
  exact h2.trans (h3.trans h4)

open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four in
theorem card_fixedPoints_psl34 {σ : MulAut ↥S}
    (hσ : orderOf σ = 2) :
    Nat.card (fixedPoints σ) = 64 ∨ Nat.card (fixedPoints σ) = 168 ∨
      Nat.card (fixedPoints σ) = 60 ∨ Nat.card (fixedPoints σ) = 72 := by
  obtain ⟨eR, heR, -⟩ := full_automorphism_action
  set x := eR.symm σ with hx
  have hx2 : orderOf x = 2 := by rw [hx, MulEquiv.orderOf_eq]; exact hσ
  have hσx : ∀ s : S, ((σ s : S) : Equiv.Perm (Fin 42)) = x * s * (x : Equiv.Perm (Fin 42))⁻¹ := by
    intro s
    rw [show σ = eR x by rw [hx, MulEquiv.apply_symm_apply], heR, Subgroup.coe_inv]
  rw [card_fixedPoints_eq_inf_centralizer hσx]
  have hnorm : ∀ {c : Equiv.Perm (Fin 42)}, c ∈ R → ∀ t,
      Nat.card ↥(S ⊓ centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 42)))) =
        Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 42))) ⊓ S) := by
    intro c hc t
    rw [inf_centralizer_conj_eq' (fun p hp => conj_mem_S hc hp) (fun p hp => by
      have := conj_mem_S (R.inv_mem hc) hp
      rwa [inv_inv] at this) t, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      inf_comm]
  rcases (PSL3Four.orderOf_eq_two_iff x).1 hx2 with h | h | h | h
  · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
    left
    rw [hxc, hnorm hc]
    exact card_C₁
  · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
    right; left
    rw [hxc, hnorm hc]
    exact card_C₂
  · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
    right; right; left
    rw [hxc, hnorm hc]
    exact card_C₃
  · obtain ⟨c, hc, hxc⟩ := eq_conj_of_isConj h
    right; right; right
    rw [hxc, hnorm hc]
    exact card_C₄

theorem harris415SmallTypesIndex :
    ∀ (Y : Type) [Group Y] [Finite Y],
      (Nonempty (Y ≃* Blueprint.NativeSporadic.J2) ∨ Nonempty (Y ≃* Blueprint.NativeSporadic.J3) ∨
        Blueprint.LieModel Y .PSL 3 2 2) →
      ∀ τ : MulAut Y, orderOf τ = 2 →
      ∀ K : Subgroup Y, IsTwoComponentIn K (fixedPoints τ) →
      ∀ p m : ℕ, p.Prime → p ≠ 2 → 1 ≤ m → 16 ∣ p ^ (2 * m) - 1 →
        Blueprint.LieModel (↥K ⧸ pPrimeCore 2 ↥K) .PSL 2 p m →
        4 * twoPart (fixedPoints τ) ≤ twoPart (⊤ : Subgroup Y) := by
  intro Y _ _ hY τ hτ K hK p m hp hp2 hm h16 hL
  have hKd := pow_dvd_card_fixedPoints hK hp hp2 hL
  rcases hY with he | he | hL34
  ·
    obtain ⟨e⟩ := he
    set ψ := e.trans j2PermEquiv with hψ
    obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
      ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
    obtain ⟨r, hr, hcard, -⟩ := exists_row_of_autModel j2_autModel
      (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩) hcover
      (σ := MulAut.congr ψ τ) (by rw [orderOf_congr]; exact hτ)
    rw [card_fixedPoints_congr] at hcard
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(true, 1800, 336), (false, 2520, 240), (false, 315, 1920)] := by
      rw [← hmap]
      exact List.mem_map_of_mem hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    have htop : twoPart (⊤ : Subgroup Y) = 2 ^ 7 :=
      twoPart_top_eq (m := 4725) ⟨2362, rfl⟩
        (by rw [Nat.card_congr ψ.toEquiv, card_j2P]; norm_num)
    have h1 : twoPart (fixedPoints τ) ≤ 2 ^ 4 := by
      rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · exact twoPart_le_of_dvd_mul (m := 21) ⟨10, rfl⟩ (by rw [hcard, h]; norm_num)
      · exact twoPart_le_of_dvd_mul (m := 15) ⟨7, rfl⟩ (by rw [hcard, h]; norm_num)
      · rw [hcard, h] at hKd
        exact absurd hKd (not_pow_dvd_1920 hp hp2 hm h16)
    rw [htop]
    norm_num at h1 ⊢
    omega
  ·
    obtain ⟨e⟩ := he
    set ψ := e.trans j3PermEquiv with hψ
    obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
      ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
    obtain ⟨r, hr, hcard, -⟩ := exists_row_of_autModel j3_autModel
      (fun r hr => ⟨(hrows r hr).1, (hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩) hcover
      (σ := MulAut.congr ψ τ) (by rw [orderOf_congr]; exact hτ)
    rw [card_fixedPoints_congr] at hcard
    have hmem : (r.outer, r.classSize, r.centOrder) ∈
        [(false, 26163, 1920), (true, 20520, 2448)] := by
      rw [← hmap]
      exact List.mem_map_of_mem hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    have htop : twoPart (⊤ : Subgroup Y) = 2 ^ 7 :=
      twoPart_top_eq (m := 392445) ⟨196222, rfl⟩
        (by rw [Nat.card_congr ψ.toEquiv, card_j3P]; norm_num)
    have h1 : twoPart (fixedPoints τ) ≤ 2 ^ 4 := by
      rcases hmem with ⟨-, -, h⟩ | ⟨-, -, h⟩
      · rw [hcard, h] at hKd
        exact absurd hKd (not_pow_dvd_1920 hp hp2 hm h16)
      · exact twoPart_le_of_dvd_mul (m := 153) ⟨76, rfl⟩ (by rw [hcard, h]; norm_num)
    rw [htop]
    norm_num at h1 ⊢
    omega
  ·
    obtain ⟨ψ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hL34
    have hcard := card_fixedPoints_psl34 (σ := MulAut.congr ψ τ) (by rw [orderOf_congr]; exact hτ)
    rw [card_fixedPoints_congr] at hcard
    have htop : twoPart (⊤ : Subgroup Y) = 2 ^ 6 :=
      twoPart_top_eq (m := 315) ⟨157, rfl⟩
        (by rw [Nat.card_congr ψ.toEquiv, PSL3Four.card_S]; norm_num)
    have h1 : twoPart (fixedPoints τ) ≤ 2 ^ 3 := by
      rcases hcard with h | h | h | h
      · rw [h] at hKd
        exact absurd hKd (not_pow_dvd_64 hp hp2 hm)
      · exact twoPart_le_of_dvd_mul (m := 21) ⟨10, rfl⟩ (by rw [h]; norm_num)
      · exact twoPart_le_of_dvd_mul (m := 15) ⟨7, rfl⟩ (by rw [h]; norm_num)
      · exact twoPart_le_of_dvd_mul (m := 9) ⟨4, rfl⟩ (by rw [h]; norm_num)
    rw [htop]
    norm_num at h1 ⊢
    omega

end CFSG.ComponentClassification.GrSLit.L34Facts
